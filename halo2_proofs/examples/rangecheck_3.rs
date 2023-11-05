use std::marker::PhantomData;
use group::ff::PrimeField;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};


#[derive(Debug, Clone)]
pub struct RangeTableConfig<F:PrimeField> {
    pub table_col: TableColumn,
    _maker: PhantomData<F>
}

impl<F:PrimeField> RangeTableConfig<F>{
    pub fn configure(table_col:TableColumn) -> Self{
        RangeTableConfig{
            table_col: table_col,
            _maker: PhantomData
        }
    }

    //load table contents
    pub fn load(&self, layouter: &mut impl Layouter<F>, range:usize) -> Result<(), Error> {
        layouter.assign_table(
            || "load range-check table",
            |mut table| {
                let mut offset = 0;
                for value in 0..range {
                    table.assign_cell(
                        || format!("load {}", value),
                        self.table_col,
                        offset,
                        || Value::known(F::from(value as u64)),
                    )?;
                    offset += 1;
                }

                Ok(())
            },
        )
    }


} 


// ANCHOR: instructions
trait Instructions<F: PrimeField>: Chip<F> { 
    /// 非约束版本的数值计算。
    fn check(
        &self,
        layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedCell<F,F>, Error>;
}

#[derive(Clone, Debug)]
pub struct RangeCheckConfig<F:PrimeField> {
    range:usize,
    value_col: Column<Advice>,
    range_check_enable: Selector,
    table_config: RangeTableConfig<F>,
}

pub struct RangeCheckChip<F: PrimeField> {
    config: RangeCheckConfig<F>,
}

impl<F: PrimeField> RangeCheckChip<F> {
    pub fn construct(config: RangeCheckConfig<F>) -> Self {
        RangeCheckChip { config }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        range: usize,
        value_col :Column<Advice>,
        range_check_enable: Selector,
        table_col: TableColumn
    ) -> RangeCheckConfig<F> {       
        let table_config = RangeTableConfig::<F>::configure(table_col);
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(range_check_enable);
            let value = meta.query_advice(value_col, Rotation::cur());
    
            vec![(q_lookup * value, table_config.table_col)]  //从table_config中取出table_column
        });

        RangeCheckConfig {
            range,
            value_col,
            range_check_enable,
            table_config,
        }
    }

}

impl<F: PrimeField> Chip<F> for RangeCheckChip<F> {
    type Config = RangeCheckConfig<F>;
    type Loaded = (); //综合时需要,可以理解为chip的初始状态

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()  //返回对空元组的不可变引用。
    }
}

impl <F: PrimeField>  Instructions<F> for RangeCheckChip<F> {
    fn check(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedCell<F,F>, Error>{
        let config = self.config.clone();
        layouter.assign_region(
            || "assign value ",
            |mut region: Region<'_, F>| {
                //enable the range check，填充cell，并将
                config.range_check_enable.enable(&mut region, 0)?; //
                let value_cell = region.assign_advice(||"value", config.value_col, 0, || value)?;
                Ok(value_cell)
            }
        )
    }
}


fn main(){}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[derive(Default)]
    struct RangeCheckCircuit<F: PrimeField, const RANGE: usize> {
        pub value: Value<F>,
    }

    impl<F: PrimeField, const RANGE: usize> Circuit<F> for RangeCheckCircuit<F, RANGE> {
        // Since we are using a single chip for everything, we can just reuse its config.
        //此电路只包含一个chip，因此可以复用它的config
        type Config = RangeCheckConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;
    
        fn without_witnesses(&self) -> Self {
            Self::default()
        }
        //把本电路的的config，为chip 分配资源。
        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            // We create the two advice columns that IsZeroChip uses for I/O.
            let value_col = meta.advice_column();
            let selector = meta.complex_selector();
            let table_col = meta.lookup_table_column();

            RangeCheckChip::configure(meta, RANGE, value_col, selector,table_col)
        }
        
        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            //load table
            config.table_config.load(&mut layouter, RANGE)?;  //initialze the table 

            // 构建一个chip
            let rang_check_chip = RangeCheckChip::<F>::construct(config);
         
            let res = rang_check_chip.check(layouter.namespace(|| "check"), self.value)?;
            println!("res: {:?}", res);
            
            Ok(())
        }
    }

    #[test]
    fn test_circuit_in_range() {
        let k = 5;
        const RANGE: usize = 8; // 3-bit value

 
        // Instantiate the circuit with the private inputs.
        for i in 0..RANGE {
            let circuit: RangeCheckCircuit<Fp, 8> = RangeCheckCircuit::<Fp, RANGE> {
                value: Value::known(Fp::from(i as u64).into()),
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }    
    }


    #[test]
    fn test_circuit_in_range_2() {
        let k = 4;
        const RANGE: usize = 8; // 3-bit value

        //
        let mut circuit: RangeCheckCircuit<Fp, 8> = RangeCheckCircuit::<Fp, RANGE> {
            value: Value::known(Fp::from((1) as u64).into()),
        };

        circuit.value  = Value::known(Fp::from(2));
        let mut  prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        circuit.value  = Value::known(Fp::from(3));
        prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }


    #[test]
    fn test_circuit_out_of_range() {
        let k = 5;
        const RANGE: usize = 8; // 3-bit value

        //
        let circuit: RangeCheckCircuit<Fp, 8> = RangeCheckCircuit::<Fp, RANGE> {
            value: Value::known(Fp::from((10) as u64).into()),
        };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied(); 
    }

}