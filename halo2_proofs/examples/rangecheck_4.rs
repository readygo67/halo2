use std::marker::PhantomData;
use group::ff::PrimeField;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};


fn num_of_bits(v:usize) -> usize{
    if v == 0 {
       return 1
    }

    let mut n = v;
    let mut n_bits = 0;
    while n > 0 {
        n >>=1;
        n_bits += 1;
    }
    
    n_bits

}

#[derive(Debug, Clone)]
pub struct RangeTable<F:PrimeField> {
    pub value: TableColumn,
    pub n_bits: TableColumn,
    _maker: PhantomData<F>
}

impl<F:PrimeField> RangeTable<F>{
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self{
        let n_bits = meta.lookup_table_column();
        let value = meta. lookup_table_column();

        RangeTable{
            value: value,
            n_bits: n_bits,
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
                        || format!("load value {}", value),
                        self.value,
                        offset,
                        || Value::known(F::from(value as u64)),
                    )?;

                    let n_bits = num_of_bits(value);
                    table.assign_cell(
                        || format!("load n_bits of  {}", value),
                        self.n_bits,
                        offset,
                        || Value::known(F::from(n_bits as u64)),
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
        n_bits: Value<F>,
    ) -> Result<(AssignedCell<F,F>, AssignedCell<F,F>), Error>;
}

#[derive(Clone, Debug)]
pub struct RangeCheckConfig<F:PrimeField> {
    range:usize,
    value: Column<Advice>,
    n_bits: Column<Advice>,
    q_lookup: Selector,
    table: RangeTable<F>,
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
        range:usize,
        value: Column<Advice>,
        n_bits: Column<Advice>,
        q_lookup: Selector,
    ) -> RangeCheckConfig<F> {       
        let table= RangeTable::<F>::configure(meta);

        meta.lookup(|meta| {
            let sel = meta.query_selector(q_lookup);
            let mut v = meta.query_advice(value, Rotation::cur());
            let mut b = meta.query_advice(n_bits, Rotation::cur());

            let default_value = Expression::Constant(F::ZERO);
            let default_bit = Expression::Constant(F::ONE);
            let non_sel = Expression::Constant(F::ONE) - sel.clone();

            v = v * sel.clone(); //+ default_value * non_sel.clone();
            b = b * sel; //+ default_bit * non_sel;

            vec![(v, table.value), (b, table.n_bits)]
        });

        RangeCheckConfig {
            range,
            value, 
            n_bits,
            q_lookup,
            table,
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
        n_bits: Value<F>,
    ) -> Result<(AssignedCell<F,F>, AssignedCell<F,F>), Error>{
        let config = self.config.clone();
        layouter.assign_region(
            || "assign value ",
            |mut region: Region<'_, F>| {
                //enable the range check，填充cell，并将
                config.q_lookup.enable(&mut region, 0)?; //

                let value_cell = region.assign_advice(||"value", config.value, 0, || value)?;
                let bits_cell = region.assign_advice(||"n_bits", config.n_bits, 0, || n_bits)?;
                
                Ok((value_cell, bits_cell))
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
        pub n_bits: Value<F>
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
            let value = meta.advice_column();
            let n_bits = meta.advice_column();
            let q_lookup = meta.complex_selector();
    
            RangeCheckChip::configure(meta, RANGE, value,  n_bits, q_lookup)
        }
        
        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            //load table
            config.table.load(&mut layouter, RANGE)?;  //initialze the table 

            // 构建一个chip
            let rang_check_chip = RangeCheckChip::<F>::construct(config);
            let res = rang_check_chip.check(layouter.namespace(|| "check"), self.value, self.n_bits)?;
            println!("res: {:?}", res);
            
            Ok(())
        }
    }

    #[test]
    fn test_num_of_bits(){
        assert_eq!(1, num_of_bits(0));
        assert_eq!(1, num_of_bits(1));
        assert_eq!(2, num_of_bits(2));
        assert_eq!(2, num_of_bits(3));
        assert_eq!(3, num_of_bits(4));
        assert_eq!(3, num_of_bits(5));
        assert_eq!(3, num_of_bits(6));
        assert_eq!(3, num_of_bits(7));
        assert_eq!(8, num_of_bits(255));
        assert_eq!(9, num_of_bits(256));
    }

    #[test]
    fn test_circuit_in_range() {
        let k = 9;
        const RANGE: usize = 256; // 3-bit value
 
        // Instantiate the circuit with the private inputs.
        for i in 0..RANGE {
            let circuit = RangeCheckCircuit::<Fp, RANGE> {
                value: Value::known(Fp::from(i as u64)),
                n_bits: Value::known(Fp::from(num_of_bits(i) as u64)),
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }    
    }
    


    #[test]
    fn test_circuit_in_range_2() {
        let k = 4;
        const RANGE: usize = 8; // 3-bit value

        let mut circuit = RangeCheckCircuit::<Fp, RANGE> {
            value: Value::unknown(),
            n_bits: Value::unknown(),
        };

        circuit.value  = Value::known(Fp::from(3));
        circuit.n_bits = Value::known(Fp::from(num_of_bits(3) as u64));
        let mut  prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_get_table_contents() {
        let k = 4;
        const RANGE: usize = 8; // 3-bit value

        let mut circuit = RangeCheckCircuit::<Fp, RANGE> {
            value: Value::known(Fp::from((1) as u64)),
            n_bits: Value::known(Fp::from(num_of_bits(1) as u64)),
        };

        circuit.value  = Value::known(Fp::from(3));
        circuit.n_bits = Value::known(Fp::from(num_of_bits(3) as u64));
        let mut  prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }



    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_multi_cols_rangecheck_lookup() {
        // Instantiate the circuit with the private inputs.
        let k = 4;
        let circuit = circuit();
        // Create the area you want to draw on.
        // Use SVGBackend if you want to render to .svg instead.
        use plotters::prelude::*;
        let root = BitMapBackend::new("./circuit_layouter_plots/chap_4_multi_cols_rangecheck_lookup.png", (1024, 768))
            .into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Lookup2 Circuit", ("sans-serif", 60)).unwrap();

        halo2_proofs::dev::CircuitLayout::default()
            // You can optionally render only a section of the circuit.
            // .view_width(0..2)
            // .view_height(0..16)
            // You can hide labels, which can be useful with smaller areas.
            .show_labels(true)
            // Render the circuit onto your area!
            // The first argument is the size parameter for the circuit.
            .render(5, &circuit, &root)
            .unwrap();
    }

}