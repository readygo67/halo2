use std::marker::PhantomData;
use group::ff::PrimeField;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};


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
pub struct RangeCheckConfig<F:PrimeField, const RANGE: usize> {
    value_col: Column<Advice>,
    range_check_enable: Selector,
    _marker: PhantomData<F>,
}

pub struct RangeCheckChip<F: PrimeField, const RANGE: usize> {
    config: RangeCheckConfig<F, RANGE>,
}

impl<F: PrimeField, const RANGE:usize> RangeCheckChip<F, RANGE> {
    pub fn construct(config: RangeCheckConfig<F, RANGE>) -> Self {
        RangeCheckChip { config }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value_col :Column<Advice>,
        range_check_enable: Selector
    ) -> RangeCheckConfig<F, RANGE> {        
        meta.create_gate("range check ", |meta| {
            
            let q = meta.query_selector(range_check_enable);
            let value = meta.query_advice(value_col, Rotation::cur());
            
            // Given a range R and a value v, returns the expression
            // (v) * (1 - v) * (2 - v) * ... * (R - 1 - v), 这个范围是 0 <= v < R
            // expr = (v) * (v-1) * (v-2) * ... * (v-R-1)
            
            //The 1st implementation 
            /* 
            let mut expr = value.clone();
            for i in 1..RANGE{
                expr = expr * (value.clone() - Expression::Constant(F::from(i as u64)));
            }
            vec![q * expr]
            */
            
            //The 2nd implementation, use normal function
            /* 
            fn range_check<F:PrimeField> (range:usize, value:&Expression<F>)->Expression<F>{
                (0..range).fold(value.clone(), |expr, i| {
                    expr * (value.clone() - Expression::Constant(F::from(i as u64)))
                })
            }
            let expr = range_check(RANGE, &value);
            vec![q * expr]
            */

            //The 3rd implementation, use closue function
            let range_check = |range:usize, value:&Expression<F>|{
                (0..range).fold(value.clone(), |expr, i| {
                    expr * (value.clone() - Expression::Constant(F::from(i as u64)))
                })
            };
            Constraints::with_selector(q, [("range check", range_check(RANGE, &value))])
        });

        RangeCheckConfig {
            value_col,
            range_check_enable,
            _marker: PhantomData,
        }
    }

}

impl<F: PrimeField, const RANGE:usize> Chip<F> for RangeCheckChip<F, RANGE> {
    type Config = RangeCheckConfig<F, RANGE>;
    type Loaded = (); //综合时需要,可以理解为chip的初始状态

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()  //返回对空元组的不可变引用。
    }
}

impl <F: PrimeField, const RANGE:usize>  Instructions<F> for RangeCheckChip<F, RANGE> {
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
        type Config = RangeCheckConfig<F, RANGE>;
        type FloorPlanner = SimpleFloorPlanner;
    
        fn without_witnesses(&self) -> Self {
            Self::default()
        }
        //把本电路的的config，为chip 分配资源。
        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            // We create the two advice columns that IsZeroChip uses for I/O.
            let value_col = meta.advice_column();
            let selector = meta.selector();

            RangeCheckChip::configure(meta, value_col, selector)
        }
        
        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // 构建一个chip
            let rang_check_chip = RangeCheckChip::<F, RANGE>::construct(config);
         
            let res = rang_check_chip.check(layouter.namespace(|| "check"), self.value)?;
            println!("res: {:?}", res);
            
            Ok(())
        }
    }

    #[test]
    fn test_circuit_in_range_1() {
        let k = 4;
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
        let k = 4;
        const RANGE: usize = 8; // 3-bit value

        //
        let circuit: RangeCheckCircuit<Fp, 8> = RangeCheckCircuit::<Fp, RANGE> {
            value: Value::known(Fp::from((10) as u64).into()),
        };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());       
    }

}