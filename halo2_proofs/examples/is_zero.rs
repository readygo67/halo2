use group::ff::PrimeField;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};


// ANCHOR: instructions
trait Instructions<F: PrimeField>: Chip<F> { 
    /// 非约束版本的数值计算。
    fn check(
        &self,
        layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> Result<Value<F>, Error>;
}

#[derive(Clone, Debug)]
pub struct IsZeroConfig<F:PrimeField> {
    advices: [Column<Advice>;3],
    // value: Column<Advice>,
    // value_inv: Column<Advice>,
    // is_zero: Column<Advice>,
    pub is_zero_expr: Expression<F>,  //
}

// impl<F: PrimeField> IsZeroConfig<F> {
//     pub fn expr(&self) -> Expression<F> {
//         self.is_zero_expr.clone()
//     }
// }

pub struct IsZeroChip<F: PrimeField> {
    config: IsZeroConfig<F>,
}

impl<F: PrimeField> IsZeroChip<F> {
    pub fn construct(config: IsZeroConfig<F>) -> Self {
        IsZeroChip { config }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        // value: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        // value_inv: Column<Advice>,
        advices: [Column<Advice>; 3],
    ) -> IsZeroConfig<F> {
        let mut is_zero_expr = Expression::Constant(F::ZERO);

        meta.create_gate("is_zero", |meta| {
            //
            //IsZero Chip 需要通过
            // 1. value * (1 - value* value_inv)=0 检查有效性，防止恶意攻击者。
            // 2. 假设is_zero是synthesize 时的结果，那么可以比较synthesize阶段和 verify 阶段的结果， 即检查 is_zero = 1 - value * value_inv
            //   实际使用的时候，可以省略is_zero ，直接返回is_zero_expr，减少不必要的约束，
            //
            //
            // valid | value |  value_inv |  1 - value * value_inv | value * (1 - value* value_inv) ｜  is_zero
            // ------+-------+------------+------------------------+------------------------------- ｜----------------
            //  yes  |   x   |    1/x     |         0              |  0                             ｜     0
            //  no   |   x   |    0       |         1              |  x(恶意填value_inv,无法通过检查)  ｜     
            //  yes  |   0   |    0       |         1              |  0                             |      1
            //  yes  |   0   |    y       |         1              |  0                             |      1
            //
            let value = meta.query_advice(advices[0], Rotation::cur());
            let value_inv = meta.query_advice(advices[1], Rotation::cur());
            let is_zero = meta.query_advice(advices[2], Rotation::cur());   //check result in synthesize stage

            let q_enable = q_enable(meta);
            is_zero_expr = Expression::Constant(F::ONE) - value.clone() * value_inv;

            vec![q_enable.clone() * value * is_zero_expr.clone(), q_enable*(is_zero - is_zero_expr.clone())]
        });

        IsZeroConfig {
            advices,
            is_zero_expr,
        }
    }

}

impl<F: PrimeField> Chip<F> for IsZeroChip<F> {
    type Config = IsZeroConfig<F>;
    type Loaded = (); //综合时需要,可以理解为chip的初始状态

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()  //返回对空元组的不可变引用。
    }
}

impl <F: PrimeField>  Instructions<F> for IsZeroChip<F> {
    fn check(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> Result<Value<F>, Error>{
        let value_inv = value.map(|value| value.invert().unwrap_or(F::ZERO));
        let is_zero  = Value::known(F::ONE) - value.clone() * value_inv;
    
        layouter.assign_region(
            || "check",
            |mut region: Region<'_, F>| {

                let value_cell = region.assign_advice(|| "value", self.config.advices[0], 0, || value)?;
                let value_inv_cell= region.assign_advice(|| "value_inv", self.config.advices[1], 0, || value_inv)?;
                let is_zero_cell = region.assign_advice(|| "is_zero", self.config.advices[2], 0,||is_zero)?;
                
                println!("check value");
                println!("value: {:?}", value_cell);
                println!("value_inv: {:?}", value_inv_cell);
                println!("is_zero: {:?}", is_zero_cell);
                Ok(is_zero)
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
    struct IsZeroCircuit<F: PrimeField> {
        value: Value<F>,
    }

    impl<F: PrimeField> Circuit<F> for IsZeroCircuit<F> {
        // Since we are using a single chip for everything, we can just reuse its config.
        //此电路只包含一个chip，因此可以复用它的config
        type Config = IsZeroConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;
    
        fn without_witnesses(&self) -> Self {
            Self::default()
        }
        //把本电路的的config，为chip 分配资源。
        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            // We create the two advice columns that IsZeroChip uses for I/O.
            let advices = [meta.advice_column(), meta.advice_column(), meta.advice_column()];
            let enable = meta.selector();
    
            IsZeroChip::configure(meta, 
                |meta| {meta.query_selector(enable)}, advices)
        }
        

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // 构建一个chip
            let zero_chip = IsZeroChip::<F>::construct(config);
         
            let res = zero_chip.check(layouter.namespace(|| "check"), self.value)?;
            println!("res: {:?}", res);
            
            Ok(())
        }
    }



    #[test]
    fn test_expression() {

        let one = Expression::Constant(Fp::one());
        println!("one: {:?}", one);
        let zero = Expression::Constant(Fp::zero());
        println!("zero: {:?}", zero);
    }

    #[test]
    fn test_circuit() {
        let k = 4;
 
        // Instantiate the circuit with the private inputs.
        let circuit = IsZeroCircuit {
            value: Value::known(Fp::from(100)),
        };

        // Arrange the public input. We expose the multiplication result in row 0
        // of the instance column, so we position it there in our public inputs.
        // let public_inputs = vec![];

        // Given the correct public input, our circuit will verify.
        let prover = MockProver::<Fp>::run(k as u32, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
        
    }


}