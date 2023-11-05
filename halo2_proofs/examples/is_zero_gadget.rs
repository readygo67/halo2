use group::ff::PrimeField;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};


// ANCHOR: instructions
trait IsZeroInstructions<F: PrimeField>: Chip<F> { 
    /// 非约束版本的数值计算。
    fn check(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<Value<F>, Error>;
}

#[derive(Clone, Debug)]
pub struct IsZeroConfig<F:PrimeField> {
    value_inv: Column<Advice>,
    pub is_zero_expr: Expression<F>,  //
}

impl<F: PrimeField> IsZeroConfig<F> {
    pub fn expr(&self) -> Expression<F> {
        self.is_zero_expr.clone()
    }
}

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
        value: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value_inv: Column<Advice>,
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
            let q_enable = q_enable(meta);
            let value = value(meta);
            let value_inv = meta.query_advice(value_inv, Rotation::cur()); //在creat_gate中重复使用value_inv 变量名
            is_zero_expr = Expression::Constant(F::ONE) - value.clone() * value_inv;

            vec![q_enable.clone() * value * is_zero_expr.clone()]
        });

        IsZeroConfig {
            value_inv,
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

impl <F: PrimeField>  IsZeroInstructions<F> for IsZeroChip<F> {
    fn check(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<Value<F>, Error> {
        let value_inv = value.map(|value| value.invert().unwrap_or(F::ZERO));
        let is_zero = Value::known(F::ONE) - value.clone() * value_inv;

        let value_inv_cell = region.assign_advice(|| "value inv", self.config.value_inv, offset, || value_inv)?;
        println!("is_zero_chip, value_inv_cell: {:?}", value_inv_cell);
        Ok(is_zero)
    }
}



#[derive(Debug, Clone)]
struct FunctionConfig<F: PrimeField> {
    selector: Selector,
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    is_zero_chip_config: IsZeroConfig<F>, 
    output: Column<Advice>,
}

#[derive(Debug, Clone)]
struct FunctionChip<F: PrimeField> {
    config: FunctionConfig<F>,
}

impl<F: PrimeField> FunctionChip<F> {
    pub fn construct(config: FunctionConfig<F>) -> Self {
        Self { config }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FunctionConfig<F> {
        let selector = meta.selector();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let output = meta.advice_column();


        let value_inv_column = meta.advice_column();  //必须要用local 变量先存下来，否则报错
        let is_zero_chip_config = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(selector),
            |meta| meta.query_advice(a, Rotation::cur()) - meta.query_advice(b, Rotation::cur()),
            value_inv_column,
        );

        meta.create_gate("f(a, b, c) = if a == b {c} else {a - b}", |meta| {
            let s = meta.query_selector(selector);
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let output = meta.query_advice(output, Rotation::cur());
            vec![
                s.clone() * (is_zero_chip_config.expr() * (output.clone() - c)),  
                s * (Expression::Constant(F::ONE) - is_zero_chip_config.expr()) * (output - (a - b)),
            ]
        });

        FunctionConfig {
            selector,
            a,
            b,
            c,
            is_zero_chip_config,
            output,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        a: F,
        b: F,
        c: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero_chip = IsZeroChip::construct(self.config.is_zero_chip_config.clone());

        layouter.assign_region(
            || "f(a, b, c) = if a == b {c} else {a - b}",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                let a_cell = region.assign_advice(|| "a", self.config.a, 0, || Value::known(a))?;
                let b_cell = region.assign_advice(|| "b", self.config.b, 0, || Value::known(b))?;
                let c_cell = region.assign_advice(|| "c", self.config.c, 0, || Value::known(c))?;
                let is_zero = is_zero_chip.check(&mut region, 0, Value::known(a - b))?;

                let output = if a == b { c } else { a - b };
                let output_cell = region.assign_advice(|| "output", self.config.output, 0, || Value::known(output))?;
                println!("a_cell: {:?}", a_cell);
                println!("b_cell: {:?}", b_cell);
                println!("c_cell: {:?}", c_cell);
                println!("output_cell: {:?}", output_cell);
                println!("is_zero: {:?}", is_zero);
        
                Ok(output_cell)
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
    struct FunctionCircuit<F> {
        a: F,
        b: F,
        c: F,
    }
    
    impl<F: PrimeField> Circuit<F> for FunctionCircuit<F> {
        type Config = FunctionConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;
    
        fn without_witnesses(&self) -> Self {
            Self::default()
        }
    
        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            FunctionChip::configure(meta)
        }
    
        fn synthesize(&self, config: Self::Config, layouter: impl Layouter<F>) -> Result<(), Error> {
            let chip = FunctionChip::construct(config);
            chip.assign(layouter, self.a, self.b, self.c)?;
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
        let circuit = FunctionCircuit {
            a: Fp::from(10),
            b: Fp::from(12),
            c: Fp::from(15),
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
        
    }


}