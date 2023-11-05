use std::marker::PhantomData;

use group::ff::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector},
    poly::Rotation,
};

// 这个chip 支持的操作或者指令
// ANCHOR: instructions
trait NumericInstructions<F: Field>: Chip<F> {
    /// Variable representing a number.
    type Num;

    /// Loads a number into the circuit as a private input.
    fn load_private(&self, layouter: impl Layouter<F>, a: Value<F>) -> Result<Self::Num, Error>;

    /// Loads a number into the circuit as a fixed constant.
    fn load_constant(&self, layouter: impl Layouter<F>, constant: F) -> Result<Self::Num, Error>;

    /// Returns `c = a * b`.
    fn mul(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    /// Exposes a number as a public input to the circuit.
    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}
// ANCHOR_END: instructions

// ANCHOR: chip
/// The chip that will implement our instructions! Chips store their own
/// config, as well as type markers if necessary.
struct FieldChip<F: Field>  {
    config: FieldConfig,
    _marker: PhantomData<F>,
}
// ANCHOR_END: chip

// ANCHOR: chip-config
/// Chip state is stored in a config struct. This is generated by the chip
/// during configuration, and then stored inside the chip.
#[derive(Clone, Debug)]
struct FieldConfig {
    /// For this chip, we will use two advice columns to implement our instructions.
    /// These are also the columns through which we communicate with other parts of
    /// the circuit.
    advice: [Column<Advice>; 3],

    /// This is the public input (instance) column.
    instance: Column<Instance>,

    // We need a selector to enable the multiplication gate, so that we aren't placing
    // any constraints on cells where `NumericInstructions::mul` is not being used.
    // This is important when building larger circuits, where columns are used by
    // multiple sets of instructions.
    s_mul: Selector,
}

impl<F: Field> FieldChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {  
        Self {
            config,
            _marker: PhantomData,
        }
    }

    //配置chip 需要满足的约束
    fn configure(
        meta: &mut ConstraintSystem<F>,  //meta = arkworks中的cs
        advice: [Column<Advice>; 3],
        instance: Column<Instance>,
        constant: Column<Fixed>,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance); //启用 instance 和 constant 列以用于约束。
        meta.enable_constant(constant);
        for column in &advice {
            meta.enable_equality(*column);  //遍历 advice 列表中的每个列，并启用它们以用于约束。
        }
        let s_mul = meta.selector();

        // Define our multiplication gate!
        //create_gate 创建custom gate, 这里的作用是
        meta.create_gate("mul", |meta| {
            // To implement multiplication, we need three advice cells and a selector
            // cell. We arrange them like so:
            //
            // | a0  | a1  | a3    | s_mul |
            // |-----|-----|-------|-------|
            // | lhs | rhs | out   | s_mul |
            //
            // Gates may refer to any relative offsets we want, but each distinct
            // offset adds a cost to the proof. The most common offsets are 0 (the
            // current row), 1 (the next row), and -1 (the previous row), for which
            // `Rotation` has specific constructors.
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[2], Rotation::cur());
            let s_mul = meta.query_selector(s_mul);

            // Finally, we return the polynomial expressions that constrain this gate.
            // For our multiplication gate, we only need a single polynomial constraint.
            //
            // The polynomial expressions returned from `create_gate` will be
            // constrained by the proving system to equal zero. Our expression
            // has the following properties:
            // - When s_mul = 0, any value is allowed in lhs, rhs, and out.
            // - When s_mul != 0, this constrains lhs * rhs = out.
            vec![s_mul * (lhs * rhs - out)] 
        });

        FieldConfig {
            advice,
            instance,
            s_mul,
        }
    }
}
// ANCHOR_END: chip-config

// ANCHOR: chip-impl
impl<F: Field> Chip<F> for FieldChip<F> {
    type Config = FieldConfig;
    type Loaded = (); //综合时需要的

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()  //返回对空元组的不可变引用。
    }
}
// ANCHOR_END: chip-impl

// ANCHOR: instructions-impl
/// A variable representing a number.
#[derive(Clone)]
struct Number<F: Field>(AssignedCell<F, F>);

// FieldChip 实现 NumericInstructions
impl<F: Field> NumericInstructions<F> for FieldChip<F> {
    type Num = Number<F>;

    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load private",
            |mut region| {
                region
                    .assign_advice(|| "private input", config.advice[0], 0, || value)
                    .map(Number)
            },
        )
    }

    fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        constant: F,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load constant",
            |mut region| {
                region
                    .assign_advice_from_constant(|| "constant value", config.advice[0], 0, constant)
                    .map(Number)
            },
        )
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "mul",
            |mut region: Region<'_, F>| {
                // We only want to use a single multiplication gate in this region,
                // so we enable it at region offset 0; this means it will constrain
                // cells at offsets 0 and 1.
                config.s_mul.enable(&mut region, 0)?;

                // The inputs we've been given could be located anywhere in the circuit,
                // but we can only rely on relative offsets inside this region. So we
                // assign new cells inside the region and constrain them to have the
                // same values as the inputs.
                a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                // Now we can assign the multiplication result, which is to be assigned
                // into the output position.
                let value = a.0.value().copied() * b.0.value();

                // Finally, we do the assignment to the output, returning a
                // variable to be used in another part of the circuit.
                region
                    .assign_advice(|| "lhs * rhs", config.advice[2], 0, || value)
                    .map(Number)
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();

        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }
}
// ANCHOR_END: instructions-impl

// ANCHOR: circuit
/// The full circuit implementation.
///
/// In this struct we store the private input variables. We use `Option<F>` because
/// they won't have any value during key generation. During proving, if any of these
/// were `None` we would get an error.
#[derive(Default)]
struct MyCircuit<F: Field> {
    constant: F,
    a: Value<F>,
    b: Value<F>,
}

impl<F: Field> Circuit<F> for MyCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = FieldConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }
    //把本电路的的config，为chip 分配资源。
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // We create the two advice columns that FieldChip uses for I/O.
        let advice = [meta.advice_column(), meta.advice_column(), meta.advice_column()];

        // We also need an instance column to store public inputs.
        let instance = meta.instance_column();

        // Create a fixed column to load constants.
        let constant = meta.fixed_column();

        FieldChip::configure(meta, advice, instance, constant)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let field_chip = FieldChip::<F>::construct(config); //构造一个chip实例

        // Load our private values into the circuit.
        let a = field_chip.load_private(layouter.namespace(|| "load a"), self.a)?;
        let b = field_chip.load_private(layouter.namespace(|| "load b"), self.b)?;

        // Load the constant factor into the circuit.
        let constant =
            field_chip.load_constant(layouter.namespace(|| "load constant"), self.constant)?;

        // We only have access to plain multiplication.
        // We could implement our circuit as:
        //     asq  = a*a
        //     bsq  = b*b
        //     absq = asq*bsq
        //     c    = constant*asq*bsq
        //
        // but it's more efficient to implement it as:
        //     ab   = a*b
        //     absq = ab^2
        //     c    = constant*absq
        let ab = field_chip.mul(layouter.namespace(|| "a * b"), a, b)?;
        let absq = field_chip.mul(layouter.namespace(|| "ab * ab"), ab.clone(), ab)?;
        let c = field_chip.mul(layouter.namespace(|| "constant * absq"), constant, absq)?;

        // Expose the result as a public input to the circuit.
        field_chip.expose_public(layouter.namespace(|| "expose c"), c, 0)
    }
}
// ANCHOR_END: circuit

fn main() {
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 4;

    // Prepare the private and public inputs to the circuit!
    let constant = Fp::from(7);
    let a = Fp::from(2);
    let b = Fp::from(3);
    let c = constant * a.square() * b.square();

    // Instantiate the circuit with the private inputs.
    let circuit = MyCircuit {
        constant,
        a: Value::known(a),
        b: Value::known(b),
    };

    // Arrange the public input. We expose the multiplication result in row 0
    // of the instance column, so we position it there in our public inputs.
    let mut public_inputs = vec![c];

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    // If we try some other public input, the proof will fail!
    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
    // ANCHOR_END: test-circuit
}


#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, pasta::Fp};


    #[test]
    fn test_circuit() {
        let k = 4;

        // Prepare the private and public inputs to the circuit!
        let constant = Fp::from(7);
        let a = Fp::from(4);
        let b = Fp::from(5);
        let c = constant * a.square() * b.square();

        // Instantiate the circuit with the private inputs.
        let circuit = MyCircuit {
            constant,
            a: Value::known(a),
            b: Value::known(b),
        };

        // Arrange the public input. We expose the multiplication result in row 0
        // of the instance column, so we position it there in our public inputs.
        let mut public_inputs = vec![c];

        // Given the correct public input, our circuit will verify.
        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
        println!("verifiy success");

        // If we try some other public input, the proof will fail!
        public_inputs[0] += Fp::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err());
    }


    // #[test]
    // fn test_closure() {
        
    //     let x = vec![1,2,3]; 
    //     fn_once(|z| {z == x.len()});
    
        
        
    //     // 此处声明闭包f实现了 Copy，闭包没有发生所有权转移所有func调用两次不崩溃
    //     fn fn_once_with_copy<F: FnOnce(usize) -> bool + Copy> (f: F) {  //F: 
    //         println!("{}", f(3)); // true
    //         println!("{}", f(4)); // false
    //     }

    //     // 此处声明闭包f实现了 Copy，闭包没有发生所有权转移所有func调用两次不崩溃
    //     fn fn_once<F: FnOnce(usize) -> bool > (f: F) {  //F:是一个采用获取x所有权方式使用x的闭包函数
    //         println!("{}", f(3)); // true
    //         println!("{}", f(4)); // false
    //     }
    // }

    #[test]
    fn test_borrowed_string(){
        let mut s1 = String::from("hello");
        let s2 = String::from("world");

        let append_to = |str: &mut String| str.push_str(&s2);  //类型推导， 不可变应用了s2, s2的所有权没有发生转移。
     
        append_to(&mut s1); 
        println!("{:?}", s1);
        println!("{:?}", s2);
    }

    #[test]
    fn test_moved_string(){
        let s1 = String::from("hello");
        let s2 = String::from("world");

        let moved_string = || {let moved = s2; moved};  //转移s2的所有权。
        let s3 = moved_string();

        println!("{:?}", s1);
        // println!("{:?}", s2); value borrowed here after move
        println!("{:?}", s3);
    }
    

    #[test]
    fn test_mut_borrowed_string(){
        let mut s1 = String::from("hello");
        let mut append_to = || s1.push_str("world");  //类型推导， 不可变应用了s2, s2的所有权没有发生转移。
        append_to();
        println!("{:?}", s1);
        // println!("{:?}", s2); value borrowed here after move
        // println!("{:?}", s3);
    }


    #[test]
    fn test_moved_owershhip(){
        let s = String::from("hello");
        println!("{:?}", s);  //println 采用不可变应用的方式使用s, s的所有权没有发生转移

        let s1 = s;  //value moved here
        println!("{:?}", s1); 
        // println!("{:?}", s); //error,value borrowed here after move
    }


    fn exec<F: FnOnce()>(f: F)  { // 规则1: 所有闭包自动实现FnOnce
        f()
    }
    
    fn exec1<F: FnMut()>(mut f: F)  {// 规则2: 没有移出捕获变量所有的闭包自动实现FnMut
        f()
    }
    
    fn exec2<F: Fn()>(f: F)  {// 规则3: 不需要对捕获变量进行改变的自动实现Fn
        f()
    }

    #[test]
    fn test_clouse2(){
      
        let s = String::from("hello");
        let update_string =  || println!("{}",s); // 闭包进行了不可变借用，没有移出变量所有权，不改变变量
        
        exec(update_string);
        exec1(update_string);
        exec2(update_string);
    }

    #[test]
    fn test_clouse3(){
      
        let s = String::from("hello");
        let update_string = ||{
            let s1= s; //s的所有权转移到s1中,因此不能自动实现FnMut
        };
        
        exec(update_string);
   
    }

    #[test]
    fn test_clouse4(){
        let x = 10;
        let c1 = || {
            println!("{}", x);
        };
        c1();
        c1();
        println!("{}", x);
    }

    #[test]
    fn test_closure5() {
        let mut y = 10;
        let mut c2 = || {
            y += 10;
            println!("{}", y);
        };
        c2();
        c2();
        println!("{}", y);
    }



    #[test]
    fn test_closure6(){

        let mut x = vec![1,2,3];
        
        let mut closure  = |z|{x.push(4); z == x.len()}; // 修改了外部的 x, 实现了 FnMut， x 所有权没有转移
        closure(4);
        
        println!("{:?}", x);
    }

    #[test]
    fn test_closure7(){
        fn fn_once<F>(func: F)
        where
            F: FnOnce(usize) -> bool, // F是一个泛型trait约上好友
        {
            println!("{}", func(4));
        }

        let x = vec![1, 2, 3];
        let closure = |z|{z == x.len()}; // 此闭包实现了 Fn、 FnMut 和 FnOnce
        fn_once(closure); // Fn 可传入标注为 FnOnce 的参数
        println!("{:?}", x); // x 还能用，所有权没转移

        // let closure2 = move |z|{z == x.len()}; //  此闭包只实现了 FnOnce，因为 x 被强制转移所有权到闭包内部
        // fn_once(closure2); // 传入 FnOnce
        // println!("{:?}", x); // 报错，x 已经没了
    }

    #[test]
    fn test_closure8() {
        fn outter<T>(mut func: T)
        where T: FnMut(usize) -> bool { // Fn 可以传到 FnMut 标注的参数上
            let a = func;
        }
        
        let mut x = vec![1,2,3];
    
        let closure = |z:usize|{ z == x.len()}; // 实现了 Fn
        outter(closure); // 通过
        outter(closure); // 通过
    
        let closure2 = |z:usize|{ x.push(4);z == x.len()}; // 实现了 FnMut
        outter(closure2); // 通过
        // outter(closure2); // 报错, closure2 的所有权已被转移
    }
    


}