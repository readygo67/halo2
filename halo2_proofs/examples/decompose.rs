use std::{marker::PhantomData, io::Read};
use ff::PrimeFieldBits;
use group::ff::PrimeField;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};
use maybe_rayon::prelude::IndexedParallelIterator;


// fn num_of_bits(v:usize) -> usize{
//     if v == 0 {
//        return 1
//     }

//     let mut n = v;
//     let mut n_bits = 0;
//     while n > 0 {
//         n >>=1;
//         n_bits += 1;
//     }
    
//     n_bits

// }

#[derive(Debug, Clone)]
pub struct RangeTable<F:PrimeField, const NUM_BITS_PER_CHUNK:usize> {
    pub value: TableColumn,
    _maker: PhantomData<F>
}

impl<F:PrimeField, const NUM_BITS_PER_CHUNK:usize> RangeTable<F, NUM_BITS_PER_CHUNK>{
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self{
        // let n_bits = meta.lookup_table_column();
        let value = meta. lookup_table_column();

        RangeTable{
            value: value,
            _maker: PhantomData
        }
    }

    //load table contents
    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "load range-check table",
            |mut table| {
                let mut offset = 0;
                for value in 0..1<<NUM_BITS_PER_CHUNK {
                    table.assign_cell(
                        || format!("load value {}", value),
                        self.value,
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

/// This gadget range-constrains an element witnessed in the circuit to be N bits.
///
/// Internally, this gadget uses the `range_check` helper, which provides a K-bit
/// lookup table.
///
/// Given an element `value`, we use a running sum to break it into K-bit chunks.
/// Assume for now that N | K, and define C = N / K.
///
///     value = [b_0, b_1, ..., b_{N-1}]   (little-endian)
///           = c_0 + 2^K * c_1  + 2^{2K} * c_2 + ... + 2^{(C-1)K} * c_{C-1}
///
/// Initialise the running sum at
///                                 value = z_0.
///
/// Consequent terms of the running sum are z_{i+1} = (z_i - c_i) * 2^{-K}:
///
///                           z_1 = (z_0 - c_0) * 2^{-K}
///                           z_2 = (z_1 - c_1) * 2^{-K}
///                              ...
///                       z_{C-1} = c_{C-1}
///                           z_C = (z_{C-1} - c_{C-1}) * 2^{-K}
///                               = 0
///
/// One configuration for this gadget could look like:
///
///     | running_sum |  q_decompose  |  table_value  |
///     -----------------------------------------------
///     |     z_0     |       1       |       0       |
///     |     z_1     |       1       |       1       |
///     |     ...     |      ...      |      ...      |
///     |   z_{C-1}   |       1       |      ...      |
///     |     z_C     |       0       |      ...      |
///
/// Stretch task: use the tagged lookup table to constrain arbitrary bitlengths
/// (even non-multiples of K)

#[derive(Clone, Debug)]
pub struct DecomposeChip<F:PrimeField+PrimeFieldBits, const NUM_BITS_PER_CHUNK:usize> {
    running_sum: Column<Advice>,
    q_decompose: Selector,
    table: RangeTable<F, NUM_BITS_PER_CHUNK>,
}

impl<F: PrimeField+PrimeFieldBits, const NUM_BITS_PER_CHUNK:usize> DecomposeChip<F, NUM_BITS_PER_CHUNK> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        running_sum: Column<Advice>,
    ) -> DecomposeChip<F, NUM_BITS_PER_CHUNK> {       
        let q_decompose = meta.complex_selector();
        let table= RangeTable::<F,NUM_BITS_PER_CHUNK>::configure(meta);
        
        meta.enable_equality(running_sum);

        // Range-constrain each K-bit chunk `c_i = z_i - z_{i+1} * 2^K` derived from the running sum.
        meta.lookup(|meta| {
            
            let q_decompose = meta.query_selector(q_decompose);
            let z_cur = meta.query_advice(running_sum, Rotation::cur());
            let z_next = meta.query_advice(running_sum, Rotation::next());
            let chunk = z_cur - z_next * F::from(1 << NUM_BITS_PER_CHUNK);

            let not_q_decompose = Expression::Constant(F::ONE) - q_decompose.clone();
            let default_chunk = Expression::Constant(F::ZERO);
            
            let expr = q_decompose * chunk + not_q_decompose * default_chunk;

            vec![(expr, table.value)]
        });

        DecomposeChip {
            running_sum,
            q_decompose, 
            table,
        }
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
        num_bits: usize,
    ) -> Result<(), Error>{
        // `num_bits` must be a multiple of K.
        assert_eq!(num_bits % NUM_BITS_PER_CHUNK, 0);

        layouter.assign_region(
            || "decompose value",
            |mut region: Region<'_, F>| {
                let mut offset = 0;
                let mut z = region.assign_advice(
                    ||"assign initial value",
                     self.running_sum, offset, 
                     || value
                    )?;
        
                offset +=1;
            
                let running_sum = compute_running_sum::<_,NUM_BITS_PER_CHUNK>(value, num_bits);  //泛型的第一个参数由推导得到，第二个参数明确指定

                for z_i in running_sum.into_iter() {
                    z = region.assign_advice(
                        || format!("assign z_{:?}", offset),
                        self.running_sum,
                        offset,
                        || z_i,
                    )?;
                    offset += 1;
                }
            
                // 3. Make sure to enable the relevant selector on each row of the running sum
                // (but not on the row where z_C is witnessed)
                for offset in 0..(num_bits / NUM_BITS_PER_CHUNK) {
                    self.q_decompose.enable(&mut region, offset)?;
                }

                 // 4. Constrain the final running sum `z_C` to be 0.
                 region.constrain_constant(z.cell(), F::ZERO)
            }
        )
    }


}

//from boolean array to u64
fn from_le_bits(bits: &[bool]) -> u64 {
    assert!(bits.len() <= 64);
    bits.iter()
        .enumerate()
        .fold(0u64, |acc, (i, b)| acc + if *b { 1 << i } else { 0 })
}

//
fn compute_running_sum<F: PrimeField + PrimeFieldBits, const NUM_BITS_PER_CHUNK: usize>(
    value: Value<F>,
    num_bits: usize,
) -> Vec<Value<F>>{
    assert_eq!(num_bits % NUM_BITS_PER_CHUNK, 0);

    let multipiler = Value::known(F::from(1u64 << NUM_BITS_PER_CHUNK).invert().expect("should be invertible"));
    let mut running_sum = vec![];
 
    let mut v = F::ZERO;
    value.map(|x| v = x); //get he F type value from Value<F>
    let bits: Vec<_> = v
        .to_le_bits()
        .into_iter()
        .take(num_bits)
        .collect();
    println!("v: {:?}", bits);

    let mut z = value;
    let limbs = bits.chunks(NUM_BITS_PER_CHUNK);
    println!("chunks: {:?}", limbs);

    for limb in limbs{
        let chunk = Value::known(F::from(from_le_bits(limb)));
        z = (z - chunk)* multipiler;
        running_sum.push(z);
    }

    assert_eq!(running_sum.len(), num_bits / NUM_BITS_PER_CHUNK);
    running_sum    
}


fn main(){}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{
        dev::MockProver, 
        pasta::Fp, 
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
        poly::commitment::Params,

    };
    use pasta_curves::{pallas, vesta};
    use rand::rngs::OsRng;
    use rand_core::RngCore;

    #[derive(Default)]
    struct DecomposeCirsuit<F: PrimeField+PrimeFieldBits, const NUM_BITS_PER_CHUNK: usize> {
        pub value: Value<F>,
        pub num_bits: usize,
    }

    impl<F: PrimeField+PrimeFieldBits, const NUM_BITS_PER_CHUNK: usize> Circuit<F> for DecomposeCirsuit<F, NUM_BITS_PER_CHUNK> {

        type Config = DecomposeChip<F, NUM_BITS_PER_CHUNK>;
        type FloorPlanner = SimpleFloorPlanner;
    
        fn without_witnesses(&self) -> Self {
            Self::default()
        }
        //把本电路的的config，为chip 分配资源。
        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let constants = meta.fixed_column();
            meta.enable_constant(constants);

            // We create the two advice columns that IsZeroChip uses for I/O.
            let running_sum = meta.advice_column();
       
            DecomposeChip::configure(meta, running_sum)
        }
        
        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            //load table
            config.table.load(&mut layouter)?;  //initialze the table
            config.assign(layouter.namespace(|| "decompose value"), self.value, self.num_bits)?;
            Ok(())
        }
    }


    #[test]
    fn test_from_le_bits() {
        let bits = [false, true];
        let mut value = from_le_bits(&bits);
        assert_eq!(value, 2);

        let bits = [true, true];
        value = from_le_bits(&bits);
        assert_eq!(value, 3);

        let bits = [false, false, false];
        value = from_le_bits(&bits);
        assert_eq!(value, 0);

        let bits = [true];
        value = from_le_bits(&bits);
        assert_eq!(value, 1);
    }


    #[test]
    fn test_compute_running_sum() {
        let value = Value::known(Fp::from(100100u64));
        let res = compute_running_sum::<Fp, 8>(value, 24);
        println!("res: {:?}", res);

    }
   
    #[test]

    fn test_decompose_1() {
        let k = 9;
        const NUM_BITS_PER_CHUNK: usize = 8;
 
        // Random u64 value
        let value: u64 = rand::random();
        let value = Value::known(Fp::from(value));

        let circuit = DecomposeCirsuit::<Fp, NUM_BITS_PER_CHUNK> {
            value,
            num_bits: 64,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

     
    #[test]
    fn test_decompose_2() {
        let k = 9;
        const NUM_BITS_PER_CHUNK: usize = 8;
 
        // Random u64 value
        let value: u64 = 100100u64;
        let value = Value::known(Fp::from(value));

        let circuit = DecomposeCirsuit::<Fp, NUM_BITS_PER_CHUNK> {
            value,
            num_bits: 64,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_prover_verifier() {
        let k = 9;
        const NUM_BITS_PER_CHUNK: usize = 8;


        let params: Params<vesta::Affine> = Params::new(k);

        let empty_circuit = DecomposeCirsuit::<Fp, NUM_BITS_PER_CHUNK> {
            value: Value::unknown(),
            num_bits: 0,
        };

        let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

        let circuit = DecomposeCirsuit::<Fp, NUM_BITS_PER_CHUNK> {
            value: Value::known(Fp::from(100100u64)),
            num_bits: 32,
        };

        let mut rng = OsRng;
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(
            &params,
            &pk,
            &[circuit],
            &[&[]],   
            &mut rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        println!("proof: {:?}", hex::encode(proof.clone()));

        let strategy = SingleVerifier::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(verify_proof(
            &params,
            pk.get_vk(),
            strategy,
            &[&[]],
            &mut transcript
        )
        .is_ok());
    }
}