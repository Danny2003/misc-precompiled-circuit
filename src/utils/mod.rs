extern crate flux_rs;
use flux_rs::extern_spec;

/// This trait represents an element of a field.
pub trait Field:
    Sized
    + Eq
    + Copy
    + Clone
    + Default
    + Send
    + Sync
{
    /// The zero element of the field, the additive identity.
    const ZERO: Self;

    /// The one element of the field, the multiplicative identity.
    const ONE: Self;

}

/// This represents an element of a non-binary prime field.
pub trait PrimeField: Field + From<u64> {
    /// The prime field can be converted back and forth into this binary
    /// representation.
    type Repr: Copy + Default + Send + Sync + 'static + AsRef<[u8]> + AsMut<[u8]>;

    /// Modulus of the field written as a string for debugging purposes.
    ///
    /// The encoding of the modulus is implementation-specific. Generic users of the
    /// `PrimeField` trait should treat this string as opaque.
    const MODULUS: &'static str;

    /// How many bits are needed to represent an element of this field.
    const NUM_BITS: u32;

    /// How many bits of information can be reliably stored in the field element.
    ///
    /// This is usually `Self::NUM_BITS - 1`.
    const CAPACITY: u32;

    /// Inverse of $2$ in the field.
    const TWO_INV: Self;

    /// A fixed multiplicative generator of `modulus - 1` order. This element must also be
    /// a quadratic nonresidue.
    ///
    /// It can be calculated using [SageMath] as `GF(modulus).primitive_element()`.
    ///
    /// Implementations of this trait MUST ensure that this is the generator used to
    /// derive `Self::ROOT_OF_UNITY`.
    ///
    /// [SageMath]: https://www.sagemath.org/
    const MULTIPLICATIVE_GENERATOR: Self;

    /// An integer `s` satisfying the equation `2^s * t = modulus - 1` with `t` odd.
    ///
    /// This is the number of leading zero bits in the little-endian bit representation of
    /// `modulus - 1`.
    const S: u32;

    /// The `2^s` root of unity.
    ///
    /// It can be calculated by exponentiating `Self::MULTIPLICATIVE_GENERATOR` by `t`,
    /// where `t = (modulus - 1) >> Self::S`.
    const ROOT_OF_UNITY: Self;

    /// Inverse of [`Self::ROOT_OF_UNITY`].
    const ROOT_OF_UNITY_INV: Self;

    /// Generator of the `t-order` multiplicative subgroup.
    ///
    /// It can be calculated by exponentiating [`Self::MULTIPLICATIVE_GENERATOR`] by `2^s`,
    /// where `s` is [`Self::S`].
    const DELTA: Self;
}

pub(crate) type BigDigit = u64;

/// A big unsigned integer type.
struct BigUint {
    data: Vec<BigDigit>,
}

trait FromUniformBytes<const N: usize>: PrimeField {
    /// Returns a field element that is congruent to the provided little endian unsigned
    /// byte representation of an integer.
    fn from_uniform_bytes(bytes: &[u8; N]) -> Self;
}

#[derive(Debug)]
struct TestVec {
    data: Vec<u8>,
}

impl TestVec {
    fn len(&self) -> usize {
        unimplemented!()
    }
}

impl BigUint {
    fn len(&self) -> usize {
        unimplemented!()
    }
    /// Returns the byte representation of the [`BigUint`] in little-endian byte order.
    fn to_bytes_le(&self) -> TestVec {
        unimplemented!()
    }
}

pub trait TestTryInto: Sized {
    /// Performs the conversion.
    fn try_into(self) -> TestResult;
}

impl TestTryInto for TestVec {
    fn try_into(self) -> TestResult {
        unimplemented!()
    }
}

pub enum TestResult {
    /// Contains the success value
    Ok([u8; 64]),

    /// Contains the error value
    Err(TestVec),
}

impl TestResult {
    fn unwrap(self) -> [u8; 64] {
        match self {
            TestResult::Ok(val) => val,
            TestResult::Err(_) => panic!("called `TestResult::unwrap()` on an `Err` value"),
        }
    }
}

#[extern_spec]
#[flux::refined_by(len: int)]
struct TestVec;

#[extern_spec]
impl TestVec {
    #[flux::sig(fn (&TestVec[@n]) -> usize[n])]
    fn len(s: &TestVec) -> usize;
}

#[extern_spec]
impl TestTryInto for TestVec {
    #[flux::sig(fn ({TestVec[@n] | n <= 64}) -> TestResult)]
    fn try_into(s: TestVec) -> TestResult;
}

#[extern_spec]
#[flux::refined_by(len: int)]
struct BigUint;

#[extern_spec]
impl BigUint {
    #[flux::sig(fn (&BigUint[@n]) -> usize[n])]
    fn len(s: &BigUint) -> usize;

    #[flux::sig(fn (&BigUint) -> TestVec)]
    fn to_bytes_le(s: &BigUint) -> TestVec;
}

pub fn bn_to_field<F: FromUniformBytes<64>>(bn: &BigUint) -> F {
    let bytes = bn.to_bytes_le();
    F::from_uniform_bytes(&bytes.try_into().unwrap())
}
