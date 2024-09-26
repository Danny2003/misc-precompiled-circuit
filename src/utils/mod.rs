extern crate flux_rs;
use flux_rs::extern_spec;
use std::convert::TryInto;

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
pub struct BigUint {
    data: Vec<BigDigit>,
}

// pub fn field_to_bn<F: PrimeField>(f: &F) -> BigUint {
//     let bytes = f.to_repr();
//     // to_repr is little-endian as per the test below.
//     BigUint::from_bytes_le(bytes.as_ref())
// }

pub trait FromUniformBytes<const N: usize>: PrimeField {
    /// Returns a field element that is congruent to the provided little endian unsigned
    /// byte representation of an integer.
    fn from_uniform_bytes(bytes: &[u8; N]) -> Self;
}

impl BigUint {
    #[inline]
    fn zero() -> BigUint {
        BigUint { data: Vec::new() }
    }

    #[inline]
    fn set_zero(&mut self) {
        self.data.clear();
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.data.is_empty()
    }
    #[inline]
    fn one() -> BigUint {
        BigUint { data: vec![1] }
    }

    #[inline]
    fn set_one(&mut self) {
        self.data.clear();
        self.data.push(1);
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.data[..] == [1]
    }
    /// Creates and initializes a [`BigUint`].
    ///
    /// The base 2<sup>32</sup> digits are ordered least significant digit first.
    #[inline]
    pub fn new(digits: Vec<u32>) -> BigUint {
        let mut big = BigUint::zero();
        unimplemented!()
    }

    /// Creates and initializes a [`BigUint`].
    ///
    /// The base 2<sup>32</sup> digits are ordered least significant digit first.
    #[inline]
    pub fn from_slice(slice: &[u32]) -> BigUint {
        let mut big = BigUint::zero();
        big.assign_from_slice(slice);
        big
    }

    /// Assign a value to a [`BigUint`].
    ///
    /// The base 2<sup>32</sup> digits are ordered least significant digit first.
    #[inline]
    pub fn assign_from_slice(&mut self, slice: &[u32]) {
        unimplemented!()
    }

    /// Creates and initializes a [`BigUint`].
    ///
    /// The bytes are in big-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::BigUint;
    ///
    /// assert_eq!(BigUint::from_bytes_be(b"A"),
    ///            BigUint::parse_bytes(b"65", 10).unwrap());
    /// assert_eq!(BigUint::from_bytes_be(b"AA"),
    ///            BigUint::parse_bytes(b"16705", 10).unwrap());
    /// assert_eq!(BigUint::from_bytes_be(b"AB"),
    ///            BigUint::parse_bytes(b"16706", 10).unwrap());
    /// assert_eq!(BigUint::from_bytes_be(b"Hello world!"),
    ///            BigUint::parse_bytes(b"22405534230753963835153736737", 10).unwrap());
    /// ```
    #[inline]
    pub fn from_bytes_be(bytes: &[u8]) -> BigUint {
        if bytes.is_empty() {
            Self::zero()
        } else {
            let mut v = bytes.to_vec();
            v.reverse();
            BigUint::from_bytes_le(&v)
        }
    }

    /// Creates and initializes a [`BigUint`].
    ///
    /// The bytes are in little-endian byte order.
    #[inline]
    pub fn from_bytes_le(bytes: &[u8]) -> BigUint {
        if bytes.is_empty() {
            Self::zero()
        } else {
            unimplemented!()
        }
    }

    /// Creates and initializes a [`BigUint`]. The input slice must contain
    /// ascii/utf8 characters in [0-9a-zA-Z].
    /// `radix` must be in the range `2...36`.
    ///
    /// The function `from_str_radix` from the `Num` trait provides the same logic
    /// for `&str` buffers.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigUint, ToBigUint};
    ///
    /// assert_eq!(BigUint::parse_bytes(b"1234", 10), ToBigUint::to_biguint(&1234));
    /// assert_eq!(BigUint::parse_bytes(b"ABCD", 16), ToBigUint::to_biguint(&0xABCD));
    /// assert_eq!(BigUint::parse_bytes(b"G", 16), None);
    /// ```
    #[inline]
    pub fn parse_bytes(buf: &[u8], radix: u32) -> Option<BigUint> {
        unimplemented!()
    }

    /// Creates and initializes a [`BigUint`]. Each `u8` of the input slice is
    /// interpreted as one digit of the number
    /// and must therefore be less than `radix`.
    ///
    /// The bytes are in big-endian byte order.
    /// `radix` must be in the range `2...256`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigUint};
    ///
    /// let inbase190 = &[15, 33, 125, 12, 14];
    /// let a = BigUint::from_radix_be(inbase190, 190).unwrap();
    /// assert_eq!(a.to_radix_be(190), inbase190);
    /// ```
    pub fn from_radix_be(buf: &[u8], radix: u32) -> Option<BigUint> {
        unimplemented!()
    }

    /// Creates and initializes a [`BigUint`]. Each `u8` of the input slice is
    /// interpreted as one digit of the number
    /// and must therefore be less than `radix`.
    ///
    /// The bytes are in little-endian byte order.
    /// `radix` must be in the range `2...256`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigUint};
    ///
    /// let inbase190 = &[14, 12, 125, 33, 15];
    /// let a = BigUint::from_radix_be(inbase190, 190).unwrap();
    /// assert_eq!(a.to_radix_be(190), inbase190);
    /// ```
    pub fn from_radix_le(buf: &[u8], radix: u32) -> Option<BigUint> {
        unimplemented!()
    }

    /// Returns the byte representation of the [`BigUint`] in big-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::BigUint;
    ///
    /// let i = BigUint::parse_bytes(b"1125", 10).unwrap();
    /// assert_eq!(i.to_bytes_be(), vec![4, 101]);
    /// ```
    #[inline]
    pub fn to_bytes_be(&self) -> Vec<u8> {
        let mut v = self.to_bytes_le();
        v.reverse();
        v
    }

    pub fn to_bitwise_digits_le(u: &BigUint, bits: u8) -> Vec<u8> {
        unimplemented!()
    }

    /// Returns the byte representation of the [`BigUint`] in little-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::BigUint;
    ///
    /// let i = BigUint::parse_bytes(b"1125", 10).unwrap();
    /// assert_eq!(i.to_bytes_le(), vec![101, 4]);
    /// ```
    #[inline]
    pub fn to_bytes_le(&self) -> Vec<u8> {
        if self.is_zero() {
            vec![0]
        } else {
            Self::to_bitwise_digits_le(self, 8)
        }
    }
}

pub fn bn_to_field<F: FromUniformBytes<64>>(bn: &BigUint) -> F {
    let bytes = bn.to_bytes_le();
    F::from_uniform_bytes(&bytes.try_into().unwrap())
}
