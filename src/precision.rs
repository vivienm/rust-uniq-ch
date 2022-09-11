//! The BJKST precision.

use std::{cmp::min, fmt, str::FromStr};

/// The precision of the BJKST data structure, in bits.
///
/// A [`Bjkst`](super::Bjkst) with precision `p` can store up to `2^p` elements before shrinking.
/// The internal array will be at most twice as large.
///
/// Default precision is 16 bits, that is, 65,536 elements.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
#[repr(u8)]
pub enum Precision {
    #[non_exhaustive]
    /// 1-bit precision.
    P1,
    /// 2-bit precision.
    P2,
    /// 3-bit precision.
    P3,
    /// 4-bit precision.
    P4,
    /// 5-bit precision.
    P5,
    /// 6-bit precision.
    P6,
    /// 7-bit precision.
    P7,
    /// 8-bit precision.
    P8,
    /// 9-bit precision.
    P9,
    /// 10-bit precision.
    P10,
    /// 11-bit precision.
    P11,
    /// 12-bit precision.
    P12,
    /// 13-bit precision.
    P13,
    /// 14-bit precision.
    P14,
    /// 15-bit precision.
    P15,
    /// 16-bit precision (default).
    P16,
    /// 17-bit precision.
    P17,
    /// 18-bit precision.
    P18,
    /// 19-bit precision.
    P19,
    /// 20-bit precision.
    P20,
    /// 21-bit precision.
    P21,
    /// 22-bit precision.
    P22,
    /// 23-bit precision.
    P23,
    /// 24-bit precision.
    P24,
}

impl Precision {
    /// The smallest precision value.
    pub const MIN: Self = Self::P1;

    /// The largest precision value.
    pub const MAX: Self = Self::P24;

    /// Creates a new `Precision` if the given value is valid.
    pub const fn new(value: u8) -> Option<Precision> {
        match value {
            1 => Some(Precision::P1),
            2 => Some(Precision::P2),
            3 => Some(Precision::P3),
            4 => Some(Precision::P4),
            5 => Some(Precision::P5),
            6 => Some(Precision::P6),
            7 => Some(Precision::P7),
            8 => Some(Precision::P8),
            9 => Some(Precision::P9),
            10 => Some(Precision::P10),
            11 => Some(Precision::P11),
            12 => Some(Precision::P12),
            13 => Some(Precision::P13),
            14 => Some(Precision::P14),
            15 => Some(Precision::P15),
            16 => Some(Precision::P16),
            17 => Some(Precision::P17),
            18 => Some(Precision::P18),
            19 => Some(Precision::P19),
            20 => Some(Precision::P20),
            21 => Some(Precision::P21),
            22 => Some(Precision::P22),
            23 => Some(Precision::P23),
            24 => Some(Precision::P24),
            _ => None,
        }
    }

    /// Returns the precision value as a primitive type.
    #[inline]
    pub const fn get(&self) -> u8 {
        match self {
            Precision::P1 => 1,
            Precision::P2 => 2,
            Precision::P3 => 3,
            Precision::P4 => 4,
            Precision::P5 => 5,
            Precision::P6 => 6,
            Precision::P7 => 7,
            Precision::P8 => 8,
            Precision::P9 => 9,
            Precision::P10 => 10,
            Precision::P11 => 11,
            Precision::P12 => 12,
            Precision::P13 => 13,
            Precision::P14 => 14,
            Precision::P15 => 15,
            Precision::P16 => 16,
            Precision::P17 => 17,
            Precision::P18 => 18,
            Precision::P19 => 19,
            Precision::P20 => 20,
            Precision::P21 => 21,
            Precision::P22 => 22,
            Precision::P23 => 23,
            Precision::P24 => 24,
        }
    }

    /// Returns the precision variants.
    pub const fn variants() -> &'static [Precision] {
        &[
            Precision::P1,
            Precision::P2,
            Precision::P3,
            Precision::P4,
            Precision::P5,
            Precision::P6,
            Precision::P7,
            Precision::P8,
            Precision::P9,
            Precision::P10,
            Precision::P11,
            Precision::P12,
            Precision::P13,
            Precision::P14,
            Precision::P15,
            Precision::P16,
            Precision::P17,
            Precision::P18,
            Precision::P19,
            Precision::P20,
            Precision::P21,
            Precision::P22,
            Precision::P23,
            Precision::P24,
        ]
    }

    /// Checks whether the given value is in the range of available precisions.
    #[inline]
    pub fn in_range(&self, value: u8) -> bool {
        Self::MIN.get() <= value && value <= Self::MAX.get()
    }

    /// Converts a string slice in a given base to a precision.
    ///
    /// The string is expected to be an optional `+` sign followed by digits.
    /// Leading and trailing whitespace represent an error.
    /// Digits are a subset of these characters, depending on `radix`:
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// # Panics
    ///
    /// Panics if `radix` is not in the range from 2 to 36.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Precision;
    ///
    /// assert_eq!(Precision::from_str_radix("10", 10), Ok(Precision::P10));
    /// ```
    pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseError> {
        use ParseErrorKind as PEK;

        assert!(
            (2..=36).contains(&radix),
            "from_str_radix: radix must lie in the range `[2, 36]` - found {}",
            radix,
        );

        if src.is_empty() {
            return Err(ParseError { kind: PEK::Empty });
        }

        let src = src.as_bytes();

        let digits = match src[0] {
            b'+' if src[1..].is_empty() => return Err(ParseError { kind: PEK::Empty }),
            b'+' => &src[1..],
            _ => src,
        };

        let mut result = 0u8;
        let radix_u8 = radix as u8;

        for &digit in digits {
            result = result.checked_mul(radix_u8).ok_or(ParseError {
                kind: PEK::AboveMax,
            })?;
            let digit = char::from(digit).to_digit(radix).ok_or(ParseError {
                kind: PEK::InvalidDigit,
            })? as u8;
            result = result.checked_add(digit).ok_or(ParseError {
                kind: PEK::AboveMax,
            })?;
            if result > Self::MAX.get() {
                return Err(ParseError {
                    kind: PEK::AboveMax,
                });
            }
        }

        Self::new(result).ok_or(ParseError {
            kind: PEK::BelowMin,
        })
    }

    /// The initial degree of the BJKST table size.
    #[inline]
    pub(crate) fn initial_size_degree(self) -> u8 {
        min(self.max_size_degree(), 4)
    }

    /// The maximum degree of BJKST table size.
    #[inline]
    pub(crate) const fn max_size_degree(self) -> u8 {
        self.get() + 1
    }

    /// The number of least significant bits used for thinning.
    ///
    /// The remaining high-order bits are used to determine the position in the hash table.
    /// (High-order bits are taken because the younger bits will be constant after dropping some of the
    /// values.)
    pub(crate) const fn bits_to_skip(&self) -> u8 {
        64 - self.max_size_degree()
    }
}

impl fmt::Display for Precision {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

impl Default for Precision {
    #[inline]
    fn default() -> Self {
        Precision::P16
    }
}

impl From<Precision> for u8 {
    #[inline]
    fn from(precision: Precision) -> Self {
        precision.get()
    }
}

impl FromStr for Precision {
    type Err = ParseError;

    #[inline]
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str_radix(src, 10)
    }
}

impl TryFrom<u8> for Precision {
    type Error = TryFromIntError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::new(value).ok_or(TryFromIntError(()))
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Precision {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.get().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Precision {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value: u8 = serde::Deserialize::deserialize(deserializer)?;
        Ok(Precision::try_from(value).map_err(serde::de::Error::custom)?)
    }
}

/// The error type returned when converting an integer into a [`Precision`] fails.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct TryFromIntError(());

impl fmt::Display for TryFromIntError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "precision out of range")
    }
}

impl ::std::error::Error for TryFromIntError {}

/// An error which can be returned when parsing a precision.
///
/// This error is used as the error type for the [`from_str_radix()`][Precision::from_str_radix]
/// method on the [`Precision`] type.
///
/// # Examples
///
/// ```
/// use uniq_ch::Precision;
///
/// if let Err(e) = Precision::from_str_radix("a12", 10) {
///     println!("Failed conversion to precision: {e}");
/// }
/// ```
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ParseError {
    kind: ParseErrorKind,
}

impl ParseError {
    /// Outputs the detailed cause of parsing an precision failing.
    #[must_use]
    pub fn kind(&self) -> &ParseErrorKind {
        &self.kind
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self.kind {
                ParseErrorKind::Empty => "cannot parse precision from empty string",
                ParseErrorKind::InvalidDigit => "invalid digit found in string",
                ParseErrorKind::AboveMax => "number too large to fit in the precision range",
                ParseErrorKind::BelowMin => "number too small to fit in the precision range",
            }
        )
    }
}

/// Enum to store the various types of errors that can cause parsing a precision to fail.
///
/// # Examples
///
/// ```
/// use uniq_ch::Precision;
///
/// if let Err(e) = Precision::from_str_radix("a12", 10) {
///     println!("Failed conversion to precision: {:?}", e.kind());
/// }
/// ```
#[derive(Clone, Eq, PartialEq, Debug)]
#[non_exhaustive]
pub enum ParseErrorKind {
    /// Value being parsed is empty.
    ///
    /// This variant will be constructed when parsing an empty string.
    Empty,
    /// Contains an invalid digit in its context.
    ///
    /// Among other causes, this variant will be constructed when parsing a string that
    /// contains a non-ASCII char.
    InvalidDigit,
    /// The integer is too large to fit in the precision range.
    AboveMax,
    /// The integer is too small to fit in the precision range.
    BelowMin,
}

#[cfg(test)]
mod tests {
    use super::Precision;

    #[test]
    fn min_max() {
        for precision in Precision::variants().iter().copied() {
            assert!(Precision::MIN <= precision && precision <= Precision::MAX);
        }
    }

    #[test]
    fn new_get() {
        for precision in Precision::variants().iter().copied() {
            assert_eq!(precision, Precision::new(precision.get()).unwrap());
        }
    }

    #[test]
    fn variants() {
        let mut variants: Vec<_> = Precision::variants().iter().copied().collect();
        variants.reverse();
        for precision_u8 in Precision::MIN.get()..=Precision::MAX.get() {
            let precision = Precision::new(precision_u8).unwrap();
            assert!(precision == variants.pop().unwrap());
        }
        assert!(variants.is_empty());
    }
}
