//! Explicit bounded ASCII CLI input profile, not a clone of all Python parsing.
use crate::{BigInt, BigUint, Rational};
use num_traits::{One, Zero};
use std::error::Error;
use std::fmt;

pub const MAX_TOKEN_BYTES: usize = 4096;
pub const MAX_DECIMAL_EXPONENT: u32 = 4096;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError(pub &'static str);
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str(self.0) }
}
impl Error for ParseError {}

fn checked_token(s: &str) -> Result<&str, ParseError> {
    if s.len() > MAX_TOKEN_BYTES { return Err(ParseError("numeric token exceeds 4096 bytes")); }
    if !s.is_ascii() { return Err(ParseError("only ASCII numeric tokens are supported")); }
    let s = s.trim_matches(|c: char| c.is_ascii_whitespace());
    if s.is_empty() { return Err(ParseError("empty numeric token")); }
    Ok(s)
}
fn digits(s: &str) -> bool { !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) }
fn integer(s: &str) -> Result<BigInt, ParseError> {
    let body = s.strip_prefix('-').or_else(|| s.strip_prefix('+')).unwrap_or(s);
    if !digits(body) { return Err(ParseError("expected a signed decimal integer")); }
    BigInt::parse_bytes(s.strip_prefix('+').unwrap_or(s).as_bytes(), 10)
        .ok_or(ParseError("invalid integer"))
}

pub fn natural(s: &str) -> Result<BigUint, ParseError> {
    let s = checked_token(s)?;
    let s = s.strip_prefix('+').unwrap_or(s);
    if !digits(s) { return Err(ParseError("max-steps must be a nonnegative ASCII integer")); }
    BigUint::parse_bytes(s.as_bytes(), 10).ok_or(ParseError("invalid max-steps"))
}

/// Parse integer, n/d (positive unsigned denominator), or finite decimal with
/// optional e/E exponent. No float conversion, underscores, or Unicode digits.
pub fn rational(s: &str) -> Result<Rational, ParseError> {
    let s = checked_token(s)?;
    if let Some((n,d)) = s.split_once('/') {
        let n = integer(n)?;
        if !digits(d) { return Err(ParseError("fraction denominator must be unsigned decimal digits")); }
        let d = integer(d)?;
        if d.is_zero() { return Err(ParseError("zero denominator")); }
        return Ok(Rational::new(n,d));
    }
    let (mantissa, exponent) = match s.find(['e','E']) {
        None => (s, 0i32),
        Some(i) => {
            let raw = &s[i+1..];
            let body = raw.strip_prefix('-').or_else(|| raw.strip_prefix('+')).unwrap_or(raw);
            if !digits(body) { return Err(ParseError("invalid decimal exponent")); }
            // Leading zeros are harmless and must not cause a machine parse overflow.
            let significant = body.trim_start_matches('0');
            if significant.len() > 4 { return Err(ParseError("decimal exponent magnitude exceeds 4096")); }
            let magnitude = if significant.is_empty() { 0 } else {
                significant.parse::<u32>().map_err(|_| ParseError("invalid decimal exponent"))?
            };
            if magnitude > MAX_DECIMAL_EXPONENT { return Err(ParseError("decimal exponent magnitude exceeds 4096")); }
            let exponent = if raw.starts_with('-') { -(magnitude as i32) } else { magnitude as i32 };
            (&s[..i], exponent)
        }
    };
    let negative = mantissa.starts_with('-');
    let unsigned = mantissa.strip_prefix('-').or_else(|| mantissa.strip_prefix('+')).unwrap_or(mantissa);
    let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    if (whole.is_empty() && fraction.is_empty())
        || !whole.bytes().all(|b| b.is_ascii_digit())
        || !fraction.bytes().all(|b| b.is_ascii_digit()) {
        return Err(ParseError("invalid exact decimal"));
    }
    let combined = format!("{whole}{fraction}");
    let mut numerator = integer(&combined)?;
    if negative { numerator = -numerator; }
    let scale = fraction.len() as i32 - exponent;
    let ten = BigInt::from(10u8);
    if scale >= 0 { Ok(Rational::new(numerator, ten.pow(scale as u32))) }
    else { Ok(Rational::new(numerator * ten.pow((-scale) as u32), BigInt::one())) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_decimal_and_fraction_forms() {
        for (a,b) in [("  +0.125e+1  ","5/4"),(".5","1/2"),("1.","1"),("-1e-3","-1/1000"),("2/4","1/2"),("-0","0"),("1E0000000000002","100")] {
            assert_eq!(rational(a).unwrap(), rational(b).unwrap());
        }
    }
    #[test]
    fn rejects_ambiguous_or_unbounded_transport() {
        for s in ["", ".", "--1", "+", "1/0", "1/-2", "1/+2", "1/2/3", "nan", "inf", "1e", "1e1e1", "1.2.3", "1_000", "١", "1 / 2", "1e4097", "1e-4097"] {
            assert!(rational(s).is_err(), "unexpectedly accepted {s}");
        }
        assert!(rational(&"1".repeat(MAX_TOKEN_BYTES+1)).is_err());
        assert!(rational("1e4096").is_ok());
        assert!(rational("1e-4096").is_ok());
        assert_eq!(natural("+0001").unwrap(), BigUint::one());
        for s in ["-1", "-0", "true", "1_0", "1.0"] { assert!(natural(s).is_err()); }
    }
}
