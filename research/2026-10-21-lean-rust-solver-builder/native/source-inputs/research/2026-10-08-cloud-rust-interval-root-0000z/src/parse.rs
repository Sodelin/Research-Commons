//! Distinct receiver raw-ASCII and forward reduced-value input contracts.
//! Unicode Nd table is frozen from CPython's Unicode 15.0.0.
use crate::{Rational, Result, Error, bit_size};
use num_bigint::BigInt;
use num_traits::{One, Zero};
const DECIMAL_ZEROES:&[u32]=&[0x30,0x660,0x6f0,0x7c0,0x966,0x9e6,0xa66,0xae6,0xb66,0xbe6,0xc66,0xce6,0xd66,0xde6,0xe50,0xed0,0xf20,0x1040,0x1090,0x17e0,0x1810,0x1946,0x19d0,0x1a80,0x1a90,0x1b50,0x1bb0,0x1c40,0x1c50,0xa620,0xa8d0,0xa900,0xa9d0,0xa9f0,0xaa50,0xabf0,0xff10,0x104a0,0x10d30,0x11066,0x110f0,0x11136,0x111d0,0x112f0,0x11450,0x114d0,0x11650,0x116c0,0x11730,0x118e0,0x11950,0x11c50,0x11d50,0x11da0,0x11f50,0x16a60,0x16ac0,0x16b50,0x1d7ce,0x1d7d8,0x1d7e2,0x1d7ec,0x1d7f6,0x1e140,0x1e2f0,0x1e4f0,0x1e950,0x1fbf0];
fn ascii_integer(s:&str) -> Option<BigInt> { BigInt::parse_bytes(s.as_bytes(),10) }
/// Full frozen receiver str-input grammar; raw integers checked before reduction.
pub fn receiver(s:&str) -> Result<Rational> {
    if s.chars().count()>158 { return Err(Error("RAW_TEXT_LIMIT")); }
    let mut parts=s.split('/'); let n=parts.next().unwrap(); let d=parts.next();
    let magnitude=n.strip_prefix('-').unwrap_or(n);
    let digits=|v:&str| !v.is_empty() && v.len()<=78 && v.bytes().all(|c|c.is_ascii_digit());
    if parts.next().is_some() || !digits(magnitude) || d.is_some_and(|v|!digits(v)) {
        return Err(Error("RAW_GRAMMAR"));
    }
    let n=ascii_integer(n).unwrap(); let d=d.map(|x|ascii_integer(x).unwrap()).unwrap_or_else(BigInt::one);
    if d.is_zero() { return Err(Error("ZERO_DENOMINATOR")); }
    if n.bits().max(d.bits())>256 { return Err(Error("INPUT_BITS")); }
    Ok(Rational::new(n,d))
}
fn decimal(c:char) -> Option<char> {
    let n=c as u32;
    DECIMAL_ZEROES.iter().find_map(|&z| if n>=z && n<z+10 {Some((b'0'+(n-z) as u8) as char)} else {None})
}
fn normalize_digits(s:&str) -> Option<String> {
    if s.is_empty() {return None;} s.chars().map(decimal).collect()
}
/// Frozen forward string-input contract, including Unicode Nd digits from the
/// pinned Python Unicode table. Denominator's first digit must be ASCII 1..9.
pub fn forward(s:&str) -> Result<Rational> {
    if s.chars().count()>160 { return Err(Error("raw rational text exceeds160 characters")); }
    let mut parts=s.split('/'); let n=parts.next().unwrap(); let d=parts.next();
    let magnitude=n.strip_prefix('-').unwrap_or(n);
    let invalid=||Error("integer or rational n/d string required");
    let mut normalized=normalize_digits(magnitude).ok_or_else(invalid)?;
    if n.starts_with('-') { normalized.insert(0,'-'); }
    if parts.next().is_some() { return Err(invalid()); }
    let denominator=if let Some(d)=d {
        if !matches!(d.as_bytes().first(),Some(b'1'..=b'9')) { return Err(invalid()); }
        ascii_integer(&normalize_digits(d).ok_or_else(invalid)?).unwrap()
    } else {BigInt::one()};
    forward_value(Rational::new(ascii_integer(&normalized).unwrap(),denominator))
}
/// Forward int/Fraction input path; reduced value check only.
pub fn forward_value(q:Rational) -> Result<Rational> {
    if bit_size(&q)>256 { return Err(Error("reduced rational exceeds256 bits")); } Ok(q)
}
