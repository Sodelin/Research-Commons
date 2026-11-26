//! Exact finite rational bank -> one common triangular moment vector.
//! Rational implementation of retained positive-support/fiber grouping semantics.
//! This computes a supplied mathematical law; it does not admit a physical source.
#![forbid(unsafe_code)]
use exact_count_certificate::{parse, Rational};
use num_traits::{One, Zero};
use std::collections::BTreeMap;
use std::io::{self, Read};
type Result<T> = std::result::Result<T, &'static str>;
struct Input<'a>(std::str::SplitAsciiWhitespace<'a>);
impl<'a> Input<'a> {
    fn token(&mut self) -> Result<&'a str> { self.0.next().ok_or("missing token") }
    fn natural(&mut self, cap: usize) -> Result<usize> {
        let s = self.token()?;
        if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) || (s.len()>1 && s.starts_with('0')) {
            return Err("canonical natural required");
        }
        let n = s.parse::<usize>().map_err(|_| "natural overflow")?;
        if n > cap { return Err("natural cap"); }
        Ok(n)
    }
    fn rational(&mut self) -> Result<Rational> {
        let s = self.token()?;
        if s.len()>80 || !s.is_ascii() { return Err("rational token cap"); }
        let pieces: Vec<_> = s.split('/').collect();
        if pieces.len()>2 { return Err("rational syntax"); }
        let numerator = pieces[0].strip_prefix('-').unwrap_or(pieces[0]);
        let canonical = |x: &str| !x.is_empty() && x.bytes().all(|b| b.is_ascii_digit()) &&
            (x.len()==1 || !x.starts_with('0'));
        if !canonical(numerator) || (pieces.len()==2 && (!canonical(pieces[1]) || pieces[1]=="0")) {
            return Err("canonical integer or p/q required");
        }
        // Reuse the established exact parser after imposing this narrower wire.
        let q = parse::rational(s).map_err(|_| "rational parse")?;
        if q.numer().bits()>128 || q.denom().bits()>128 { return Err("rational bit cap"); }
        Ok(q)
    }
}


const INTERNAL_BITS: u64 = 8192;
fn bounded(q: Rational) -> Result<Rational> {
    if q.numer().bits() > INTERNAL_BITS || q.denom().bits() > INTERNAL_BITS {
        Err("internal_rational_cap")
    } else { Ok(q) }
}
fn add(a: &Rational, b: &Rational) -> Result<Rational> { bounded(a+b) }
fn mul(a: &Rational, b: &Rational) -> Result<Rational> { bounded(a*b) }

struct Bank { level: usize, atoms: Vec<(Rational, Rational)> }
#[derive(Debug, PartialEq)]
enum Outcome { Checked(String), Unknown(&'static str) }

fn read(raw: &str) -> Result<Bank> {
    if raw.len() > 262144 || !raw.is_ascii() { return Err("wire size or encoding"); }
    let mut input = Input(raw.split_ascii_whitespace());
    if input.token()? != "COMMON_BANK_MOMENTS_V1" { return Err("bank wire version"); }
    let level = input.natural(8)?;
    if level == 0 { return Err("positive copy-level count required"); }
    let n = input.natural(256)?;
    if n == 0 { return Err("nonempty finite carrier required"); }
    let mut atoms = Vec::with_capacity(n);
    for _ in 0..n {
        let weight = input.rational()?;
        let value = input.rational()?;
        if weight < Rational::zero() || weight > Rational::one() {
            return Err("weight domain");
        }
        // Values outside positive support have exactly zero contribution.
        if !weight.is_zero() && (value <= Rational::zero() || value > Rational::one()) {
            return Err("positive-mass survivals in (0,1] required");
        }
        atoms.push((weight, value));
    }
    if input.0.next().is_some() { return Err("trailing token"); }
    Ok(Bank { level, atoms })
}

fn calculate(bank: &Bank) -> Result<String> {
    let mut total = Rational::zero();
    let mut grouped: BTreeMap<Rational, Rational> = BTreeMap::new();
    let mut positive_atoms = 0;
    for (weight, value) in &bank.atoms {
        total = add(&total, weight)?;
        if weight.is_zero() { continue; }
        positive_atoms += 1;
        let old = grouped.get(value).cloned().unwrap_or_else(Rational::zero);
        grouped.insert(value.clone(), add(&old, weight)?);
    }
    if total != Rational::one() { return Err("mass_not_one"); }
    let mut grouped_total = Rational::zero();
    for weight in grouped.values() { grouped_total = add(&grouped_total, weight)?; }
    if grouped_total != total { return Err("grouped_mass_mismatch"); }
    let mut moments = Vec::with_capacity(bank.level);
    for k in 1..=bank.level {
        let exponent = k*(k-1)/2;
        let mut moment = Rational::zero();
        for (value, weight) in &grouped {
            let mut power = Rational::one();
            for _ in 0..exponent { power = mul(&power, value)?; }
            moment = add(&moment, &mul(weight, &power)?)?;
        }
        moments.push(moment);
    }
    // Match the existing certificate parser's exact output-language cap.
    for q in grouped.iter().flat_map(|(x,w)| [x,w]).chain(moments.iter()) {
        if q.numer().bits() > 128 || q.denom().bits() > 128 || q.to_string().len() > 80 {
            return Err("derived_rational_output_cap");
        }
    }
    let mut fields = vec!["CHECKED_RATIONAL_BANK_MOMENTS_V1".to_string(),
        bank.level.to_string(), bank.atoms.len().to_string(),
        positive_atoms.to_string(), grouped.len().to_string()];
    for (value, weight) in &grouped { fields.extend([value.to_string(),weight.to_string()]); }
    fields.extend(moments.iter().map(ToString::to_string));
    let output = fields.join(" ")+"\n";
    if output.len() > 262144 { return Err("derived_wire_cap"); }
    Ok(output)
}
fn evaluate(raw: &str) -> Result<Outcome> {
    let bank = read(raw)?;
    match calculate(&bank) {
        Ok(output) => Ok(Outcome::Checked(output)),
        Err("mass_not_one") => Err("mass_not_one"),
        Err(reason) => Ok(Outcome::Unknown(reason)),
    }
}
fn main() {
    let mut raw = String::new();
    if io::stdin().take(262145).read_to_string(&mut raw).is_err() {
        eprintln!("REFUSED invalid UTF-8/input"); std::process::exit(1);
    }
    match evaluate(&raw) {
        Ok(Outcome::Checked(output)) => print!("{output}"),
        Ok(Outcome::Unknown(reason)) => {
            println!("UNKNOWN {reason} source_existence=false"); std::process::exit(2);
        }
        Err(reason) => { eprintln!("REFUSED {reason}"); std::process::exit(1); }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const TWO: &str = "COMMON_BANK_MOMENTS_V1 5 4 1/4 1/3 1/4 2/6 1/2 2/3 0 -7";
    const EXPECTED: &str = "CHECKED_RATIONAL_BANK_MOMENTS_V1 5 4 3 2 1/3 1/2 2/3 1/2 1 1/2 1/6 65/1458 1025/118098\n";
    #[test] fn exact_duplicate_grouping_zero_omission_and_moments() {
        assert_eq!(evaluate(TWO), Ok(Outcome::Checked(EXPECTED.to_string())));
        assert_eq!(evaluate("COMMON_BANK_MOMENTS_V1 1 2 0 0 1 1"),
            Ok(Outcome::Checked("CHECKED_RATIONAL_BANK_MOMENTS_V1 1 2 1 1 1 1 1\n".to_string())));
    }
    #[test] fn same_law_for_all_triangular_copy_levels() {
        assert_eq!(evaluate("COMMON_BANK_MOMENTS_V1 8 1 1 1/2"),
            Ok(Outcome::Checked("CHECKED_RATIONAL_BANK_MOMENTS_V1 8 1 1 1 1/2 1 1 1/2 1/8 1/64 1/1024 1/32768 1/2097152 1/268435456\n".to_string())));
    }
    #[test] fn rejects_invalid_mass_without_renormalization() {
        for raw in ["COMMON_BANK_MOMENTS_V1 3 1 0 1",
            "COMMON_BANK_MOMENTS_V1 3 2 1/3 1/2 1/3 1/3"] {
            assert_eq!(evaluate(raw), Err("mass_not_one"));
        }
    }
    #[test] fn preserves_positive_node_domain_and_zero_mass_semantics() {
        for raw in ["COMMON_BANK_MOMENTS_V1 3 1 1 0",
            "COMMON_BANK_MOMENTS_V1 3 1 1 -1", "COMMON_BANK_MOMENTS_V1 3 1 1 2",
            "COMMON_BANK_MOMENTS_V1 3 2 -1 1/2 1 1/2"] {
            assert!(evaluate(raw).is_err());
        }
        assert!(matches!(evaluate("COMMON_BANK_MOMENTS_V1 3 2 0 -99 1 1/2"), Ok(Outcome::Checked(_))));
    }
    #[test] fn output_growth_is_unknown() {
        assert_eq!(evaluate("COMMON_BANK_MOMENTS_V1 3 1 1 1/170141183460469231731687303715884105727"),
            Ok(Outcome::Unknown("derived_rational_output_cap")));
    }
    #[test] fn strict_framing_and_caps() {
        for raw in ["", "COMMON_BANK_MOMENTS_V0 1 1 1 1",
            "COMMON_BANK_MOMENTS_V1 0 1 1 1", "COMMON_BANK_MOMENTS_V1 9 1 1 1",
            "COMMON_BANK_MOMENTS_V1 1 0", "COMMON_BANK_MOMENTS_V1 1 257",
            "COMMON_BANK_MOMENTS_V1 01 1 1 1", "COMMON_BANK_MOMENTS_V1 1 1 1 0.5",
            "COMMON_BANK_MOMENTS_V1 1 1 1 1/0", "COMMON_BANK_MOMENTS_V1 1 1 1",
            "COMMON_BANK_MOMENTS_V1 1 1 1 1 extra"] {
            assert!(evaluate(raw).is_err(), "{raw}");
        }
    }
}
