//! Bounded candidate-support acquisition into the ORIGINAL certificate wire.
//! UNCOMPILED proposal. Exact checking, not physical source recognition.
//! Domain: 1..3 distinct proposed rational nodes in (0,1], 2r+1 supplied
//! triangular-power moments. Every generated certificate uses super::check.
use super::{check, trim, Generation, Input, Rational, Result};
use num_traits::{One, Zero};

const INTERNAL_BITS: u64 = 8192;
fn bounded(value: Rational) -> Result<Rational> {
    if value.numer().bits() > INTERNAL_BITS || value.denom().bits() > INTERNAL_BITS {
        Err("internal_rational_cap")
    } else {
        Ok(value)
    }
}
fn add(a: &Rational, b: &Rational) -> Result<Rational> { bounded(a + b) }
fn sub(a: &Rational, b: &Rational) -> Result<Rational> { bounded(a - b) }
fn mul(a: &Rational, b: &Rational) -> Result<Rational> { bounded(a * b) }
fn divide(a: &Rational, b: &Rational) -> Result<Rational> {
    if b.is_zero() { return Err("singular_supported_interpolation"); }
    bounded(a / b)
}
fn natural(n: usize) -> Rational { Rational::from_integer(n.into()) }
fn power(a: &Rational, n: usize) -> Result<Rational> {
    let mut out = Rational::one();
    for _ in 0..n { out = mul(&out, a)?; }
    Ok(out)
}
fn product(a: &[Rational], b: &[Rational]) -> Result<Vec<Rational>> {
    let mut out = vec![Rational::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i+j] = add(&out[i+j], &mul(x, y)?)?;
        }
    }
    Ok(out)
}
fn solve(mut rows: Vec<Vec<Rational>>) -> Result<Vec<Rational>> {
    let n = rows.len();
    for col in 0..n {
        let pivot = (col..n).find(|&row| !rows[row][col].is_zero())
            .ok_or("singular_supported_interpolation")?;
        rows.swap(col, pivot);
        let scale = rows[col][col].clone();
        for entry in &mut rows[col] { *entry = divide(entry, &scale)?; }
        let pivot_row = rows[col].clone();
        for (r, row) in rows.iter_mut().enumerate() {
            if r == col { continue; }
            let factor = row[col].clone();
            for (entry, pivot_entry) in row.iter_mut().zip(&pivot_row) {
                *entry = sub(entry, &mul(&factor, pivot_entry)?)?;
            }
        }
    }
    Ok(rows.into_iter().map(|row| row[n].clone()).collect())
}
fn monic_quotient(p: &[Rational], d: &[Rational]) -> Result<Vec<Rational>> {
    if d.last() != Some(&Rational::one()) || d.len() > p.len() {
        return Err("unsupported_monic_divisor");
    }
    let mut remainder = p.to_vec();
    let mut quotient = vec![Rational::zero(); p.len()-d.len()+1];
    for top in (d.len()-1..p.len()).rev() {
        let k = top-d.len()+1;
        let a = remainder[top].clone();
        quotient[k] = a.clone();
        for (j, value) in d.iter().enumerate() {
            remainder[k+j] = sub(&remainder[k+j], &mul(&a, value)?)?;
        }
    }
    if remainder.iter().any(|x| !x.is_zero()) {
        return Err("nonzero_division_remainder");
    }
    trim(&mut quotient);
    Ok(quotient)
}
fn derive(nodes: &[Rational], supplied: &[&str]) -> Result<String> {
    let level = supplied.len();
    let exponents: Vec<_> = (0..level).map(|i| i*(i+1)/2).collect();
    let last = exponents[level-1];
    let mut rows = Vec::with_capacity(2*nodes.len());
    for a in nodes {
        let mut value_row = Vec::with_capacity(level);
        let mut derivative_row = Vec::with_capacity(level);
        for &e in &exponents[..level-1] {
            value_row.push(power(a, e)?);
            derivative_row.push(if e == 0 { Rational::zero() }
                else { mul(&natural(e), &power(a, e-1)?)? });
        }
        value_row.push(-power(a, last)?);
        derivative_row.push(-mul(&natural(last), &power(a, last-1)?)?);
        rows.push(value_row);
        rows.push(derivative_row);
    }
    let mut coefficients = solve(rows)?;
    coefficients.push(Rational::one());
    let mut polynomial = vec![Rational::zero(); last+1];
    for (&e, c) in exponents.iter().zip(&coefficients) { polynomial[e] = c.clone(); }
    let mut factor = vec![Rational::one()];
    for a in nodes { factor = product(&factor, &[-a.clone(), Rational::one()])?; }
    let divisor = product(&factor, &factor)?;
    let quotient = monic_quotient(&polynomial, &divisor)?;
    if quotient.first().is_none_or(|q| q <= &Rational::zero()) ||
        quotient.iter().any(|q| q < &Rational::zero()) {
        return Err("quotient_not_in_supported_positive_language");
    }
    // Explicitly reauthenticate the algebraic division independently of
    // interpolation. Neither a numerical root tolerance nor a sign guess is used.
    let mut reconstructed = product(&divisor, &quotient)?;
    trim(&mut reconstructed);
    trim(&mut polynomial);
    if polynomial != reconstructed { return Err("factorization_identity_mismatch"); }

    let terms = quotient.iter().filter(|q| !q.is_zero()).count();
    let mut fields = vec!["COMMON_CERT_V1".to_string(), level.to_string()];
    fields.extend(coefficients.iter().map(ToString::to_string));
    fields.extend(supplied.iter().map(|s| (*s).to_string()));
    fields.push(terms.to_string());
    for (j, weight) in quotient.iter().enumerate() {
        if weight.is_zero() { continue; }
        let mut square = vec![Rational::zero(); j/2];
        square.extend(factor.iter().cloned());
        fields.extend([weight.to_string(), (j%2).to_string(), "0".to_string(),
            square.len().to_string()]);
        fields.extend(square.iter().map(ToString::to_string));
    }
    let certificate = fields.join(" ") + "\n";
    if certificate.len() > 262144 { return Err("generated_wire_cap"); }
    // The established parser checks its own 128-bit/80-byte/level/term/degree
    // caps, exact weighted-square identity, normalization and annihilation.
    if check(&certificate) != Ok(level-1) {
        return Err("generated_certificate_not_accepted_by_existing_language");
    }
    Ok(certificate)
}

pub(super) fn generate(raw: &str) -> Result<Generation> {
    if raw.len() > 262144 || !raw.is_ascii() { return Err("wire size or encoding"); }
    let mut input = Input(raw.split_ascii_whitespace());
    if input.token()? != "COMMON_GENERATE_SUPPORT_V1" {
        return Err("generator wire version");
    }
    let count = input.natural(3)?;
    if count == 0 { return Err("positive support required"); }
    let nodes: Vec<_> = (0..count).map(|_| input.rational()).collect::<Result<_>>()?;
    if nodes.iter().any(|a| a <= &Rational::zero() || a > &Rational::one()) ||
        nodes.iter().enumerate().any(|(i,a)| nodes[..i].contains(a)) {
        return Err("distinct candidate survivals in (0,1] required");
    }
    let level = input.natural(8)?;
    if level != 2*count+1 { return Err("exactly 2r+1 supplied moments required"); }
    // Original moment token spellings cross this proposal unchanged.
    let supplied: Vec<_> = input.0.clone().take(level).collect();
    let moments: Vec<_> = (0..level).map(|_| input.rational()).collect::<Result<_>>()?;
    if input.0.next().is_some() { return Err("trailing token"); }
    if moments[0] != Rational::one() ||
        moments.iter().any(|y| y < &Rational::zero() || y > &Rational::one()) {
        return Err("normalized moment domain");
    }
    // Only malformed requests above are refusals. Unsupported interpolation,
    // internal growth, output-language caps and nonannihilation are UNKNOWN.
    Ok(match derive(&nodes, &supplied) {
        Ok(certificate) => Generation::Checked(certificate),
        Err(reason) => Generation::Unknown(reason),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    const TWO: &str = "COMMON_GENERATE_SUPPORT_V1 2 1/3 2/3 5 1 1/2 1/6 65/1458 1025/118098";
    const EXPECTED: &str = "COMMON_CERT_V1 5 151168/13640319 -3856/72171 11428/56133 -11323/18711 1 1 1/2 1/6 65/1458 1025/118098 7 37792/168399 0 0 3 2/9 -1 1 17548/18711 1 0 3 2/9 -1 1 35108/18711 0 0 4 0 2/9 -1 1 8/3 1 0 4 0 2/9 -1 1 23/9 0 0 5 0 0 2/9 -1 1 2 1 0 5 0 0 2/9 -1 1 1 0 0 6 0 0 0 2/9 -1 1\n";
    #[test] fn exact_two_atom_sparse_certificate() {
        assert_eq!(generate(TWO), Ok(Generation::Checked(EXPECTED.to_string())));
        assert_eq!(check(EXPECTED), Ok(4));
        assert_eq!(generate(&TWO.replacen("1/3 2/3", "2/3 1/3", 1)), generate(TWO));
    }
    #[test] fn singleton_compatibility_and_literals() {
        assert_eq!(generate("COMMON_GENERATE_SUPPORT_V1 1 1/2 3 1 1/2 1/8"),
            super::super::generate_singleton("COMMON_GENERATE_SINGLETON_V1 1 1/2 1/8"));
        let Ok(Generation::Checked(c)) = generate("COMMON_GENERATE_SUPPORT_V1 1 2/4 3 2/2 2/4 2/16")
            else { panic!("equivalent rational literals"); };
        assert!(c.contains(" 2/2 2/4 2/16 "));
        assert_eq!(check(&c), Ok(2));
    }
    #[test] fn endpoint_and_three_atom_language() {
        for raw in ["COMMON_GENERATE_SUPPORT_V1 1 1 3 1 1 1",
            "COMMON_GENERATE_SUPPORT_V1 3 1/4 1/2 3/4 7 1 1/2 3/16 397/6144 30037/1572864 1198473/268435456 871870863/1099511627776"] {
            let Ok(Generation::Checked(c)) = generate(raw) else { panic!("{raw}"); };
            assert!(check(&c).is_ok());
        }
    }
    #[test] fn candidate_failure_is_unknown_not_no() {
        assert!(matches!(generate("COMMON_GENERATE_SUPPORT_V1 1 1/2 3 1 1/2 1/7"),
            Ok(Generation::Unknown(_))));
        assert!(matches!(generate(&TWO.replace("1025/118098", "1/2")),
            Ok(Generation::Unknown(_))));
    }
    #[test] fn malformed_refusals() {
        for raw in ["", "COMMON_GENERATE_SUPPORT_V1 0", "COMMON_GENERATE_SUPPORT_V1 4",
            "COMMON_GENERATE_SUPPORT_V1 01", "COMMON_GENERATE_SUPPORT_V1 1 0 3 1 0 0",
            "COMMON_GENERATE_SUPPORT_V1 1 2 3 1 1 1",
            "COMMON_GENERATE_SUPPORT_V1 2 1/3 2/6 5 1 1/2 1/6 65/1458 1025/118098",
            "COMMON_GENERATE_SUPPORT_V1 1 0.5 3 1 1/2 1/8",
            "COMMON_GENERATE_SUPPORT_V1 1 1/0 3 1 1/2 1/8",
            "COMMON_GENERATE_SUPPORT_V1 1 1/2 2 1 1/2",
            "COMMON_GENERATE_SUPPORT_V1 1 1/2 3 1 1/2",
            "COMMON_GENERATE_SUPPORT_V1 1 1/2 3 1 1/2 1/8 extra"] {
            assert!(generate(raw).is_err(), "{raw}");
        }
    }
}
