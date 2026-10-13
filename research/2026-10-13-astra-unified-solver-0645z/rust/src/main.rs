//! Exact arithmetic component only. No native-code refinement theorem claimed.
#![forbid(unsafe_code)]
use exact_count_certificate::{parse, Rational};
use num_traits::{One, Zero};
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

fn add(a: &mut Vec<Rational>, b: &[Rational]) {
    a.resize(a.len().max(b.len()), Rational::zero());
    for (x,y) in a.iter_mut().zip(b) { *x += y; }
}
fn multiply(a: &[Rational], b: &[Rational]) -> Vec<Rational> {
    let mut out=vec![Rational::zero(); a.len()+b.len()-1];
    for (i,x) in a.iter().enumerate() {
        for (j,y) in b.iter().enumerate() { out[i+j] += x*y; }
    }
    out
}
fn trim(a: &mut Vec<Rational>) {
    while a.last().is_some_and(Zero::is_zero) { a.pop(); }
}

fn check(raw: &str) -> Result<usize> {
    if raw.len()>262144 || !raw.is_ascii() { return Err("wire size or encoding"); }
    let mut input=Input(raw.split_ascii_whitespace());
    if input.token()? != "COMMON_CERT_V1" { return Err("wire version"); }
    let level=input.natural(8)?;
    if level==0 { return Err("positive level required"); }
    let coefficients: Vec<_>=(0..level).map(|_| input.rational()).collect::<Result<_>>()?;
    let moments: Vec<_>=(0..level).map(|_| input.rational()).collect::<Result<_>>()?;
    if coefficients.iter().all(Zero::is_zero) { return Err("zero polynomial"); }
    if moments[0]!=Rational::one() || moments.iter().any(|v| v<&Rational::zero() || v>&Rational::one()) {
        return Err("normalized moment domain");
    }
    let mut polynomial=vec![Rational::zero(); level*(level-1)/2+1];
    for (i,c) in coefficients.iter().enumerate() { polynomial[(i+1)*i/2]+=c; }
    let terms=input.natural(16)?;
    if terms==0 { return Err("square terms required"); }
    let mut reconstructed=vec![];
    for _ in 0..terms {
        let weight=input.rational()?;
        if weight<Rational::zero() { return Err("negative square weight"); }
        let left=input.natural(1)?;
        let right=input.natural(1)?;
        let size=input.natural(15)?;
        if size==0 { return Err("empty square polynomial"); }
        let square: Vec<_>=(0..size).map(|_|input.rational()).collect::<Result<_>>()?;
        let mut term=multiply(&square,&square);
        for x in &mut term { *x *= &weight; }
        if left==1 { term.insert(0,Rational::zero()); }
        if right==1 { term=multiply(&term,&[Rational::one(),-Rational::one()]); }
        add(&mut reconstructed,&term);
    }
    if input.0.next().is_some() { return Err("trailing token"); }
    trim(&mut polynomial); trim(&mut reconstructed);
    if polynomial!=reconstructed { return Err("nonnegative identity mismatch"); }
    let annihilation: Rational=coefficients.iter().zip(&moments).map(|(c,y)|c*y).sum();
    if !annihilation.is_zero() { return Err("nonzero annihilation"); }
    Ok(level-1)
}

fn main() {
    let mut raw=String::new();
    if io::stdin().take(262145).read_to_string(&mut raw).is_err() {
        eprintln!("REFUSED invalid UTF-8/input"); std::process::exit(1);
    }
    match check(&raw) {
        Ok(cap)=>println!("CHECKED_RATIONAL_CERTIFICATE support_cap={cap} source_existence=false"),
        Err(reason)=>{ eprintln!("REFUSED {reason}"); std::process::exit(1); }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const GOOD: &str="COMMON_CERT_V1 3 1/4 -3/4 1 1 1/2 1/8 2 1 0 0 2 -1/2 1 1 1 0 2 -1/2 1";
    #[test] fn singleton_and_endpoint() {
        assert_eq!(check(GOOD),Ok(2));
        assert_eq!(check("COMMON_CERT_V1 2 1 -1 1 1 1 1 0 1 1 1"),Ok(1));
    }
    #[test] fn malformed_or_false_certificate() {
        for raw in [GOOD.to_owned()+" extra", GOOD.replace("1/8","1/7"),
                    GOOD.replace("1/4","1/3"), GOOD.replace("1/2","0.5"),
                    GOOD.replace("-3/4","-03/4"), GOOD.replace(" 3 "," 0 "),
                    GOOD.replace("1/8","1/0"), GOOD.replace("-1/2 1","-1/2"),
                    GOOD.replace(" 2 1 0 0", " 2 -1 0 0")] {
            assert!(check(&raw).is_err(),"{raw}");
        }
    }
    #[test] fn exact_parser_has_a_narrower_contract_than_reused_library() {
        for token in ["0", "-0", "1", "-1", "2/4", "-2/4",
            "340282366920938463463374607431768211455",
            "340282366920938463463374607431768211456/340282366920938463463374607431768211456"] {
            assert!(Input(token.split_ascii_whitespace()).rational().is_ok(), "{token}");
        }
        for token in ["", "01", "-01", "+1", "0.5", "1e0", "1/0", "1/-2", "1/+2",
            "1/02", "1_0", "١", "1/2/3", "--1", "-",
            "340282366920938463463374607431768211456",
            "1/340282366920938463463374607431768211456"] {
            assert!(Input(token.split_ascii_whitespace()).rational().is_err(), "{token}");
        }
    }
    #[test] fn wire_limits_and_canonical_naturals() {
        for raw in ["".to_string(), "COMMON_CERT_V0 3".to_string(),
            GOOD.replace(" 3 "," 03 "), GOOD.replace(" 3 "," +3 "),
            GOOD.replace(" 3 "," 9 "), GOOD.replace(" 3 "," 184467440737095516160 "),
            GOOD.replace(" 2 1 0 0", " 17 1 0 0"),
            GOOD.replace(" 2 -1/2 1", " 16 -1/2 1"),
            GOOD.to_owned()+"\u{80}", " ".repeat(262145)] {
            assert!(check(&raw).is_err());
        }
    }
    #[test] fn arithmetic_certificate_does_not_assert_a_positive_survival_source() {
        // p(x)=x has a root only at zero. The arithmetic certificate is valid
        // for y=(1,0), but no (0,1] source-existence claim follows from acceptance.
        assert_eq!(check("COMMON_CERT_V1 2 0 1 1 0 1 1 1 0 1 1"), Ok(1));
    }
}
