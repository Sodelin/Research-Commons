//! RC1 strict ASCII framing and canonical byte serialization.
//! Requests carry exact shared-row semantics; certificates echo every request
//! byte. Independent checking accepts mathematical certificates, not claims of
//! source-chart admission or of unrestricted registry coverage.
use crate::{affine::{self, Decision, Row}, canonical, count, q, Rational};
use num_bigint::BigInt;
use num_traits::Zero;

pub const MAX_REQUEST_BYTES: usize = 65536;
pub const MAX_CERTIFICATE_BYTES: usize = 4 * 1024 * 1024;
pub const INVALID: &str = "RC1 ERROR INVALID_REQUEST\n";
pub const INTERNAL: &str = "RC1 ERROR INTERNAL_CERTIFICATE\n";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Request {
    Affine { n: usize, rows: Vec<Row>, cap: usize },
    Count { b: Rational, epsilon: Rational, sigma: Rational, modulus: Rational },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Response { pub bytes: String, pub exit_code: u8 }

fn natural(token: &str, limit: usize) -> Result<usize, &'static str> {
    if token.is_empty() || (token.len() > 1 && token.starts_with('0'))
        || !token.bytes().all(|b| b.is_ascii_digit()) { return Err("NATURAL"); }
    let n: usize = token.parse().map_err(|_| "NATURAL")?;
    if n > limit { return Err("LIMIT"); }
    Ok(n)
}

/// A canonical rational always renders p/q, including integers and zero.
/// Raw magnitudes are bounded before allocating arbitrary-precision values.
pub fn rational(token: &str, input: bool) -> Result<Rational, &'static str> {
    // Certificate parsing is bounded by MAX_CERTIFICATE_BYTES as a whole;
    // intermediate exact rationals have no undocumented digit restriction.
    let max_digits = if input { 78 } else { MAX_CERTIFICATE_BYTES };
    let Some((numerator, denominator)) = token.split_once('/') else { return Err("RATIONAL"); };
    let magnitude = numerator.strip_prefix('-').unwrap_or(numerator);
    let unsigned = |s: &str| !s.is_empty() && s.len() <= max_digits
        && !(s.len() > 1 && s.starts_with('0')) && s.bytes().all(|b| b.is_ascii_digit());
    if !unsigned(magnitude) || !unsigned(denominator) || denominator == "0"
        || numerator == "-0" { return Err("RATIONAL"); }
    let numerator = BigInt::parse_bytes(numerator.as_bytes(), 10).ok_or("RATIONAL")?;
    let denominator = BigInt::parse_bytes(denominator.as_bytes(), 10).ok_or("RATIONAL")?;
    if input && (numerator.bits() > 256 || denominator.bits() > 256) { return Err("RATIONAL_BITS"); }
    let value = Rational::new(numerator, denominator);
    if canonical(&value) != token { return Err("RATIONAL_CANONICAL"); }
    Ok(value)
}

fn fields(line: &str) -> Result<Vec<&str>, &'static str> {
    if line.is_empty() || line.starts_with(' ') || line.ends_with(' ') || line.contains("  ") {
        return Err("FIELDS");
    }
    Ok(line.split(' ').collect())
}

fn valid_ascii(bytes: &[u8], limit: usize) -> bool {
    !bytes.is_empty() && bytes.len() <= limit && bytes.last() == Some(&b'\n')
        && bytes.iter().all(|b| *b == b'\n' || (32..=126).contains(b))
}

pub fn parse(bytes: &[u8]) -> Result<Request, &'static str> {
    if !valid_ascii(bytes, MAX_REQUEST_BYTES) { return Err("FRAME"); }
    let text = std::str::from_utf8(bytes).map_err(|_| "ASCII")?;
    let lines: Vec<_> = text.strip_suffix('\n').unwrap().split('\n').collect();
    let header = fields(lines[0])?;
    if header.len() < 2 || header[0] != "RC1" { return Err("HEADER"); }
    match header[1] {
        "AFFINE" => {
            if header.len() != 5 { return Err("HEADER"); }
            let n = natural(header[2], 8)?;
            let m = natural(header[3], 64)?;
            let cap = natural(header[4], 4096)?;
            if lines.len() != m + 1 { return Err("ROWS"); }
            let mut rows = Vec::with_capacity(m);
            for line in &lines[1..] {
                let f = fields(line)?;
                if f.len() != n + 2 { return Err("ROW_SHAPE"); }
                let strict = match f[0] { "LE" => false, "LT" => true, _ => return Err("RELATION") };
                let bound = rational(f[1], true)?;
                let coefficients = f[2..].iter().map(|token| rational(token, true))
                    .collect::<Result<Vec<_>, _>>()?;
                rows.push(Row { coefficients, bound, strict });
            }
            Ok(Request::Affine { n, rows, cap })
        }
        "COUNT" => {
            if header.len() != 6 || lines.len() != 1 { return Err("HEADER"); }
            let values = header[2..].iter().map(|token| rational(token, true))
                .collect::<Result<Vec<_>, _>>()?;
            let request = Request::Count { b: values[0].clone(), epsilon: values[1].clone(),
                sigma: values[2].clone(), modulus: values[3].clone() };
            count::conditional_count(&values[0], &values[1], &values[2], &values[3])?;
            Ok(request)
        }
        _ => Err("COMMAND"),
    }
}

fn prefix(command: &str, request: &str) -> String {
    format!("RC1 RESULT {command}\nBEGIN_REQUEST\n{request}END_REQUEST\n")
}

fn vector(label: &str, values: &[Rational]) -> String {
    let mut line = format!("{label} {}", values.len());
    for value in values { line.push(' '); line.push_str(&canonical(value)); }
    line.push('\n');
    line
}

pub fn execute(bytes: &[u8]) -> Response {
    let invalid = || Response { bytes: INVALID.into(), exit_code: 1 };
    let request = match parse(bytes) { Ok(value) => value, Err(_) => return invalid() };
    let text = std::str::from_utf8(bytes).unwrap();
    match request {
        Request::Affine { n, rows, cap } => {
            let decision = match affine::solve(n, &rows, cap) {
                Ok(value) => value,
                Err(_) => return Response { bytes: INTERNAL.into(), exit_code: 1 },
            };
            let mut output = prefix("AFFINE", text);
            let exit_code = match decision {
                Decision::Witness(assignment) => {
                    output.push_str("STATUS SAT\n");
                    output.push_str(&vector("WITNESS", &assignment));
                    let evaluated: Vec<_> = rows.iter().map(|r| r.evaluate(&assignment).unwrap()).collect();
                    output.push_str(&vector("EVAL", &evaluated));
                    0
                }
                Decision::Exclusion(weights) => {
                    output.push_str("STATUS UNSAT\n");
                    output.push_str(&vector("MULTIPLIERS", &weights));
                    let bound = rows.iter().zip(&weights)
                        .fold(q(0, 1), |sum, (row, weight)| sum + &row.bound * weight);
                    let strict = rows.iter().zip(&weights).any(|(r, w)| r.strict && w > &q(0, 1));
                    output.push_str(&format!("BOUND {}\nSTRICT {}\n", canonical(&bound), u8::from(strict)));
                    0
                }
                Decision::Unknown { dimension, required_rows, cap } => {
                    output.push_str(&format!("STATUS UNKNOWN\nLIMIT {dimension} {required_rows} {cap}\n"));
                    2
                }
            };
            output.push_str("END\n");
            Response { bytes: output, exit_code }
        }
        Request::Count { b, epsilon, sigma, modulus } => {
            let result = count::conditional_count(&b, &epsilon, &sigma, &modulus).unwrap();
            let output = format!("{}STATUS CONDITIONAL_ARITHMETIC\nDELTA {}\nBOUND {}\nCEILING {}\nGATE UNKNOWN_SOURCE_PROVIDER\nEND\n",
                prefix("COUNT", text), canonical(&result.delta), canonical(&result.bound), result.ceiling);
            Response { bytes: output, exit_code: 2 }
        }
    }
}

fn parsed_vector(line: &str, label: &str, expected: usize) -> Result<Vec<Rational>, &'static str> {
    let f = fields(line)?;
    if f.len() != expected + 2 || f[0] != label || natural(f[1], 4096)? != expected { return Err("CERTIFICATE_VECTOR"); }
    f[2..].iter().map(|token| rational(token, false)).collect()
}

/// Verify the echoed request, every reported evaluation and an exact witness
/// or Farkas contradiction. UNKNOWN/count gate outputs are not certificates of
/// feasibility or exclusion. This function does not invoke the affine solver.
pub fn check(request_bytes: &[u8], certificate: &[u8]) -> Result<(), &'static str> {
    let request = parse(request_bytes)?;
    if !valid_ascii(certificate, MAX_CERTIFICATE_BYTES) { return Err("CERTIFICATE_FRAME"); }
    let text = std::str::from_utf8(certificate).map_err(|_| "CERTIFICATE_ASCII")?;
    let request_text = std::str::from_utf8(request_bytes).unwrap();
    match request {
        Request::Affine { n, rows, .. } => {
            let Some(body) = text.strip_prefix(&prefix("AFFINE", request_text)) else { return Err("REQUEST_IDENTITY"); };
            let lines: Vec<_> = body.strip_suffix('\n').ok_or("CERTIFICATE_FRAME")?.split('\n').collect();
            match lines.first().copied() {
                Some("STATUS SAT") if lines.len() == 4 && lines[3] == "END" => {
                    let assignment = parsed_vector(lines[1], "WITNESS", n)?;
                    let evaluated = parsed_vector(lines[2], "EVAL", rows.len())?;
                    if !affine::check_witness(n, &rows, &assignment) { return Err("INVALID_WITNESS"); }
                    if rows.iter().zip(evaluated).any(|(row, value)| row.evaluate(&assignment) != Some(value)) {
                        return Err("INVALID_EVALUATION");
                    }
                    Ok(())
                }
                Some("STATUS UNSAT") if lines.len() == 5 && lines[4] == "END" => {
                    let weights = parsed_vector(lines[1], "MULTIPLIERS", rows.len())?;
                    if !affine::check_exclusion(n, &rows, &weights) { return Err("INVALID_EXCLUSION"); }
                    let bound = rows.iter().zip(&weights).fold(q(0, 1), |sum, (r, w)| sum + &r.bound * w);
                    let strict = rows.iter().zip(&weights).any(|(r, w)| r.strict && !w.is_zero());
                    if lines[2] != format!("BOUND {}", canonical(&bound))
                        || lines[3] != format!("STRICT {}", u8::from(strict)) { return Err("INVALID_DERIVATION"); }
                    Ok(())
                }
                Some("STATUS UNKNOWN") => Err("UNKNOWN_NOT_CERTIFICATE"),
                _ => Err("CERTIFICATE_SHAPE"),
            }
        }
        Request::Count { .. } => {
            if execute(request_bytes).bytes == text { Err("CONDITIONAL_NOT_SOURCE_CERTIFICATE") }
            else { Err("INVALID_CONDITIONAL_ARITHMETIC") }
        }
    }
}
