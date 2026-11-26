//! RC1 strict ASCII framing and canonical byte serialization.
//! Requests carry exact shared-row semantics; certificates echo every request
//! byte. Independent checking accepts mathematical certificates, not claims of
//! source-chart admission or of unrestricted registry coverage.
use crate::{affine::{self, Decision, Row}, canonical, count, law, polynomial::Polynomial, q, Rational};
use num_bigint::BigInt;
use num_traits::Zero;
use crate::natural_cell::{self as cell, AgeAtom, AgeConstraint, Bound, Chart,
    Comparison, Edge, Exposure, Hybrid, Interval, Population, Source};

pub const MAX_REQUEST_BYTES: usize = 65536;
pub const MAX_CERTIFICATE_BYTES: usize = 4 * 1024 * 1024;
pub const INVALID: &str = "RC1 ERROR INVALID_REQUEST\n";
pub const INTERNAL: &str = "RC1 ERROR INTERNAL_CERTIFICATE\n";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Request {
    Affine { n: usize, rows: Vec<Row>, cap: usize },
    Count { b: Rational, epsilon: Rational, sigma: Rational, modulus: Rational },
    Chart(Chart),
    Law(law::Request),
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

fn reference(token: &str, count: usize) -> Result<usize, &'static str> {
    let n = natural(token, 32)?;
    if n >= count { Err("REFERENCE") } else { Ok(n) }
}
fn age_atom(token: &str, vertices: usize) -> Result<AgeAtom, &'static str> {
    match token.split_once(':') {
        Some(("V", id)) => Ok(AgeAtom::Node(reference(id, vertices)?)),
        Some(("Q", value)) => Ok(AgeAtom::Fixed(rational(value, true)?)),
        _ => Err("AGE_ATOM"),
    }
}
fn chart_bound(token: &str) -> Result<Option<Bound>, &'static str> {
    if token == "NONE" { return Ok(None); }
    match token.split_once(':') {
        Some((tag @ ("LE" | "LT"), value)) => Ok(Some(Bound { value: rational(value, true)?, strict: tag == "LT" })),
        _ => Err("INTERVAL_BOUND"),
    }
}
fn interval(lower: &str, upper: &str) -> Result<Interval, &'static str> {
    Ok(Interval { lower: chart_bound(lower)?, upper: chart_bound(upper)? })
}
fn chart(header: &[&str], lines: &[&str]) -> Result<Chart, &'static str> {
    if header.len() != 9 { return Err("CHART_HEADER"); }
    let v = natural(header[2], 32)?;
    let e = natural(header[3], 32)?;
    let l = natural(header[4], 32)?;
    let h = natural(header[5], 32)?;
    let c = natural(header[6], 32)?;
    let x = natural(header[7], 32)?;
    let cap = natural(header[8], 4096)?;
    if v < 3 || e < 2 || l < 2 || v + e + 1 + h > 32
        || lines.len() != 2 + e + l + h + c + x + h { return Err("CHART_SIZE"); }
    let mut index = 1;
    let mut next = || { let line = lines[index]; index += 1; fields(line) };
    let root_fields = next()?;
    if root_fields.len() != 2 || root_fields[0] != "ROOT" { return Err("ROOT_RECORD"); }
    let root = reference(root_fields[1], v)?;
    let mut edges = Vec::with_capacity(e);
    for id in 0..e {
        let f = next()?;
        if f.len() != 4 || f[0] != "EDGE" || natural(f[1], 32)? != id { return Err("EDGE_RECORD"); }
        edges.push(Edge { source: reference(f[2], v)?, target: reference(f[3], v)? });
    }
    let mut leaves = Vec::with_capacity(l);
    for id in 0..l {
        let f = next()?;
        if f.len() != 3 || f[0] != "LEAF" || natural(f[1], 32)? != id { return Err("LEAF_RECORD"); }
        leaves.push(reference(f[2], v)?);
    }
    let mut hybrids = Vec::with_capacity(h);
    for id in 0..h {
        let f = next()?;
        if f.len() != 5 || f[0] != "HYBRID" || natural(f[1], 32)? != id { return Err("HYBRID_RECORD"); }
        hybrids.push(Hybrid { vertex: reference(f[2], v)?, incoming: [reference(f[3], e)?, reference(f[4], e)?] });
    }
    let mut chronology = Vec::with_capacity(c);
    for _ in 0..c {
        let f = next()?;
        if f.len() != 4 || f[0] != "AGE" { return Err("AGE_RECORD"); }
        let kind = match f[1] { "LT" => Comparison::Strict, "LE" => Comparison::Weak,
                              "EQ" => Comparison::Equal, _ => return Err("AGE_COMPARISON") };
        chronology.push(AgeConstraint { kind, left: age_atom(f[2], v)?, right: age_atom(f[3], v)? });
    }
    let mut exposures = Vec::with_capacity(x);
    for id in 0..x {
        let f = next()?;
        if f.len() != 7 || f[0] != "EXPOSURE" || natural(f[1], 32)? != id { return Err("EXPOSURE_RECORD"); }
        let population = if f[2] == "A" { Population::Ancestral }
            else if let Some(id) = f[2].strip_prefix("E:") { Population::Edge(reference(id, e)?) }
            else { return Err("POPULATION"); };
        exposures.push(Exposure { population, younger: age_atom(f[3], v)?, older: age_atom(f[4], v)?,
                                 interval: interval(f[5], f[6])? });
    }
    let mut coins = Vec::with_capacity(h);
    for id in 0..h {
        let f = next()?;
        if f.len() != 4 || f[0] != "COIN" || natural(f[1], 32)? != id { return Err("COIN_RECORD"); }
        coins.push(interval(f[2], f[3])?);
    }
    let chart = Chart { source: Source { vertices: v, root, edges, leaves, hybrids }, chronology, exposures, coins, cap };
    cell::compile(&chart)?;
    Ok(chart)
}

fn law_request(header: &[&str], lines: &[&str]) -> Result<law::Request, &'static str> {
    if header.len() != 10 { return Err("LAW_HEADER"); }
    let v = natural(header[2], 32)?;
    let e = natural(header[3], 32)?;
    let l = natural(header[4], 32)?;
    let h = natural(header[5], 32)?;
    let s = natural(header[6], 4)?;
    let budgets = law::Budgets { states: natural(header[7], 4096)?, terms: natural(header[8], 65536)?,
        histories: natural(header[9], 4096)? };
    if v < 3 || e < 2 || l < 2 || s == 0 || v + e + 1 + h > 32
        || lines.len() != 3 + e + l + h + s { return Err("LAW_SIZE"); }
    let mut index = 1;
    let mut next = || { let line = lines[index]; index += 1; fields(line) };
    let mechanism = match next()?.as_slice() {
        ["MECHANISM", "COMMON"] => law::Mechanism::Common,
        ["MECHANISM", "INDEPENDENT"] => law::Mechanism::Independent,
        _ => return Err("LAW_MECHANISM"),
    };
    let root_fields = next()?;
    if root_fields.len() != 2 || root_fields[0] != "ROOT" { return Err("ROOT_RECORD"); }
    let root = reference(root_fields[1], v)?;
    let mut edges = Vec::with_capacity(e);
    for id in 0..e {
        let f = next()?;
        if f.len() != 4 || f[0] != "EDGE" || natural(f[1], 32)? != id { return Err("EDGE_RECORD"); }
        edges.push(Edge { source: reference(f[2], v)?, target: reference(f[3], v)? });
    }
    let mut leaves = Vec::with_capacity(l);
    for id in 0..l {
        let f = next()?;
        if f.len() != 3 || f[0] != "LEAF" || natural(f[1], 32)? != id { return Err("LEAF_RECORD"); }
        leaves.push(reference(f[2], v)?);
    }
    let mut hybrids = Vec::with_capacity(h);
    for id in 0..h {
        let f = next()?;
        if f.len() != 5 || f[0] != "HYBRID" || natural(f[1], 32)? != id { return Err("HYBRID_RECORD"); }
        hybrids.push(Hybrid { vertex: reference(f[2], v)?, incoming: [reference(f[3], e)?, reference(f[4], e)?] });
    }
    let mut samples = Vec::with_capacity(s);
    for id in 0..s {
        let f = next()?;
        if f.len() != 3 || f[0] != "SAMPLE" || natural(f[1], 4)? != id { return Err("SAMPLE_RECORD"); }
        samples.push(reference(f[2], l)?);
    }
    let request = law::Request { source: Source { vertices: v, root, edges, leaves, hybrids },
        samples, mechanism, budgets };
    request.validate()?;
    Ok(request)
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
        "CHART" => Ok(Request::Chart(chart(&header, &lines)?)),
        "LAW" => Ok(Request::Law(law_request(&header, &lines)?)),
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

fn decision_payload(rows: &[Row], decision: Decision) -> (String, u8) {
    let mut output = String::new();
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
            let bound = rows.iter().zip(&weights).fold(q(0, 1), |sum, (row, weight)| sum + &row.bound * weight);
            let strict = rows.iter().zip(&weights).any(|(r, w)| r.strict && w > &q(0, 1));
            output.push_str(&format!("BOUND {}\nSTRICT {}\n", canonical(&bound), u8::from(strict)));
            0
        }
        Decision::Unknown { dimension, required_rows, cap } => {
            output.push_str(&format!("STATUS UNKNOWN\nLIMIT {dimension} {required_rows} {cap}\n"));
            2
        }
    };
    (output, exit_code)
}

fn chart_prefix(chart: &Chart, compiled: &cell::Compiled, raw: &str) -> String {
    let mut output = prefix("CHART", raw);
    output.push_str(&format!("BANK {} {}\n", compiled.dimension, compiled.bank_names.join(" ")));
    output.push_str(&format!("MATRIX {} {} {}\n", compiled.dimension, compiled.rows.len(), chart.cap));
    for row in &compiled.rows {
        output.push_str(if row.strict { "LT " } else { "LE " });
        output.push_str(&canonical(&row.bound));
        for coefficient in &row.coefficients { output.push(' '); output.push_str(&canonical(coefficient)); }
        output.push('\n');
    }
    output.push_str("END_MATRIX\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n");
    output
}

fn law_prefix(request: &law::Request, raw: &str) -> String {
    let variables: Vec<_> = (0..request.source.edges.len()).map(|i| format!("X:{i}"))
        .chain((0..request.source.hybrids.len()).map(|i| format!("G:{i}"))).collect();
    format!("{}VARIABLES {} {}\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n",
        prefix("LAW", raw), variables.len(), variables.join(" "))
}
fn polynomial_terms(output: &mut String, polynomial: &Polynomial) {
    for (powers, coefficient) in &polynomial.terms {
        output.push_str(&format!("TERM {}", canonical(coefficient)));
        for power in powers { output.push_str(&format!(" {power}")); }
        output.push('\n');
    }
}
fn law_unknown(request: &law::Request, raw: &str, limit: &law::Limit) -> Response {
    Response { bytes: format!("{}STATUS UNKNOWN\nLIMIT {} {} {} {}\nEND\n",
        law_prefix(request, raw), limit.kind.token(), limit.vertex, limit.required, limit.cap), exit_code: 2 }
}
fn law_response(request: &law::Request, raw: &str, decision: law::Decision) -> Response {
    match decision {
        law::Decision::Unknown(limit) => law_unknown(request, raw, &limit),
        law::Decision::Table(table) => {
            let mut output = law_prefix(request, raw);
            output.push_str(&format!("STATUS TABLE\nROOTED {}\n", table.rooted.len()));
            for (tree, (_, polynomial)) in &table.rooted {
                output.push_str(&format!("TREE {} {}\n", tree, polynomial.terms.len()));
                polynomial_terms(&mut output, polynomial);
            }
            output.push_str(&format!("UNROOTED {}\n", table.unrooted.len()));
            for (split, polynomial) in &table.unrooted {
                output.push_str(&format!("SPLIT {} {}\n", split, polynomial.terms.len()));
                polynomial_terms(&mut output, polynomial);
            }
            output.push_str("END\n");
            if output.len() > MAX_CERTIFICATE_BYTES {
                law_unknown(request, raw, &law::Limit { kind: law::LimitKind::Output, vertex: request.source.root,
                    required: output.len().into(), cap: MAX_CERTIFICATE_BYTES.into() })
            } else { Response { bytes: output, exit_code: 0 } }
        }
    }
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
            let (body, exit_code) = decision_payload(&rows, decision);
            output.push_str(&body);
            output.push_str("END\n");
            Response { bytes: output, exit_code }
        }
        Request::Count { b, epsilon, sigma, modulus } => {
            let result = count::conditional_count(&b, &epsilon, &sigma, &modulus).unwrap();
            let output = format!("{}STATUS CONDITIONAL_ARITHMETIC\nDELTA {}\nBOUND {}\nCEILING {}\nGATE UNKNOWN_SOURCE_PROVIDER\nEND\n",
                prefix("COUNT", text), canonical(&result.delta), canonical(&result.bound), result.ceiling);
            Response { bytes: output, exit_code: 2 }
        }
        Request::Chart(chart) => {
            let compiled = cell::compile(&chart).unwrap();
            let decision = match affine::solve(compiled.dimension, &compiled.rows, chart.cap) {
                Ok(value) => value, Err(_) => return Response { bytes: INTERNAL.into(), exit_code: 1 },
            };
            if matches!(&decision, Decision::Witness(bank) if !cell::check_bank(&chart, bank)) {
                return Response { bytes: INTERNAL.into(), exit_code: 1 };
            }
            let (body, exit_code) = decision_payload(&compiled.rows, decision);
            let mut output = chart_prefix(&chart, &compiled, text);
            output.push_str(&body);
            output.push_str("END\n");
            Response { bytes: output, exit_code }
        }
        Request::Law(request) => {
            match law::compile(&request) {
                Ok(decision) => law_response(&request, text, decision),
                Err(_) => Response { bytes: INTERNAL.into(), exit_code: 1 },
            }
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
/// LAW uses exact bounded forward re-execution, so its check is a replay, not
/// an independent law algorithm or scientific source-admission proof.
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
        Request::Chart(chart) => {
            let compiled = cell::compile(&chart)?;
            let Some(body) = text.strip_prefix(&chart_prefix(&chart, &compiled, request_text)) else { return Err("REQUEST_OR_MATRIX_IDENTITY"); };
            let lines: Vec<_> = body.strip_suffix('\n').ok_or("CERTIFICATE_FRAME")?.split('\n').collect();
            match lines.first().copied() {
                Some("STATUS SAT") if lines.len() == 4 && lines[3] == "END" => {
                    let assignment = parsed_vector(lines[1], "WITNESS", compiled.dimension)?;
                    let evaluated = parsed_vector(lines[2], "EVAL", compiled.rows.len())?;
                    if !affine::check_witness(compiled.dimension, &compiled.rows, &assignment)
                        || !cell::check_bank(&chart, &assignment) { return Err("INVALID_CHART_WITNESS"); }
                    if compiled.rows.iter().zip(evaluated).any(|(row, value)| row.evaluate(&assignment) != Some(value)) { return Err("INVALID_EVALUATION"); }
                    Ok(())
                }
                Some("STATUS UNSAT") if lines.len() == 5 && lines[4] == "END" => {
                    let weights = parsed_vector(lines[1], "MULTIPLIERS", compiled.rows.len())?;
                    if !affine::check_exclusion(compiled.dimension, &compiled.rows, &weights) { return Err("INVALID_EXCLUSION"); }
                    let bound = compiled.rows.iter().zip(&weights).fold(q(0, 1), |sum, (r, w)| sum + &r.bound * w);
                    let strict = compiled.rows.iter().zip(&weights).any(|(r, w)| r.strict && !w.is_zero());
                    if lines[2] != format!("BOUND {}", canonical(&bound)) || lines[3] != format!("STRICT {}", u8::from(strict)) { return Err("INVALID_DERIVATION"); }
                    Ok(())
                }
                Some("STATUS UNKNOWN") => Err("UNKNOWN_NOT_CERTIFICATE"),
                _ => Err("CERTIFICATE_SHAPE"),
            }
        }
        Request::Law(_) => {
            let response = execute(request_bytes);
            if response.exit_code != 0 { return Err("LAW_UNKNOWN_NOT_CERTIFICATE"); }
            if response.bytes.as_bytes() != certificate { return Err("LAW_REPLAY_DIFFERENCE"); }
            Ok(())
        }
    }
}
