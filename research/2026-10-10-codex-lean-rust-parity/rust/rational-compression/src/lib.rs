//! Private exact port of review_g6_source_generators.py (SHA256 4760fcd13b...).
//! The original-index certificate is checked without RREF. Source realization,
//! arbitrary-real extraction and general native refinement are not supplied.
#![forbid(unsafe_code)]

use calendar_cli::request::Nat;
use parity_solver::{canonical, q, Rational};
use serde::{Deserialize, Serialize};

pub const MAX_REQUEST_BYTES: usize = 65_536;
pub const MAX_RESULT_BYTES: usize = 4 * 1024 * 1024;
pub const DEFAULT_ATOMS: usize = 64;
pub const DEFAULT_MATRIX_CELLS: usize = 8192;
pub const DEFAULT_RATIONAL_BITS: usize = 4096;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AtomDto { pub z: String, pub alpha: String }
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LimitsDto { pub atoms: Nat, pub matrix_cells: Nat, pub rational_bits: Nat }
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RequestDto {
    pub schema: String,
    #[serde(rename = "M")]
    pub m: Nat,
    pub atoms: Vec<AtomDto>,
    pub limits: LimitsDto,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Work { pub elimination_steps: Nat, pub matrix_cells: Nat }
impl Default for Work {
    fn default() -> Self { Self { elimination_steps: Nat(0), matrix_cells: Nat(0) } }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Limit { pub stage: String, pub kind: String, pub required: Nat, pub cap: Nat }
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OutputAtom { pub input_index: Nat, pub beta: String }
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TailMoment { pub level: Nat, pub moment: String }

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Frame {
    pub schema: String,
    pub status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub request_raw: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub request: Option<RequestDto>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub work: Option<Work>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_admission_verified: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_factor_realization_verified: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub arbitrary_real_extraction_verified: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub output_atoms: Option<Vec<OutputAtom>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mass: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tail_moments: Option<Vec<TailMoment>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub limit: Option<Limit>,
}
impl Frame {
    pub fn error(kind: &str) -> Self {
        Self { schema: "g6_rational_compression_result_v1".into(), status: "ERROR".into(),
            error: Some(kind.into()), request_raw: None, request: None, work: None,
            source_admission_verified: None, source_factor_realization_verified: None,
            arbitrary_real_extraction_verified: None, output_atoms: None, mass: None,
            tail_moments: None, limit: None }
    }
    fn bound(raw: &str, dto: RequestDto, work: Work) -> Self {
        Self { request_raw: Some(raw.into()), request: Some(dto), work: Some(work),
            source_admission_verified: Some(false), source_factor_realization_verified: Some(false),
            arbitrary_real_extraction_verified: Some(false), error: None, ..Self::error("") }
    }
    pub fn exit_code(&self) -> i32 {
        match self.status.as_str() { "COMPRESSED" => 0, "UNKNOWN" => 2, _ => 1 }
    }
}

#[derive(Clone)]
struct Atom { index: usize, z: Rational, alpha: Rational }
#[derive(Debug)]
enum Failure { Limit(Limit), Internal }
type Answer<T> = Result<T, Failure>;

fn rational(token: &str) -> Result<Rational, ()> {
    let (num, den) = token.split_once('/').ok_or(())?;
    if den.is_empty() || den == "0" || !den.bytes().all(|b| b.is_ascii_digit())
        || (den.len() > 1 && den.starts_with('0')) { return Err(()); }
    let value = Rational::new(num.parse().map_err(|_| ())?, den.parse().map_err(|_| ())?);
    if canonical(&value) == token { Ok(value) } else { Err(()) }
}
fn bits(value: &Rational) -> usize {
    value.numer().bits().max(value.denom().bits()) as usize
}
fn certificate_rational(token: &str, cap: usize) -> Result<Rational, ()> {
    let (num, den) = token.split_once('/').ok_or(())?;
    // A B-bit integer has at most B/3+1 decimal digits because log10(2)<1/3.
    // This guard follows the explicit bit budget; it adds no hidden digit cap.
    let digits = num.strip_prefix('-').unwrap_or(num);
    if digits.len() > cap / 3 + 1 || den.len() > cap / 3 + 1
        || den.is_empty() || den == "0" || !den.bytes().all(|b| b.is_ascii_digit())
        || (den.len() > 1 && den.starts_with('0')) { return Err(()); }
    let unreduced = Rational::new_raw(num.parse().map_err(|_| ())?, den.parse().map_err(|_| ())?);
    if bits(&unreduced) > cap { return Err(()); }
    // Only bounded numerator/denominator operands reach gcd normalization.
    rational(token)
}
fn parse(raw: &[u8]) -> Result<(RequestDto, Vec<Atom>), ()> {
    if raw.len() > MAX_REQUEST_BYTES { return Err(()); }
    let dto: RequestDto = serde_json::from_slice(raw).map_err(|_| ())?;
    if dto.schema != "g6_rational_compression_request_v1" || !(2..=4).contains(&dto.m.0)
        || dto.limits.atoms.0 > 64 || dto.limits.matrix_cells.0 > 8192
        || dto.limits.rational_bits.0 > 65_536 { return Err(()); }
    let mut atoms = Vec::new();
    for (index, atom) in dto.atoms.iter().enumerate() {
        let z = rational(&atom.z)?;
        let alpha = rational(&atom.alpha)?;
        if z <= q(0, 1) || z >= q(1, 1) || alpha < q(0, 1) { return Err(()); }
        atoms.push(Atom { index, z, alpha });
    }
    Ok((dto, atoms))
}

struct Arithmetic<'a> { cap: usize, stage: &'a str }
impl Arithmetic<'_> {
    fn check(&self, value: &Rational) -> Answer<()> {
        let required = bits(value);
        if required > self.cap { return Err(Failure::Limit(Limit {
            stage: self.stage.into(), kind: "rational_bits".into(), required: Nat(required), cap: Nat(self.cap) })); }
        Ok(())
    }
    fn result(&self, value: Rational) -> Answer<Rational> { self.check(&value)?; Ok(value) }
    fn add(&self, a: &Rational, b: &Rational) -> Answer<Rational> {
        self.check(a)?; self.check(b)?; self.result(a + b)
    }
    fn sub(&self, a: &Rational, b: &Rational) -> Answer<Rational> {
        self.check(a)?; self.check(b)?; self.result(a - b)
    }
    fn mul(&self, a: &Rational, b: &Rational) -> Answer<Rational> {
        self.check(a)?; self.check(b)?; self.result(a * b)
    }
    fn div(&self, a: &Rational, b: &Rational) -> Answer<Rational> {
        self.check(a)?; self.check(b)?;
        if b == &q(0, 1) { return Err(Failure::Internal); }
        self.result(a / b)
    }
    fn geom(&self, level: usize, z: &Rational) -> Answer<Rational> {
        let length = level * (level - 1) / 2;
        let mut value = q(0, 1);
        let mut power = q(1, 1);
        for i in 0..length {
            value = self.add(&value, &power)?;
            if i + 1 < length { power = self.mul(&power, z)?; }
        }
        Ok(value)
    }
}

fn null_vector(original: &[Vec<Rational>], cap: usize) -> Answer<Vec<Rational>> {
    let arithmetic = Arithmetic { cap, stage: "RREF" };
    let mut a = original.to_vec();
    let rows = a.len();
    let cols = a[0].len();
    let mut pivots = Vec::new();
    for col in 0..cols {
        let Some(pivot) = (pivots.len()..rows).find(|i| a[*i][col] != q(0, 1)) else { continue; };
        let row = pivots.len();
        a.swap(row, pivot);
        let divisor = a[row][col].clone();
        for j in 0..cols { a[row][j] = arithmetic.div(&a[row][j], &divisor)?; }
        for other in 0..rows {
            if other == row || a[other][col] == q(0, 1) { continue; }
            let factor = a[other][col].clone();
            for j in 0..cols {
                let term = arithmetic.mul(&factor, &a[row][j])?;
                a[other][j] = arithmetic.sub(&a[other][j], &term)?;
            }
        }
        pivots.push(col);
        if pivots.len() == rows { break; }
    }
    let free = (0..cols).find(|c| !pivots.contains(c)).ok_or(Failure::Internal)?;
    let mut direction = vec![q(0, 1); cols];
    direction[free] = q(1, 1);
    for (row, col) in pivots.into_iter().enumerate() {
        direction[col] = arithmetic.result(-a[row][free].clone())?;
    }
    for row in original {
        let mut sum = q(0, 1);
        for (entry, delta) in row.iter().zip(&direction) {
            sum = arithmetic.add(&sum, &arithmetic.mul(entry, delta)?)?;
        }
        if sum != q(0, 1) { return Err(Failure::Internal); }
    }
    if !direction.iter().any(|x| x > &q(0, 1)) || !direction.iter().any(|x| x < &q(0, 1)) {
        return Err(Failure::Internal);
    }
    Ok(direction)
}

fn moment(level: usize, atoms: &[Atom], cap: usize) -> Answer<Rational> {
    let arithmetic = Arithmetic { cap, stage: "CERTIFICATE" };
    let mut result = q(0, 1);
    for atom in atoms {
        if atom.alpha == q(0, 1) { continue; }
        let coordinate = if level == 2 { q(1, 1) } else { arithmetic.geom(level, &atom.z)? };
        result = arithmetic.add(&result, &arithmetic.mul(&atom.alpha, &coordinate)?)?;
    }
    arithmetic.check(&result)?;
    Ok(result)
}

fn run(dto: &RequestDto, original: &[Atom], work: &mut Work) -> Answer<(Vec<Atom>, Rational, Vec<TailMoment>)> {
    if original.len() > dto.limits.atoms.0 { return Err(Failure::Limit(Limit {
        stage: "INPUT".into(), kind: "atoms".into(), required: Nat(original.len()), cap: dto.limits.atoms })); }
    let input_bits = original.iter().flat_map(|atom| [bits(&atom.z), bits(&atom.alpha)]).max().unwrap_or(1).max(1);
    if input_bits > dto.limits.rational_bits.0 { return Err(Failure::Limit(Limit {
        stage: "INPUT".into(), kind: "rational_bits".into(), required: Nat(input_bits), cap: dto.limits.rational_bits })); }
    let m = dto.m.0;
    let mut current: Vec<Atom> = original.iter().filter(|a| a.alpha != q(0, 1)).cloned().collect();
    while current.len() > m - 1 {
        let required = (m - 1).checked_mul(current.len()).and_then(|n| work.matrix_cells.0.checked_add(n))
            .ok_or(Failure::Internal)?;
        if required > dto.limits.matrix_cells.0 { return Err(Failure::Limit(Limit {
            stage: "MOMENTS".into(), kind: "matrix_cells".into(), required: Nat(required), cap: dto.limits.matrix_cells })); }
        // Precheck and charge BEFORE generating any of the moment columns.
        work.matrix_cells = Nat(required);
        let arithmetic = Arithmetic { cap: dto.limits.rational_bits.0, stage: "MOMENTS" };
        let mut matrix = vec![Vec::new(); m - 1];
        for atom in &current {
            matrix[0].push(q(1, 1));
            for level in 3..=m { matrix[level - 2].push(arithmetic.geom(level, &atom.z)?); }
        }
        let direction = null_vector(&matrix, dto.limits.rational_bits.0)?;
        let arithmetic = Arithmetic { cap: dto.limits.rational_bits.0, stage: "UPDATE" };
        let mut theta: Option<Rational> = None;
        for (atom, delta) in current.iter().zip(&direction) {
            if delta > &q(0, 1) {
                let candidate = arithmetic.div(&atom.alpha, delta)?;
                if theta.as_ref().map_or(true, |old| candidate < *old) { theta = Some(candidate); }
            }
        }
        let theta = theta.ok_or(Failure::Internal)?;
        let old_len = current.len();
        let mut reduced = Vec::new();
        for (mut atom, delta) in current.into_iter().zip(direction) {
            atom.alpha = arithmetic.sub(&atom.alpha, &arithmetic.mul(&theta, &delta)?)?;
            if atom.alpha < q(0, 1) { return Err(Failure::Internal); }
            if atom.alpha != q(0, 1) { reduced.push(atom); }
        }
        if reduced.len() >= old_len { return Err(Failure::Internal); }
        current = reduced;
        work.elimination_steps = Nat(work.elimination_steps.0.checked_add(1).ok_or(Failure::Internal)?);
    }
    let mass = moment(2, original, dto.limits.rational_bits.0)?;
    if mass != moment(2, &current, dto.limits.rational_bits.0)? { return Err(Failure::Internal); }
    let mut tails = Vec::new();
    for level in 3..=m {
        let original_moment = moment(level, original, dto.limits.rational_bits.0)?;
        if original_moment != moment(level, &current, dto.limits.rational_bits.0)? { return Err(Failure::Internal); }
        tails.push(TailMoment { level: Nat(level), moment: canonical(&original_moment) });
    }
    Ok((current, mass, tails))
}

pub fn solve(raw: &[u8]) -> Frame {
    let Ok((dto, original)) = parse(raw) else { return Frame::error("INVALID_REQUEST"); };
    let Ok(raw_string) = std::str::from_utf8(raw) else { return Frame::error("INVALID_REQUEST"); };
    let mut work = Work::default();
    let answer = run(&dto, &original, &mut work);
    let mut result = Frame::bound(raw_string, dto, work);
    match answer {
        Ok((atoms, mass, tails)) => {
            result.status = "COMPRESSED".into();
            result.output_atoms = Some(atoms.into_iter().map(|atom| OutputAtom {
                input_index: Nat(atom.index), beta: canonical(&atom.alpha) }).collect());
            result.mass = Some(canonical(&mass));
            result.tail_moments = Some(tails);
        }
        Err(Failure::Limit(limit)) => { result.status = "UNKNOWN".into(); result.limit = Some(limit); }
        Err(Failure::Internal) => return Frame::error("INTERNAL"),
    }
    result
}

#[derive(Serialize)]
pub struct Check {
    pub schema: &'static str, pub status: &'static str, pub certificate_valid: bool,
    pub producer_work_verified: bool, pub resource_exhaustion_verified: bool,
    pub source_admission_verified: bool, pub source_factor_realization_verified: bool,
    pub arbitrary_real_extraction_verified: bool,
}
impl Check {
    pub fn rejected() -> Self {
        Self { schema: "g6_rational_compression_check_v1", status: "REJECT", certificate_valid: false,
            producer_work_verified: false, resource_exhaustion_verified: false,
            source_admission_verified: false, source_factor_realization_verified: false,
            arbitrary_real_extraction_verified: false }
    }
}

fn verify_inner(raw_request: &[u8], raw_result: &[u8]) -> Result<bool, ()> {
    if raw_result.len() > MAX_RESULT_BYTES { return Err(()); }
    let (dto, original) = parse(raw_request)?;
    let frame: Frame = serde_json::from_slice(raw_result).map_err(|_| ())?;
    // Exact variant fields and canonical output: an explicit null is not an
    // absent field. Reencoding also enforces ordered compact JSON and one LF.
    if encode(&frame)?.as_slice() != raw_result { return Err(()); }
    if frame.schema != "g6_rational_compression_result_v1" || frame.error.is_some()
        || frame.request.as_ref() != Some(&dto)
        || frame.request_raw.as_deref().map(str::as_bytes) != Some(raw_request)
        || frame.source_admission_verified != Some(false) || frame.source_factor_realization_verified != Some(false)
        || frame.arbitrary_real_extraction_verified != Some(false) { return Err(()); }
    let work = frame.work.ok_or(())?;
    if work.matrix_cells.0 > dto.limits.matrix_cells.0 || work.elimination_steps.0 > original.len() { return Err(()); }
    if frame.status == "UNKNOWN" {
        if frame.output_atoms.is_some() || frame.mass.is_some() || frame.tail_moments.is_some() { return Err(()); }
        let limit = frame.limit.ok_or(())?;
        let cap = match limit.kind.as_str() {
            "atoms" => dto.limits.atoms,
            "matrix_cells" => dto.limits.matrix_cells,
            "rational_bits" => dto.limits.rational_bits,
            _ => return Err(()),
        };
        if limit.cap != cap || limit.required.0 <= cap.0
            || !["INPUT", "MOMENTS", "RREF", "UPDATE", "CERTIFICATE"].contains(&limit.stage.as_str()) { return Err(()); }
        if limit.kind == "atoms" && (limit.stage != "INPUT" || limit.required.0 != original.len() || work != Work::default())
            || limit.kind == "matrix_cells" && limit.stage != "MOMENTS" { return Err(()); }
        return Ok(false); // Canonical resource framing, no exhaustion proof.
    }
    if frame.status != "COMPRESSED" || frame.limit.is_some() || original.len() > dto.limits.atoms.0 { return Err(()); }
    let input_bits = original.iter().flat_map(|atom| [bits(&atom.z), bits(&atom.alpha)]).max().unwrap_or(1).max(1);
    if input_bits > dto.limits.rational_bits.0 { return Err(()); }
    let outputs = frame.output_atoms.ok_or(())?;
    if outputs.len() > dto.m.0 - 1 || outputs.windows(2).any(|pair| pair[0].input_index.0 >= pair[1].input_index.0) { return Err(()); }
    let mut selected = Vec::new();
    for atom in outputs {
        let original_atom = original.get(atom.input_index.0).ok_or(())?;
        let beta = certificate_rational(&atom.beta, dto.limits.rational_bits.0)?;
        if beta <= q(0, 1) || bits(&beta) > dto.limits.rational_bits.0 { return Err(()); }
        selected.push(Atom { index: atom.input_index.0, z: original_atom.z.clone(), alpha: beta });
    }
    let mass = certificate_rational(&frame.mass.ok_or(())?, dto.limits.rational_bits.0)?;
    let tails = frame.tail_moments.ok_or(())?;
    if tails.len() != dto.m.0 - 2 || bits(&mass) > dto.limits.rational_bits.0 { return Err(()); }
    let cap = dto.limits.rational_bits.0;
    let original_mass = moment(2, &original, cap).map_err(|_| ())?;
    if mass != original_mass || mass != moment(2, &selected, cap).map_err(|_| ())? { return Err(()); }
    for (level, wire) in (3..=dto.m.0).zip(tails) {
        let reported = certificate_rational(&wire.moment, cap)?;
        if wire.level.0 != level || bits(&reported) > cap
            || reported != moment(level, &original, cap).map_err(|_| ())?
            || reported != moment(level, &selected, cap).map_err(|_| ())? { return Err(()); }
    }
    Ok(true)
}

/// Independent of the elimination routine: exact certificate equations only.
pub fn check(raw_request: &[u8], raw_result: &[u8]) -> Check {
    match verify_inner(raw_request, raw_result) {
        Ok(certificate_valid) => Check { status: "ACCEPT", certificate_valid, ..Check::rejected() },
        Err(()) => Check::rejected(),
    }
}

pub fn encode<T: Serialize>(value: &T) -> Result<Vec<u8>, ()> {
    let ordered = serde_json::to_value(value).map_err(|_| ())?;
    let mut bytes = serde_json::to_vec(&ordered).map_err(|_| ())?;
    bytes.push(b'\n');
    if bytes.len() > MAX_RESULT_BYTES || !bytes.is_ascii() { return Err(()); }
    Ok(bytes)
}
