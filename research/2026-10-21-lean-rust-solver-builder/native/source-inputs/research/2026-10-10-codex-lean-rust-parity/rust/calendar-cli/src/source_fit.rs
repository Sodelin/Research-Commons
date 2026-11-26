//! Bounded JSON adapter for a supplied exact assignment and equation trace.
//! Trace satisfaction does not authenticate the source of those equations.
use crate::request::{CompilerLimitsDto, ContextDto, Nat, TerminalDto};
use parity_solver::{canonical, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial,
    source_calendar, source_fit_bank as bank, source_population::Context, source_word, Rational};
use serde::Deserialize;
use num_bigint::BigInt;
use std::collections::BTreeMap;

#[derive(Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
pub enum ValueDto {
    #[serde(rename = "RATIONAL")]
    Rational { value: String },
    #[serde(rename = "ALGEBRAIC")]
    Algebraic { polynomial_ascending: Vec<String>, real_root_index: Nat },
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TermDto { pub powers: Vec<Nat>, pub coefficient: String }
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EquationDto { pub dimension: Nat, pub terms: Vec<TermDto> }
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LimitsDto {
    pub equations: Nat, pub terms: Nat, pub arithmetic_steps: Nat,
    pub rational_bits: Nat, pub power_exponent: Nat,
}
#[derive(Deserialize)]
pub enum MechanismDto { #[serde(rename = "COMMON")] Common, #[serde(rename = "INDEPENDENT")] Independent }
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RequestDto {
    pub schema: String,
    pub context: ContextDto,
    pub vertex_names: Vec<String>, pub taxon_labels: Vec<String>,
    pub hybrid_labels: Vec<String>, pub copy_labels: Vec<String>,
    pub variables: Vec<String>, pub values: Vec<ValueDto>, pub equations: Vec<EquationDto>,
    pub mechanism: MechanismDto, pub terminal: TerminalDto,
    pub compiler_limits: CompilerLimitsDto, pub limits: LimitsDto,
}

fn rational(token: &str) -> Result<Rational, &'static str> {
    let bad = "SOURCE_FIT_RATIONAL";
    let (n, d) = token.split_once('/').ok_or(bad)?;
    let digits = n.strip_prefix('-').unwrap_or(n);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit())
        || (digits.len() > 1 && digits.starts_with('0')) || n == "-0"
        || d.is_empty() || d == "0" || !d.bytes().all(|b| b.is_ascii_digit())
        || (d.len() > 1 && d.starts_with('0')) { return Err(bad); }
    let numerator = n.parse::<BigInt>().map_err(|_| bad)?;
    let denominator = d.parse::<BigInt>().map_err(|_| bad)?;
    if numerator.bits().max(denominator.bits()) > 65_536 { return Err("SOURCE_FIT_HARD_RATIONAL_BITS"); }
    let q = Rational::new(numerator, denominator);
    if canonical(&q) != token { return Err(bad); }
    Ok(q)
}

pub fn parse(raw: &[u8]) -> Result<bank::Request, &'static str> {
    if raw.len() > bank::MAX_REQUEST_BYTES { return Err("SOURCE_FIT_REQUEST_BYTES"); }
    let dto: RequestDto = serde_json::from_slice(raw).map_err(|_| "SOURCE_FIT_JSON")?;
    if dto.schema != "source_fit_request_v1" { return Err("SOURCE_FIT_SCHEMA"); }
    dto.to_request()
}
impl RequestDto {
    pub fn to_request(&self) -> Result<bank::Request, &'static str> {
        let c = &self.context;
        let values = self.values.iter().map(|value| match value {
            ValueDto::Rational { value } => rational(value).map(bank::ExactValue::Rational),
            ValueDto::Algebraic { polynomial_ascending, real_root_index } => Ok(bank::ExactValue::Algebraic {
                polynomial_ascending: polynomial_ascending.iter().map(|q| rational(q)).collect::<Result<_, _>>()?,
                real_root_index: real_root_index.0,
            }),
        }).collect::<Result<_, _>>()?;
        let equations = self.equations.iter().map(|row| {
            let mut terms = BTreeMap::new();
            let mut previous = None;
            for term in &row.terms {
                let powers = term.powers.iter().map(|n| n.0).collect::<Vec<_>>();
                if powers.len() != row.dimension.0 || previous.as_ref().is_some_and(|p| p >= &powers) {
                    return Err("SOURCE_FIT_CANONICAL_TERMS");
                }
                let coefficient = rational(&term.coefficient)?;
                if coefficient == parity_solver::q(0, 1) { return Err("SOURCE_FIT_ZERO_TERM"); }
                previous = Some(powers.clone());
                terms.insert(powers, coefficient);
            }
            Ok(Polynomial { dimension: row.dimension.0, terms })
        }).collect::<Result<_, &'static str>>()?;
        Ok(bank::Request {
            context: Context { source: Source {
                vertices: c.vertices.0, root: c.root.0,
                edges: c.edges.iter().map(|e| Edge { source: e[0].0, target: e[1].0 }).collect(),
                leaves: c.leaves.iter().map(|v| v.0).collect(),
                hybrids: c.hybrids.iter().map(|h| Hybrid { vertex: h[0].0, incoming: [h[1].0, h[2].0] }).collect(),
            }, sample: c.local_samples.iter().map(|v| v.0).collect(),
                global_labels: c.global_labels.iter().map(|v| v.0).collect() },
            vertex_names: self.vertex_names.clone(), taxon_labels: self.taxon_labels.clone(),
            hybrid_labels: self.hybrid_labels.clone(), copy_labels: self.copy_labels.clone(),
            variables: self.variables.clone(), values, equations,
            mechanism: match self.mechanism { MechanismDto::Common => bank::Mechanism::Common,
                MechanismDto::Independent => bank::Mechanism::Independent },
            terminal: match self.terminal { TerminalDto::FullView => source_word::Terminal::FullView,
                TerminalDto::AncestralComplete => source_word::Terminal::AncestralComplete },
            compiler_limits: source_calendar::CompilerLimits { word_length: self.compiler_limits.word_length.0,
                slots: self.compiler_limits.slots.0, variables: self.compiler_limits.variables.0 },
            limits: bank::Limits { equations: self.limits.equations.0, terms: self.limits.terms.0,
                arithmetic_steps: self.limits.arithmetic_steps.0, rational_bits: self.limits.rational_bits.0,
                power_exponent: self.limits.power_exponent.0 },
        })
    }
}

pub struct Frame { pub bytes: Vec<u8>, pub exit_code: u8 }
fn failure(status: &'static str, code: &'static str, exit_code: u8) -> Frame {
    Frame { bytes: format!("{{\"schema\":\"source_fit_error_v1\",\"status\":\"{status}\",\"code\":\"{code}\"}}\n").into_bytes(), exit_code }
}
pub fn error(code: &'static str) -> Frame {
    failure("INVALID_REQUEST", code, 1)
}
pub fn execution_error(code: &'static str) -> Frame { failure("EXECUTION_FAILURE", code, 1) }
pub fn internal_error(code: &'static str) -> Frame { failure("INTERNAL", code, 1) }
pub fn limit_error(code: &'static str) -> Frame { failure("UNKNOWN", code, 2) }
pub fn bind(raw: &[u8]) -> Frame {
    let request = match parse(raw) { Ok(r) => r, Err(code) => return error(code) };
    let decision = match bank::bind(&request) {
        Ok(d) => d,
        Err(bank::Error::InvalidInput(code)) => return error(code),
        Err(bank::Error::Internal(code)) => return failure("INTERNAL", code, 1),
        Err(bank::Error::FrameLimit { .. }) => return failure("UNKNOWN", "SOURCE_FIT_FRAME_LIMIT", 2),
    };
    let exit_code = if matches!(decision, bank::Decision::SymbolicBank(_)) { 0 } else { 2 };
    match bank::canonical_response(&request, &decision) {
        Ok(bytes) => Frame { bytes: bytes.into_bytes(), exit_code },
        Err(_) => failure("UNKNOWN", "SOURCE_FIT_RESPONSE_LIMIT", 2),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const COMMON: &[u8] = include_bytes!("../../fixtures/source-fit/hybrid-common-sat.request.json");
    const INDEPENDENT: &[u8] = include_bytes!("../../fixtures/source-fit/hybrid-independent-sat.request.json");

    #[test]
    fn saved_shared_witnesses_bind_and_changed_equation_is_refused() {
        for raw in [COMMON, INDEPENDENT] {
            let frame = bind(raw);
            assert_eq!(frame.exit_code, 0);
            let result: serde_json::Value = serde_json::from_slice(&frame.bytes).unwrap();
            assert_eq!(result["status"], "SYMBOLIC_BANK");
            assert_eq!(result["source_observation_fit_verified"], false);
            assert_eq!(result["source_admission_verified"], false);
        }
        let mut changed: serde_json::Value = serde_json::from_slice(COMMON).unwrap();
        changed["equations"][0]["terms"][0]["coefficient"] = serde_json::json!("123/1");
        assert_eq!(bind(&serde_json::to_vec(&changed).unwrap()).exit_code, 1);
    }

    #[test]
    fn duplicate_fields_fractional_indices_and_unknown_fields_are_rejected() {
        let source = String::from_utf8(COMMON.to_vec()).unwrap();
        let duplicated = source.replacen('{', "{\"mechanism\":\"COMMON\",", 1);
        assert!(parse(duplicated.as_bytes()).is_err());
        let mut fractional: serde_json::Value = serde_json::from_slice(COMMON).unwrap();
        fractional["context"]["vertices"] = serde_json::json!(7.0);
        assert!(parse(&serde_json::to_vec(&fractional).unwrap()).is_err());
        fractional["context"]["vertices"] = serde_json::json!(7);
        fractional["source_admission_verified"] = serde_json::json!(true);
        assert!(parse(&serde_json::to_vec(&fractional).unwrap()).is_err());
    }

    #[test]
    fn oversized_integer_and_noncanonical_rational_inputs_are_refused() {
        let large = BigInt::from(1u8) << 65_536usize;
        assert_eq!(rational(&format!("{large}/1")), Err("SOURCE_FIT_HARD_RATIONAL_BITS"));
        for token in ["2/4", "-0/1", "1/0", "01/2", "+1/2", "1/-2"] {
            assert!(rational(token).is_err(), "{token}");
        }
        assert_eq!(parse(&vec![b' '; bank::MAX_REQUEST_BYTES + 1]), Err("SOURCE_FIT_REQUEST_BYTES"));
    }
}
