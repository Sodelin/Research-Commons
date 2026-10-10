//! Explicit natural completed rooted observer, with bounded result serialization.
use crate::source_fit::{self, Frame};
use parity_solver::{canonical, source_fit_bank as bank, source_fit_readout as readout,
    source_population::tree_string};
use serde::{Serialize, Serializer, ser::SerializeSeq};
use serde_json::{json, value::RawValue, Value};
use std::io::{self, Write};

struct Terms<'a>(&'a parity_solver::polynomial::Polynomial);
impl Serialize for Terms<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.0.terms.len()))?;
        for (powers, coefficient) in &self.0.terms { seq.serialize_element(&(powers, canonical(coefficient)))?; }
        seq.end()
    }
}
#[derive(Serialize)]
struct Outcome<'a> { tree: String, probability: String, edge_polynomial: Terms<'a> }
struct Outcomes<'a>(&'a [readout::Outcome]);
impl Serialize for Outcomes<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for row in self.0 { seq.serialize_element(&Outcome {
            tree: tree_string(&row.tree), probability: canonical(&row.probability), edge_polynomial: Terms(&row.polynomial),
        })?; }
        seq.end()
    }
}
#[derive(Serialize)]
struct Configuration<'a> { label: &'a str, weight: String, forcing: &'a [Option<bool>], outcomes: Outcomes<'a> }
struct Configurations<'a>(&'a [readout::ConfigurationLaw]);
impl Serialize for Configurations<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for row in self.0 { seq.serialize_element(&Configuration {
            label: &row.label, weight: canonical(&row.weight), forcing: &row.forcing, outcomes: Outcomes(&row.outcomes),
        })?; }
        seq.end()
    }
}
#[derive(Serialize)]
struct Response<'a> {
    schema: &'static str, status: &'static str, observer: &'static str,
    bank_result: &'a RawValue, readout_request: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    configurations: Option<Configurations<'a>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    mixture: Option<Outcomes<'a>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    limit: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    reason: Option<Value>,
    work: Value,
    source_admission_verified: bool, source_observation_fit_verified: bool,
    source_provenance_verified: bool, timed_readout_verified: bool,
    full_code_evaluated: bool, universal_native_refinement_verified: bool,
    certificate_valid: bool, full_solver_verified: bool,
}
struct BoundedBuffer { bytes: Vec<u8> }
impl Write for BoundedBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.bytes.len().saturating_add(buf.len()) > bank::MAX_RESULT_BYTES {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "SOURCE_FIT_RESULT_BYTES"));
        }
        self.bytes.extend_from_slice(buf); Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}
fn request_value(request: &readout::Request) -> Value {
    let w = &request.word_limits; let p = &request.provider_limits; let l = &request.limits;
    json!({"observer":"ROOTED_UNRANKED_COMPLETE", "forget_configuration_label":request.forget_configuration_label,
        "program":request.program.iter().map(|t| json!({"label":t.label,"weight":canonical(&t.weight),"forcing":t.forcing})).collect::<Vec<_>>(),
        "word_limits":{"initial_assignments":w.initial_assignments,"initial_terms":w.initial_terms,
            "queries":w.queries,"branches":w.branches,"term_products":w.term_products,"destinations":w.destinations,"terms":w.terms},
        "provider_limits":{"epoch":{"calls":p.epoch.calls,"destinations":p.epoch.destinations,"lifted_terms":p.epoch.lifted_terms,
                "branches":p.epoch.branches,"term_products":p.epoch.term_products},
            "boundary":{"assignments":p.boundary.assignments,"destinations":p.boundary.destinations,"term_contributions":p.boundary.term_contributions},
            "completion":{"calls":p.completion.calls,"destinations":p.completion.destinations,"lifted_terms":p.completion.lifted_terms}},
        "limits":{"word_rows":l.word_rows,"monomial_contributions":l.monomial_contributions,"normalized_terms":l.normalized_terms,
            "arithmetic_steps":l.arithmetic_steps,"rational_bits":l.rational_bits,"power_exponent":l.power_exponent}})
}

pub fn natural(raw: &[u8]) -> Frame {
    let request = match source_fit::parse(raw) { Ok(r) => r, Err(code) => return source_fit::error(code) };
    let decision = match bank::bind(&request) {
        Ok(d) => d, Err(_) => return source_fit::bind(raw),
    };
    let bank = match &decision { bank::Decision::SymbolicBank(b) => b, _ => return source_fit::bind(raw) };
    let bank_json = match bank::canonical_response(&request, &decision) {
        Ok(j) => j, Err(_) => return source_fit::limit_error("SOURCE_FIT_RESPONSE_LIMIT"),
    };
    let bank_json = RawValue::from_string(bank_json).expect("checked bank serializer emits JSON");
    let readout_request = readout::Request::natural(bank);
    let result = match readout::readout(bank, &readout_request) {
        Ok(r) => r,
        Err(readout::Error::InvalidInput(code)) => return source_fit::error(code),
        Err(readout::Error::Internal(code)) => return source_fit::internal_error(code),
    };
    let mut response = Response { schema:"source_fit_rooted_result_v1", status:"UNKNOWN", observer:"ROOTED_UNRANKED_COMPLETE",
        bank_result:&bank_json, readout_request:request_value(&readout_request), configurations:None, mixture:None, limit:None, reason:None,
        work:json!({}), source_admission_verified:false, source_observation_fit_verified:false, source_provenance_verified:false,
        timed_readout_verified:false, full_code_evaluated:false, universal_native_refinement_verified:false,
        certificate_valid:false, full_solver_verified:false };
    let exit_code = match &result {
        readout::Decision::Table(table) => {
            response.status = "TABLE"; response.configurations = Some(Configurations(&table.configurations));
            response.mixture = table.mixture.as_deref().map(Outcomes);
            response.work = json!({"word_rows":table.work.word_rows,"monomial_contributions":table.work.monomial_contributions,
                "largest_normalized_terms":table.work.largest_normalized_terms,"arithmetic_steps":table.work.arithmetic_steps});
            0
        },
        readout::Decision::Unknown(readout::Unknown::Collection(limit)) => {
            response.limit = Some(json!({"stage":limit.stage,"kind":limit.kind,"required":limit.required,"cap":limit.cap})); 2
        },
        readout::Decision::Unknown(readout::Unknown::Provider(limit)) => {
            let population = limit.population.map(|p| match p {
                parity_solver::source_population::Location::Node(v) => json!(["V",v]),
                parity_solver::source_population::Location::Edge(e) => json!(["E",e]),
                parity_solver::source_population::Location::Ancestral(r) => json!(["A",r]),
            });
            response.limit = Some(json!({"stage":format!("{:?}",limit.stage),"kind":format!("{:?}",limit.kind),
                "population":population,"required":limit.required,"cap":limit.cap})); 2
        },
        readout::Decision::Unsupported(reason) => {
            response.status = "UNSUPPORTED";
            response.reason = Some(match reason {
                readout::Unsupported::RequiresNaturalCompletedWord => json!({"kind":"REQUIRES_NATURAL_COMPLETED_WORD"}),
                readout::Unsupported::UsedInactiveOrAncestralVariable { tree, variable } =>
                    json!({"kind":"USED_INACTIVE_OR_ANCESTRAL_VARIABLE","tree":tree,"variable":format!("{variable:?}")}),
                readout::Unsupported::ResidualFractionalExponent { tree, original_edge, exponent } =>
                    json!({"kind":"RESIDUAL_FRACTIONAL_EXPONENT","tree":tree,"original_edge":original_edge,"exponent":canonical(exponent)}),
            }); 2
        },
    };
    let mut output = BoundedBuffer { bytes:Vec::new() };
    if serde_json::to_writer(&mut output, &response).is_err() || output.write_all(b"\n").is_err() {
        return source_fit::limit_error("SOURCE_FIT_ROOTED_RESULT_BYTES");
    }
    Frame { bytes:output.bytes, exit_code }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn old_common_independent_and_permuted_global_laws_agree_exactly() {
        let cases: &[(&[u8], &[u8])] = &[
            (include_bytes!("../../fixtures/source-fit/hybrid-common-sat.request.json"), include_bytes!("../../fixtures/source-fit/hybrid-common-sat.expected.json")),
            (include_bytes!("../../fixtures/source-fit/hybrid-independent-sat.request.json"), include_bytes!("../../fixtures/source-fit/hybrid-independent-sat.expected.json")),
            (include_bytes!("../../fixtures/source-fit/hybrid-common-permuted.request.json"), include_bytes!("../../fixtures/source-fit/hybrid-common-permuted.expected.json")),
        ];
        for (raw, expected) in cases {
            let frame = natural(raw); assert_eq!(frame.exit_code, 0, "{}", String::from_utf8_lossy(&frame.bytes));
            let actual: Value = serde_json::from_slice(&frame.bytes).unwrap();
            let expected: Value = serde_json::from_slice(expected).unwrap();
            let rows = actual["mixture"].as_array().unwrap().iter().map(|r| json!({"tree":r["tree"],"probability":r["probability"]})).collect::<Vec<_>>();
            assert_eq!(json!(rows), expected["expected_global_rows"]);
            assert_eq!(actual["configurations"][0]["outcomes"], actual["mixture"]);
            for flag in ["source_admission_verified", "source_observation_fit_verified", "source_provenance_verified",
                "timed_readout_verified", "full_code_evaluated", "universal_native_refinement_verified", "certificate_valid", "full_solver_verified"] {
                assert_eq!(actual[flag], false, "{flag}");
            }
        }
    }
    #[test]
    fn full_view_request_is_explicitly_unsupported_by_completed_observer() {
        let mut raw: Value = serde_json::from_slice(include_bytes!("../../fixtures/source-fit/hybrid-common-sat.request.json")).unwrap();
        raw["terminal"] = json!("FULL_VIEW");
        let result = natural(&serde_json::to_vec(&raw).unwrap());
        assert_eq!(result.exit_code, 2);
        let response: Value = serde_json::from_slice(&result.bytes).unwrap();
        assert_eq!(response["status"], "UNSUPPORTED");
        assert_eq!(response["reason"]["kind"], "REQUIRES_NATURAL_COMPLETED_WORD");
    }
}
