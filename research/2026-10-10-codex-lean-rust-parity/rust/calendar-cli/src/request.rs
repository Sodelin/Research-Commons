//! Typed, duplicate-rejecting JSON transport for the frozen nine-field calendar.
use parity_solver::{canonical, natural_cell::{Edge, Hybrid, Source}, Rational,
    source_boundary as boundary, source_calendar as calendar, source_epoch as epoch,
    source_population::{self as population, Context}, source_word as word};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::Error as _;
use serde_json::value::RawValue;

pub const MAX_REQUEST_BYTES: usize = 65_536;

/// Exact semantic natural JSON integer. The permitted token -0 becomes 0;
/// floating point, exponent notation, booleans and strings are rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Nat(pub usize);

impl<'de> Deserialize<'de> for Nat {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let raw = Box::<RawValue>::deserialize(deserializer)?;
        let token = raw.get();
        if token == "-0" { return Ok(Self(0)); }
        if token.is_empty() || !token.bytes().all(|c| c.is_ascii_digit())
            || (token.len() > 1 && token.starts_with('0')) {
            return Err(D::Error::custom("nonnegative JSON integer required"));
        }
        let value = token.parse::<u64>().map_err(D::Error::custom)?;
        usize::try_from(value).map(Self).map_err(D::Error::custom)
    }
}
impl Serialize for Nat {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u64(self.0 as u64)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContextDto {
    pub vertices: Nat,
    pub root: Nat,
    pub edges: Vec<[Nat; 2]>,
    pub leaves: Vec<Nat>,
    pub hybrids: Vec<[Nat; 3]>,
    pub local_samples: Vec<Nat>,
    pub global_labels: Vec<Nat>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompilerLimitsDto {
    pub word_length: Nat, pub slots: Nat, pub variables: Nat,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WordLimitsDto {
    pub initial_assignments: Nat, pub initial_terms: Nat, pub queries: Nat,
    pub branches: Nat, pub term_products: Nat, pub destinations: Nat, pub terms: Nat,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EpochLimitsDto {
    pub calls: Nat, pub destinations: Nat, pub lifted_terms: Nat,
    pub branches: Nat, pub term_products: Nat,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundaryLimitsDto {
    pub assignments: Nat, pub destinations: Nat, pub term_contributions: Nat,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompletionLimitsDto {
    pub calls: Nat, pub destinations: Nat, pub lifted_terms: Nat,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProviderLimitsDto {
    pub epoch: EpochLimitsDto,
    pub boundary: BoundaryLimitsDto,
    pub completion: CompletionLimitsDto,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum TerminalDto {
    #[serde(rename = "FULL_VIEW")]
    FullView,
    #[serde(rename = "ANCESTRAL_COMPLETE")]
    AncestralComplete,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RequestDto {
    pub context: ContextDto,
    pub ages: Vec<String>,
    pub inverse_rates: Vec<String>,
    pub original_gamma: Vec<String>,
    pub common: Vec<bool>,
    pub terminal: TerminalDto,
    pub compiler_limits: CompilerLimitsDto,
    pub word_limits: WordLimitsDto,
    pub provider_limits: ProviderLimitsDto,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RequestError(pub &'static str);

pub fn parse_request(raw: &[u8]) -> Result<RequestDto, RequestError> {
    if raw.len() > MAX_REQUEST_BYTES { return Err(RequestError("SOURCE_CALENDAR_REQUEST_BYTES")); }
    serde_json::from_slice(raw).map_err(|_| RequestError("SOURCE_CALENDAR_JSON"))
}

fn rational(token: &str) -> Result<Rational, RequestError> {
    let bad = || RequestError("SOURCE_CALENDAR_RATIONAL");
    let (numerator, denominator) = token.split_once('/').ok_or_else(bad)?;
    // Avoid the arithmetic constructor's zero-denominator panic before reduction.
    if denominator.is_empty() || denominator == "0"
        || !denominator.bytes().all(|c| c.is_ascii_digit())
        || (denominator.len() > 1 && denominator.starts_with('0')) {
        return Err(bad());
    }
    let value = Rational::new(numerator.parse().map_err(|_| bad())?,
                              denominator.parse().map_err(|_| bad())?);
    if canonical(&value) != token { return Err(bad()); }
    Ok(value)
}

impl RequestDto {
    pub fn to_request(&self) -> Result<calendar::Request, RequestError> {
        let c = &self.context;
        let w = &self.word_limits;
        let p = &self.provider_limits;
        Ok(calendar::Request {
            context: Context { source: Source {
                vertices: c.vertices.0, root: c.root.0,
                edges: c.edges.iter().map(|pair| Edge { source: pair[0].0, target: pair[1].0 }).collect(),
                leaves: c.leaves.iter().map(|x| x.0).collect(),
                hybrids: c.hybrids.iter().map(|triple| Hybrid { vertex: triple[0].0,
                    incoming: [triple[1].0, triple[2].0] }).collect(),
            }, sample: c.local_samples.iter().map(|x| x.0).collect(),
               global_labels: c.global_labels.iter().map(|x| x.0).collect() },
            ages: self.ages.iter().map(|q| rational(q)).collect::<Result<_, _>>()?,
            inverse_rates: self.inverse_rates.iter().map(|q| rational(q)).collect::<Result<_, _>>()?,
            original_gamma: self.original_gamma.iter().map(|q| rational(q)).collect::<Result<_, _>>()?,
            common: self.common.clone(),
            terminal: match self.terminal {
                TerminalDto::FullView => word::Terminal::FullView,
                TerminalDto::AncestralComplete => word::Terminal::AncestralComplete,
            },
            compiler_limits: calendar::CompilerLimits { word_length: self.compiler_limits.word_length.0,
                slots: self.compiler_limits.slots.0, variables: self.compiler_limits.variables.0 },
            word_limits: word::Limits { initial_assignments: w.initial_assignments.0,
                initial_terms: w.initial_terms.0, queries: w.queries.0, branches: w.branches.0,
                term_products: w.term_products.0, destinations: w.destinations.0, terms: w.terms.0 },
            provider_limits: word::ProviderLimits {
                epoch: epoch::Limits { calls: p.epoch.calls.0, destinations: p.epoch.destinations.0,
                    lifted_terms: p.epoch.lifted_terms.0, branches: p.epoch.branches.0,
                    term_products: p.epoch.term_products.0 },
                boundary: boundary::Limits { assignments: p.boundary.assignments.0,
                    destinations: p.boundary.destinations.0, term_contributions: p.boundary.term_contributions.0 },
                completion: population::Limits { calls: p.completion.calls.0,
                    destinations: p.completion.destinations.0, lifted_terms: p.completion.lifted_terms.0 },
            },
        })
    }
}
