//! Exact finite positive laws and a literal Lean certificate caller.
//! Reuses CM-T02 and the retained grouped-rational receiver; no physical
//! source admission, solver completeness or unbounded search is inferred.
use parity_solver::{q, Rational};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositiveLaw { atoms: BTreeMap<Rational, Rational> }
#[derive(Clone, Copy, Debug)]
pub struct Limits { pub atoms: usize, pub rational_chars: usize, pub render_bytes: usize }
impl Default for Limits {
    fn default() -> Self { Self { atoms: 1024, rational_chars: 4096, render_bytes: 262144 } }
}
const LEVELS: [u32;5] = [0,1,3,6,10];
impl PositiveLaw {
    /// Group equal scalar values before counting support. A refused input
    /// never becomes a negative mathematical decision.
    pub fn new(input: Vec<(Rational,Rational)>, limits: Limits) -> Result<Self,String> {
        if input.is_empty() || input.len()>limits.atoms { return Err("empty or excessive input bank".into()); }
        let mut atoms=BTreeMap::new();
        for (value,weight) in input {
            if value<=q(0,1) || weight<=q(0,1) { return Err("nodes and on-set weights must be positive".into()); }
            if value.to_string().len()>limits.rational_chars || weight.to_string().len()>limits.rational_chars {
                return Err("rational input limit; UNKNOWN".into());
            }
            let total=atoms.entry(value).or_insert_with(||q(0,1));
            *total+=weight;
            if total.to_string().len()>limits.rational_chars { return Err("grouped coefficient limit; UNKNOWN".into()); }
        }
        if atoms.values().cloned().fold(q(0,1),|a,b|a+b)!=q(1,1) {
            return Err("weights are not normalized".into());
        }
        Ok(Self{atoms})
    }
    pub fn support_len(&self)->usize { self.atoms.len() }
    pub fn moment(&self, degree:u32)->Result<Rational,String> {
        if !LEVELS.contains(&degree) { return Err("outside the CM-T02 level set".into()); }
        Ok(self.atoms.iter().fold(q(0,1),|sum,(value,weight)| {
            let power=(0..degree).fold(q(1,1),|a,_|a*value);
            sum+weight*power
        }))
    }
}
pub fn separating_level(sigma:&PositiveLaw,tau:&PositiveLaw)->Result<u32,String> {
    if sigma.support_len()<3 || tau.support_len()>2 {
        return Err("CM-T02 requires at least three versus at most two grouped positive nodes".into());
    }
    for k in LEVELS { if sigma.moment(k)?!=tau.moment(k)? { return Ok(k); } }
    Err("no certificate found; inconsistent with the stated theorem; no NO result".into())
}
fn literal(r:&Rational)->String {
    format!("({} / {} : ℚ)",r.numer(),r.denom())
}
fn bank(name:&str,law:&PositiveLaw)->String {
    let nodes=law.atoms.keys().map(literal).collect::<Vec<_>>().join(", ");
    let mut weight=String::new();
    for (x,w) in &law.atoms { weight.push_str(&format!("if q = {} then {} else ",literal(x),literal(w))); }
    weight.push('0');
    let cases=std::iter::repeat_n("rfl",law.support_len()).collect::<Vec<_>>().join(" | ");
    format!(r#"
def {name}Nodes : Finset ℚ := {{{nodes}}}
def {name}Weight (q : ℚ) : ℚ := {weight}
theorem {name}NodePos : ∀ q ∈ {name}Nodes, 0 < q := by
  intro q hq
  norm_num [{name}Nodes] at hq
  rcases hq with {cases}
  all_goals norm_num
theorem {name}WeightPos : ∀ q ∈ {name}Nodes, 0 < {name}Weight q := by
  intro q hq
  norm_num [{name}Nodes] at hq
  rcases hq with {cases}
  all_goals norm_num [{name}Weight]
theorem {name}Mass : (∑ q ∈ {name}Nodes, {name}Weight q) = 1 := by
  norm_num [{name}Nodes, {name}Weight]
noncomputable def {name} : FinitePositiveLaw :=
  fromGroupedRationals {name}Nodes {name}Weight {name}NodePos {name}WeightPos {name}Mass
"#)
}
/// Emits complete literals and proofs, with no holes or supplied-law axiom.
/// Successful rendering is not acceptance: the emitted module must be checked.
pub fn lean_certificate(sigma:&PositiveLaw,tau:&PositiveLaw,limits:Limits)->Result<String,String> {
    let k=separating_level(sigma,tau)?;
    let mut source=String::from("import CMSeparation\nimport CMRationalBank\n\nnamespace ResearchCommons.Generated.CMExample\nopen Astra.CommonMoment Astra.CommonMoment.RationalBank\nopen scoped BigOperators\n");
    source.push_str(&bank("sigma",sigma));
    source.push_str(&bank("tau",tau));
    source.push_str(&format!(r#"
theorem different_moment : moment sigma {k} ≠ moment tau {k} := by
  unfold sigma tau
  rw [fromGroupedRationals_moment, fromGroupedRationals_moment]
  norm_num [sigmaNodes, sigmaWeight, tauNodes, tauWeight]
theorem separation :
    ∃ k ∈ capFiveLevels, moment sigma k ≠ moment tau k := by
  exact ⟨{k}, by norm_num [capFiveLevels], different_moment⟩
end ResearchCommons.Generated.CMExample
"#));
    if source.len()>limits.render_bytes { return Err("Lean source byte limit; UNKNOWN".into()); }
    Ok(source)
}
/// Bounds for the complete consecutive moment signature and proof document.
/// Refusal is UNKNOWN; it is never an exclusion of a reaction or source family.
#[derive(Clone,Copy,Debug)]
pub struct SignatureLimits {
 pub degree:usize,pub products:usize,pub rational_chars:usize,pub render_bytes:usize,
}
impl Default for SignatureLimits {
 fn default()->Self{Self{degree:4096,products:2_000_000,rational_chars:8192,render_bytes:262144}}
}
#[derive(Debug,PartialEq,Eq)]
pub enum SignatureError {
 Limit{kind:&'static str,required:usize,cap:usize},Overflow,
}
fn signature_bound(kind:&'static str,n:usize,cap:usize)->Result<(),SignatureError>{
 if n>cap{Err(SignatureError::Limit{kind,required:n,cap})}else{Ok(())}
}
fn signature_rational(q:&Rational,limits:SignatureLimits)->Result<(),SignatureError>{
 signature_bound("rational_chars",q.to_string().len(),limits.rational_chars)
}
/// ONE grouped finite positive target supplies M0..M2r. Powers are reused
/// successively; existing CM-T02 moment API and its emitted bytes are unchanged.
/// Limits are observed after each exact rational operation, not a global allocator.
pub fn consecutive_signature(law:&PositiveLaw,limits:SignatureLimits)
 ->Result<Vec<Rational>,SignatureError>{
 let degree=law.support_len().checked_mul(2).ok_or(SignatureError::Overflow)?;
 signature_bound("degree",degree,limits.degree)?;
 let work=law.support_len().checked_mul(degree.checked_mul(2).and_then(|n|n.checked_add(1))
   .ok_or(SignatureError::Overflow)?).ok_or(SignatureError::Overflow)?;
 signature_bound("rational_products",work,limits.products)?;
 let mut moments=vec![q(0,1);degree.checked_add(1).ok_or(SignatureError::Overflow)?];
 for (value,weight) in &law.atoms {
  signature_rational(value,limits)?;signature_rational(weight,limits)?;
  let mut power=q(1,1);
  for (k,moment) in moments.iter_mut().enumerate(){
   let term=weight*&power;signature_rational(&term,limits)?;
   *moment+=term;signature_rational(moment,limits)?;
   if k<degree{power*=value;signature_rational(&power,limits)?;}
  }
 }
 Ok(moments)
}
/// Particular exact target signature -> all-finite positive atomic-law consumer.
/// Every supplied coordinate is checked again against the literal rational target
/// in Lean. The final theorem quantifies over ALL finite positive rival laws.
/// No stopped-diffusion, derivative-acquisition or latent-reaction refinement is
/// provided by rendering these mathematical finite-law observations.
pub fn lean_signature_certificate(reference:&PositiveLaw,limits:SignatureLimits)
 ->Result<String,SignatureError>{
 let signature=consecutive_signature(reference,limits)?;
 let r=reference.support_len();let count=signature.len();
 let coordinates=signature.iter().map(literal).collect::<Vec<_>>().join(", ");
 let mut source=String::from("import CMFullMomentUniqueness\nimport CMRationalBank\nimport Mathlib.Tactic\n\nnamespace ResearchCommons.Generated.PositiveMomentSignature\nopen Astra.CommonMoment Astra.CommonMoment.RationalBank\nopen scoped Classical BigOperators\n");
 source.push_str(&bank("reference",reference));
 source.push_str(&format!(r#"
def suppliedSignature : Fin {count} → ℚ := ![{coordinates}]
theorem reference_support_cardinality : reference.nodes.card = {r} := by
  change (referenceNodes.image (fun q : ℚ => (q : ℝ))).card = {r}
  rw [Finset.card_image_of_injective _ Rat.cast_injective]
  norm_num [referenceNodes]

theorem literal_signature_checked (i : Fin {count}) :
    moment reference i.val = (suppliedSignature i : ℝ) := by
  fin_cases i
  all_goals unfold reference
  all_goals rw [fromGroupedRationals_moment]
  all_goals norm_num [referenceNodes, referenceWeight, suppliedSignature]

theorem supplied_signature_identifies_every_finite_positive_rival
    (rival : FinitePositiveLaw)
    (h : ∀ i : Fin {count}, moment rival i.val = (suppliedSignature i : ℝ)) :
    atomMass rival = atomMass reference := by
  apply atomMass_eq_of_equal_consecutive_moments
  intro k hk
  have hi : k < {count} := by
    rw [reference_support_cardinality] at hk
    omega
  exact (h ⟨k, hi⟩).trans (literal_signature_checked ⟨k, hi⟩).symm

theorem supplied_signature_determines_every_further_moment
    (rival : FinitePositiveLaw)
    (h : ∀ i : Fin {count}, moment rival i.val = (suppliedSignature i : ℝ)) :
    ∀ k, moment rival k = moment reference k := by
  apply all_moments_eq_of_equal_consecutive_moments
  intro k hk
  have hi : k < {count} := by
    rw [reference_support_cardinality] at hk
    omega
  exact (h ⟨k, hi⟩).trans (literal_signature_checked ⟨k, hi⟩).symm
#check literal_signature_checked
#check supplied_signature_identifies_every_finite_positive_rival
#check supplied_signature_determines_every_further_moment
end ResearchCommons.Generated.PositiveMomentSignature
"#));
 signature_bound("render_bytes",source.len(),limits.render_bytes)?;
 Ok(source)
}
pub fn example()->Result<(PositiveLaw,PositiveLaw),String> {
    let l=Limits::default();
    Ok((PositiveLaw::new(vec![(q(1,1),q(1,3)),(q(2,1),q(1,3)),(q(3,1),q(1,3))],l)?,
        PositiveLaw::new(vec![(q(1,1),q(1,2)),(q(3,1),q(1,2))],l)?))
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn grouped_support_is_the_theorem_support() {
        let l=PositiveLaw::new(vec![(q(2,1),q(1,4)),(q(2,1),q(3,4))],Limits::default()).unwrap();
        assert_eq!(l.support_len(),1);
        assert_eq!(l.moment(3).unwrap(),q(8,1));
    }
    #[test] fn first_sparse_separation_is_exact() {
        let(s,t)=example().unwrap();
        assert_eq!(s.moment(0).unwrap(),t.moment(0).unwrap());
        assert_eq!(s.moment(1).unwrap(),t.moment(1).unwrap());
        assert_eq!(separating_level(&s,&t).unwrap(),3);
        assert_eq!(s.moment(3).unwrap(),q(12,1));
        assert_eq!(t.moment(3).unwrap(),q(14,1));
    }
    #[test] fn invalid_and_out_of_scope_banks_are_refused() {
        let l=Limits::default();
        assert!(PositiveLaw::new(vec![(q(0,1),q(1,1))],l).is_err());
        assert!(PositiveLaw::new(vec![(q(1,1),q(-1,1))],l).is_err());
        assert!(PositiveLaw::new(vec![(q(1,1),q(1,2))],l).is_err());
        let(s,t)=example().unwrap();
        assert!(separating_level(&t,&s).is_err());
        assert!(s.moment(2).is_err());
    }
    #[test] fn output_limit_is_unknown_not_a_negative_claim() {
        let(s,t)=example().unwrap();
        assert!(lean_certificate(&s,&t,Limits{render_bytes:1,..Limits::default()}).is_err());
    }
    #[test] fn complete_signature_matches_the_actual_three_atom_target() {
        let (reference,_)=example().unwrap();
        assert_eq!(consecutive_signature(&reference,SignatureLimits::default()).unwrap(),
          vec![q(1,1),q(2,1),q(14,3),q(12,1),q(98,3),q(92,1),q(794,3)]);
        let source=lean_signature_certificate(&reference,SignatureLimits::default()).unwrap();
        assert!(source.contains("suppliedSignature : Fin 7"));
        assert!(source.contains("supplied_signature_identifies_every_finite_positive_rival"));
        assert!(!source.contains("sorry")&&!source.contains("native_decide"));
    }
    #[test] fn signature_size_uses_grouped_support_and_does_not_refit_a_target() {
        let law=PositiveLaw::new(vec![(q(1,1),q(1,4)),(q(1,1),q(1,4)),
          (q(2,1),q(1,2))],Limits::default()).unwrap();
        assert_eq!(consecutive_signature(&law,SignatureLimits::default()).unwrap(),
          vec![q(1,1),q(3,2),q(5,2),q(9,2),q(17,2)]);
    }
    #[test] fn signature_operation_and_exact_magnitude_limits_return_no_partial_result() {
        let (reference,_)=example().unwrap();
        assert!(matches!(consecutive_signature(&reference,
          SignatureLimits{products:1,..SignatureLimits::default()}),Err(SignatureError::Limit{kind:"rational_products",..})));
        let big=PositiveLaw::new(vec![(q(100,1),q(1,1))],Limits::default()).unwrap();
        assert!(matches!(consecutive_signature(&big,
          SignatureLimits{rational_chars:3,..SignatureLimits::default()}),Err(SignatureError::Limit{kind:"rational_chars",..})));
        assert!(matches!(lean_signature_certificate(&reference,
          SignatureLimits{render_bytes:1,..SignatureLimits::default()}),Err(SignatureError::Limit{kind:"render_bytes",..})));
    }

}
