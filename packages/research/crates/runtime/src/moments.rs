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
}
