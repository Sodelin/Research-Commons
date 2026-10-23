//! Exact application of the retained finite-ensemble residual top-k theorem.
//! This consumes a COMPLETE supplied ensemble. It does not infer RNA support,
//! class weights, concentration, source admission or stochastic discovery.
use parity_solver::{q,Rational};
use std::collections::BTreeSet;

#[derive(Clone,Copy,Debug)]
pub struct Limits {
 pub items:usize,pub classes:usize,pub rational_chars:usize,pub render_bytes:usize,
}
impl Default for Limits {
 fn default()->Self {Self{items:256,classes:128,rational_chars:4096,render_bytes:262144}}
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Error {Invalid(&'static str),Unknown(&'static str),Inconclusive}

#[derive(Clone,Debug,PartialEq,Eq)]
pub struct Item {pub class:usize,pub weight:Rational}
/// Private owning data prevent replacing the ensemble after certification.
/// Repeated classes/weights remain distinct ensemble positions.
#[derive(Debug)]
pub struct Ensemble {
 items:Vec<Item>,classes:usize,class_weights:Vec<Rational>,total:Rational,
}
#[derive(Debug)]
pub struct Certificate {
 ensemble:Ensemble,selected:Vec<usize>,residual:Rational,
}
fn bounded(value:&Rational,limit:usize)->Result<(),Error> {
 if value.to_string().len()>limit {Err(Error::Unknown("rational_chars"))} else {Ok(())}
}
impl Ensemble {
 pub fn new(items:Vec<Item>,classes:usize,limits:Limits)->Result<Self,Error> {
  if items.len()>limits.items||classes>limits.classes{return Err(Error::Unknown("ensemble_size"));}
  if classes==0||items.is_empty(){return Err(Error::Invalid("empty source ensemble"));}
  let mut class_weights=vec![q(0,1);classes];let mut total=q(0,1);
  for item in &items {
   if item.class>=classes{return Err(Error::Invalid("class outside declared carrier"));}
   if item.weight<q(0,1){return Err(Error::Invalid("negative source weight"));}
   bounded(&item.weight,limits.rational_chars)?;
   class_weights[item.class]+=&item.weight;total+=&item.weight;
   bounded(&class_weights[item.class],limits.rational_chars)?;
   bounded(&total,limits.rational_chars)?;
  }
  if total<=q(0,1){return Err(Error::Invalid("zero partition"));}
  Ok(Self{items,classes,class_weights,total})
 }
 /// A successful sufficient certificate proves the selected set, not an
 /// internal order. Failure is INCONCLUSIVE, even for a true top-k set.
 pub fn certify(self,selected:Vec<usize>,k:usize,limits:Limits)->Result<Certificate,Error> {
  if selected.len()!=k{return Err(Error::Invalid("selected cardinality"));}
  let mut seen=BTreeSet::new();
  for &c in &selected {
   if c>=self.classes{return Err(Error::Invalid("selected class outside carrier"));}
   if !seen.insert(c){return Err(Error::Invalid("duplicate selected class"));}
  }
  let mut residual=q(0,1);
  for item in &self.items {
   if !seen.contains(&item.class){residual+=&item.weight;}
   bounded(&residual,limits.rational_chars)?;
  }
  if selected.iter().any(|c|self.class_weights[*c]<=residual){return Err(Error::Inconclusive);}
  Ok(Certificate{ensemble:self,selected,residual})
 }
}
fn real(x:&Rational)->String{format!("({} / {} : ℝ)",x.numer(),x.denom())}
fn vector(items:Vec<String>)->String{
 if items.is_empty(){"Fin.elim0".into()}else{format!("![{}]",items.join(", "))}
}
impl Certificate {
 pub fn selected(&self)->&[usize]{&self.selected}
 pub fn partition(&self)->&Rational{&self.ensemble.total}
 pub fn residual_weight(&self)->&Rational{&self.residual}
 pub fn selected_mass(&self,c:usize)->Option<Rational>{
  if self.selected.contains(&c){Some(&self.ensemble.class_weights[c]/&self.ensemble.total)}else{None}
 }
 /// Render a complete independent proof from the SAME owned raw ensemble.
 /// No native comparison is used as a theorem premise; Lean checks all literal
 /// weights, original sums, cardinality and residual gaps again.
 pub fn lean_certificate(&self,limits:Limits)->Result<String,Error> {
  if self.ensemble.items.len()>limits.items||self.ensemble.classes>limits.classes{
   return Err(Error::Unknown("ensemble_size"));
  }
  let n=self.ensemble.items.len();let m=self.ensemble.classes;let k=self.selected.len();
  let weights=vector(self.ensemble.items.iter().map(|i|real(&i.weight)).collect());
  let classes=vector(self.ensemble.items.iter().map(|i|format!("⟨{}, by decide +kernel⟩",i.class)).collect());
  let selected=self.selected.iter().map(|c|format!("⟨{c}, by decide +kernel⟩")).collect::<Vec<_>>().join(", ");
  let source=format!(r#"import E8ExactResidualMass
import Mathlib.Tactic

namespace ResearchCommons.Generated.ResidualTopK
open scoped BigOperators
open E8ExactResidualMass E8DeterministicTopKCertificate
def weight : Fin {n} → ℝ := {weights}
def classify : Fin {n} → Fin {m} := {classes}
def selected : Finset (Fin {m}) := {{{selected}}}

/-- The SAME literal full finite ensemble supplies every class and residual
mass. There is no independently fitted probability vector or missing-support
assumption. The theorem proves a selected SET, not its internal ranking. -/
theorem supplied_ensemble_strict_top_k :
    IsStrictTopKSet (classMass Finset.univ classify weight) selected {k} := by
  apply exact_residual_topK Finset.univ classify weight selected {k}
  · norm_num [selected]
  · intro r _
    fin_cases r <;> norm_num [weight]
  · norm_num [partition, weight, Fin.sum_univ_succ]
  · intro c hc
    fin_cases c <;>
      norm_num [selected, residualMass, classMass, outsidePartition,
        classPartition, partition, classify, weight, Fin.sum_univ_succ] at hc ⊢

theorem same_ensemble_residual_conservation :
    residualMass Finset.univ classify weight selected =
      1 - ∑ c ∈ selected, classMass Finset.univ classify weight c := by
  apply normalized_residual_eq_one_sub_selected
  norm_num [partition, weight, Fin.sum_univ_succ]
end ResearchCommons.Generated.ResidualTopK
"#);
  if source.len()>limits.render_bytes{return Err(Error::Unknown("render_bytes"));}
  Ok(source)
 }
}
pub fn example()->Result<Certificate,Error> {
 let limits=Limits::default();
 Ensemble::new(vec![
  Item{class:0,weight:q(3,2)},Item{class:0,weight:q(1,2)},
  Item{class:1,weight:q(1,2)},Item{class:2,weight:q(0,1)},
  Item{class:3,weight:q(1,4)},
 ],4,limits)?.certify(vec![0],1,limits)
}
#[cfg(test)]mod tests {
 use super::*;
 #[test]fn duplicated_class_and_zero_weight_rows_conserve_the_same_ensemble(){
  let c=example().unwrap();
  assert_eq!(c.partition(),&q(11,4));assert_eq!(c.residual_weight(),&q(3,4));
  assert_eq!(c.selected_mass(0),Some(q(8,11)));assert_eq!(c.selected_mass(1),None);
  assert_eq!(c.ensemble.items.len(),5);
 }
 #[test]fn a_true_top_set_can_be_inconclusive_not_no(){
  let l=Limits::default();
  let e=Ensemble::new(vec![Item{class:0,weight:q(5,1)},Item{class:1,weight:q(4,1)},Item{class:2,weight:q(3,1)}],3,l).unwrap();
  assert!(matches!(e.certify(vec![0],1,l),Err(Error::Inconclusive)));
 }
 #[test]fn invalid_weight_carrier_and_selected_scope_are_refused(){
  let l=Limits::default();
  assert!(matches!(Ensemble::new(vec![Item{class:0,weight:q(-1,1)}],1,l),Err(Error::Invalid(_))));
  assert!(matches!(Ensemble::new(vec![Item{class:1,weight:q(1,1)}],1,l),Err(Error::Invalid(_))));
  assert!(matches!(Ensemble::new(vec![Item{class:0,weight:q(0,1)}],1,l),Err(Error::Invalid(_))));
  let e=Ensemble::new(vec![Item{class:0,weight:q(1,1)}],1,l).unwrap();
  assert!(matches!(e.certify(vec![0,0],2,l),Err(Error::Invalid(_))));
 }
 #[test]fn proof_source_rechecks_raw_rows_and_refuses_truncation(){
  let c=example().unwrap();let source=c.lean_certificate(Limits::default()).unwrap();
  assert!(source.contains("weight : Fin 5"));assert!(source.contains("classify : Fin 5 → Fin 4"));
  assert!(source.contains("apply exact_residual_topK"));assert!(source.contains("same_ensemble_residual_conservation"));
  assert!(!source.contains("sorry"));assert!(!source.contains("native_decide"));
  assert_eq!(c.lean_certificate(Limits{render_bytes:10,..Limits::default()}),Err(Error::Unknown("render_bytes")));
 }
}
