//! Owning proof receiver for the OLD normalized Poisson-prefix engine.
//! It calls the retained engine, never another cutoff search. A proof-render
//! profile refusal/RESOURCE_LIMIT is UNKNOWN, never source/target NO.
//! No exp/log/float, physical source construction or file/process access.
use exact_count_certificate::{certify as original_certify, Certified, ResourceLimit,
 BigUint, Rational};

#[derive(Clone,Copy,Debug)]
pub struct Limits{
 pub rational_chars:usize,pub inspected_candidates:usize,
 pub cutoff:usize,pub render_bytes:usize,
}
impl Default for Limits{
 fn default()->Self{Self{rational_chars:4096,inspected_candidates:256,
  cutoff:64,render_bytes:262144}}
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Error{
 Invalid(&'static str),Unknown(&'static str),ResourceLimit(ResourceLimit),
}
/// The raw result and requested budget cannot be replaced after construction.
#[derive(Debug)]
pub struct Certificate{raw:Certified,budget:BigUint}
fn bounded(r:&Rational,limits:Limits)->Result<(),Error>{
 if r.to_string().len()>limits.rational_chars{Err(Error::Unknown("rational_chars"))}
 else{Ok(())}
}
fn namespace_ok(s:&str)->bool{
 !s.is_empty()&&s.len()<=64&&s.as_bytes()[0].is_ascii_alphabetic()&&
 s.bytes().all(|b|b.is_ascii_alphanumeric()||b==b'_')
}
fn literal(r:&Rational)->String{format!("({} / {} : ℝ)",r.numer(),r.denom())}
impl Certificate{
 pub fn new(a:&Rational,epsilon:&Rational,budget:&BigUint,limits:Limits)
  ->Result<Self,Error>{
  if limits.rational_chars==0||limits.render_bytes==0{
   return Err(Error::Invalid("positive rendering profile required"));
  }
  bounded(a,limits)?;bounded(epsilon,limits)?;
  if budget>&BigUint::from(limits.inspected_candidates){
   return Err(Error::Unknown("candidate_budget"));
  }
  let result=original_certify(a,epsilon,Some(budget))
   .map_err(|_|Error::Invalid("require a>=0 and 0<epsilon<1"))?;
  let raw=match result{
   exact_count_certificate::Outcome::Certified(c)=>c,
   exact_count_certificate::Outcome::ResourceLimit(r)=>return Err(Error::ResourceLimit(r)),
  };
  if raw.k()>&BigUint::from(limits.cutoff){return Err(Error::Unknown("cutoff"));}
  for r in [raw.a(),raw.epsilon(),raw.s(),raw.t(),raw.u(),raw.delta()]{
   bounded(r,limits)?;
  }
  Ok(Self{raw,budget:budget.clone()})
 }
 pub fn native(&self)->&Certified{&self.raw}
 pub fn requested_budget(&self)->&BigUint{&self.budget}
 pub fn lean(&self,namespace:&str,limits:Limits)->Result<String,Error>{
  if !namespace_ok(namespace){return Err(Error::Invalid("Lean namespace"));}
  if self.raw.k()>&BigUint::from(limits.cutoff)||
     self.budget>BigUint::from(limits.inspected_candidates){
   return Err(Error::Unknown("proof_profile"));
  }
  for r in [self.raw.a(),self.raw.epsilon(),self.raw.s(),self.raw.t(),self.raw.u(),self.raw.delta()]{
   bounded(r,limits)?;
  }
  let k=self.raw.k().to_string().parse::<usize>().map_err(|_|Error::Unknown("cutoff"))?;
  let width=k.checked_add(1).ok_or(Error::Unknown("cutoff"))?;
  // The unchanged engine constructs ALL weights only after success.
  let weights=self.raw.weights();
  if weights.len()!=width{return Err(Error::Invalid("native weight arity"));}
  for w in &weights{bounded(w,limits)?;}
  let vector=format!("![{}]",weights.iter().map(literal).collect::<Vec<_>>().join(", "));
  let c=&self.raw;
  let mut out=format!(
   "import ResearchCommons.Numerics.CountPrefix\nimport Mathlib.Data.Fin.VecNotation\nnoncomputable section\nopen scoped BigOperators\n\
    namespace ResearchCommons.Generated.«{namespace}»\n\
    open ResearchCommons.Numerics.CountPrefix\n\
    def inputA : ℝ := {}\ndef epsilon : ℝ := {}\ndef cutoff : ℕ := {}\n\
    def requestedBudget : ℕ := {}\ndef inspected : ℕ := {}\n\
    def returnedS : ℝ := {}\ndef returnedT : ℝ := {}\ndef returnedU : ℝ := {}\n\
    def returnedDelta : ℝ := {}\ndef returnedWeights : Fin (cutoff+1) → ℝ := {vector}\n",
   literal(c.a()),literal(c.epsilon()),c.k(),self.budget,c.inspected(),
   literal(c.s()),literal(c.t()),literal(c.u()),literal(c.delta()));
  let defs="inputA, epsilon, cutoff, requestedBudget, inspected, returnedS, returnedT, returnedU, returnedDelta, returnedWeights, prefixSum, poissonTerm, upper, deficit, Finset.sum_range_succ, Nat.factorial";
  out.push_str(&format!(r#"theorem actual_domain : 0 ≤ inputA ∧ 0 < epsilon ∧ epsilon < 1 := by
  norm_num [inputA, epsilon]
theorem actual_fields :
    returnedS = prefixSum inputA cutoff ∧
    returnedT = poissonTerm inputA (cutoff+1) ∧
    returnedU = upper inputA cutoff ∧
    returnedDelta = deficit inputA cutoff ∧
    inspected = cutoff+1 ∧ inspected ≤ requestedBudget := by
  norm_num [{defs}]
theorem actual_guards :
    2*inputA ≤ ((cutoff+2 : ℕ) : ℝ) ∧ returnedDelta ≤ epsilon := by
  norm_num [{defs}]
theorem actual_first_cutoff :
    ∀ j ∈ Finset.range cutoff,
      ¬ (2*inputA ≤ ((j+2 : ℕ) : ℝ) ∧ deficit inputA j ≤ epsilon) := by
  intro j hj
  have bound : j < cutoff := Finset.mem_range.mp hj
  unfold cutoff at bound
  interval_cases j <;> norm_num [{defs}]
theorem actual_complete_weights :
    ∀ i : Fin (cutoff+1), returnedWeights i = poissonTerm inputA i.val / prefixSum inputA cutoff := by
  intro i
  fin_cases i <;> norm_num [{defs}, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ']
theorem actual_weights_sum_one : (∑ i : Fin (cutoff+1), returnedWeights i) = 1 := by
  norm_num [returnedWeights, cutoff, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ']
theorem actual_error : 0 ≤ lostMass inputA cutoff ∧ lostMass inputA cutoff ≤ epsilon := by
  have accuracy : deficit inputA cutoff ≤ epsilon := by
    rw [← actual_fields.2.2.2.1]
    exact actual_guards.2
  exact certified_error inputA epsilon cutoff actual_domain.1 actual_guards.1 accuracy
end ResearchCommons.Generated.«{namespace}»
"#));
  if out.len()>limits.render_bytes{return Err(Error::Unknown("render_bytes"));}
  Ok(out)
 }
}
pub fn example(zero:bool,limits:Limits)->Result<Certificate,Error>{
 let a=if zero{Rational::from_integer(0.into())}else{Rational::new(5.into(),7.into())};
 Certificate::new(&a,&Rational::new(1.into(),9.into()),&BigUint::from(3u8),limits)
}
#[cfg(test)]mod tests{
 use super::*;
 fn q(n:i64,d:i64)->Rational{Rational::new(n.into(),d.into())}
 #[test]fn unchanged_native_first_cutoff_and_full_exact_fields_are_owned(){
  let c=example(false,Limits::default()).unwrap();
  assert_eq!(c.native().k(),&BigUint::from(2u8));
  assert_eq!(c.native().inspected(),&BigUint::from(3u8));
  assert_eq!(c.native().s(),&q(193,98));
  assert_eq!(c.native().t(),&q(125,2058));
  assert_eq!(c.native().u(),&q(4303,2058));
  assert_eq!(c.native().delta(),&q(250,4303));
  assert_eq!(c.native().weights(),vec![q(98,193),q(70,193),q(25,193)]);
  let out=c.lean("CountPrefixOrdinary",Limits::default()).unwrap();
  assert!(out.contains("def requestedBudget : ℕ := 3"));
  assert!(out.contains("def returnedS : ℝ := (193 / 98 : ℝ)"));
  assert!(out.contains("theorem actual_first_cutoff"));
  assert!(out.contains("theorem actual_complete_weights"));
  assert!(out.contains("theorem actual_error"));
  assert!(out.contains(":= by\n  intro j hj\n  have bound"));
  assert!(out.contains(":= by\n  intro i\n  fin_cases i"));
  assert!(out.contains(":= by\n  have accuracy"));
 }
 #[test]fn zero_source_and_original_domain_before_zero_budget_remain_distinct(){
  let c=example(true,Limits::default()).unwrap();
  assert_eq!(c.native().k(),&BigUint::from(0u8));
  assert_eq!(c.native().weights(),vec![q(1,1)]);
  assert!(c.lean("CountPrefixZero",Limits::default()).is_ok());
  assert!(matches!(Certificate::new(&q(1,1),&q(0,1),&BigUint::from(0u8),Limits::default()),
   Err(Error::Invalid(_))));
  match Certificate::new(&q(5,7),&q(1,9),&BigUint::from(2u8),Limits::default()){
   Err(Error::ResourceLimit(r))=>{
    assert_eq!(r.inspected(),&BigUint::from(2u8));
    assert_eq!(r.next_k(),&BigUint::from(2u8));
   },_=>panic!("must retain the original resource outcome"),
  }
 }
 #[test]fn delivery_limits_and_namespace_refuse_without_partial_proof_or_negative_claim(){
  let c=example(false,Limits::default()).unwrap();
  assert!(matches!(c.lean("X\naxiom bad : False",Limits::default()),Err(Error::Invalid(_))));
  assert!(matches!(c.lean("Small",Limits{render_bytes:1,..Limits::default()}),Err(Error::Unknown("render_bytes"))));
  assert!(matches!(example(false,Limits{cutoff:1,..Limits::default()}),Err(Error::Unknown("cutoff"))));
  assert!(matches!(example(false,Limits{rational_chars:2,..Limits::default()}),Err(Error::Unknown("rational_chars"))));
  assert!(matches!(example(false,Limits{inspected_candidates:2,..Limits::default()}),Err(Error::Unknown("candidate_budget"))));
 }
}
