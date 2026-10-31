//! Retained normalized clock-JC branch channel over the four literal bases.
//! Exact Rational arithmetic only; no exponential/log fitting or source/model
//! simulation. Whole-genealogy/locus/provider and universal native refinement
//! are separate from this explicit branch and its checked public certificate.
use parity_solver::{q,Rational};
use crate::moments::literal;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Base(u8);
impl Base{
 pub fn new(i:u8)->Result<Self,Error>{if i<4{Ok(Self(i))}else{Err(Error::Invalid("four-base index"))}}
 pub fn index(self)->u8{self.0}
 pub fn add_character(self,other:Self)->Self{Self(self.0^other.0)}
}
#[derive(Clone,Copy,Debug)]
pub struct Limits{pub rational_chars:usize,pub source_bytes:usize}
impl Default for Limits{fn default()->Self{Self{rational_chars:4096,source_bytes:262144}}}
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Error{Invalid(&'static str),Limit{kind:&'static str,required:usize,cap:usize}}
fn size(kind:&'static str,required:usize,cap:usize)->Result<(),Error>{
 if required>cap{Err(Error::Limit{kind,required,cap})}else{Ok(())}
}
fn check_survival(x:&Rational,limits:Limits)->Result<(),Error>{
 if x<&q(0,1)||x>&q(1,1){return Err(Error::Invalid("survival must be in [0,1]"));}
 size("rational_chars",x.to_string().len(),limits.rational_chars)
}
pub fn character(k:Base,a:Base)->i8{
 if (k.0&a.0).count_ones()%2==0{1}else{-1}
}
fn probability_unchecked(x:&Rational,a:Base,b:Base)->Rational{
 if a==b{(q(1,1)+q(3,1)*x)/q(4,1)}else{(q(1,1)-x)/q(4,1)}
}
pub fn probability(x:&Rational,a:Base,b:Base,limits:Limits)->Result<Rational,Error>{
 check_survival(x,limits)?;
 let value=probability_unchecked(x,a,b);
 size("rational_chars",value.to_string().len(),limits.rational_chars)?;
 Ok(value)
}
pub fn row(x:&Rational,a:Base,limits:Limits)->Result<[Rational;4],Error>{
 check_survival(x,limits)?;
 let values=std::array::from_fn(|i|probability_unchecked(x,a,Base(i as u8)));
 for v in &values{size("rational_chars",v.to_string().len(),limits.rational_chars)?;}
 Ok(values)
}
/// Checks the WHOLE sixteen-entry actual rational output, and ties the SAME
/// survival to an explicit finite nonnegative normalized-clock time in Lean.
/// No private input is persisted and no partially rendered source is returned.
pub fn lean_certificate(x:&Rational,limits:Limits)->Result<String,Error>{
 check_survival(x,limits)?;
 if x==&q(0,1){return Err(Error::Invalid("finite clock realization requires positive survival"));}
 let rows=(0..4).map(|a|row(x,Base(a),limits)).collect::<Result<Vec<_>,_>>()?;
 let matrix=rows.iter().map(|r|format!("![{}]",r.iter().map(literal).collect::<Vec<_>>().join(", ")))
  .collect::<Vec<_>>().join(",\n  ");
 let source=format!(r#"import ResearchCommons.MSCI.JC69
import Mathlib.Tactic

namespace ResearchCommons.Generated.JC69Branch
open ResearchCommons.MSCI.JC69
open scoped BigOperators NNReal
def suppliedSurvival : ℚ := {survival}
def nativeRows : Fin 4 → Fin 4 → ℚ := ![{matrix}]
theorem survival_admitted : 0 < (suppliedSurvival : ℝ) ∧ (suppliedSurvival : ℝ) ≤ 1 := by
  norm_num [suppliedSurvival]
noncomputable def returnedTime : ℝ≥0 :=
  timeOfSurvival ⟨(suppliedSurvival : ℝ), survival_admitted⟩
theorem every_native_probability_checked (a b : Base) :
    (nativeRows (number a) (number b) : ℝ) = probability (suppliedSurvival : ℝ) a b := by
  rcases a with ⟨a0,a1⟩
  rcases b with ⟨b0,b1⟩
  fin_cases a0 <;> fin_cases a1 <;> fin_cases b0 <;> fin_cases b1 <;>
    norm_num [nativeRows, suppliedSurvival, probability, number]
theorem complete_native_row_normalized (a : Base) :
    (∑ b : Base, (nativeRows (number a) (number b) : ℝ)) = 1 := by
  simp_rw [every_native_probability_checked]
  exact probability_row_sum _ a
theorem same_returned_clock_kernel (a b : Base) :
    (nativeRows (number a) (number b) : ℝ) = (clockKernel returnedTime a b).toReal := by
  rw [clockKernel, kernel_probability]
  have ht : (clockSurvival returnedTime : ℝ) = (suppliedSurvival : ℝ) :=
    clock_survival_timeOfSurvival ⟨(suppliedSurvival : ℝ), survival_admitted⟩
  rw [ht]
  exact every_native_probability_checked a b
#check every_native_probability_checked
#check complete_native_row_normalized
#check same_returned_clock_kernel
end ResearchCommons.Generated.JC69Branch
"#,survival=literal(x));
 size("source_bytes",source.len(),limits.source_bytes)?;
 Ok(source)
}
pub fn example()->Result<String,Error>{lean_certificate(&q(3,5),Limits::default())}
#[cfg(test)]mod tests{
 use super::*;
 #[test]fn exact_channel_semigroup_and_character_identities_hold_for_all_four_bases(){
  let limits=Limits::default();
  for x in [q(0,1),q(1,5),q(3,5),q(1,1)]{
   for a in 0..4{
    let r=row(&x,Base(a),limits).unwrap();
    assert!(r.iter().all(|p|p>=&q(0,1)));
    assert_eq!(r.iter().cloned().fold(q(0,1),|a,b|a+b),q(1,1));
    for k in 0..4{
     let fourier=(0..4).fold(q(0,1),|sum,b|sum+
      &r[b]*q(i64::from(character(Base(k),Base(b as u8))),1));
     let eigen=if k==0{q(1,1)}else{x.clone()};
     assert_eq!(fourier,eigen*q(i64::from(character(Base(k),Base(a))),1));
    }
    for y in [q(0,1),q(2,7),q(1,1)]{
     for c in 0..4{
      let composed=(0..4).fold(q(0,1),|sum,b|sum+
       probability_unchecked(&x,Base(a),Base(b))*probability_unchecked(&y,Base(b),Base(c)));
      assert_eq!(composed,probability_unchecked(&(&x*&y),Base(a),Base(c)));
     }
    }
   }
  }
  for k in 0..4{for l in 0..4{for a in 0..4{
   assert_eq!(character(Base(k).add_character(Base(l)),Base(a)),
    character(Base(k),Base(a))*character(Base(l),Base(a)));
  }}}
 }
 #[test]fn finite_clock_certificate_refuses_invalid_or_unrecoverable_survival_and_no_partial_source(){
  let l=Limits::default();
  assert!(Base::new(4).is_err());
  assert!(matches!(probability(&q(-1,3),Base(0),Base(1),l),Err(Error::Invalid(_))));
  assert!(matches!(probability(&q(4,3),Base(0),Base(1),l),Err(Error::Invalid(_))));
  assert!(matches!(lean_certificate(&q(0,1),l),Err(Error::Invalid(_))));
  assert!(matches!(lean_certificate(&q(3,5),Limits{source_bytes:16,..l}),
   Err(Error::Limit{kind:"source_bytes",..})));
  let source=example().unwrap();
  assert!(source.contains("every_native_probability_checked"));
  assert!(source.contains("same_returned_clock_kernel"));
  assert!(!source.contains("native_decide")&&!source.contains("sorry"));
 }
}
