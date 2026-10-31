//! Exact JC pruning on the RETAINED ordered Tree. This is a mutation channel,
//! not a genealogy/source/LAW engine. Every output column uses one immutable
//! tree and one occurrence-indexed branch bank. Refusal returns no partial law.
use parity_solver::{forest::Tree,q,Rational};
use crate::jc69::{self,Base};
use crate::moments::literal;
use std::collections::BTreeSet;

#[derive(Clone,Debug,PartialEq,Eq)]
pub struct Branch{pub left:Rational,pub right:Rational}
#[derive(Clone,Copy,Debug)]
pub struct Limits{pub leaves:usize,pub nodes:usize,pub depth:usize,pub patterns:usize,
 pub arithmetic_ops:usize,pub rational_chars:usize,pub source_bytes:usize}
impl Default for Limits{fn default()->Self{Self{leaves:16,nodes:31,depth:32,patterns:4096,
 arithmetic_ops:2_000_000,rational_chars:4096,source_bytes:262144}}}
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Error{Invalid(&'static str),Limit{kind:&'static str,required:usize,cap:usize},Allocation}
fn bound(kind:&'static str,n:usize,cap:usize)->Result<(),Error>{
 if n>cap{Err(Error::Limit{kind,required:n,cap})}else{Ok(())}
}
#[derive(Clone,Debug)]
enum Op{Leaf(usize),Fork{left:usize,right:usize,branch:usize}}
struct Work{used:usize,limits:Limits}
impl Work{
 fn step(&mut self)->Result<(),Error>{
  self.used=self.used.checked_add(1).ok_or(Error::Limit{kind:"arithmetic_ops",required:usize::MAX,cap:self.limits.arithmetic_ops})?;
  bound("arithmetic_ops",self.used,self.limits.arithmetic_ops)
 }
 fn exact(&mut self,value:Rational)->Result<Rational,Error>{
  self.step()?;bound("rational_chars",value.to_string().len(),self.limits.rational_chars)?;Ok(value)
 }
 fn add(&mut self,a:&Rational,b:&Rational)->Result<Rational,Error>{self.exact(a+b)}
 fn mul(&mut self,a:&Rational,b:&Rational)->Result<Rational,Error>{self.exact(a*b)}
}
/// A complete table; fields stay private so a caller cannot replace its tree,
// bank, labels or returned entries after construction.
#[derive(Clone,Debug)]
pub struct ColumnLaw{tree:Tree,branches:Vec<Branch>,labels:Vec<usize>,probabilities:Vec<Rational>,work:usize}
impl ColumnLaw{
 pub fn tree(&self)->&Tree{&self.tree}
 pub fn branches(&self)->&[Branch]{&self.branches}
 pub fn labels(&self)->&[usize]{&self.labels}
 pub fn probabilities(&self)->&[Rational]{&self.probabilities}
 pub fn arithmetic_ops(&self)->usize{self.work}
 pub fn probability(&self,pattern:&[Base])->Result<&Rational,Error>{
  if pattern.len()!=self.labels.len(){return Err(Error::Invalid("complete original-label pattern"));}
  let mut i=0usize;
  for b in pattern{i=i.checked_mul(4).and_then(|i|i.checked_add(usize::from(b.index())))
    .ok_or(Error::Invalid("pattern index"))?;}
  self.probabilities.get(i).ok_or(Error::Invalid("pattern index"))
 }
}
fn plan(tree:&Tree,labels:&[usize],depth:usize,next:&mut usize,seen:&mut BTreeSet<usize>,
 ops:&mut Vec<Op>,limits:Limits)->Result<usize,Error>{
 bound("depth",depth,limits.depth)?;
 let op=match tree{
  Tree::Leaf(label)=>{
   if !seen.insert(*label){return Err(Error::Invalid("repeated original leaf"));}
   let pos=labels.binary_search(label).map_err(|_|Error::Invalid("original leaf universe"))?;
   Op::Leaf(pos)
  },
  Tree::Node(a,b)=>{
   let branch=*next;*next=next.checked_add(1).ok_or(Error::Invalid("branch count"))?;
   let left=plan(a,labels,depth+1,next,seen,ops,limits)?;
   let right=plan(b,labels,depth+1,next,seen,ops,limits)?;
   Op::Fork{left,right,branch}
  }
 };
 bound("nodes",ops.len().checked_add(1).ok_or(Error::Invalid("node count"))?,limits.nodes)?;
 ops.try_reserve(1).map_err(|_|Error::Allocation)?;
 let i=ops.len();ops.push(op);Ok(i)
}
/// Branch records are in PREORDER, left/right fields in retained child order.
// Labels are the exact sorted original ID universe, with no 1-based/0-based
// convention silently imposed. Endpoints 0/1 are valid stochastic coordinates;
// positive finite clock realization is a separate, explicit certificate join.
pub fn column_law(tree:&Tree,branches:&[Branch],labels:&[usize],limits:Limits)->Result<ColumnLaw,Error>{
 if labels.is_empty()||labels.windows(2).any(|w|w[0]>=w[1]){return Err(Error::Invalid("nonempty sorted injective labels"));}
 bound("leaves",labels.len(),limits.leaves)?;
 bound("branches",branches.len(),limits.nodes)?;
 let mut count=1usize;
 for _ in labels{count=count.checked_mul(4).ok_or(Error::Limit{kind:"patterns",required:usize::MAX,cap:limits.patterns})?;
  bound("patterns",count,limits.patterns)?;}
 let mut ops=Vec::new();let mut seen=BTreeSet::new();let mut next=0;
 let root=plan(tree,labels,0,&mut next,&mut seen,&mut ops,limits)?;
 if next!=branches.len()||seen.len()!=labels.len(){return Err(Error::Invalid("complete branch/leaf carrier"));}
 let jl=jc69::Limits{rational_chars:limits.rational_chars,source_bytes:limits.source_bytes};
 let mut bank=Vec::new();bank.try_reserve_exact(branches.len()).map_err(|_|Error::Allocation)?;
 for b in branches{
  let mut left:Vec<[Rational;4]>=Vec::new();let mut right=Vec::new();
  for a in 0..4{
   let a=Base::new(a).map_err(|_|Error::Invalid("base"))?;
   left.push(jc69::row(&b.left,a,jl).map_err(|e|match e{
    jc69::Error::Invalid(_)=>Error::Invalid("branch survival"),
    jc69::Error::Limit{kind,required,cap}=>Error::Limit{kind,required,cap}})?);
   right.push(jc69::row(&b.right,a,jl).map_err(|e|match e{
    jc69::Error::Invalid(_)=>Error::Invalid("branch survival"),
    jc69::Error::Limit{kind,required,cap}=>Error::Limit{kind,required,cap}})?);
  }
  bank.push((left,right));
 }
 let mut work=Work{used:0,limits};let mut probabilities=Vec::new();
 probabilities.try_reserve_exact(count).map_err(|_|Error::Allocation)?;
 let mut total=q(0,1);
 for index in 0..count{
  let mut digits=vec![0usize;labels.len()];let mut value=index;
  for d in digits.iter_mut().rev(){*d=value%4;value/=4;}
  let mut table:Vec<[Rational;4]>=Vec::new();table.try_reserve_exact(ops.len()).map_err(|_|Error::Allocation)?;
  for op in &ops{
   let value=match *op{
    Op::Leaf(pos)=>std::array::from_fn(|a|if a==digits[pos]{q(1,1)}else{q(0,1)}),
    Op::Fork{left,right,branch}=>{
     let mut values=std::array::from_fn(|_|q(0,1));
     for a in 0..4{
      let mut l=q(0,1);let mut r=q(0,1);
      for b in 0..4{
       let lp=work.mul(&bank[branch].0[a][b],&table[left][b])?;
       let rp=work.mul(&bank[branch].1[a][b],&table[right][b])?;
       l=work.add(&l,&lp)?;r=work.add(&r,&rp)?;
      }
      values[a]=work.mul(&l,&r)?;
     }
     values
    }
   };
   table.push(value);
  }
  let mut mass=q(0,1);
  for p in &table[root]{let term=work.mul(&q(1,4),p)?;mass=work.add(&mass,&term)?;}
  if mass<q(0,1)||mass>q(1,1){return Err(Error::Invalid("constructed JC probability"));}
  total=work.add(&total,&mass)?;probabilities.push(mass);
 }
 if total!=q(1,1){return Err(Error::Invalid("whole column normalization"));}
 Ok(ColumnLaw{tree:tree.clone(),branches:branches.to_vec(),labels:labels.to_vec(),probabilities,work:work.used})
}
fn example_law()->Result<ColumnLaw,Error>{
 let tree=Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(0)),Box::new(Tree::Leaf(1)))),Box::new(Tree::Leaf(2)));
 column_law(&tree,&[Branch{left:q(2,3),right:q(2,5)},Branch{left:q(3,5),right:q(3,5)}],&[0,1,2],Limits::default())
}
/// The fixed public certificate checks ALL64 entries and the SAME returned
// chronological clock/decoded pair-age matrix, not a calibrated demographic
// source law. Generic Rust/source/parser refinement remains separate.
pub fn example_certificate()->Result<String,Error>{
 let law=example_law()?;let l=Limits::default();
 let mut slabs=Vec::new();
 for a in 0..4{
  let mut rows=Vec::new();
  for b in 0..4{
   let values=(0..4).map(|c|literal(&law.probabilities[a*16+b*4+c])).collect::<Vec<_>>().join(", ");
   rows.push(format!("![{values}]"));
  }slabs.push(format!("![{}]",rows.join(", ")));
 }
 let source=format!(r#"import ResearchCommons.MSCI.JC69Tree
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.Generated.JC69TreeColumn
noncomputable section
open ResearchCommons.MSCI.JC69
open ResearchCommons.MSCI.JC69Tree
open GProgram.SourceForest
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.ChronologicalDecoration
open scoped BigOperators NNReal Classical
def originalTree : Genealogy (Fin 3) := .graft (.graft (.leaf 0) (.leaf 1)) (.leaf 2)
def suppliedSurvivals : Survivals originalTree :=
  ((2/3 : ℝ), (2/5 : ℝ), ((3/5 : ℝ), (3/5 : ℝ), PUnit.unit, PUnit.unit), PUnit.unit)
def nativeRows : Fin 4 → Fin 4 → Fin 4 → ℚ := ![{}]
theorem every_native_pattern_checked (a b c : Base) :
    (nativeRows (number a) (number b) (number c) : ℝ) =
      rootLikelihood originalTree suppliedSurvivals ((a,b),c) := by
  dsimp only [originalTree, suppliedSurvivals, rootLikelihood, likelihood, Pattern, patternFintype]
  rcases a with ⟨a0,a1⟩
  rcases b with ⟨b0,b1⟩
  rcases c with ⟨c0,c1⟩
  fin_cases a0 <;> fin_cases a1 <;> fin_cases b0 <;> fin_cases b1 <;>
    fin_cases c0 <;> fin_cases c1 <;>
    norm_num [nativeRows, originalTree, suppliedSurvivals, rootLikelihood, likelihood,
      probability, number, Fintype.sum_prod_type, Fin.sum_univ_two]
theorem complete_native_column_normalized :
    (∑ a : Base, ∑ b : Base, ∑ c : Base,
      (nativeRows (number a) (number b) (number c) : ℝ)) = 1 := by
  simp_rw [every_native_pattern_checked]
  have h := root_likelihood_sum originalTree suppliedSurvivals
  simpa only [originalTree, Pattern, patternFintype, Fintype.sum_prod_type] using h

noncomputable def innerTime : ℝ≥0 := timeOfSurvival ⟨(3/5 : ℝ), by norm_num⟩
noncomputable def rootTime : ℝ≥0 := timeOfSurvival ⟨(2/5 : ℝ), by norm_num⟩
def leafAge : Fin 3 → ℝ := fun _ => 0
noncomputable def actualDecoration : Decoration originalTree :=
  ((rootTime : ℝ), ((innerTime : ℝ), PUnit.unit, PUnit.unit), PUnit.unit)
theorem inner_positive : 0 < (innerTime : ℝ) := by
  change 0 < -((3/4 : ℝ)) * Real.log (3/5 : ℝ)
  have h := Real.log_neg (by norm_num : (0 : ℝ) < 3/5) (by norm_num : (3/5 : ℝ) < 1)
  nlinarith
theorem times_ordered : (innerTime : ℝ) < (rootTime : ℝ) := by
  change -((3/4 : ℝ)) * Real.log (3/5 : ℝ) < -((3/4 : ℝ)) * Real.log (2/5 : ℝ)
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2/5) (by norm_num : (2/5 : ℝ) < 3/5)
  nlinarith
theorem actual_chronology : Chronological leafAge originalTree actualDecoration := by
  change (True ∧ True ∧ (0 : ℝ) < innerTime ∧ (0 : ℝ) < innerTime) ∧
    True ∧ (innerTime : ℝ) < rootTime ∧ (0 : ℝ) < rootTime
  exact ⟨⟨True.intro,True.intro,inner_positive,inner_positive⟩,
    True.intro,times_ordered,inner_positive.trans times_ordered⟩
theorem inner_clock : (clockSurvival innerTime : ℝ) = 3/5 :=
  clock_survival_timeOfSurvival ⟨(3/5 : ℝ), by norm_num⟩
theorem root_clock : (clockSurvival rootTime : ℝ) = 2/5 :=
  clock_survival_timeOfSurvival ⟨(2/5 : ℝ), by norm_num⟩
theorem branch_clock :
    Real.exp (-((4/3 : ℝ) * ((rootTime : ℝ) - innerTime))) = 2/3 := by
  have h : Real.exp (-((4/3 : ℝ) * ((rootTime : ℝ) - innerTime))) =
      (clockSurvival rootTime : ℝ) / (clockSurvival innerTime : ℝ) := by
    change Real.exp _ = Real.exp _ / Real.exp _
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [h,root_clock,inner_clock]
  norm_num
theorem same_returned_clock :
    clockSurvivals leafAge originalTree actualDecoration = suppliedSurvivals := by
  have hi : Real.exp (-((4/3 : ℝ) * (innerTime : ℝ))) = 3/5 := inner_clock
  have hr : Real.exp (-((4/3 : ℝ) * (rootTime : ℝ))) = 2/5 := root_clock
  simp only [originalTree, actualDecoration, clockSurvivals, rootAge, leafAge, sub_zero,
    branch_clock, hi, hr, suppliedSurvivals] <;> rfl
theorem original_tree_valid : originalTree.WellLabelled := by
  simp [originalTree, Genealogy.WellLabelled, Genealogy.leaves]
noncomputable def originalPairMatrix : Fin 3 → Fin 3 → ℝ :=
  pairAge leafAge originalTree actualDecoration
theorem same_decoded_matrix_clock :
    clockSurvivals leafAge originalTree (decode originalPairMatrix originalTree) = suppliedSurvivals := by
  rw [originalPairMatrix,decode_pairAge leafAge originalTree original_tree_valid]
  exact same_returned_clock
theorem same_decoded_clock_column (a b c : Base) :
    (nativeRows (number a) (number b) (number c) : ℝ) =
      rootLikelihood originalTree
        (clockSurvivals leafAge originalTree (decode originalPairMatrix originalTree)) ((a,b),c) := by
  rw [same_decoded_matrix_clock]
  exact every_native_pattern_checked a b c
theorem same_tree_conditional_locus (L : Nat) (p : Fin L → Pattern originalTree) :
    locusLikelihood L originalTree
      (clockSurvivals leafAge originalTree (decode originalPairMatrix originalTree)) p =
        ∏ j, rootLikelihood originalTree suppliedSurvivals (p j) := by
  rw [same_decoded_matrix_clock]
  rfl
#check every_native_pattern_checked
#check complete_native_column_normalized
#check same_decoded_clock_column
#check same_tree_conditional_locus
end
end ResearchCommons.Generated.JC69TreeColumn
"#,slabs.join(",\n  "));
 bound("source_bytes",source.len(),l.source_bytes)?;Ok(source)
}
#[cfg(test)]mod tests{
 use super::*;
 #[test]fn complete_pruned_channel_retains_full_labelled_patterns_and_the_same_branch_bank(){
  let law=example_law().unwrap();
  assert_eq!(law.probabilities().len(),64);
  assert_eq!(law.labels(),&[0,1,2]);
  assert_eq!(law.probabilities().iter().cloned().fold(q(0,1),|a,b|a+b),q(1,1));
  for k in 1..4{
   let k=Base::new(k).unwrap();
   for (first,second,survival) in [(0,1,q(9,25)),(0,2,q(4,25)),(1,2,q(4,25))]{
    let mut corr=q(0,1);
    for index in 0..64{
     let bits=[index/16,(index/4)%4,index%4];
     let sign=jc69::character(k,Base::new(bits[first] as u8).unwrap())*
       jc69::character(k,Base::new(bits[second] as u8).unwrap());
     corr+=&law.probabilities[index]*q(i64::from(sign),1);
    }
    assert_eq!(corr,survival);
   }
  }
  let doc=example_certificate().unwrap();
  assert!(doc.contains("every_native_pattern_checked")&&doc.contains("same_decoded_matrix_clock"));
  assert!(!doc.contains("native_decide")&&!doc.contains("sorry"));
 }
 #[test]fn original_labels_and_complete_carriers_are_checked_before_output(){
  let leaf=Tree::Leaf(19);
  let law=column_law(&leaf,&[],&[19],Limits::default()).unwrap();
  assert_eq!(law.probabilities(),&[q(1,4),q(1,4),q(1,4),q(1,4)]);
  assert!(column_law(&leaf,&[],&[0],Limits::default()).is_err());
  let duplicate=Tree::Node(Box::new(Tree::Leaf(0)),Box::new(Tree::Leaf(0)));
  assert!(column_law(&duplicate,&[Branch{left:q(1,1),right:q(1,1)}],&[0],Limits::default()).is_err());
  let law=example_law().unwrap();
  assert!(law.probability(&[Base::new(0).unwrap()]).is_err());
  assert!(column_law(law.tree(),&law.branches()[..1],law.labels(),Limits::default()).is_err());
 }
 #[test]fn every_profile_refusal_returns_no_partial_column_law(){
  let law=example_law().unwrap();let l=Limits::default();
  for limits in [Limits{patterns:63,..l},Limits{arithmetic_ops:8,..l},Limits{depth:0,..l},
    Limits{nodes:2,..l},Limits{leaves:2,..l},Limits{rational_chars:1,..l}]{
   assert!(matches!(column_law(law.tree(),law.branches(),law.labels(),limits),Err(Error::Limit{..})));
  }
  let bad=[Branch{left:q(-1,2),right:q(2,5)},Branch{left:q(3,5),right:q(3,5)}];
  assert!(matches!(column_law(law.tree(),&bad,law.labels(),l),Err(Error::Invalid("branch survival"))));
 }
}
