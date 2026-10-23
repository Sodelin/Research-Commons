//! Existing full native epoch -> total formal coefficient/fibre certificate.
//! Literal renderers and the actual epoch engine are reused. No I/O, compiler,
//! new transition oracle, independent rate fit or observation is introduced.
use crate::exact_law::{cell_rows,population_certificate as retained};
use parity_solver::{source_epoch,source_population::{Context,Snapshot,Location},forest::Tree};
pub use retained::{Bindings,Limits as RenderLimits};
pub use source_epoch::Limits as EpochLimits;

#[derive(Debug,PartialEq,Eq)]
pub enum Error {
 Invalid(&'static str),Capture(String),Unknown(source_epoch::Limit),Render(retained::Error),
 Validity(crate::population_certificate::Error),SourceLimit,
}
fn put(out:&mut String,text:&str,cap:usize)->Result<(),Error>{
 let n=out.len().checked_add(text.len()).ok_or(Error::SourceLimit)?;
 if n>cap{return Err(Error::SourceLimit);}
 out.try_reserve(text.len()).map_err(|_|Error::SourceLimit)?;out.push_str(text);Ok(())
}
fn fin(i:usize)->String{format!("⟨{i}, by decide +kernel⟩")}
fn population(place:Location)->Result<String,Error>{
 match place {
  Location::Edge(e)=>Ok(format!("some {}",fin(e))),
  Location::Ancestral(_)=>Ok("none".into()),
  Location::Node(_)=>Err(Error::Invalid("node is not an epoch variable")),
 }
}
fn sparse(polynomial:&parity_solver::polynomial::Polynomial,variables:&[Location],limits:RenderLimits)
 ->Result<String,Error>{
 if polynomial.dimension!=variables.len(){return Err(Error::Invalid("epoch coefficient dimension"));}
 let mut parts=Vec::new();
 for (powers,q) in &polynomial.terms {
  if powers.len()!=variables.len(){return Err(Error::Invalid("epoch exponent arity"));}
  if q.numer().bits().max(q.denom().bits())>limits.rational_bits{return Err(Error::SourceLimit);}
  let mut monomial=Vec::new();
  for (i,power) in powers.iter().enumerate(){
   if *power!=0{monomial.push(format!("({}, {power})",population(variables[i])?));}
  }
  parts.push(format!("([{}], (({} : ℚ) / ({} : ℚ)))",monomial.join(", "),q.numer(),q.denom()));
 }
 Ok(format!("[{}]",parts.join(", ")))
}
fn snapshot(out:&mut String,context:&Context,value:&Snapshot,label:&str,limits:RenderLimits)
 ->Result<(),Error>{
 let source=retained::render_snapshot_declarations(context,value,label,limits).map_err(Error::Render)?;
 let source=crate::population_certificate::repair_literal_snapshot(source,context,value,label).map_err(Error::Validity)?;
 put(out,&source,limits.rendered_bytes)?;
 let view=retained::render_selected_view_declarations(context,value,label,limits).map_err(Error::Render)?;
 let view=view.replace("by decide","by decide +kernel");
 put(out,&view,limits.rendered_bytes)?;
 let proof=format!(r#"theorem {label}_selected_fields_exact :
    (project N Finset.univ {label}).val = {label}View := by
  apply SelectedView.ext
  · funext copy
    fin_cases copy <;> decide +kernel
  · funext copy
    fin_cases copy <;> decide +kernel
  · funext vertex
    fin_cases vertex <;> decide +kernel

"#);
 put(out,&proof,limits.rendered_bytes)
}
/// Generate from one immutable Context/entering snapshot. The native result
/// must retain every selected-view/range-witness field and original bank ID.
/// A resource refusal returns no partial table or negative theorem.
pub fn emit(context:&Context,entering:&Snapshot,bindings:Bindings<'_>,limits:EpochLimits,render:RenderLimits)
 ->Result<String,Error>{
 context.validate_snapshot(entering).map_err(Error::Invalid)?;
 let table=match source_epoch::epoch_row(context,entering,limits).map_err(Error::Invalid)? {
  source_epoch::Decision::Table(table)=>table,
  source_epoch::Decision::Unknown(limit)=>return Err(Error::Unknown(limit)),
 };
 let expected=(0..context.source.edges.len()).map(Location::Edge)
  .chain(std::iter::once(Location::Ancestral(context.source.root))).collect::<Vec<_>>();
 if table.variables!=expected{return Err(Error::Invalid("original edge then ancestral bank order"));}
 if table.transitions.len()>render.destinations{return Err(Error::SourceLimit);}
 let declarations=retained::render_context_declarations(context,bindings,render).map_err(Error::Render)?
  .replace("private abbrev N :","private noncomputable abbrev N :")
  .replace("theorem taxa_exact : N.leaf =","theorem taxa_exact : (fun x => N.leaf x) =")
  .replace("by decide","by decide +kernel");
 let mut out=String::new();
 put(&mut out,&format!(r#"import OriginalEpochTableCertificate
import {}

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace {}
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceFiniteProjection
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.FullEpochSupport GProgram.G7.FullEpochPolynomial
open Astra.OriginalEpochTableCertificate
open scoped NNReal

"#,bindings.original_module,bindings.namespace),render.rendered_bytes)?;
 put(&mut out,&declarations,render.rendered_bytes)?;
 snapshot(&mut out,context,entering,"entering",render)?;
 let mut rows=Vec::new();let mut monomials=0usize;
 for (i,transition) in table.transitions.iter().enumerate(){
  if source_epoch::selected_view(context,&transition.witness).map_err(Error::Invalid)?!=transition.view
   || transition.witness.register!=entering.register{return Err(Error::Invalid("selected range/register witness"));}
  monomials=monomials.checked_add(transition.polynomial.terms.len()).ok_or(Error::SourceLimit)?;
  if monomials>render.monomials{return Err(Error::SourceLimit);}
  let label=format!("destination{i}");
  snapshot(&mut out,context,&transition.witness,&label,render)?;
  rows.push(format!("({label}, {})",sparse(&transition.polynomial,&table.variables,render)?));
 }
 let todo=table.variables.iter().map(|v|population(*v)).collect::<Result<Vec<_>,_>>()?.join(", ");
 put(&mut out,&format!(r#"private def todo : List (Option (Fin {})) := [{todo}]
private def rows : Rows (Option (Fin {})) (Code N sample) := [{}]

theorem active_original_populations : ActiveIn N entering todo.toFinset := by
  intro copy i _
  cases i with
  | none => simp [todo]
  | some edge => fin_cases edge <;> simp [todo]

theorem complete_coefficient_fibres_checked : check N todo entering rows = true := by
  decide +kernel

theorem actual_same_source_epoch (b : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates (Fin {})) (t : ℝ≥0) :
    value (readRows (project N Finset.univ) rows b) (survival r t) =
      (((sourceTimeKernel N r t entering).map (projection N Finset.univ)) b).toReal :=
  checked_original_epoch N todo entering rows complete_coefficient_fibres_checked
    active_original_populations b r t

end {}
"#,context.source.edges.len(),context.source.edges.len(),rows.join(",\n  "),
 context.source.edges.len(),bindings.namespace),render.rendered_bytes)?;
 Ok(out)
}
pub fn example()->Result<String,Error>{
 let (input,_)=crate::source_certificate::example_request("tree").map_err(|e|Error::Capture(format!("{e:?}")))?;
 let cell=cell_rows::compile_request(input).map_err(|e|Error::Capture(format!("{e:?}")))?;
 let context=Context{source:cell.original_chart().source.clone(),sample:vec![0,0,2,2],global_labels:vec![0,1,2,3]};
 let entering=Snapshot{
  live:vec![0,1,2,3],ancestor:vec![0,1,2,3],
  genealogy:(0..4).map(|i|Some(Tree::Leaf(i))).collect(),
  population:vec![Some(Location::Edge(2)),Some(Location::Edge(2)),Some(Location::Edge(4)),Some(Location::Edge(4))],
  register:vec![false;context.source.vertices],
 };
 let document=emit(&context,&entering,Bindings{
  original_module:"OriginalTreeBank",original_source:"ResearchCommons.Generated.OriginalTreeBank.originalSource",
  namespace:"ResearchCommons.Generated.MixedPopulationEpoch",
 },EpochLimits::default(),RenderLimits{rendered_bytes:262144,..RenderLimits::default()})?;
 let ending="\nend ResearchCommons.Generated.MixedPopulationEpoch\n";
 let prefix=document.strip_suffix(ending).ok_or(Error::Invalid("epoch namespace boundary"))?;
 let joined=format!(r#"{prefix}
noncomputable abbrev returnedRates := ResearchCommons.Generated.OriginalTreeBank.sharedBank.rates
theorem same_returned_bank_epoch (b : SelectedIndex N sample Finset.univ) (t : ℝ≥0) :
    value (readRows (project N Finset.univ) rows b) (survival returnedRates t) =
      (((sourceTimeKernel N returnedRates t entering).map (projection N Finset.univ)) b).toReal :=
  actual_same_source_epoch b returnedRates t
end ResearchCommons.Generated.MixedPopulationEpoch
"#);
 if joined.len()>262144{return Err(Error::SourceLimit);}
 Ok(joined)
}
#[cfg(test)]mod tests{
 use super::*;
 #[test]fn complete_mixed_epoch_retains_original_variables_and_selected_fields(){
  let s=example().unwrap();
  assert!(s.contains("sample : Fin 4"));assert!(s.contains("destination8"));
  assert!(s.contains("SelectedView (Fin 7) (Fin 6) (Fin 4)"));
  assert!(s.contains("complete_coefficient_fibres_checked"));assert!(s.contains("same_returned_bank_epoch"));
  assert!(s.contains("none]"));assert!(!s.contains("sorry"));assert!(!s.contains("native_decide"));
 }
 #[test]fn a_real_native_epoch_limit_is_unknown_not_no(){
  use parity_solver::natural_cell::{Source,Edge};
  let context=Context{source:Source{vertices:3,root:0,edges:vec![Edge{source:0,target:1},Edge{source:0,target:2}],leaves:vec![1,2],hybrids:vec![]},sample:vec![0,0],global_labels:vec![0,1]};
  let s=Snapshot::from_lineages(&context,&[(0,Tree::Leaf(0)),(1,Tree::Leaf(1))],Location::Edge(0),vec![false;3]).unwrap();
  let result=emit(&context,&s,Bindings{original_module:"Original",original_source:"Original.N",namespace:"Candidate"},
   EpochLimits{calls:0,..EpochLimits::default()},RenderLimits::default());
  assert!(matches!(result,Err(Error::Unknown(_))));
 }
}
