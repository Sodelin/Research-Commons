//! Existing full ordered completion -> total actual Lean table certificate.
//! No new law, source factory, timing fit, hidden observer or stochastic seed.
use crate::exact_law::{cell_rows,population_certificate as retained};
use parity_solver::{source_completion,source_population::{Context,Snapshot,Location},source_epoch,forest::Tree};
pub use retained::{Bindings,Limits as RenderLimits};
pub use parity_solver::source_population::Limits as CompletionLimits;

#[derive(Debug,PartialEq,Eq)]
pub enum Error {
 Invalid(&'static str),Capture(String),Native(source_completion::Error),
 Unknown(parity_solver::source_population::Limit),Render(retained::Error),
 Snapshot(crate::epoch_certificate::Error),SourceLimit,
}
fn put(out:&mut String,text:&str,cap:usize)->Result<(),Error>{
 let n=out.len().checked_add(text.len()).ok_or(Error::SourceLimit)?;
 if n>cap{return Err(Error::SourceLimit);}
 out.try_reserve(text.len()).map_err(|_|Error::SourceLimit)?;
 out.push_str(text);Ok(())
}
/// Actual nonempty ancestral input, complete selected destination table and
/// exact constant coefficients. A refusal returns no partial proof/table.
pub fn emit(context:&Context,entering:&Snapshot,bindings:Bindings<'_>,
 limits:CompletionLimits,render:RenderLimits)->Result<String,Error>{
 let table=match source_completion::completion_row(context,entering,limits).map_err(Error::Native)?{
  source_completion::Decision::Table(table)=>table,
  source_completion::Decision::Unknown(limit)=>return Err(Error::Unknown(limit)),
 };
 if table.population!=Location::Ancestral(context.source.root){return Err(Error::Invalid("one original ancestral population"));}
 if table.transitions.len()>render.destinations || table.transitions.len()>render.monomials{return Err(Error::SourceLimit);}
 let declarations=retained::render_context_declarations(context,bindings,render).map_err(Error::Render)?
  .replace("private abbrev N :","private noncomputable abbrev N :")
  .replace("theorem taxa_exact : N.leaf =","theorem taxa_exact : (fun x => N.leaf x) =")
  .replace("by decide","by decide +kernel");
 let mut out=String::new();
 put(&mut out,&format!(r#"import OriginalCompletionTableCertificate
import ResearchCommons.Claims.G4Observers
import {}

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace {}
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.EffectiveAncestralCompletion
open GProgram.G7.SelectedCompletionPolynomial
open DotG34.SpecifiedCombEvent
open Astra.OriginalCompletionTableCertificate

"#,bindings.original_module,bindings.namespace),render.rendered_bytes)?;
 put(&mut out,&declarations,render.rendered_bytes)?;
 crate::epoch_certificate::snapshot(&mut out,context,entering,"entering",render).map_err(Error::Snapshot)?;
 let mut rows=Vec::new();
 for (i,t) in table.transitions.iter().enumerate(){
  if source_epoch::selected_view(context,&t.witness).map_err(Error::Invalid)?!=t.view ||
     t.witness.register!=entering.register{return Err(Error::Invalid("completion selected/register witness"));}
  if t.weight.numer().bits().max(t.weight.denom().bits())>render.rational_bits{return Err(Error::SourceLimit);}
  let label=format!("destination{i}");
  crate::epoch_certificate::snapshot(&mut out,context,&t.witness,&label,render).map_err(Error::Snapshot)?;
  rows.push(format!("({label}, [([], (({} : ℚ) / ({} : ℚ)))])",t.weight.numer(),t.weight.denom()));
 }
 let ne=context.source.edges.len();
 put(&mut out,&format!(r#"
private def rows : Rows (Fin 0) (Code N sample) := [{}]
private def nativeSelectedRows : Nat := {}
theorem complete_output_count : rows.length = nativeSelectedRows := by decide +kernel
#print nativeSelectedRows

theorem actual_all_copy_root_support : AncestralRoot N entering := by
  intro copy
  fin_cases copy <;> rfl

theorem complete_completion_coefficient_fibres_checked :
    checkCompletion N entering rows = true := by
  decide +kernel
#check complete_completion_coefficient_fibres_checked

theorem actual_same_source_completion (b : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates (Fin {ne})) :
    value (readRows (project N Finset.univ) rows b) (fun i : Fin 0 => Fin.elim0 i) =
      (((completionKernel N r entering).map (projection N Finset.univ)) b).toReal :=
  checked_original_completion N entering rows complete_completion_coefficient_fibres_checked
    actual_all_copy_root_support b r (fun i : Fin 0 => Fin.elim0 i)
end {}
"#,rows.join(",\n  "),table.transitions.len(),bindings.namespace),render.rendered_bytes)?;
 Ok(out)
}
fn example_input()->Result<(Context,Snapshot),Error>{
 let(input,_)=crate::source_certificate::example_request("tree").map_err(|e|Error::Capture(format!("{e:?}")))?;
 let cell=cell_rows::compile_request(input).map_err(|e|Error::Capture(format!("{e:?}")))?;
 let context=Context{source:cell.original_chart().source.clone(),sample:vec![0,0,1],global_labels:vec![0,1,2]};
 let entering=Snapshot{live:vec![0,1,2],ancestor:vec![0,1,2],
  genealogy:(0..3).map(|i|Some(Tree::Leaf(i))).collect(),
  population:vec![Some(Location::Ancestral(context.source.root));3],
  register:vec![false;context.source.vertices]};
 Ok((context,entering))
}
pub fn example()->Result<String,Error>{
 let(context,entering)=example_input()?;
 let doc=emit(&context,&entering,Bindings{original_module:"OriginalTreeBank",
  original_source:"ResearchCommons.Generated.OriginalTreeBank.originalSource",
  namespace:"ResearchCommons.Generated.AncestralCompletion"},
  CompletionLimits::default(),RenderLimits{rendered_bytes:262144,..RenderLimits::default()})?;
 let end="\nend ResearchCommons.Generated.AncestralCompletion\n";
 let prefix=doc.strip_suffix(end).ok_or(Error::Invalid("completion namespace boundary"))?;
 let out=format!(r#"{prefix}
noncomputable abbrev returnedRates := ResearchCommons.Generated.OriginalTreeBank.sharedBank.rates
theorem same_returned_bank_completion (b : SelectedIndex N sample Finset.univ) :
    value (readRows (project N Finset.univ) rows b) (fun i : Fin 0 => Fin.elim0 i) =
      (((completionKernel N returnedRates entering).map (projection N Finset.univ)) b).toReal :=
  actual_same_source_completion b returnedRates

theorem flat_original_input (copy : Fin 3) :
    (state entering).genealogy ((state entering).ancestor copy) = .leaf copy := by
  fin_cases copy <;> rfl

theorem actual_passive_specified_comb :
    ((selectedCompletion N returnedRates (projection N Finset.univ entering)).map
      (fun a => unrankedForest a.val)) {{toUnranked (comb (2 : Fin 3) [0,1])}} =
        ENNReal.ofReal (1 / 3 : ℝ) := by
  have h := DotG34.SpecifiedCombSelectedObservation.actual_selected_specified_comb_probability
    N returnedRates entering (2 : Fin 3) [0,1] actual_all_copy_root_support
    flat_original_input (by intro x; fin_cases x <;> simp)
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h
#check actual_passive_specified_comb

theorem native_rows_passive_specified_comb :
    observedValue N rows (fun a => unrankedForest a.val)
      {{toUnranked (comb (2 : Fin 3) [0,1])}} (fun i : Fin 0 => Fin.elim0 i) = (1 / 3 : ℝ) := by
  classical
  rw [checked_completion_observer N entering rows complete_completion_coefficient_fibres_checked
    actual_all_copy_root_support (fun a => unrankedForest a.val)
    {{toUnranked (comb (2 : Fin 3) [0,1])}} returnedRates (fun i : Fin 0 => Fin.elim0 i),
    actual_source_completion_projection N returnedRates entering actual_all_copy_root_support,
    actual_passive_specified_comb]
  norm_num
#check native_rows_passive_specified_comb
end ResearchCommons.Generated.AncestralCompletion
"#);
 if out.len()>262144{return Err(Error::SourceLimit);}
 Ok(out)
}
#[cfg(test)]mod tests{
 use super::*;
 #[test]fn actual_complete_row_retains_source_bank_and_passive_observer(){
  let s=example().unwrap();
  assert!(s.contains("Rows (Fin 0)"));assert!(s.contains("actual_all_copy_root_support"));
  assert!(s.contains("complete_completion_coefficient_fibres_checked"));
  assert!(s.contains("same_returned_bank_completion"));
  assert!(s.contains("actual_passive_specified_comb"));assert!(!s.contains("native_decide"));
 }
 #[test]fn empty_and_nonroot_inputs_are_refused_before_resource_budget(){
  let(c,mut s)=example_input().unwrap();
  s.population=vec![Some(Location::Edge(0));3];
  let binding=Bindings{original_module:"OriginalTreeBank",original_source:"ResearchCommons.Generated.OriginalTreeBank.originalSource",namespace:"Candidate"};
  assert!(matches!(emit(&c,&s,binding,CompletionLimits{calls:0,..CompletionLimits::default()},RenderLimits::default()),
    Err(Error::Native(source_completion::Error::InvalidInput(_)))));
  let empty=Context{source:c.source,sample:vec![],global_labels:vec![]};
  let value=Snapshot{live:vec![],ancestor:vec![],genealogy:vec![],population:vec![],register:vec![false;empty.source.vertices]};
  assert!(matches!(emit(&empty,&value,binding,CompletionLimits{calls:0,..CompletionLimits::default()},RenderLimits::default()),
    Err(Error::Native(source_completion::Error::InvalidInput("SOURCE_WORD_COMPLETION_EMPTY_COPY")))));
 }
}
