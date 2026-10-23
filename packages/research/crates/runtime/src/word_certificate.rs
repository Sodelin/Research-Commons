//! Actual retained natural word -> total selected coefficient-fibre certificate.
//! The engine, initial register weights, source parser and literal renderers
//! are reused. This public-source emitter does no I/O or proof checking.
use crate::exact_law::{cell_rows,population_certificate as retained};
use parity_solver::{source_word::{self,Request,Initial,Symbol,Terminal,Variable},
    source_epoch,source_population::Location};
pub use retained::{Bindings,Limits as RenderLimits};
use std::collections::BTreeMap;

#[derive(Debug,PartialEq,Eq)]
pub enum Error {
 Invalid(&'static str),Capture(String),Native(source_word::Error),Unknown(source_word::Limit),
 Render(retained::Error),Snapshot(crate::epoch_certificate::Error),SourceLimit,
 SourceBytes{required:usize,cap:usize},
}
fn put(out:&mut String,text:&str,cap:usize)->Result<(),Error>{
 let n=out.len().checked_add(text.len()).ok_or(Error::SourceLimit)?;
 if n>cap{return Err(Error::SourceBytes{required:n,cap});}
 out.try_reserve(text.len()).map_err(|_|Error::SourceLimit)?;out.push_str(text);Ok(())
}
fn fin(i:usize)->String{format!("⟨{i}, by decide +kernel⟩")}
fn vector(xs:Vec<String>)->String{
 if xs.is_empty(){"Fin.elim0".into()}else{format!("![{}]",xs.join(", "))}
}
fn sparse(p:&parity_solver::polynomial::Polynomial,variables:&[Variable],
 monomials:&BTreeMap<Vec<usize>,usize>,limits:RenderLimits)->Result<String,Error>{
 if p.dimension!=variables.len(){return Err(Error::Invalid("word coefficient dimension"));}
 let mut parts=Vec::new();
 for (powers,q) in &p.terms {
  if powers.len()!=variables.len(){return Err(Error::Invalid("word exponent arity"));}
  if q.numer().bits().max(q.denom().bits())>limits.rational_bits{return Err(Error::SourceLimit);}
  let i=monomials.get(powers).ok_or(Error::Invalid("complete monomial dictionary"))?;
  let rational=if q.denom()==parity_solver::q(1,1).denom(){q.numer().to_string()}
   else{format!("({} / {} : ℚ)",q.numer(),q.denom())};
  parts.push(format!("(monomial{i}, {rational})"));
 }
 Ok(format!("[{}]",parts.join(", ")))
}
/// Explicit literal original-variable/native-position binding. Finite fields
/// and both inverse cases are checked in Lean, never inferred from a separate
/// noncomputable numbering or from a matching vector length alone.
fn indexed_bank(request:&Request,dimension:usize,render:RenderLimits)->Result<String,Error>{
 let source=&request.context.source;
 let nv=source.vertices;let ne=source.edges.len();let nh=source.hybrids.len();let slots=request.slots;
 let mut out=String::new();
 let sites=vector(source.hybrids.iter().map(|h|fin(h.vertex)).collect());
 put(&mut out,&format!(r#"
local instance : DecidablePred N.graph.IsHybrid := hybridDecidable N
private def hybridVertices : Fin {nh} → Fin {nv} := {sites}
private theorem captured_hybrid_vertices :
    ∀ i : Fin {nh}, N.graph.IsHybrid (hybridVertices i) := by decide +kernel
private def nativeHybrid (i : Fin {nh}) : Hybrid N :=
  ⟨hybridVertices i, captured_hybrid_vertices i⟩
"#),render.rendered_bytes)?;
 if nh==0{
  put(&mut out,&format!(r#"
private theorem no_original_hybrid : ∀ v : Fin {nv}, ¬ N.graph.IsHybrid v := by decide +kernel
private def hybridNumber (h : Hybrid N) : Fin 0 :=
  False.elim (no_original_hybrid h.val h.property)
private theorem nativeHybrid_number (h : Hybrid N) : nativeHybrid (hybridNumber h) = h := by
  exact False.elim (no_original_hybrid h.val h.property)
"#),render.rendered_bytes)?;
 }else{
  let mut indices=vec![fin(0);nv];
  for(i,h)in source.hybrids.iter().enumerate(){indices[h.vertex]=fin(i);}
  put(&mut out,&format!(r#"
private def vertexHybridNumber : Fin {nv} → Fin {nh} := {}
private theorem captured_hybrid_indices :
    ∀ v : Fin {nv}, N.graph.IsHybrid v → hybridVertices (vertexHybridNumber v) = v := by
  decide +kernel
private def hybridNumber (h : Hybrid N) : Fin {nh} := vertexHybridNumber h.val
private theorem nativeHybrid_number (h : Hybrid N) : nativeHybrid (hybridNumber h) = h := by
  apply Subtype.ext
  exact captured_hybrid_indices h.val h.property
"#,vector(indices)),render.rendered_bytes)?;
 }
 let mut slots_data=Vec::new();
 for j in 0..slots{
  let edges=vector((0..ne).map(|e|fin(j*(ne+1)+e)).collect());
  slots_data.push(format!("fun place => match place with | some edge => ({edges}) edge | none => {}",fin(j*(ne+1)+ne)));
 }
 let gammas=vector((0..nh).map(|h|fin(slots*(ne+1)+h)).collect());
 put(&mut out,&format!(r#"
private def slotCoordinate : Fin {slots} → Option (Fin {ne}) → Fin {dimension} := {}
private def gammaCoordinate : Fin {nh} → Fin {dimension} := {gammas}
private def encodeVariable : WordVariable N (Fin {slots}) → Fin {dimension}
  | .inl p => slotCoordinate p.1 p.2
  | .inr h => gammaCoordinate (hybridNumber h)
"#,vector(slots_data)),render.rendered_bytes)?;
 let vars=(0..slots).flat_map(|j|(0..ne).map(move|e|format!("Sum.inl ({}, some {})",fin(j),fin(e)))
  .chain(std::iter::once(format!("Sum.inl ({}, none)",fin(j)))))
  .chain((0..nh).map(|i|format!("Sum.inr (nativeHybrid {})",fin(i)))).collect::<Vec<_>>();
 put(&mut out,&format!(r#"
private def variableBank : Fin {dimension} → WordVariable N (Fin {slots}) := {}
private theorem variableBank_gamma (i : Fin {nh}) :
    variableBank (gammaCoordinate i) = Sum.inr (nativeHybrid i) := by
  fin_cases i <;> rfl
"#,vector(vars)),render.rendered_bytes)?;
 if slots==0{
  put(&mut out,&format!(r#"
private theorem variableBank_interval (slot : Fin 0) (place : Option (Fin {ne})) :
    variableBank (slotCoordinate slot place) = Sum.inl (slot,place) := by
  exact Fin.elim0 slot
"#),render.rendered_bytes)?;
 }else{
  put(&mut out,&format!(r#"
private theorem variableBank_interval (slot : Fin {slots}) (place : Option (Fin {ne})) :
    variableBank (slotCoordinate slot place) = Sum.inl (slot,place) := by
  fin_cases slot <;> cases place with
  | none => rfl
  | some edge => fin_cases edge <;> rfl
"#),render.rendered_bytes)?;
 }
 put(&mut out,&format!(r#"
theorem original_variable_native_bank_left_inverse :
    Function.LeftInverse variableBank encodeVariable := by
  intro i
  cases i with
  | inl pair => exact variableBank_interval pair.1 pair.2
  | inr h =>
    change variableBank (gammaCoordinate (hybridNumber h)) = Sum.inr h
    rw [variableBank_gamma, nativeHybrid_number]
#check original_variable_native_bank_left_inverse
"#),render.rendered_bytes)?;
 Ok(out)
}
/// Complete immutable natural-word request, preserving ALL register-labelled
/// destinations and variables. FullView is explicit; completion has a separate
/// receiver. Failed validation/resource/rendering returns no partial document.
pub fn emit(request:&Request,bindings:Bindings<'_>,render:RenderLimits)->Result<String,Error>{
 if request.initial!=Initial::Natural || request.terminal!=Terminal::FullView{
  return Err(Error::Invalid("natural FullView word required"));
 }
 let context=&request.context;let source=&context.source;
 let table=match source_word::word_row(request).map_err(Error::Native)?{
  source_word::Decision::Table(table)=>table,
  source_word::Decision::Unknown(limit)=>return Err(Error::Unknown(limit)),
 };
 let expected=(0..request.slots).flat_map(|slot|
  (0..source.edges.len()).map(move|e|Variable::Survival{slot,population:Location::Edge(e)})
   .chain(std::iter::once(Variable::Survival{slot,population:Location::Ancestral(source.root)})))
  .chain((0..source.hybrids.len()).map(Variable::OriginalGamma)).collect::<Vec<_>>();
 if table.variables!=expected{return Err(Error::Invalid("original shared word variable order"));}
 if table.transitions.len()>render.destinations{return Err(Error::SourceLimit);}
 let declarations=retained::render_context_declarations(context,bindings,render).map_err(Error::Render)?
  .replace("private abbrev N :","private noncomputable abbrev N :")
  .replace("theorem taxa_exact : N.leaf =","theorem taxa_exact : (fun x => N.leaf x) =")
  .replace("by decide","by decide +kernel");
 let mut out=String::new();
 put(&mut out,&format!(r#"import OriginalWordTableCertificate
import {}

set_option maxRecDepth 10000
set_option maxHeartbeats 30000000
namespace {}
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.EffectiveInitializationCoefficients
open GProgram.G7.EffectiveWordCoefficients GProgram.G7.SymbolicProgramPolynomial
open Astra.OriginalWordTableCertificate
open scoped NNReal
"#,bindings.original_module,bindings.namespace),render.rendered_bytes)?;
 put(&mut out,&declarations,render.rendered_bytes)?;
 let mut p0=vec!["0".to_owned();source.vertices];let mut p1=p0.clone();
 let mut modes=vec!["false".to_owned();source.vertices];
 for (i,h) in source.hybrids.iter().enumerate(){
  p0[h.vertex]=fin(h.incoming[0]);p1[h.vertex]=fin(h.incoming[1]);
  modes[h.vertex]=request.common[i].to_string();
 }
 let nv=source.vertices;let ne=source.edges.len();let slots=request.slots;
 put(&mut out,&format!(r#"
private def parent0 : Fin {nv} → Fin {ne} := {}
private def parent1 : Fin {nv} → Fin {ne} := {}
private theorem captured_parent_fields :
    ∀ v : Fin {nv}, N.graph.IsHybrid v →
      N.graph.target (parent0 v) = v ∧
      N.graph.target (parent1 v) = v ∧ parent0 v ≠ parent1 v := by
  decide +kernel
private def parentRegistry : OriginalParentRegistry N where
  parents h := ⟨h.val, h.property, parent0 h.val, parent1 h.val,
    (captured_parent_fields h.val h.property).1,
    (captured_parent_fields h.val h.property).2.1,
    (captured_parent_fields h.val h.property).2.2⟩
  original_site _ := rfl
private def vertexMode : Fin {nv} → Bool := {}
private def common (h : Hybrid N) : Bool := vertexMode h.val
"#,vector(p0),vector(p1),vector(modes)),render.rendered_bytes)?;
 let word=request.word.iter().map(|s|match s {
  Symbol::Interval(j)=>format!(".interval {}",fin(*j)),
  Symbol::Exit(e)=>format!(".exit {}",fin(*e)),
  Symbol::Enter(v)=>format!(".enter {}",fin(*v)),
 }).collect::<Vec<_>>().join(", ");
 put(&mut out,&format!(r#"
private def word : List (Symbol (Fin {slots}) (Fin {nv}) (Fin {ne})) := [{word}]
"#),render.rendered_bytes)?;
 put(&mut out,&indexed_bank(request,table.variables.len(),render)?,render.rendered_bytes)?;
 let dimension=table.variables.len();
 let mut monomial_ids:BTreeMap<Vec<usize>,usize>=BTreeMap::new();
 for t in &table.transitions {
  for powers in t.polynomial.terms.keys(){
   let next=monomial_ids.len();monomial_ids.entry(powers.clone()).or_insert(next);
  }
 }
 for (powers,i) in &monomial_ids{
  if powers.len()!=table.variables.len(){return Err(Error::Invalid("word dictionary exponent arity"));}
  let body=powers.iter().enumerate().filter(|(_,power)|**power!=0)
   .map(|(v,power)|format!("({v}, {power})")).collect::<Vec<_>>().join(", ");
  put(&mut out,&format!(
   "private def monomial{i} : List (Fin {dimension} × Nat) := [{body}]\n"),
   render.rendered_bytes)?;
 }
 let mut rows=Vec::new();let mut monomials=0usize;
 for (i,t) in table.transitions.iter().enumerate(){
  if source_epoch::selected_view(context,&t.witness).map_err(Error::Invalid)?!=t.view{
   return Err(Error::Invalid("complete selected range witness"));
  }
  monomials=monomials.checked_add(t.polynomial.terms.len()).ok_or(Error::SourceLimit)?;
  if monomials>render.monomials{return Err(Error::SourceLimit);}
  let label=format!("destination{i}");
  crate::epoch_certificate::snapshot(&mut out,context,&t.witness,&label,render).map_err(Error::Snapshot)?;
  put(&mut out,&format!("#check {label}_selected_fields_exact\n"),render.rendered_bytes)?;
  rows.push(format!("({label}, {})",sparse(&t.polynomial,&table.variables,&monomial_ids,render)?));
 }
 put(&mut out,&format!(r#"
private def rows : Rows (Fin {dimension}) (Code N sample) := [{}]
private def nativeSelectedRows : Nat := {}
theorem complete_output_count : rows.length = nativeSelectedRows := by decide +kernel
#print nativeSelectedRows

-- Full table has been decoded; the next check compares ALL original fibres.
#check parentRegistry
#check word

theorem complete_word_coefficient_fibres_checked :
    checkNaturalWordIndexed N sample parentRegistry common word encodeVariable rows = true := by
  decide +kernel

#check complete_word_coefficient_fibres_checked

theorem actual_same_source_natural_word (b : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates (Fin {ne})) (p : HybridProbabilities N)
    (dur : Fin {slots} → ℝ≥0) :
    value (readRows (project N Finset.univ) rows b)
        (fun i => wordVariables N r (originalGamma p) dur (variableBank i)) =
      (((initializedWordLaw N sample parentRegistry p common r dur word).map
        (projection N Finset.univ)) b).toReal :=
  checked_natural_word_indexed N sample parentRegistry common word encodeVariable variableBank
    original_variable_native_bank_left_inverse rows complete_word_coefficient_fibres_checked b r p dur
#check actual_same_source_natural_word
end {}
"#,rows.join(",\n  "),table.transitions.len(),bindings.namespace),render.rendered_bytes)?;
 Ok(out)
}
fn example_request(common:bool)->Result<Request,Error>{
 let (input,_)=crate::source_certificate::example_request("parallel").map_err(|e|Error::Capture(format!("{e:?}")))?;
 let cell=cell_rows::compile_request(input).map_err(|e|Error::Capture(format!("{e:?}")))?;
 Ok(Request{
  context:parity_solver::source_population::Context{source:cell.original_chart().source.clone(),
   sample:vec![3,3,3],global_labels:vec![0,1,2]},
  initial:Initial::Natural,common:vec![common],slots:2,
  word:vec![Symbol::Enter(8),Symbol::Interval(0),Symbol::Exit(8),
   Symbol::Enter(7),Symbol::Interval(1),Symbol::Exit(6),Symbol::Exit(7)],
  terminal:Terminal::FullView,limits:source_word::Limits::default(),provider_limits:source_word::ProviderLimits::default(),
 })
}
pub fn example(mode:&str)->Result<String,Error>{
 let (is_common,namespace)=match mode{
  "independent"=>(false,"ResearchCommons.Generated.NaturalIndependentWord"),
  "common"=>(true,"ResearchCommons.Generated.NaturalCommonWord"),
  _=>return Err(Error::Invalid("word example mode")),
 };
 let request=example_request(is_common)?;
 let document=emit(&request,Bindings{original_module:"OriginalParallelBank",
  original_source:"ResearchCommons.Generated.OriginalParallelBank.originalSource",namespace},
  RenderLimits{rendered_bytes:262144,..RenderLimits::default()})?;
 let ending=format!("\nend {namespace}\n");
 let prefix=document.strip_suffix(&ending).ok_or(Error::Invalid("word namespace boundary"))?;
 let joined=format!(r#"{prefix}
theorem named_parent_order_matches_capture (b : Bool) :
    (parentRegistry.parents ⟨(7 : Fin 9), by decide +kernel⟩).parent b =
      ResearchCommons.Generated.OriginalParallelBank.code.2.2.2.2.2 (0 : Fin 1) b := by
  cases b <;> decide +kernel

noncomputable abbrev returnedBank := ResearchCommons.Generated.OriginalParallelBank.sharedBank
noncomputable def returnedDur : Fin 2 → ℝ≥0 :=
  ![⟨returnedBank.calendar.age (7 : Fin 9) - returnedBank.calendar.age (8 : Fin 9),
       le_of_lt (sub_pos.mpr (returnedBank.calendar.edge_older (8 : Fin 9)))⟩,
    ⟨returnedBank.calendar.age (6 : Fin 9) - returnedBank.calendar.age (7 : Fin 9),
       le_of_lt (sub_pos.mpr (returnedBank.calendar.edge_older (6 : Fin 9)))⟩]

#check returnedDur
theorem same_returned_bank_natural_word (b : SelectedIndex N sample Finset.univ) :
    value (readRows (project N Finset.univ) rows b)
        (fun i => wordVariables N returnedBank.rates (originalGamma returnedBank.inheritance) returnedDur (variableBank i)) =
      (((initializedWordLaw N sample parentRegistry returnedBank.inheritance common
        returnedBank.rates returnedDur word).map (projection N Finset.univ)) b).toReal :=
  actual_same_source_natural_word b returnedBank.rates returnedBank.inheritance returnedDur
#check same_returned_bank_natural_word
end {namespace}
"#);
 if joined.len()>262144{return Err(Error::SourceBytes{required:joined.len(),cap:262144});}
 Ok(joined)
}
#[cfg(test)]mod tests{
 use super::*;
 #[test]fn complete_natural_words_keep_original_register_parent_order_and_shared_bank(){
  for mode in ["independent","common"]{
   let s=example(mode).unwrap_or_else(|e|panic!("{mode}: {e:?}"));
   assert!(s.contains("sample : Fin 3"));
   assert!(s.contains("complete_word_coefficient_fibres_checked"));
   assert!(s.contains("named_parent_order_matches_capture"));
   assert!(s.contains("same_returned_bank_natural_word"));
   assert!(s.contains("destination13"));assert!(s.contains("Sum.inr"));
   assert!(!s.contains("native_decide"));assert!(!s.contains("sorry"));
  }
 }
 #[test]fn retained_word_refusal_does_not_emit_a_partial_table_or_budget_no(){
  let mut request=example_request(false).unwrap();request.limits.queries=0;
  let result=emit(&request,Bindings{original_module:"OriginalParallelBank",
   original_source:"ResearchCommons.Generated.OriginalParallelBank.originalSource",namespace:"Candidate"},RenderLimits::default());
  assert!(matches!(result,Err(Error::Unknown(_))));
 }
}
