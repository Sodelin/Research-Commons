//! Captured original CHART -> literal Code/fields/certificate proof source.
//! Reuses the original parser, immutable cell snapshot, affine solver, Lean
//! admission predicates, field reflection and physical-bank receiver.
//! Rendering itself is not verification. Lean must accept the entire document.
//! The result contains its input data and stays in RAM; this library does no IO.
use crate::exact_law::cell_rows::{self,CompiledCellRows};
use parity_solver::{affine::{self,Decision},natural_cell::{AgeAtom,Comparison,Interval,Population},Rational};
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Error { Invalid(&'static str), Capture(String), Unknown, SourceLimit }
fn rat(q:&Rational)->String {format!("({} / {} : ℚ)",q.numer(),q.denom())}
fn vector(values:Vec<String>)->String {
 if values.is_empty() {"Fin.elim0".into()} else {format!("![{}]",values.join(", "))}
}
fn list(values:Vec<String>)->String {format!("[{}]",values.join(", "))}
fn interval(c:&Interval)->String {
 let bound=|b:&Option<parity_solver::natural_cell::Bound>| b.as_ref()
    .map(|b|format!("some ⟨{}, {}⟩",rat(&b.value),b.strict)).unwrap_or_else(||"none".into());
 format!("⟨{}, {}⟩",bound(&c.lower),bound(&c.upper))
}
fn atom(a:&AgeAtom)->String {match a {
 AgeAtom::Node(v)=>format!(".node {v}"),AgeAtom::Fixed(q)=>format!(".fixed {}",rat(q))}}
fn typed_atom(a:&AgeAtom)->String {match a {
 AgeAtom::Node(v)=>format!(".node ⟨{v}, by norm_num [vertexCount, edgeCount]⟩"),
 AgeAtom::Fixed(q)=>format!(".fixed {}",rat(q))}}
fn typed_population(p:Population)->String {match p {
 Population::Edge(e)=>format!("some ⟨{e}, by norm_num [vertexCount, edgeCount]⟩"),
 Population::Ancestral=>"none".into()}}
fn comparison(c:Comparison)->&'static str {match c {
 Comparison::Strict=>".strict",Comparison::Weak=>".weak",Comparison::Equal=>".equal"}}
fn population(p:Population)->String {match p {Population::Edge(e)=>format!("some {e}"),Population::Ancestral=>"none".into()}}
fn lean_string(s:&str)->String {
 format!("\"{}\"",s.replace('\\',"\\\\").replace('"',"\\\"").replace('\n',"\\n").replace('\r',"\\r").replace('\t',"\\t"))
}
fn valid_namespace(s:&str)->bool {
 !s.is_empty() && s.as_bytes()[0].is_ascii_alphabetic() &&
    s.bytes().all(|b|b.is_ascii_alphanumeric()||b==b'_')
}
/// Generate the complete literal proof from ONE immutable original snapshot.
/// No native predicate is treated as the Lean admission proof. Every graph
/// field, parent occurrence, coin bound, chart row and coordinate is retained.
pub fn emit(input:&[u8],namespace:&str,require_cut_child:bool,limit:usize)->Result<String,Error> {
 if !valid_namespace(namespace){return Err(Error::Invalid("namespace"));}
 let text=std::str::from_utf8(input).map_err(|_|Error::Invalid("UTF8"))?;
 if text.bytes().any(|b|b<32&&!matches!(b,b'\n'|b'\r'|b'\t')) {return Err(Error::Invalid("control byte"));}
 let captured=cell_rows::compile_request(input).map_err(|e|Error::Capture(format!("{e:?}")))?;
 emit_snapshot(&captured,text,namespace,require_cut_child,limit)
}
fn emit_snapshot(captured:&CompiledCellRows,text:&str,namespace:&str,require_cut_child:bool,limit:usize)->Result<String,Error> {
 let chart=captured.original_chart();let source=&chart.source;
 let nt=source.leaves.len();let nh=source.hybrids.len();
 let nv=nt.checked_mul(2).and_then(|n|nh.checked_mul(2).and_then(|h|n.checked_add(h)))
    .and_then(|n|n.checked_sub(1)).ok_or(Error::Invalid("vertex census overflow"))?;
 let ne=nt.checked_mul(2).and_then(|n|nh.checked_mul(3).and_then(|h|n.checked_add(h)))
    .and_then(|n|n.checked_sub(2)).ok_or(Error::Invalid("edge census overflow"))?;
 if nt<2||nv!=source.vertices||ne!=source.edges.len()||chart.coins.len()!=nh {
    return Err(Error::Invalid("original finite-code census"));
 }
 let n=captured.dimension();let cap=captured.projection_cap();
 let decision=affine::solve(n,captured.rows(),cap).map_err(Error::Invalid)?;
 if matches!(decision,Decision::Unknown{..}){return Err(Error::Unknown);}
 let edge_sources=vector(source.edges.iter().map(|e|e.source.to_string()).collect());
 let edge_targets=vector(source.edges.iter().map(|e|e.target.to_string()).collect());
 let leaves=vector(source.leaves.iter().map(usize::to_string).collect());
 let sites=vector(source.hybrids.iter().map(|h|h.vertex.to_string()).collect());
 let parents=vector(source.hybrids.iter().map(|h|
    format!("fun b => if b then {} else {}",h.incoming[1],h.incoming[0])).collect());
 let wire_edges=list(source.edges.iter().map(|e|format!("⟨{}, {}⟩",e.source,e.target)).collect());
 let wire_leaves=list(source.leaves.iter().map(usize::to_string).collect());
 let wire_hybrids=list(source.hybrids.iter().map(|h|
    format!("⟨{}, {}, {}⟩",h.vertex,h.incoming[0],h.incoming[1])).collect());
 let constraints=chart.chronology.iter().map(|c|
    format!("⟨{}, {}, {}⟩",comparison(c.kind),atom(&c.left),atom(&c.right))).collect::<Vec<_>>();
 let exposures=chart.exposures.iter().map(|e|
    format!("⟨{}, {}, {}, {}⟩",population(e.population),atom(&e.younger),atom(&e.older),interval(&e.interval))).collect::<Vec<_>>();
 let coins=chart.coins.iter().map(interval).collect::<Vec<_>>();
 let wire_chronology=list(constraints);
 let chronology=vector(chart.chronology.iter().map(|c|
    format!("⟨{}, {}, {}⟩",typed_atom(&c.left),typed_atom(&c.right),comparison(c.kind))).collect());
 let wire_exposures=list(exposures);
 let exposures=vector(chart.exposures.iter().map(|e|
    format!("⟨{}, {}, {}, {}⟩",typed_population(e.population),typed_atom(&e.younger),typed_atom(&e.older),interval(&e.interval))).collect());
 let wire_coins=list(coins.clone());let coin_vector=vector(coins);
 let root=source.root;let nc=chart.chronology.len();let ni=chart.exposures.len();
 let original=lean_string(text);
 let cut=if require_cut_child {"theorem cut_child : GProgram.G7.OriginalAdmission.CutChild code := by decide\n"}else{""};
 let mut output=format!(r#"import OriginalCodeChartReceiver
import Mathlib.Tactic.FinCases

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Particular captured original source and shared cell bank. No whole-source
census, physical readout law, universal parser/Rust refinement or policy
completeness is inferred. Rendering is not acceptance. -/
namespace ResearchCommons.Generated.{namespace}
open Nanuq.Source GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.RationalNaturalCellWitness
open Astra.OriginalCodeChartReflection Astra.OriginalCodeChartReceiver

def originalRequest : String := {original}
def code : Code (Fin {nt}) (Fin {nh}) := by
  simp only [Code, vertexCount, edgeCount, Fintype.card_fin]
  exact ⟨{edge_sources}, {edge_targets}, {root}, {leaves}, {sites}, {parents}⟩
theorem binary_valid : BinaryValid code := by decide
theorem registry_valid : RegistryValid code := by decide
noncomputable abbrev originalSource := sourceOfValid code binary_valid
{cut}
def chronology : Fin {nc} → AgeConstraint (NV (X:=Fin {nt}) (ID:=Fin {nh})) := {chronology}
def exposures : Fin {ni} → Exposure (NV (X:=Fin {nt}) (ID:=Fin {nh})) (NE (X:=Fin {nt}) (ID:=Fin {nh})) := {exposures}
def coinIntervals : Fin {nh} → RationalInterval := {coin_vector}
noncomputable def coins (h : Hybrid (sourceOfValid code binary_valid)) : RationalInterval :=
  coinIntervals ((decodedIDs code binary_valid registry_valid).symm h)
def capturedSource : GParity.Chart.Source :=
  ⟨{nv}, {root}, {wire_edges}, {wire_leaves}, {wire_hybrids}⟩
def capturedInput : GParity.Chart.Input :=
  ⟨capturedSource, {wire_chronology}, {wire_exposures}, {wire_coins}, {cap}⟩
theorem source_fields_exact :
    sourceOfCode code (Equiv.refl (Fin {nt})) (Equiv.refl (Fin {nh})) = capturedSource := by rfl
theorem input_fields_exact :
    inputOfCode code binary_valid registry_valid (Equiv.refl (Fin {nt})) (Equiv.refl (Fin {nh}))
      chronology exposures coins {cap} = capturedInput := by
  simp only [inputOfCode, coins, Equiv.refl_symm,
    Equiv.refl_apply, Equiv.symm_apply_apply]
  rw [source_fields_exact]
  norm_num [capturedInput, chronology, exposures, coinIntervals,
    Astra.NativeCellAggregateReflection.reflectChronology,
    Astra.NativeCellAggregateReflection.reflectExposure, Astra.NativeCellAggregateReflection.reflectAge,
    Astra.NativeCellFormReflection.encodeComparison, Astra.NativeCellFormReflection.encodeInterval,
    Astra.NativeCellFormReflection.encodeBound, List.ofFn_succ]
"#);
 match decision {
  Decision::Witness(x)=>{
    if !affine::check_witness(n,captured.rows(),&x){return Err(Error::Invalid("native witness"));}
    let values=list(x.iter().map(rat).collect());
    output.push_str(&format!(r#"
def returned : List Rat := {values}
theorem checked :
    GParity.Affine.checkWitness {n} (GParity.Chart.emitRows capturedInput) returned = true := by
  decide +kernel
noncomputable def sharedBank :=
  checked_original_bank code binary_valid registry_valid (Equiv.refl (Fin {nt})) (Equiv.refl (Fin {nh}))
    chronology exposures coins {cap} returned (by simpa only [input_fields_exact, vertexCount, edgeCount, Fintype.card_fin] using checked)
theorem actual_source_cell_feasible :
    originalCellFeasible (sourceOfValid code binary_valid) chronology exposures coins :=
  checked_original_bank_feasible code binary_valid registry_valid (Equiv.refl (Fin {nt})) (Equiv.refl (Fin {nh}))
    chronology exposures coins {cap} returned (by simpa only [input_fields_exact, vertexCount, edgeCount, Fintype.card_fin] using checked)
"#));
  }
  Decision::Exclusion(weights)=>{
    if !affine::check_exclusion(n,captured.rows(),&weights){return Err(Error::Invalid("native exclusion"));}
    let values=list(weights.iter().map(rat).collect());
    output.push_str(&format!(r#"
def weights : List Rat := {values}
theorem weights_complete : weights.length = (GParity.Chart.emitRows capturedInput).length := by decide
theorem checked :
    GParity.Affine.checkContradiction {n} (GParity.Chart.emitRows capturedInput) weights = true := by
  decide +kernel
theorem actual_source_cell_infeasible :
    ¬ originalCellFeasible (sourceOfValid code binary_valid) chronology exposures coins :=
  checked_original_exclusion code binary_valid registry_valid (Equiv.refl (Fin {nt})) (Equiv.refl (Fin {nh}))
    chronology exposures coins {cap} weights
    (by simpa only [input_fields_exact, vertexCount, edgeCount, Fintype.card_fin] using weights_complete)
    (by simpa only [input_fields_exact, vertexCount, edgeCount, Fintype.card_fin] using checked)
"#));
  }
  Decision::Unknown{..}=>return Err(Error::Unknown),
 }
 output.push_str(&format!("end ResearchCommons.Generated.{namespace}\n"));
 if output.len()>limit {return Err(Error::SourceLimit);}
 Ok(output)
}
/// Public deterministic engineering inputs, not new biological experiments.
/// Four original taxa, plus an ordered non-half parallel-arm case.
pub(crate) fn example_request(which:&str)->Result<(&'static [u8],&'static str),Error> {
 let (input,namespace)=match which {
  "tree"=>("RC1 CHART 7 6 4 0 1 2 4096\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nEDGE 2 1 3\nEDGE 3 1 4\nEDGE 4 2 5\nEDGE 5 2 6\nLEAF 0 3\nLEAF 1 4\nLEAF 2 5\nLEAF 3 6\nAGE EQ V:0 Q:5/1\nEXPOSURE 0 E:0 V:1 V:0 LE:1/2 LE:5/1\nEXPOSURE 1 A Q:0/1 Q:2/1 LE:1/2 NONE\n","OriginalTreeBank"),
  "parallel"=>("RC1 CHART 9 9 4 1 1 2 4096\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nEDGE 2 1 3\nEDGE 3 1 4\nEDGE 4 2 5\nEDGE 5 2 6\nEDGE 6 6 7\nEDGE 7 6 7\nEDGE 8 7 8\nLEAF 0 3\nLEAF 1 4\nLEAF 2 5\nLEAF 3 8\nHYBRID 0 7 7 6\nAGE EQ V:0 Q:8/1\nEXPOSURE 0 E:6 V:7 V:6 LE:1/2 LE:5/1\nEXPOSURE 1 A Q:0/1 Q:2/1 LE:1/2 NONE\nCOIN 0 LE:1/3 LE:1/3\n","OriginalParallelBank"),
  "infeasible"=>("RC1 CHART 7 6 4 0 1 0 4096\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nEDGE 2 1 3\nEDGE 3 1 4\nEDGE 4 2 5\nEDGE 5 2 6\nLEAF 0 3\nLEAF 1 4\nLEAF 2 5\nLEAF 3 6\nAGE EQ V:0 Q:0/1\n","OriginalCellExclusion"),
  _=>return Err(Error::Invalid("example name")),
 };
 Ok((input.as_bytes(),namespace))
}
pub fn example(which:&str)->Result<String,Error> {
 let (input,namespace)=example_request(which)?;
 emit(input,namespace,true,262144)
}
#[cfg(test)] mod tests {
 use super::*;
 #[test] fn four_taxon_graph_and_actual_shared_coordinates_are_emitted(){
  let source=example("tree").unwrap();
  assert!(source.contains("Code (Fin 4) (Fin 0)"));
  assert!(source.contains("actual_source_cell_feasible"));
  assert!(source.contains("some ⟨(1 / 2 : ℚ), false⟩, none"));
 }
 #[test] fn distinct_parallel_occurrences_and_parent_bit_order_are_literal(){
  let source=example("parallel").unwrap();
  assert!(source.contains("⟨7, 7, 6⟩"));
  assert!(source.contains("fun b => if b then 6 else 7"));
  assert!(source.contains("some ⟨(1 / 3 : ℚ), false⟩"));
 }
 #[test] fn negative_certificate_keeps_the_supplied_original_cell_scope(){
  let source=example("infeasible").unwrap();
  assert!(source.contains("weights_complete"));
  assert!(source.contains("actual_source_cell_infeasible"));
  assert!(!source.contains("actual_source_cell_feasible"));
 }
 #[test] fn unknown_is_not_rendered_as_infeasibility_or_a_proof(){
  let raw=b"RC1 CHART 3 2 2 0 0 0 0\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nLEAF 0 1\nLEAF 1 2\n";
  assert_eq!(emit(raw,"NoProof",true,262144),Err(Error::Unknown));
  assert!(matches!(emit(raw,"Bad;Injection",true,262144),Err(Error::Invalid(_))));
 }
}
