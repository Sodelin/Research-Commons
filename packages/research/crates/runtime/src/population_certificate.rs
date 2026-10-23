//! Existing original population recurrence -> existing total-table proof source.
//! The exact Context, raw entering Snapshot and returned Table remain associated
//! in RAM. Rendering is not kernel acceptance or whole-word refinement.
use crate::exact_law::{cell_rows, population_certificate as retained};
use parity_solver::{forest::Tree, source_population::{self,Context,Snapshot,Location}};
pub use retained::{Bindings,Limits as RenderLimits};
pub use source_population::Limits as PopulationLimits;

#[derive(Debug,PartialEq,Eq)]
pub enum Error {
 Invalid(&'static str), Capture(String), Unknown(source_population::Limit), Render(retained::Error),
}

fn finite(value:usize)->String {format!("⟨{value}, by decide +kernel⟩")}
/// Produce an original-edge occurrence path, not another source predicate or
/// stochastic engine. Every emitted step is independently checked by Lean.
fn path(context:&Context,start:usize,target:usize)->Result<Vec<usize>,Error> {
 let count=context.source.vertices;
 if start>=count||target>=count{return Err(Error::Invalid("path endpoint"));}
 let mut previous=vec![None;count];let mut seen=vec![false;count];let mut pending=vec![start];
 seen[start]=true;
 while let Some(v)=pending.pop() {
  if v==target{break;}
  for (id,edge) in context.source.edges.iter().enumerate() {
   if edge.source==v&&!seen[edge.target] {
    seen[edge.target]=true;previous[edge.target]=Some(id);pending.push(edge.target);
   }
  }
 }
 if !seen[target]{return Err(Error::Invalid("missing original descendant path"));}
 let mut result=Vec::new();let mut cursor=target;
 while cursor!=start {
  let edge=previous[cursor].ok_or(Error::Invalid("path reconstruction"))?;
  result.push(edge);cursor=context.source.edges[edge].source;
 }
 result.reverse();Ok(result)
}
fn descendant_proof(context:&Context,population:Location)->Result<String,Error> {
 let mut out=String::new();
 for taxon in &context.sample {
  let named=finite(*taxon);
  match population {
   Location::Ancestral(root)=>{
    let root=finite(root);
    out.push_str(&format!(r#"      · change {root} = N.root ∧ N.graph.DReach {root} (N.leaf {named})
        refine ⟨root_exact.symm, ?_⟩
        simpa only [root_exact] using N.rooted (N.leaf {named})
"#));
   },
   Location::Edge(edge)=>{
    let numbered=finite(edge);let start=context.source.edges[edge].target;
    let target=context.source.leaves[*taxon];let edges=path(context,start,target)?;
    let first=finite(start);let last=finite(target);
    out.push_str(&format!(r#"      · change N.graph.DReach (N.graph.target {numbered}) (N.leaf {named})
        have target_at : N.graph.target {numbered} = {first} :=
          congrFun edge_targets_exact {numbered}
        have leaf_at : N.leaf {named} = {last} :=
          congrFun taxa_exact {named}
        rw [target_at, leaf_at]
"#));
    for (position,id) in edges.iter().enumerate() {
     let a=finite(context.source.edges[*id].source);
     let b=finite(context.source.edges[*id].target);let occurrence=finite(*id);
     out.push_str(&format!(r#"        have step{position} : N.graph.DReach {a} {b} := by
          have literal : N.graph.DReach (N.graph.source {occurrence}) (N.graph.target {occurrence}) :=
            Relation.ReflTransGen.single ⟨{occurrence}, rfl, rfl⟩
          simpa [edge_sources_exact, edge_targets_exact] using literal
"#));
    }
    if edges.is_empty(){out.push_str("        exact Relation.ReflTransGen.refl\n");}
    else {
     let mut proof=format!("step{}",edges.len()-1);
     for position in (0..edges.len()-1).rev(){
      proof=format!("Relation.ReflTransGen.trans step{position} ({proof})");
     }
     out.push_str(&format!("        exact {proof}\n"));
    }
   },
   Location::Node(_)=>return Err(Error::Invalid("node is not a population coefficient row")),
  }
 }
 Ok(out)
}
fn replace_validity(document:String,context:&Context,population:Location,destinations:usize)->Result<String,Error> {
 let descendants=descendant_proof(context,population)?;
 let labels=std::iter::once("entering".to_owned()).chain((0..destinations).map(|i|format!("destination{i}")));
 let mut output=document;
 for label in labels {
  let old=format!("    letI := sourceValidDecidable N sample (decode N.root {label}Snapshot)\n    decide +kernel⟩");
  if output.matches(&old).count()!=1{return Err(Error::Invalid("retained source-validity proof boundary"));}
  let replacement=format!(r#"    refine ⟨?_, ?_⟩
    · exact @of_decide_eq_true _ (forestValidDecidable (decode N.root {label}Snapshot))
        (by decide +kernel)
    · intro copy
      fin_cases copy
{descendants}  ⟩"#);
  output=output.replacen(&old,&replacement,1);
 }
 Ok(output)
}

/// Invoke the unchanged bounded recurrence and existing exporter together.
/// Resource refusal yields no table/proof and never a negative source claim.
/// The later complete Lean document must prove every literal SourceValid,
/// colocation and total coefficient-check premise.
pub fn emit(context:&Context,entering:&Snapshot,population:Location,bindings:Bindings<'_>,
    limits:PopulationLimits,render:RenderLimits)->Result<String,Error> {
 let result=source_population::population_row(context,entering,population,limits).map_err(Error::Invalid)?;
 let table=match result {
  source_population::Decision::Table(t)=>t,
  source_population::Decision::Unknown(limit)=>return Err(Error::Unknown(limit)),
 };
 let prepared=retained::prepare(context,entering,&table,bindings,render).map_err(Error::Render)?;
 let mut document=prepared.document().to_owned();
 // Portable proof-only projection fixes exposed by the first actual check.
 // Literal graph, snapshots, coefficient tables and theorem targets are unchanged.
 document=document.replacen("-- SOURCE CANDIDATE;", "set_option maxRecDepth 10000\nset_option maxHeartbeats 4000000\n\n-- SOURCE CANDIDATE;",1);
 document=document.replace("private abbrev N :","private noncomputable abbrev N :")
    .replace("theorem taxa_exact : N.leaf =", "theorem taxa_exact : (fun x => N.leaf x) =")
    .replace("by decide","by decide +kernel")
    .replace("    decide⟩","    decide +kernel⟩");
 document=replace_validity(document,context,population,table.transitions.len())?;
 document=document.replace("CoLocated N entering population := by decide +kernel",
    "CoLocated N entering population := by\n  unfold CoLocated\n  decide +kernel");
 if document.len()>render.rendered_bytes {
  return Err(Error::Render(retained::Error::Unknown{kind:"portable_rendered_bytes",required:Some(document.len()),cap:render.rendered_bytes}));
 }
 Ok(document)
}
/// Two actual raw ordered-copy rows on the same captured four-taxon graph.
/// Edge uses two copies of taxon0; ancestral uses the original taxa0/1.
/// The theorem concerns all positive rates/durations in that one population;
/// actual full-calendar/history/readout composition remains a separate join.
fn captured_example(edge:Option<usize>,namespace:&'static str)->Result<String,Error> {
 let ancestral=edge.is_none();
 let (input,_)=crate::source_certificate::example_request("tree")
    .map_err(|e|Error::Capture(format!("{e:?}")))?;
 let cell=cell_rows::compile_request(input).map_err(|e|Error::Capture(format!("{e:?}")))?;
 let source=cell.original_chart().source.clone();
 let sample=if ancestral {vec![0,1]}else{vec![0,0]};
 let register=vec![false;source.vertices];
 let population=if let Some(e)=edge {Location::Edge(e)}else{Location::Ancestral(source.root)};
 let context=Context{source,sample,global_labels:vec![0,1]};
 let entering=Snapshot::from_lineages(&context,&[(0,Tree::Leaf(0)),(1,Tree::Leaf(1))],population,register)
    .map_err(Error::Invalid)?;
 let document=emit(&context,&entering,population,Bindings {
   original_module:"OriginalTreeBank",
   original_source:"ResearchCommons.Generated.OriginalTreeBank.originalSource",
   namespace,
 },PopulationLimits::default(),RenderLimits{rendered_bytes:262144,..RenderLimits::default()})?;
 let ending=format!("\nend {namespace}\n");
 let prefix=document.strip_suffix(&ending).ok_or(Error::Invalid("retained namespace boundary"))?;
 let joined=format!(r#"{prefix}
noncomputable abbrev returnedRates :=
  ResearchCommons.Generated.OriginalTreeBank.sharedBank.rates
theorem same_returned_bank_population_probability (d : Code N sample) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-pairRate returnedRates population * (t : ℝ)))
      (exprPolynomial (collect rows d)) =
        (sourceTimeKernel N returnedRates t entering d).toReal :=
  original_population_probability d returnedRates t
end {namespace}
"#);
 if joined.len()>262144{return Err(Error::Render(retained::Error::Unknown{
  kind:"joined_rendered_bytes",required:Some(joined.len()),cap:262144}));}
 Ok(joined)
}
pub fn example(ancestral:bool)->Result<String,Error> {
 if ancestral {captured_example(None,"ResearchCommons.Generated.AncestralPopulation")}
 else {captured_example(Some(2),"ResearchCommons.Generated.EdgePopulation")}
}
/// Same four-taxon graph/rate bank, with a nontrivial original edge2 path
/// below the selected edge0 population. This exercises step-witness transport.
pub fn path_example()->Result<String,Error> {
 captured_example(Some(0),"ResearchCommons.Generated.PathPopulation")
}
#[cfg(test)]mod tests {
 use super::*;
 #[test]fn actual_edge_table_is_emitted_with_total_destination_and_original_source_targets(){
  let source=example(false).unwrap();
  assert!(source.contains("OriginalTreeBank.originalSource"));
  assert!(source.contains("coefficient_table_checked"));
  assert!(source.contains("original_population_probability (d : Code N sample)"));
  assert!(source.contains("private def population"));
  assert!(source.contains("same_returned_bank_population_probability"));
  assert!(source.contains("private noncomputable abbrev N"));
  assert!(source.contains("forestValidDecidable"));
  assert!(!source.contains("letI := sourceValidDecidable"));
 }
 #[test]fn actual_ancestral_table_retains_root_population_and_declared_sample(){
  let source=example(true).unwrap();
  assert!(source.contains("AncestralPopulation"));
  assert!(source.contains("rootPopulation"));
  assert!(source.contains("private def sample : Fin 2 → Fin 4"));
 }
 #[test]fn original_occurrence_path_is_emitted_for_a_nontrivial_descendant(){
  let source=path_example().unwrap();
  assert!(source.contains("PathPopulation"));
  assert!(source.contains("Relation.ReflTransGen.single"));
  assert!(source.contains("step0"));
 }
 #[test]fn inherited_population_limit_is_unknown_not_a_negative_proof(){
  use parity_solver::natural_cell::{Source,Edge};
  let context=Context{source:Source{vertices:3,root:0,edges:vec![Edge{source:0,target:1},Edge{source:0,target:2}],
    leaves:vec![1,2],hybrids:vec![]},sample:vec![0,0],global_labels:vec![0,1]};
  let entering=Snapshot::from_lineages(&context,&[(0,Tree::Leaf(0)),(1,Tree::Leaf(1))],
    Location::Edge(0),vec![false;3]).unwrap();
  let result=emit(&context,&entering,Location::Edge(0),
    Bindings{original_module:"Existing",original_source:"Existing.N",namespace:"Example"},
    PopulationLimits{calls:0,..PopulationLimits::default()},RenderLimits::default());
  assert!(matches!(result,Err(Error::Unknown(_))));
 }
}
