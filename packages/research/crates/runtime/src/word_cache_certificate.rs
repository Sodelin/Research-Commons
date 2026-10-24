//! Checked primitive-row bundle for the SAME retained natural source word.
//! SourceWord, its conditional providers, full ordered snapshots and the
//! original natural register bank are reused without modifying an engine.
use crate::word_certificate as direct;
use crate::exact_law::population_certificate as retained;
use parity_solver::{source_word::{self,Request,Initial,Symbol,Terminal,Table,Variable},
    source_epoch::{SelectedView,Transition},source_population::{Snapshot,Location}};

#[derive(Clone,Copy,Debug)]
pub struct Limits {
 pub modules:usize,pub entries:usize,pub source_bytes:usize,pub total_bytes:usize,
}
impl Default for Limits {
 fn default()->Self{Self{modules:8192,entries:4096,source_bytes:262144,total_bytes:16*1024*1024}}
}
#[derive(Debug,PartialEq,Eq)]
pub enum Error {
 Invalid(&'static str),Direct(direct::Error),Native(source_word::Error),
 NativeUnknown{letter:Option<usize>,limit:source_word::Limit},
 Limit{kind:&'static str,required:usize,cap:usize},Overflow,
}
#[derive(Debug)]
pub struct Module {pub name:String,pub source:String}
#[derive(Debug)]
pub struct Bundle {
 pub modules:Vec<Module>,pub final_module:String,pub primitive_entries:usize,
 pub source_word_length:usize,pub total_bytes:usize,
}
impl Bundle {
 pub fn json(&self)->Result<String,Error>{
  serde_json::to_string(&serde_json::json!({
   "schema":1,"kind":"original-natural-word-checked-cache","final_module":self.final_module,
   "primitive_entries":self.primitive_entries,"source_word_length":self.source_word_length,
   "total_source_bytes":self.total_bytes,"kernel_checked":false,
   "scope":"Full ordered same-word/source/bank; every primitive and final fibre check still required",
   "modules":self.modules.iter().map(|m|serde_json::json!({"module":m.name,"source":m.source})).collect::<Vec<_>>()
  })).map_err(|_|Error::Invalid("bundle JSON"))
 }
}
struct Entry {operation:Symbol,input:Snapshot,view:SelectedView,table:Table}
fn bound(kind:&'static str,required:usize,cap:usize)->Result<(),Error>{
 if required>cap{Err(Error::Limit{kind,required,cap})}else{Ok(())}
}
fn add(a:usize,b:usize)->Result<usize,Error>{a.checked_add(b).ok_or(Error::Overflow)}
fn fin(n:usize)->String{format!("⟨{n}, by decide +kernel⟩")}
fn symbol(s:Symbol)->String{match s{
 Symbol::Interval(i)=>format!(".interval {}",fin(i)),
 Symbol::Exit(i)=>format!(".exit {}",fin(i)),
 Symbol::Enter(i)=>format!(".enter {}",fin(i)),
}}
fn query(request:&Request,letter:Option<usize>)->Result<Table,Error>{
 match source_word::word_row(request).map_err(Error::Native)?{
  source_word::Decision::Table(t)=>Ok(t),
  source_word::Decision::Unknown(limit)=>Err(Error::NativeUnknown{letter,limit}),
 }
}
fn observe_work(total:&mut [usize;3],table:&Table,request:&Request)->Result<(),Error>{
 let work=[table.work.queries,table.work.branches,table.work.term_products];
 let caps=[request.limits.queries,request.limits.branches,request.limits.term_products];
 let names=["extra_queries","extra_branches","extra_term_products"];
 for i in 0..3{total[i]=add(total[i],work[i])?;bound(names[i],total[i],caps[i])?;}
 Ok(())
}
fn append(bundle:&mut Bundle,name:String,source:String,limits:Limits)->Result<(),Error>{
 bound("modules",add(bundle.modules.len(),1)?,limits.modules)?;
 bound("source_bytes",source.len(),limits.source_bytes)?;
 let next=add(bundle.total_bytes,source.len())?;bound("total_source_bytes",next,limits.total_bytes)?;
 if bundle.modules.iter().any(|m|m.name==name){return Err(Error::Invalid("duplicate bundle module"));}
 bundle.total_bytes=next;bundle.modules.push(Module{name,source});Ok(())
}
fn header(imports:&[String],namespace:&str,context:&str)->String{
 let imports=imports.iter().map(|s|format!("import {s}\n")).collect::<String>();
 format!(r#"{imports}
set_option maxRecDepth 10000
set_option maxHeartbeats 30000000
namespace {namespace}
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
open GProgram.G7.FullEpochPolynomial GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveInitializationCoefficients
open GProgram.G7.EffectiveWordCoefficients GProgram.G7.SymbolicProgramPolynomial
open Astra.NativeSparseTableCertificate Astra.OriginalWordCacheCertificate
open scoped NNReal BigOperators
open {context}
"#)
}
/// Split only after a COMPLETE destination declaration/proof block. Public
/// constants stay in one reopened namespace, and modules import their predecessor.
/// This is serialization of already returned fields, never truncation or a
/// new source/transition constructor.
fn data_parts(bundle:&mut Bundle,base:&str,namespace:&str,context_module:&str,
 context_namespace:&str,declarations:&str,limits:Limits)->Result<String,Error>{
 let marker="_selected_fields_exact\n";
 let mut blocks=Vec::new();let mut start=0usize;let mut at=0usize;
 while let Some(offset)=declarations[at..].find(marker){
  let end=at+offset+marker.len();blocks.push(&declarations[start..end]);start=end;at=end;
 }
 if start<declarations.len(){blocks.push(&declarations[start..]);}
 let mut imports=vec![context_module.to_string()];let mut content=String::new();let mut part=0usize;
 let cap=limits.source_bytes.min(131072);
 let mut last=context_module.to_string();
 for block in blocks {
  let block=block.replace("private ","");
  let prefix=header(&imports,namespace,context_namespace);
  let end=format!("\nend {namespace}\n");
  if !content.is_empty() && prefix.len()+content.len()+block.len()+end.len()>cap {
   let name=format!("{base}Data{part}");let source=format!("{prefix}{content}{end}");
   append(bundle,name.clone(),source,limits)?;last=name.clone();part+=1;
   imports=vec![context_module.to_string(),name];content.clear();
  }
  let prefix=header(&imports,namespace,context_namespace);
  bound("destination_data_part",prefix.len()+content.len()+block.len()+end.len(),limits.source_bytes)?;
  content.push_str(&block);
 }
 if !content.is_empty(){
  let name=format!("{base}Data{part}");
  let source=format!("{}{}\nend {namespace}\n",header(&imports,namespace,context_namespace),content);
  append(bundle,name.clone(),source,limits)?;last=name;
 }
 Ok(last)
}
/// Original population order, restricted to ALL actual current populations.
/// Node copies are inert during this interval. The generated ActiveIn proof
/// checks coverage against the literal source-valid input; this is metadata,
/// never an independently assumed omission or re-fitted rate bank.
fn active_populations(request:&Request,input:&Snapshot)->Vec<String>{
 (0..request.context.source.edges.len()).map(Location::Edge)
  .chain(std::iter::once(Location::Ancestral(request.context.source.root)))
  .filter(|place|input.live.iter().any(|&a|input.population[a]==Some(*place)))
  .map(|place|match place{
   Location::Edge(e)=>format!("some {}",fin(e)),
   Location::Ancestral(_)=>"none".into(),
   Location::Node(_)=>unreachable!(),
  }).collect()
}
fn interval_form(request:&Request,entry:&Entry)->Result<String,Error>{
 if let Symbol::Interval(slot)=entry.operation {
  if let Some(&first)=entry.input.live.first() {
   if let Some(place)=entry.input.population[first] {
    if !matches!(place,Location::Node(_)) &&
       entry.input.live.iter().all(|&a|entry.input.population[a]==Some(place)) {
     let variable=entry.table.variables.iter().position(|v|
      *v==(Variable::Survival{slot,population:place}))
      .ok_or(Error::Invalid("same original colocated survival coordinate"))?;
     let mut rows=Vec::new();
     for (i,destination) in entry.table.transitions.iter().enumerate(){
      let mut terms=Vec::new();
      for (powers,q) in &destination.polynomial.terms {
       if powers.len()!=entry.table.variables.len() ||
          powers.iter().enumerate().any(|(j,p)|j!=variable && *p!=0) {
        return Err(Error::Invalid("foreign coordinate in colocated scalar row"));
       }
       let scalar=if q.denom()==parity_solver::q(1,1).denom(){q.numer().to_string()}
        else{format!("({} / {} : ℚ)",q.numer(),q.denom())};
       terms.push(format!("({}, {scalar})",powers[variable]));
      }
      rows.push(format!("(destination{i}, [{}])",terms.join(", ")));
     }
     let population=match place{
      Location::Edge(e)=>format!("(some {})",fin(e)),
      Location::Ancestral(_)=>"none".into(),
      Location::Node(_)=>unreachable!(),
     };
     return Ok(format!(".colocated {population} (by\n    unfold CoLocated\n    decide +kernel) [{}]",
       rows.join(",\n    ")));
    }
   }
  }
 }
 Ok(format!(".active [{}] (by\n    unfold ActiveIn\n    decide +kernel)",
    active_populations(request,&entry.input).join(", ")))
}
fn rows_declaration(rows:&[String],dimension:usize,copies:usize)->String{
 // copies is metadata only; the actual shared sample type comes from Context.
 format!("\n-- {} full-copy literal carrier; no quotient by a forest.\nprivate def rows : Rows (Fin {dimension}) (Code N sample) := [{}]\n",
  copies,rows.join(",\n  "))
}
/// Produce all source in RAM or refuse. Original child/provider caps remain.
/// Cache construction has a separate cumulative extra-work cap; it is observed
/// after each child and is not a global allocator guarantee. No partial bundle
/// is returned on any failure.
pub fn emit(request:&Request,bindings:retained::Bindings<'_>,limits:Limits,
 render:retained::Limits)->Result<Bundle,Error>{
 if request.initial!=Initial::Natural || request.terminal!=Terminal::FullView {
  return Err(Error::Invalid("natural FullView original word required"));
 }
 let final_module=bindings.namespace.rsplit('.').next().ok_or(Error::Invalid("namespace"))?.to_string();
 if final_module.is_empty(){return Err(Error::Invalid("namespace"));}
 let context_module=format!("{final_module}Context");
 let context_namespace=format!("{}Context",bindings.namespace);
 let render_all=retained::Limits{rendered_bytes:limits.total_bytes,..render};
 // This validates the ENTIRE old request, including its original word tail,
 // before cache limits can obscure invalid-input errors. It executes the
 // unchanged final native word provider once and retains its exact full rows.
 let complete=direct::emit(request,retained::Bindings{
  original_module:bindings.original_module,original_source:bindings.original_source,
  namespace:&context_namespace},render_all).map_err(Error::Direct)?;
 let marker="#check original_variable_native_bank_left_inverse\n";
 let (context_prefix,remaining)=complete.split_once(marker).ok_or(Error::Invalid("context source boundary"))?;
 let mut context=format!("{context_prefix}{marker}\nend {context_namespace}\n");
 context=context.replace("import OriginalWordTableCertificate\n","import OriginalWordCacheCertificate\n")
   .replace("private ","");
 let mut bundle=Bundle{modules:Vec::new(),final_module:final_module.clone(),
  primitive_entries:0,source_word_length:request.word.len(),total_bytes:0};
 append(&mut bundle,context_module.clone(),context,limits)?;
 let mut initial_request=request.clone();initial_request.word.clear();
 let initial=query(&initial_request,None)?;
 let variables=initial.variables.clone();let dimension=variables.len();
 let mut extra_work=[0usize;3];observe_work(&mut extra_work,&initial,request)?;
 let mut frontier=initial.transitions.clone();let mut entries:Vec<Entry>=Vec::new();
 for (letter,&operation) in request.word.iter().enumerate(){
  let mut next:Vec<Transition>=Vec::new();
  for entering in &frontier {
   let index=if let Some(i)=entries.iter().position(|e|e.operation==operation && e.view==entering.view){i}
   else{
    bound("primitive_entries",add(entries.len(),1)?,limits.entries)?;
    let mut child=request.clone();child.initial=Initial::Conditional(entering.witness.clone());
    child.word=vec![operation];
    let table=query(&child,Some(letter))?;
    observe_work(&mut extra_work,&table,request)?;
    if table.variables!=variables{return Err(Error::Invalid("same complete original variable bank"));}
    let i=entries.len();
    entries.push(Entry{operation,input:entering.witness.clone(),view:entering.view.clone(),table});i
   };
   for destination in &entries[index].table.transitions {
    if !next.iter().any(|old|old.view==destination.view){next.push(destination.clone());}
   }
  }
  frontier=next;
 }
 bundle.primitive_entries=entries.len();
 let slots=request.slots;let copies=request.context.sample.len();
 // One actual original register initialization, checked independently.
 let initial_module=format!("{final_module}Initial");
 let initial_namespace=format!("{}.Initial",bindings.namespace);
 let (decl,rows)=direct::table_body(request,&initial,render_all).map_err(Error::Direct)?;
 let data=data_parts(&mut bundle,&initial_module,&initial_namespace,&context_module,
  &context_namespace,&decl,limits)?;
 let src=format!(r#"{header}{rows}
theorem initial_coefficient_fibres_checked :
    checkInitial N sample encodeVariable rows = true := by decide +kernel
def certificate : CertifiedInitial N sample encodeVariable :=
  ⟨rows, initial_coefficient_fibres_checked⟩
#check certificate
end {initial_namespace}
"#,header=header(&[context_module.clone(),data],&initial_namespace,&context_namespace),
 rows=rows_declaration(&rows,dimension,copies).replace("private ",""));
 append(&mut bundle,initial_module.clone(),src,limits)?;
 let mut certificates=Vec::new();let mut imports=vec![context_module.clone(),initial_module];
 for (i,entry) in entries.iter().enumerate(){
  let name=format!("{final_module}Step{i}");let namespace=format!("{}.Step{i}",bindings.namespace);
  let mut input=String::new();
  crate::epoch_certificate::snapshot(&mut input,&request.context,&entry.input,"input",render_all)
   .map_err(|e|Error::Direct(direct::Error::Snapshot(e)))?;
  let (decl,rows)=direct::table_body(request,&entry.table,render_all).map_err(Error::Direct)?;
  let data=data_parts(&mut bundle,&name,&namespace,&context_module,&context_namespace,
   &format!("{input}{decl}"),limits)?;
  let source=format!(r#"{header}{rows}
def entry : StepEntry N sample (Fin {dimension}) (Fin {slots}) where
  operation := {operation}
  input := input
  rows := rows
  interval := {interval}
theorem primitive_coefficient_fibres_checked :
    checkStep N sample parentRegistry common encodeVariable entry = true := by decide +kernel
def certificate : CertifiedStep N sample parentRegistry common encodeVariable :=
  ⟨entry, primitive_coefficient_fibres_checked⟩
#check certificate
end {namespace}
"#,header=header(&[context_module.clone(),data],&namespace,&context_namespace),
 rows=rows_declaration(&rows,dimension,copies),operation=symbol(entry.operation),
 interval=interval_form(request,entry)?);
  append(&mut bundle,name.clone(),source,limits)?;
  imports.push(name);certificates.push(format!("{namespace}.certificate"));
 }
 // The empty-word path retains the already small direct composition check.
 if request.word.is_empty(){
 // Reuse the exact final native table rendered by the original emitter.
 let row_marker="private def rows : Rows";
 let row_start=remaining.find(row_marker).ok_or(Error::Invalid("final row boundary"))?;
 let proof_marker="theorem complete_word_coefficient_fibres_checked :";
 let proof_start=remaining.find(proof_marker).ok_or(Error::Invalid("final proof boundary"))?;
 let data=data_parts(&mut bundle,&final_module,bindings.namespace,&context_module,&context_namespace,
  &remaining[..row_start],limits)?;
 imports.push(data);
 let final_source=format!(r#"{header}{rows}
private def cache : List (CertifiedStep N sample parentRegistry common encodeVariable) :=
  [{certificates}]
theorem complete_word_coefficient_fibres_checked :
    checkComposedWord N sample parentRegistry common encodeVariable
      {initial_namespace}.certificate cache word rows = true := by decide +kernel
#check complete_word_coefficient_fibres_checked
theorem actual_same_source_natural_word (b : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates (Fin {edges})) (p : HybridProbabilities N)
    (dur : Fin {slots} → ℝ≥0) :
    value (readRows (project N Finset.univ) rows b)
        (fun i => wordVariables N r (originalGamma p) dur (variableBank i)) =
      (((initializedWordLaw N sample parentRegistry p common r dur word).map
        (projection N Finset.univ)) b).toReal :=
  checked_same_source_natural_word N sample parentRegistry common encodeVariable variableBank
    original_variable_native_bank_left_inverse {initial_namespace}.certificate cache word rows
    complete_word_coefficient_fibres_checked b r p dur
#check actual_same_source_natural_word
end {namespace}
"#,header=header(&imports,bindings.namespace,&context_namespace),
 rows=&remaining[row_start..proof_start],certificates=certificates.join(",\n   "),
 edges=request.context.source.edges.len(),namespace=bindings.namespace);
 append(&mut bundle,final_module,final_source,limits)?;
 return Ok(bundle);
 }
 // Reuse the original certified primitive list once for every compact prefix.
 let cache_module=format!("{final_module}Cache");
 let cache_namespace=format!("{}.Cache",bindings.namespace);
 let cache_source=format!(r#"{header}
def cache : List (CertifiedStep N sample parentRegistry common encodeVariable) :=
  [{certificates}]
end {cache_namespace}
"#,header=header(&imports,&cache_namespace,&context_namespace),
 certificates=certificates.join(",\n   "));
 append(&mut bundle,cache_module.clone(),cache_source,limits)?;
 let row_marker="private def rows : Rows";
 let row_start=remaining.find(row_marker).ok_or(Error::Invalid("final row boundary"))?;
 let proof_marker="theorem complete_word_coefficient_fibres_checked :";
 let proof_start=remaining.find(proof_marker).ok_or(Error::Invalid("final proof boundary"))?;
 let mut previous_module=format!("{final_module}Initial");
 let mut previous_rows=format!("{initial_namespace}.certificate.rows");
 let mut stage_names=Vec::new();let mut stage_definitions=Vec::new();let mut stage_checks=Vec::new();
 let mut previous_namespace=initial_namespace.clone();
 let mut previous_views=initial.transitions.iter().map(|t|t.view.clone()).collect::<Vec<_>>();
 for (letter,&operation) in request.word.iter().enumerate(){
  let stage_module=format!("{final_module}Stage{letter}");
  let stage_namespace=format!("{}.Stage{letter}",bindings.namespace);
  // Native full-view matches are only hints. Every exact typed source/cache
  // identity below must be proved by the kernel before it can simplify the
  // unchanged total coefficient-fibre check.
  let mut hit_proofs=String::new();let mut hit_names=Vec::new();
  for (input,view) in previous_views.iter().enumerate(){
   let index=entries.iter().position(|e|e.operation==operation && &e.view==view)
    .ok_or(Error::Invalid("complete current-prefix cache match"))?;
   let name=format!("cached_input{input}_exact");
   hit_names.push(format!("{stage_namespace}.{name}"));
   hit_proofs.push_str(&format!(r#"
theorem {name} :
    cachedStep N sample parentRegistry common encodeVariable {cache_namespace}.cache
      ({operation}) {previous_namespace}.destination{input} =
        {namespace}.Step{index}.certificate.entry.rows := by
  rfl
"#,operation=symbol(operation),namespace=bindings.namespace));
  }
  let mut next_views=Vec::new();
  let (declarations,rows)=if letter+1==request.word.len(){
   // These are the EXACT original complete native final rows already obtained
   // by direct::emit. No second final query, fitting or independent bank.
   (remaining[..row_start].to_string(),remaining[row_start..proof_start].replace("private ",""))
  }else{
   let mut prefix=request.clone();prefix.word=request.word[..=letter].to_vec();
   let table=query(&prefix,Some(letter))?;observe_work(&mut extra_work,&table,request)?;
   if table.variables!=variables{return Err(Error::Invalid("prefix complete original variable bank"));}
   let (declarations,rows)=direct::table_body(request,&table,render_all).map_err(Error::Direct)?;
   next_views=table.transitions.iter().map(|t|t.view.clone()).collect();
   (declarations,rows_declaration(&rows,dimension,copies).replace("private ",""))
  };
  let data=data_parts(&mut bundle,&stage_module,&stage_namespace,&context_module,
   &context_namespace,&declarations,limits)?;
  let previous_definitions=if letter==0 {
   format!("{initial_namespace}.certificate, {initial_namespace}.rows")
  }else{format!("{previous_namespace}.rows")};
  let hit_rules=hit_names.join(",\n    ");
  let source=format!(r#"{header}{rows}{hit_proofs}
def stage : WordStage N sample (Fin {dimension}) (Fin {slots}) where
  operation := {operation}
  rows := rows
theorem coefficient_fibres_checked :
    checkRows (project N Finset.univ)
      (GProgram.G7.SparseWordComposition.bindRows {previous_rows}
        (cachedStep N sample parentRegistry common encodeVariable {cache_namespace}.cache
          ({operation}))) rows = true := by
  simp only [{previous_definitions}, GProgram.G7.SparseWordComposition.bindRows,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    {hit_rules}]
  decide +kernel
#check coefficient_fibres_checked
end {stage_namespace}
"#,header=header(&[cache_module.clone(),previous_module.clone(),data],
  &stage_namespace,&context_namespace),operation=symbol(operation));
  append(&mut bundle,stage_module.clone(),source,limits)?;
  stage_names.push(format!("{stage_namespace}.stage"));
  stage_definitions.push(format!("{stage_namespace}.stage"));
  stage_checks.push(format!("{stage_namespace}.coefficient_fibres_checked"));
  previous_module=stage_module;previous_rows=format!("{stage_namespace}.rows");
  previous_namespace=stage_namespace;previous_views=next_views;
 }
 let proof_rules=stage_definitions.into_iter().chain(stage_checks).collect::<Vec<_>>().join(",\n    ");
 let source=format!(r#"{header}
private def stages : List (WordStage N sample (Fin {dimension}) (Fin {slots})) :=
  [{stage_names}]
private abbrev rows := {previous_rows}
theorem stages_retain_every_original_operation :
    stages.map WordStage.operation = word := by rfl
theorem final_rows_are_the_complete_original_native_output :
    finalStageRows N sample {initial_namespace}.certificate.rows stages = rows := by rfl
theorem complete_word_coefficient_fibres_checked :
    checkStages N sample parentRegistry common encodeVariable {cache_namespace}.cache
      {initial_namespace}.certificate.rows stages = true := by
  simp only [stages, checkStages, {proof_rules}, Bool.true_and]
#check complete_word_coefficient_fibres_checked
theorem actual_same_source_natural_word (b : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates (Fin {edges})) (p : HybridProbabilities N)
    (dur : Fin {slots} → ℝ≥0) :
    value (readRows (project N Finset.univ) rows b)
        (fun i => wordVariables N r (originalGamma p) dur (variableBank i)) =
      (((initializedWordLaw N sample parentRegistry p common r dur word).map
        (projection N Finset.univ)) b).toReal := by
  have h := checked_staged_same_source_natural_word N sample parentRegistry common
    encodeVariable variableBank original_variable_native_bank_left_inverse
    {initial_namespace}.certificate {cache_namespace}.cache stages
    complete_word_coefficient_fibres_checked b r p dur
  simpa only [stages_retain_every_original_operation,
    final_rows_are_the_complete_original_native_output] using h
#check actual_same_source_natural_word
end {namespace}
"#,header=header(&[cache_module,previous_module],bindings.namespace,&context_namespace),
 stage_names=stage_names.join(",\n   "),edges=request.context.source.edges.len(),namespace=bindings.namespace);
 append(&mut bundle,final_module,source,limits)?;
 Ok(bundle)
}
pub fn example(mode:&str)->Result<Bundle,Error>{
 let (common,namespace)=match mode{
  "independent"=>(false,"ResearchCommons.Generated.NaturalIndependentWord"),
  "common"=>(true,"ResearchCommons.Generated.NaturalCommonWord"),
  _=>return Err(Error::Invalid("word mode")),
 };
 let request=direct::example_request(common).map_err(Error::Direct)?;
 let mut bundle=emit(&request,retained::Bindings{original_module:"OriginalParallelBank",
  original_source:"ResearchCommons.Generated.OriginalParallelBank.originalSource",namespace},
  Limits::default(),retained::Limits::default())?;
 let last=bundle.modules.last_mut().ok_or(Error::Invalid("missing final module"))?;
 let joined=direct::join_example(&last.source,namespace).map_err(Error::Direct)?;
 bundle.total_bytes=bundle.total_bytes.checked_sub(last.source.len()).ok_or(Error::Overflow)?;
 bundle.total_bytes=add(bundle.total_bytes,joined.len())?;last.source=joined;
 bound("final_source_bytes",last.source.len(),Limits::default().source_bytes)?;
 bound("total_source_bytes",bundle.total_bytes,Limits::default().total_bytes)?;
 Ok(bundle)
}
#[cfg(test)] mod tests{
 use super::*;
 use std::collections::BTreeSet;
 #[test]fn same_three_copy_words_keep_full_bank_rows_and_every_checked_primitive(){
  for mode in ["independent","common"] {
   let b=example(mode).unwrap_or_else(|e|panic!("{mode}: {e:?}"));
   assert!(b.primitive_entries>0);assert_eq!(b.source_word_length,7);
   let names=b.modules.iter().map(|m|m.name.as_str()).collect::<BTreeSet<_>>();
   assert_eq!(names.len(),b.modules.len());
   assert!(b.modules.iter().all(|m|m.source.len()<=262144));
   let last=b.modules.last().unwrap();
   assert!(last.source.contains("same_returned_bank_natural_word"));
   assert!(last.source.contains("checkStages"));
   assert_eq!(b.modules.iter().filter(|m|m.source.contains("#check coefficient_fibres_checked")).count(),7);
   assert!(last.source.contains("stages_retain_every_original_operation"));
   assert!(last.source.contains("final_rows_are_the_complete_original_native_output"));
   assert!(b.modules.iter().any(|m|m.source.contains("checkInitial")));
   assert_eq!(b.modules.iter().filter(|m|m.source.contains("checkStep N sample")).count(),b.primitive_entries);
   assert!(!b.modules.iter().any(|m|m.source.contains("native_decide")||m.source.contains("sorry")));
   assert!(b.modules.iter().filter(|m|m.source.contains("checkStep N sample"))
      .all(|m|m.source.contains("interval :=")));
   assert!(b.modules.iter().any(|m|m.source.contains(".colocated")&&m.source.contains("unfold CoLocated")));
   let j:serde_json::Value=serde_json::from_str(&b.json().unwrap()).unwrap();
   assert_eq!(j["modules"].as_array().unwrap().len(),b.modules.len());
   assert_eq!(j["kernel_checked"],false);
  }
 }
 #[test]fn outer_cache_limits_return_no_partial_bundle_and_keep_unknown(){
  let request=direct::example_request(false).unwrap();
  let binding=retained::Bindings{original_module:"OriginalParallelBank",
   original_source:"ResearchCommons.Generated.OriginalParallelBank.originalSource",namespace:"Candidate"};
  assert!(matches!(emit(&request,binding,Limits{entries:0,..Limits::default()},retained::Limits::default()),
   Err(Error::Limit{kind:"primitive_entries",..})));
  let mut limited=request.clone();limited.limits.queries=0;
  assert!(matches!(emit(&limited,binding,Limits::default(),retained::Limits::default()),
   Err(Error::Direct(direct::Error::Unknown(_)))));
 }
 #[test]fn a_foreign_slot_or_natural_gamma_cannot_hide_in_a_scalar_population_certificate(){
  use parity_solver::forest::Tree;
  let mut request=direct::example_request(false).unwrap();
  let input=Snapshot::from_lineages(&request.context,
    &[(0,Tree::Leaf(0)),(1,Tree::Leaf(1)),(2,Tree::Leaf(2))],
    Location::Edge(8),vec![false;request.context.source.vertices]).unwrap();
  request.initial=Initial::Conditional(input.clone());
  request.word=vec![Symbol::Interval(0)];
  let table=query(&request,Some(0)).unwrap();
  let view=parity_solver::source_epoch::selected_view(&request.context,&input).unwrap();
  let mut entry=Entry{operation:Symbol::Interval(0),input,view,table};
  assert!(interval_form(&request,&entry).unwrap().starts_with(".colocated"));
  for foreign in [
   entry.table.variables.iter().position(|v|matches!(v,Variable::OriginalGamma(_))).unwrap(),
   entry.table.variables.iter().position(|v|matches!(v,Variable::Survival{slot:1,..})).unwrap(),
  ] {
   let old=entry.table.transitions[0].polynomial.clone();
   let (powers,coefficient)=old.terms.iter().next().map(|(p,q)|(p.clone(),q.clone())).unwrap();
   entry.table.transitions[0].polynomial.terms.remove(&powers);
   let mut tampered=powers;tampered[foreign]+=1;
   entry.table.transitions[0].polynomial.terms.insert(tampered,coefficient);
   assert!(matches!(interval_form(&request,&entry),
     Err(Error::Invalid("foreign coordinate in colocated scalar row"))));
   entry.table.transitions[0].polynomial=old;
  }
 }

}
