//! Package assembly and claim integration, not a scientific status authority.
#![forbid(unsafe_code)]
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

pub mod object_cache;

pub type Result<T> = std::result::Result<T, String>;
pub fn sha256(bytes: &[u8]) -> String { format!("{:x}", Sha256::digest(bytes)) }
pub fn read_json(path: &Path) -> Result<Value> {
    let bytes=fs::read(path).map_err(|e|format!("{}: {e}",path.display()))?;
    serde_json::from_slice(&bytes).map_err(|e|format!("{}: {e}",path.display()))
}
fn text<'a>(v: &'a Value, key: &str) -> Result<&'a str> {
    v.get(key).and_then(Value::as_str).ok_or_else(||format!("missing string: {key}"))
}
fn array<'a>(v: &'a Value, key: &str) -> Result<&'a Vec<Value>> {
    v.get(key).and_then(Value::as_array).ok_or_else(||format!("missing array: {key}"))
}
/// Upstream modules supplied by the pinned Lean toolchain or Mathlib cache.
/// This recognizes whole namespace components, never similarly prefixed project
/// names; source/owned imports still require the exact staged dependency.
fn compiler_supplied_import(name: &str) -> bool {
    matches!(name, "Mathlib" | "Std" | "Init" | "Lean")
        || ["Mathlib.", "Std.", "Init.", "Lean."].iter().any(|root|name.starts_with(*root))
}

pub fn module_path(name: &str) -> Result<PathBuf> {
    if name.is_empty() { return Err("empty Lean module".into()); }
    let mut p=PathBuf::new();
    for part in name.split('.') {
        if part.is_empty() || !part.chars().all(|c|c.is_ascii_alphanumeric()||c=='_')
            || part.chars().next().is_some_and(|c|c.is_ascii_digit()) {
            return Err(format!("unsafe Lean module: {name}"));
        }
        p.push(part);
    }
    p.set_extension("lean"); Ok(p)
}
/// All current claims survive a partial old ranking. Only actual theorem/adapter
/// dependencies constrain order; a candidate connection is not an implication.
pub fn ordered_claims(claims: &Value, ranking: &Value) -> Result<Vec<String>> {
    let cards=array(claims,"claims")?;
    let mut by_id=BTreeMap::new();
    for card in cards {
        let id=text(card,"id")?.to_owned();
        if by_id.insert(id.clone(),card).is_some(){return Err(format!("duplicate claim {id}"));}
    }
    let mut ranks=BTreeMap::new();
    for entry in array(ranking,"entries")? {
        let id=text(entry,"claim_id")?.to_owned();
        if !by_id.contains_key(&id){return Err(format!("rank references absent claim {id}"));}
        let rank=entry.get("rank").and_then(Value::as_u64).ok_or("invalid rank")?;
        if ranks.insert(id.clone(),rank).is_some(){return Err(format!("duplicate ranked claim {id}"));}
    }
    let mut pending:BTreeMap<String,BTreeSet<String>>=BTreeMap::new();
    for (id,card) in &by_id {
        let mut deps=BTreeSet::new();
        for dep in array(card,"dependencies")? {
            let other=text(dep,"claim_id")?;
            if !by_id.contains_key(other){return Err(format!("unresolved dependency {id} -> {other}"));}
            if matches!(text(dep,"relation_type")?,"proved_adapter"|"reused_theorem") {
                deps.insert(other.to_owned());
            }
        }
        pending.insert(id.clone(),deps);
    }
    let mut done=BTreeSet::new();let mut out=Vec::new();
    while !pending.is_empty() {
        let choice=pending.iter().filter(|(_,deps)|deps.is_subset(&done))
            .map(|(id,_)|id.clone())
            .min_by_key(|id|(ranks.get(id).copied().unwrap_or(u64::MAX),id.clone()));
        let Some(id)=choice else{return Err("cycle in actual theorem/adapter dependencies".into())};
        pending.remove(&id);done.insert(id.clone());out.push(id);
    }
    Ok(out)
}
pub fn coverage(claims: &Value, ranking: &Value, bindings: &Value) -> Result<Value> {
    let order=ordered_claims(claims,ranking)?;
    let ranked:BTreeSet<&str>=array(ranking,"entries")?.iter().map(|v|text(v,"claim_id")).collect::<Result<_>>()?;
    let mut maps=BTreeMap::new();
    for b in array(bindings,"claims")? {
        let id=text(b,"claim_id")?;
        if maps.insert(id,b).is_some(){return Err(format!("duplicate integration {id}"));}
    }
    let ids:BTreeSet<&str>=order.iter().map(String::as_str).collect();
    if maps.keys().copied().collect::<BTreeSet<_>>()!=ids {
        return Err("integration keys differ from pinned canonical registry".into());
    }
    let mut rows=Vec::new();let mut incomplete=Vec::new();
    for id in order {
        let b=maps[id.as_str()];
        let card=array(claims,"claims")?.iter().find(|c|c["id"]==id).ok_or("missing canonical card")?;
        // Integration is typed by the canonical claim, not by a convenient
        // binding label. Open questions need exact checked statements; measured
        // results need evidence interfaces, never invented mathematical proofs.
        let kind=if card["claim_kind"]=="question" || card["mathematical_status"]=="open" ||
            card["mathematical_status"]=="formal_integration_obligation" {"open_obligation"}
            else if card["claim_kind"]=="software_check" {"scoped_evidence"}
            else {"proof_or_algorithm"};
        let (lean_state,rust_state)=match kind {
            "open_obligation"=>("verified_open_statement","verified_obligation_binding"),
            "scoped_evidence"=>("verified_evidence_interface","verified_evidence_reader"),
            _=>("verified_binding","verified_binding"),
        };
        let ready=b["lean"]["state"]==lean_state && b["rust"]["state"]==rust_state &&
            b["lean"]["module"].as_str().is_some_and(|s|!s.is_empty()) &&
            b["lean"]["declarations"].as_array().is_some_and(|s|!s.is_empty()) &&
            b["rust"]["module"].as_str().is_some_and(|s|!s.is_empty()) &&
            b["verification"].as_array().is_some_and(|r|!r.is_empty());
        if !ready { incomplete.push(id.clone()); }
        rows.push(json!({"claim_id":id,"integration_kind":kind,"reuse_rank":b["reuse_rank"],
            "lean":b["lean"],"rust":b["rust"],"integration_complete":ready}));
    }
    Ok(json!({"canonical_claims":rows.len(),"ranked":ranked.len(),
        "unranked":rows.iter().filter(|r|r["reuse_rank"].is_null()).count(),
        "all_claims_accounted_for":true,"full_package_complete":incomplete.is_empty(),
        "incomplete_claims":incomplete,"ordered_integration":rows,
        "scope":"Coverage and integration evidence; not new proof/novelty/empirical acceptance."}))
}
pub fn check_package(root: &Path) -> Result<Value> {
    let lock=read_json(&root.join("source-lock.json"))?;
    for entry in array(&lock,"files")? {
        let rel=text(entry,"path")?;
        let p=Path::new(rel);
        if p.is_absolute() || p.components().any(|x|!matches!(x,std::path::Component::Normal(_))) {
            return Err(format!("unsafe pinned path {rel}"));
        }
        let b=fs::read(root.join(p)).map_err(|e|format!("pin {rel}: {e}"))?;
        if let Some(expected)=entry.get("sha256").and_then(Value::as_str) {
            if sha256(&b)!=expected { return Err(format!("source changed: {rel}")); }
        }
    }
    coverage(&read_json(&root.join("registry/claims.json"))?,
        &read_json(&root.join("registry/reuse-ranking.json"))?,
        &read_json(&root.join("integration/claims.json"))?)
}
/// Fresh source assembly for a portable host. It invokes no historical
/// controller, imports no old objects, and grants no historical acceptance.
pub fn prepare_lean(root: &Path) -> Result<Value> {
    let lock=read_json(&root.join("source-lock.json"))?;
    let profile=&lock["lean_profile"];
    let base=root.join(text(profile,"directory")?);
    let graph_bytes=fs::read(base.join("DEPENDENCY-GRAPH.json")).map_err(|e|e.to_string())?;
    if sha256(&graph_bytes)!=text(profile,"graph_sha256")?{return Err("graph hash mismatch".into());}
    let graph:Value=serde_json::from_slice(&graph_bytes).map_err(|e|e.to_string())?;
    let targets=graph["targets"].as_object().ok_or("missing targets")?;
    let (label,target)=targets.iter().max_by_key(|(_,t)|t["modules"].as_object().map_or(0,|m|m.len()))
        .ok_or("empty target graph")?;
    let modules=target["modules"].as_object().ok_or("missing modules")?;
    if modules.len() as u64 != profile["module_count"].as_u64().ok_or("missing module count")? {
        return Err("selected source count differs from locked profile".into());
    }
    let order=array(target,"order")?;let mut seen=BTreeSet::new();
    let output=root.join("lean/.generated");
    // Validate the entire plan before writing any generated source.
    let mut sources=Vec::new();
    let mut module_imports=BTreeMap::new();
    let mut module_hashes=BTreeMap::new();
    for item in order {
        let name=item.as_str().ok_or("non-string module")?;
        if seen.contains(name){return Err(format!("duplicate module {name}"));}
        let data=modules.get(name).ok_or_else(||format!("no source for {name}"))?;
        for dep in array(data,"imports")? {
            let dep=dep.as_str().ok_or("non-string import")?;
            if modules.contains_key(dep)&&!seen.contains(dep){return Err(format!("non-topological edge {name} -> {dep}"));}
        }
        let hash=text(data,"sha256")?;
        if hash.len()!=64 || !hash.chars().all(|c|c.is_ascii_hexdigit()){return Err("invalid source hash".into());}
        let source=fs::read(base.join("source-store").join(format!("{hash}.lean")))
            .map_err(|e|format!("source {name}: {e}"))?;
        if sha256(&source)!=hash{return Err(format!("body hash mismatch: {name}"));}
        module_imports.insert(name.to_owned(),data["imports"].clone());
        module_hashes.insert(name.to_owned(),hash.to_owned());
        seen.insert(name.to_owned());
        sources.push((name.to_owned(),module_path(name)?,source));
    }
    if seen.len()!=modules.len(){return Err("order does not cover every module".into());}
    let retained_count=sources.len();
    let extra=read_json(&root.join("integration/lean-modules.json"))?;
    for entry in array(&extra,"modules")? {
        let name=text(entry,"module")?;
        if seen.contains(name){return Err(format!("duplicate added module {name}"));}
        let rel=text(entry,"path")?;
        let path=Path::new(rel);
        if path.is_absolute() || path.components().any(|x|!matches!(x,std::path::Component::Normal(_))) {
            return Err(format!("unsafe added source path {rel}"));
        }
        let bytes=fs::read(root.join(path)).map_err(|e|format!("added source {name}: {e}"))?;
        if sha256(&bytes)!=text(entry,"sha256")? { return Err(format!("added body hash mismatch: {name}")); }
        for dep in array(entry,"imports")? {
            let dep=dep.as_str().ok_or("non-string added import")?;
            module_path(dep)?;
            if !compiler_supplied_import(dep) && !seen.contains(dep) {
                return Err(format!("added dependency not yet built: {name} -> {dep}"));
            }
        }
        let actual=std::str::from_utf8(&bytes).map_err(|e|e.to_string())?.lines()
            .filter_map(|line|line.strip_prefix("import ")).map(str::trim).collect::<Vec<_>>();
        let declared=array(entry,"imports")?.iter().map(|v|v.as_str().ok_or("non-string import")).collect::<std::result::Result<Vec<_>,_>>()?;
        if actual!=declared {return Err(format!("added import manifest mismatch: {name}"));}
        module_imports.insert(name.to_owned(),entry["imports"].clone());
        module_hashes.insert(name.to_owned(),sha256(&bytes));
        seen.insert(name.to_owned());
        sources.push((name.to_owned(),module_path(name)?,bytes));
    }
    let mut imports=String::new();
    for r in array(target,"roots")? {
        let name=r.as_str().ok_or("non-string root")?;module_path(name)?;
        if !seen.contains(name){return Err(format!("root absent: {name}"));}
        imports.push_str(&format!("import {name}\n"));
    }
    // Retained audit modules write their public JSON receipt relative to the
    // compiler workspace. Reproduce that original directory without editing proofs.
    fs::create_dir_all(root.join("evidence")).map_err(|e|e.to_string())?;
    fs::create_dir_all(&output).map_err(|e|e.to_string())?;
    for (_,path,body) in &sources {
        let p=output.join(path);fs::create_dir_all(p.parent().ok_or("no parent")?).map_err(|e|e.to_string())?;
        fs::write(p,body).map_err(|e|e.to_string())?;
    }
    for (name,_,_) in sources.iter().skip(retained_count) {
        imports.push_str(&format!("import {name}\n"));
    }
    imports.push_str("import ResearchCommons.Registry\n");
    fs::write(output.join("ResearchCommons.lean"),imports).map_err(|e|e.to_string())?;
    let registry=root.join("lean/ResearchCommons/Registry.lean");
    fs::create_dir_all(output.join("ResearchCommons")).map_err(|e|e.to_string())?;
    fs::copy(registry,output.join("ResearchCommons/Registry.lean")).map_err(|e|e.to_string())?;
    let mut owned:Vec<String>=sources.iter().map(|(n,_,_)|n.clone()).collect();
    owned.push("ResearchCommons.Registry".into());
    owned.push("ResearchCommons".into());
    let template=fs::read_to_string(base.join("scripts/AuditTemplate.lean")).map_err(|e|e.to_string())?;
    let placeholder=r##"#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]"##;
    if template.matches(placeholder).count()!=1{return Err("unexpected retained axiom-audit template".into());}
    let names=serde_json::to_string(&owned).map_err(|e|e.to_string())?;
    let audit=template.replace(placeholder,&format!("#{names}"))
        .replace("\"AUDIT-OWNED.json\"","\"../build/owned-audit.json\"");
    fs::write(output.join("OwnedAudit.lean"),format!("import ResearchCommons\n{audit}")).map_err(|e|e.to_string())?;
    let plan=json!({"profile":label,"fresh_sources":sources.len(),"retained_sources":retained_count,"added_sources":sources.len()-retained_count,
        "order":sources.iter().map(|(n,_,_)|n).collect::<Vec<_>>(),
        "compiler_invoked":false,"historical_objects_reused":false,
        "source_graph_sha256":sha256(&graph_bytes),
        "module_imports":module_imports,"module_hashes":module_hashes});
    fs::write(root.join("lean/.generated/build-plan.json"),serde_json::to_vec_pretty(&plan).map_err(|e|e.to_string())?)
        .map_err(|e|e.to_string())?;
    Ok(plan)
}

/// Exact transitive owned-source closure in the retained topological order.
/// Upstream imports remain supplied by the same pinned Mathlib. This never
/// turns a target build into completion of the entire selected profile.
pub fn selected_modules(plan:&Value,target:&str)->Result<Vec<String>> {
    module_path(target)?;
    let order=array(plan,"order")?.iter().map(|n|n.as_str().map(str::to_owned).ok_or("non-string planned module".to_owned()))
        .collect::<Result<Vec<_>>>()?;
    let all=order.iter().cloned().collect::<BTreeSet<_>>();
    if all.len()!=order.len(){return Err("duplicate planned module".into());}
    if !all.contains(target){return Err(format!("target absent from exact profile: {target}"));}
    let imports=plan["module_imports"].as_object().ok_or("missing module imports")?;
    let mut selected=BTreeSet::new();let mut todo=vec![target.to_owned()];
    while let Some(name)=todo.pop() {
        if !selected.insert(name.clone()){continue;}
        let deps=imports.get(&name).and_then(Value::as_array).ok_or_else(||format!("missing imports: {name}"))?;
        for dep in deps {
            let dep=dep.as_str().ok_or("non-string dependency")?;
            module_path(dep)?;
            if all.contains(dep){todo.push(dep.to_owned());}
        }
    }
    let mut built=BTreeSet::new();let mut result=Vec::new();
    for name in order.into_iter().filter(|n|selected.contains(n)) {
        for dep in imports[&name].as_array().ok_or("invalid imports")? {
            let dep=dep.as_str().ok_or("non-string dependency")?;
            if selected.contains(dep)&&!built.contains(dep) {
                return Err(format!("non-topological selected dependency: {name} -> {dep}"));
            }
        }
        built.insert(name.clone());result.push(name);
    }
    Ok(result)
}

/// Small isolated proof context for actual new Rust caller verification.
/// Its original abstract CM supplier shares declarations with the physical
/// supplier; separate source/object directories prevent accidental co-import.
pub fn prepare_certificate_profile(root:&Path)->Result<Value> {
    let profile=read_json(&root.join("integration/certificate-profile.json"))?;
    let destination=root.join("certificates/.generated");
    let mut seen=BTreeSet::new();
    let mut sources=Vec::new();
    for m in array(&profile,"modules")? {
        let name=text(m,"module")?;
        if seen.contains(name){return Err(format!("duplicate certificate module {name}"));}
        let path=Path::new(text(m,"path")?);
        if path.is_absolute() || path.components().any(|x|!matches!(x,std::path::Component::Normal(_))) {
            return Err("unsafe certificate source path".into());
        }
        let bytes=fs::read(root.join(path)).map_err(|e|e.to_string())?;
        if sha256(&bytes)!=text(m,"sha256")? {return Err(format!("certificate source mismatch: {name}"));}
        let declared=array(m,"imports")?.iter().map(|x|x.as_str().ok_or("invalid certificate import"))
            .collect::<std::result::Result<Vec<_>,_>>()?;
        let actual=std::str::from_utf8(&bytes).map_err(|e|e.to_string())?.lines()
            .filter_map(|l|l.strip_prefix("import ")).map(str::trim).collect::<Vec<_>>();
        if actual!=declared {return Err(format!("certificate import mismatch: {name}"));}
        for dep in declared {
            module_path(dep)?;
            if !compiler_supplied_import(dep) && !seen.contains(dep) {
                return Err(format!("certificate dependency not yet staged: {name} -> {dep}"));
            }
        }
        seen.insert(name.to_owned());
        sources.push((name.to_owned(),module_path(name)?,bytes));
    }
    let mut aggregate=String::new();
    for (name,path,bytes) in &sources {
        let output=destination.join(path);
        fs::create_dir_all(output.parent().ok_or("no certificate parent")?).map_err(|e|e.to_string())?;
        fs::write(output,bytes).map_err(|e|e.to_string())?;
        aggregate.push_str(&format!("import {name}\n"));
    }
    fs::write(destination.join("ResearchCommons.lean"),aggregate).map_err(|e|e.to_string())?;
    let plan=json!({"profile":profile["profile"],"project":"certificates",
        "order":sources.iter().map(|(n,_,_)|n).collect::<Vec<_>>(),
        "compiler_invoked":false,"full_registry_profile":false});
    fs::write(destination.join("build-plan.json"),serde_json::to_vec_pretty(&plan).map_err(|e|e.to_string())?)
        .map_err(|e|e.to_string())?;
    Ok(plan)
}

#[cfg(test)]
mod tests {
 use super::*;

 #[test] fn selected_build_retains_transitive_dependencies_and_ignores_unrelated_roots(){
  let p=json!({"order":["Base","Unrelated","Middle","Target"],"module_imports":{
    "Base":["Mathlib.Data.Real.Basic"],"Unrelated":[],"Middle":["Base"],"Target":["Middle","Base"]}});
  assert_eq!(selected_modules(&p,"Target").unwrap(),vec!["Base","Middle","Target"]);
  assert!(selected_modules(&p,"Missing").is_err());
 }
 #[test] fn selected_build_refuses_a_broken_dependency_order(){
  let p=json!({"order":["Target","Base"],"module_imports":{"Target":["Base"],"Base":[]}});
  assert!(selected_modules(&p,"Target").is_err());
 }
 fn card(id:&str,deps:Value)->Value{json!({"id":id,"dependencies":deps})}
 #[test] fn missing_rank_does_not_drop_a_claim(){
  let c=json!({"claims":[card("A",json!([])),card("B",json!([]))]});
  let r=json!({"entries":[{"claim_id":"A","rank":1}]});
  assert_eq!(ordered_claims(&c,&r).unwrap(),vec!["A","B"]);
 }
 #[test] fn proved_dependency_precedes_higher_rank(){
  let c=json!({"claims":[card("A",json!([{"claim_id":"B","relation_type":"proved_adapter"}])),card("B",json!([]))]});
  let r=json!({"entries":[{"claim_id":"A","rank":1},{"claim_id":"B","rank":9}]});
  assert_eq!(ordered_claims(&c,&r).unwrap(),vec!["B","A"]);
 }
 #[test] fn candidate_connection_is_not_a_theorem_edge(){
  let c=json!({"claims":[card("A",json!([{"claim_id":"B","relation_type":"candidate_connection"}])),card("B",json!([{"claim_id":"A","relation_type":"candidate_connection"}]))]});
  assert!(ordered_claims(&c,&json!({"entries":[]})).is_ok());
 }
 #[test] fn actual_dependency_cycle_is_refused(){
  let c=json!({"claims":[card("A",json!([{"claim_id":"B","relation_type":"reused_theorem"}])),card("B",json!([{"claim_id":"A","relation_type":"reused_theorem"}]))]});
  assert!(ordered_claims(&c,&json!({"entries":[]})).is_err());
 }
 #[test] fn unsafe_module_paths_are_refused(){
  for n in ["","../Leak","A..B","A/B","A\\B","1Bad","A.\nB"]{assert!(module_path(n).is_err(),"{n:?}");}
  assert_eq!(module_path("UnifiedLean.Source.SourceNetwork").unwrap(),PathBuf::from("UnifiedLean/Source/SourceNetwork.lean"));
 }
 #[test] fn metadata_does_not_count_as_full_integration(){
  let c=json!({"claims":[card("A",json!([]))]});
  let b=json!({"claims":[{"claim_id":"A","reuse_rank":null,"lean":{"state":"pending_binding"},"rust":{"state":"pending_binding"},"verification":[]}]});
  assert_eq!(coverage(&c,&json!({"entries":[]}),&b).unwrap()["full_package_complete"],false);
 }
 #[test] fn dropped_integration_claim_is_refused(){
  let c=json!({"claims":[card("A",json!([]))]});
  assert!(coverage(&c,&json!({"entries":[]}),&json!({"claims":[]})).is_err());
 }
 #[test] fn exact_open_statement_is_integrated_without_a_fabricated_proof(){
  let c=json!({"claims":[{"id":"A","dependencies":[],"claim_kind":"question","mathematical_status":"open"}]});
  let binding=|ls:&str,rs:&str|json!({"claims":[{"claim_id":"A","reuse_rank":null,
    "lean":{"state":ls,"module":"OpenQuestion","declarations":["OpenQuestion.statement"]},
    "rust":{"state":rs,"module":"obligations::A"},"verification":[{"kind":"checked_exact_statement"}]}]});
  let r=coverage(&c,&json!({"entries":[]}),&binding("verified_open_statement","verified_obligation_binding")).unwrap();
  assert_eq!(r["full_package_complete"],true);
  assert_eq!(r["ordered_integration"][0]["integration_kind"],"open_obligation");
  assert_eq!(coverage(&c,&json!({"entries":[]}),&binding("verified_binding","verified_binding")).unwrap()["full_package_complete"],false);
 }
 #[test] fn empirical_evidence_is_not_accepted_as_a_proved_theorem(){
  let c=json!({"claims":[{"id":"A","dependencies":[],"claim_kind":"software_check"}]});
  let b=json!({"claims":[{"claim_id":"A","reuse_rank":null,
    "lean":{"state":"verified_binding","module":"Evidence","declarations":["Evidence.record"]},
    "rust":{"state":"verified_binding","module":"reader"},"verification":[{}]}]});
  assert_eq!(coverage(&c,&json!({"entries":[]}),&b).unwrap()["full_package_complete"],false);
 }
 #[test] fn verification_labels_without_declarations_do_not_close_integration(){
  let c=json!({"claims":[card("A",json!([]))]});
  let b=json!({"claims":[{"claim_id":"A","reuse_rank":null,
    "lean":{"state":"verified_binding","module":"A","declarations":[]},
    "rust":{"state":"verified_binding","module":"A"},"verification":[{}]}]});
  assert_eq!(coverage(&c,&json!({"entries":[]}),&b).unwrap()["full_package_complete"],false);
 }

}

pub mod exports;

pub mod certificate_bundle;

/// Direct unavailable imports in the ORIGINAL validated topological plan.
/// External imports remain governed by source preparation, not this scheduler.
pub fn failed_imports(plan:&Value,module:&str,unavailable:&std::collections::BTreeSet<String>)->Result<Vec<String>> {
 let imports=plan["module_imports"][module].as_array().ok_or("missing module imports")?;
 imports.iter().map(|v|v.as_str().ok_or("non-string module import".to_owned()))
   .filter_map(|v|match v {Ok(name) if unavailable.contains(name)=>Some(Ok(name.to_owned())),
     Ok(_)=>None,Err(error)=>Some(Err(error))}).collect()
}

#[cfg(test)]mod failed_import_tests {
 use super::*;
 #[test]fn failure_propagates_to_consumers_but_not_independent_modules(){
  let plan=json!({"module_imports":{"A":["Mathlib.Data.Real.Basic"],"B":["A"],"C":[],"Target":["B","C"]}});
  let mut unavailable=std::collections::BTreeSet::from(["A".to_owned()]);
  assert_eq!(failed_imports(&plan,"B",&unavailable).unwrap(),vec!["A"]);
  assert!(failed_imports(&plan,"C",&unavailable).unwrap().is_empty());
  unavailable.insert("B".to_owned());
  assert_eq!(failed_imports(&plan,"Target",&unavailable).unwrap(),vec!["B"]);
  assert!(failed_imports(&plan,"A",&unavailable).unwrap().is_empty());
 }
 #[test]fn malformed_import_metadata_is_fatal_not_independent_success(){
  let unavailable=std::collections::BTreeSet::new();
  assert!(failed_imports(&json!({"module_imports":{}}),"A",&unavailable).is_err());
  assert!(failed_imports(&json!({"module_imports":{"A":[17]}}),"A",&unavailable).is_err());
 }
}
