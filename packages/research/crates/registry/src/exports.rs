//! Exact public registry -> declaration-check plan. This reuses Lean as the
//! proof checker; it creates no native substitute for a scientific algorithm.
use serde_json::{json,Value};
use std::collections::{BTreeMap,BTreeSet};

type Result<T> = std::result::Result<T,String>;
fn name(value:&str)->Result<()> {
 crate::module_path(value)?;
 Ok(())
}
/// Every listed declaration is checked, including scoped/candidate exports.
/// The reported integration level is retained verbatim, never upgraded merely
/// because a name exists. IDs and mathematical completion remain canonical.
pub fn plan(canonical:&Value,bindings:&Value)->Result<Value>{
 let cards=canonical["claims"].as_array().ok_or("missing canonical claims")?;
 let rows=bindings["claims"].as_array().ok_or("missing integration rows")?;
 let canonical_ids=cards.iter().map(|c|c["id"].as_str().ok_or("invalid canonical ID".to_owned())).collect::<Result<BTreeSet<_>>>()?;
 if canonical_ids.len()!=cards.len(){return Err("duplicate canonical claim ID".into());}
 let mut ids=BTreeSet::new();let mut imports=BTreeSet::new();let mut claims=Vec::new();
 let mut unbound=Vec::new();
 for row in rows {
  let id=row["claim_id"].as_str().ok_or("missing claim ID")?;
  if !ids.insert(id){return Err(format!("duplicate export ID {id}"));}
  let card=cards.iter().find(|c|c["id"]==id).ok_or_else(||format!("unknown export ID {id}"))?;
  let module=match row["lean"]["module"].as_str(){
   Some(m) if !m.is_empty()=>m,
   _=>{unbound.push(id);continue;}
  };
  let declarations=match row["lean"]["declarations"].as_array(){
   Some(ds) if !ds.is_empty()=>ds,
   _=>{unbound.push(id);continue;}
  };
  name(module)?;imports.insert(module.to_owned());
  let overrides=match &row["lean"]["declaration_modules"]{
   Value::Null=>None,
   Value::Object(m)=>Some(m),
   _=>return Err("declaration_modules must be an object".into()),
  };
  let mut local=BTreeSet::new();let mut ds=Vec::new();let mut owners=BTreeMap::new();
  for declaration in declarations {
   let d=declaration.as_str().ok_or("non-string export declaration")?;
   name(d)?;
   if !local.insert(d){return Err(format!("duplicate declaration {d}"));}
   let owner=match overrides.and_then(|m|m.get(d)){
    None=>module,
    Some(value)=>value.as_str().filter(|s|!s.is_empty()).ok_or("invalid declaration owner")?,
   };
   name(owner)?;imports.insert(owner.to_owned());owners.insert(d.to_owned(),owner.to_owned());
   ds.push(d.to_owned());
  }
  if let Some(overrides)=overrides{
   for key in overrides.keys(){
    if !local.contains(key.as_str()){return Err(format!("owner for unlisted declaration {key}"));}
   }
  }
  claims.push(json!({"claim_id":id,"module":module,"declarations":ds,"declaration_modules":owners,
   "integration_state":row["lean"]["state"],"scope":row["lean"]["scope"],
   "canonical_completion":card["completion"]}));
 }
 if ids!=canonical_ids{
  return Err("export integration does not cover canonical IDs".into());
 }
 let mut document=String::from("-- Public declaration interface, not a new proof or algorithm.\nimport Lean.Util.CollectAxioms\n");
 for module in &imports{document.push_str(&format!("import {module}\n"));}
 document.push_str("\nopen Lean Elab Command\nnamespace ResearchCommons.Generated.ClaimExports\n");
 for claim in &claims {
  for declaration in claim["declarations"].as_array().ok_or("invalid planned declarations")?{
   let d=declaration.as_str().ok_or("invalid planned declaration")?;
   document.push_str(&format!("#check @{d}\n"));
  }
 }
 document.push_str("run_cmd do\n  let environment ← getEnv\n  let requested : Array (String × Name × String) := #[\n");
 let mut records=Vec::new();
 for claim in &claims{
  for declaration in claim["declarations"].as_array().ok_or("invalid ownership declarations")?{
   let id=serde_json::to_string(claim["claim_id"].as_str().ok_or("invalid ownership ID")?).map_err(|e|e.to_string())?;
   let d=declaration.as_str().ok_or("invalid ownership declaration")?;
   let owner=serde_json::to_string(claim["declaration_modules"][d].as_str()
    .ok_or("invalid ownership module")?).map_err(|e|e.to_string())?;
   records.push(format!("    ({id}, ``{d}, {owner})"));
  }
 }
 document.push_str(&records.join(",\n"));
 document.push_str("\n  ]\n");
 document.push_str("  for (id, declaration, expected) in requested do\n");
 document.push_str("    let some index := environment.getModuleIdxFor? declaration | throwError m!\"Missing owner for {id}: {declaration}\"\n");
 document.push_str("    let actual := environment.header.moduleNames[index.toNat]!.toString\n");
 document.push_str("    unless actual == expected do\n");
 document.push_str("      throwError m!\"Wrong export owner for {id}: {declaration}, expected {expected}, actual {actual}\"\n");
 document.push_str("  logInfo m!\"Verified {requested.size} exact claim export owners\"\n");
 document.push_str("end ResearchCommons.Generated.ClaimExports\n");
 if document.len()>262144{return Err("claim export document limit".into());}
 Ok(json!({"schema":1,"claims":claims,"unbound_claims":unbound,
  "imports":imports,"document":document,
  "scope":"Exact declaration names/types in the actual current Lean package. Integration states and scientific scopes are retained; this is not a native physical provider, solver or upgraded scientific theorem."}))
}

/// Select exact canonical claims using the SAME complete planner and renderer.
/// Full input validation occurs before selection; unknown, duplicate and
/// currently unbound IDs refuse rather than producing a vacuous check.
pub fn plan_for_claims(canonical:&Value,bindings:&Value,requested:&[String])->Result<Value>{
 let full=plan(canonical,bindings)?;
 if requested.is_empty(){return Ok(full);}
 let cards=canonical["claims"].as_array().ok_or("missing canonical claims")?;
 let rows=bindings["claims"].as_array().ok_or("missing integration rows")?;
 let mut selected=BTreeSet::new();
 for id in requested {
  if !selected.insert(id.as_str()){return Err(format!("duplicate requested claim {id}"));}
  if !cards.iter().any(|c|c["id"].as_str()==Some(id.as_str())){
   return Err(format!("unknown requested claim {id}"));
  }
  if !full["claims"].as_array().ok_or("missing full export plan")?.iter()
   .any(|c|c["claim_id"].as_str()==Some(id.as_str())){
   return Err(format!("requested claim has no named binding: {id}"));
  }
 }
 let scoped_canonical=json!({"claims":cards.iter().filter(|c|c["id"].as_str()
  .is_some_and(|id|selected.contains(id))).cloned().collect::<Vec<_>>()});
 let scoped_bindings=json!({"claims":rows.iter().filter(|c|c["claim_id"].as_str()
  .is_some_and(|id|selected.contains(id))).cloned().collect::<Vec<_>>()});
 let mut result=plan(&scoped_canonical,&scoped_bindings)?;
 result["requested_claims"]=json!(selected.into_iter().collect::<Vec<_>>());
 result["canonical_claim_count"]=json!(cards.len());
 result["full_registry_selection"]=json!(false);
 result["scope"]=json!("Check plan for exactly the selected original claim declarations/owners. Actual successful source/context/name/owned checks are required. Original scopes and integration states are retained; no full-registry or native/scientific closure.");
 Ok(result)
}

#[cfg(test)]mod tests {
 use super::*;
 fn data()->(Value,Value){
  (json!({"claims":[{"id":"A","completion":{"mathematical_claim_complete":true}},{"id":"B"}]}),
   json!({"claims":[{"claim_id":"A","lean":{"module":"ResearchCommons.Claims.A","declarations":["ResearchCommons.Claims.A.endpoint"],"state":"source_binding","scope":"retained conditional endpoint"}},
    {"claim_id":"B","lean":{"state":"pending_binding","module":null}}]}))
 }
 #[test]fn candidate_scope_and_missing_claims_are_retained(){
  let(c,b)=data();let p=plan(&c,&b).unwrap();
  assert_eq!(p["claims"][0]["integration_state"],"source_binding");
  assert_eq!(p["unbound_claims"],json!(["B"]));
  assert!(p["document"].as_str().unwrap().contains("#check @ResearchCommons.Claims.A.endpoint"));
 }
 #[test]fn declarations_cannot_inject_source(){
  let(c,mut b)=data();
  b["claims"][0]["lean"]["declarations"]=json!(["ResearchCommons.Claims.A.endpoint\naxiom forged : False"]);
  assert!(plan(&c,&b).is_err());
 }
 #[test]fn module_ownership_is_checked_in_lean_not_guessed_from_namespace(){
  let(c,mut b)=data();
  b["claims"][0]["lean"]["declarations"]=json!(["ResearchCommons.Other.endpoint"]);
  let p=plan(&c,&b).unwrap();let source=p["document"].as_str().unwrap();
  assert!(source.contains("(\"A\", ``ResearchCommons.Other.endpoint, \"ResearchCommons.Claims.A\")"));
  assert!(source.contains("environment.getModuleIdxFor? declaration"));
  assert!(source.contains("unless actual == expected"));
 }
 #[test]fn one_claim_reuses_multiple_real_module_owners_without_a_wrapper_alias(){
  let(c,mut b)=data();
  b["claims"][0]["lean"]["declarations"]=json!([
   "ResearchCommons.Claims.A.endpoint","ResearchCommons.Shared.semigroup"]);
  b["claims"][0]["lean"]["declaration_modules"]=json!({
   "ResearchCommons.Shared.semigroup":"ResearchCommons.SharedLaw"});
  let p=plan(&c,&b).unwrap();let source=p["document"].as_str().unwrap();
  assert!(p["imports"].as_array().unwrap().contains(&json!("ResearchCommons.Claims.A")));
  assert!(p["imports"].as_array().unwrap().contains(&json!("ResearchCommons.SharedLaw")));
  assert!(source.contains("(\"A\", ``ResearchCommons.Shared.semigroup, \"ResearchCommons.SharedLaw\")"));
  assert!(source.contains("(\"A\", ``ResearchCommons.Claims.A.endpoint, \"ResearchCommons.Claims.A\")"));
 }
 #[test]fn ownership_metadata_cannot_add_an_unlisted_or_unsafe_dependency(){
  let(c,b)=data();
  for overrides in [
   json!(["ResearchCommons.SharedLaw"]),
   json!({"ResearchCommons.Unlisted.endpoint":"ResearchCommons.SharedLaw"}),
   json!({"ResearchCommons.Claims.A.endpoint":""}),
   json!({"ResearchCommons.Claims.A.endpoint":17}),
   json!({"ResearchCommons.Claims.A.endpoint":"Safe\naxiom forged : False"}),
  ]{
   let mut input=b.clone();input["claims"][0]["lean"]["declaration_modules"]=overrides;
   assert!(plan(&c,&input).is_err());
  }
 }
 #[test]fn duplicate_canonical_identity_is_not_collapsed(){
  let(mut c,b)=data();c["claims"].as_array_mut().unwrap().push(json!({"id":"A"}));
  assert!(plan(&c,&b).is_err());
 }


 #[test]fn selected_claims_preserve_original_names_owners_and_scope(){
  let(c,mut b)=data();
  b["claims"][1]["lean"]=json!({"module":"Other","declarations":["Other.extra"],"state":"source_binding"});
  b["claims"][0]["lean"]["declaration_modules"]=json!({"ResearchCommons.Claims.A.endpoint":"ActualOwner"});
  let p=plan_for_claims(&c,&b,&["A".to_owned()]).unwrap();
  assert_eq!(p["requested_claims"],json!(["A"]));
  assert_eq!(p["canonical_claim_count"],2);
  assert_eq!(p["full_registry_selection"],false);
  assert_eq!(p["claims"][0]["integration_state"],"source_binding");
  assert_eq!(p["claims"][0]["canonical_completion"]["mathematical_claim_complete"],true);
  assert_eq!(p["unbound_claims"],json!([]));
  let source=p["document"].as_str().unwrap();
  assert!(source.contains("import ActualOwner"));
  assert!(source.contains("(\"A\", \x60\x60ResearchCommons.Claims.A.endpoint, \"ActualOwner\")"));
  assert!(!source.contains("Other.extra"));
 }
 #[test]fn selection_refuses_unknown_duplicate_or_unbound_claims(){
  let(c,b)=data();
  for ids in [vec!["Z".to_owned()],vec!["A".to_owned(),"A".to_owned()],vec!["B".to_owned()]]{
   assert!(plan_for_claims(&c,&b,&ids).is_err());
  }
 }
 #[test]fn empty_selection_is_byte_identical_default_plan(){
  let(c,b)=data();
  assert_eq!(plan(&c,&b).unwrap(),plan_for_claims(&c,&b,&[]).unwrap());
 }
 #[test]fn selection_cannot_hide_malformed_other_binding(){
  let(c,mut b)=data();
  b["claims"][1]["lean"]=json!({"module":"Other","declarations":["bad\naxiom forged : False"]});
  assert!(plan_for_claims(&c,&b,&["A".to_owned()]).is_err());
 }

}
