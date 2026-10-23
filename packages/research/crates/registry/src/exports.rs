//! Exact public registry -> declaration-check plan. This reuses Lean as the
//! proof checker; it creates no native substitute for a scientific algorithm.
use serde_json::{json,Value};
use std::collections::BTreeSet;

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
  let mut local=BTreeSet::new();let mut ds=Vec::new();
  for declaration in declarations {
   let d=declaration.as_str().ok_or("non-string export declaration")?;
   name(d)?;
   if !d.starts_with(&(module.to_owned()+".")){
    return Err(format!("export {d} is outside declared module {module}"));
   }
   if !local.insert(d){return Err(format!("duplicate declaration {d}"));}
   ds.push(d.to_owned());
  }
  claims.push(json!({"claim_id":id,"module":module,"declarations":ds,
   "integration_state":row["lean"]["state"],"scope":row["lean"]["scope"],
   "canonical_completion":card["completion"]}));
 }
 if ids!=canonical_ids{
  return Err("export integration does not cover canonical IDs".into());
 }
 let mut document=String::from("-- Public declaration interface, not a new proof or algorithm.\n");
 for module in &imports{document.push_str(&format!("import {module}\n"));}
 document.push_str("\nnamespace ResearchCommons.Generated.ClaimExports\n");
 for claim in &claims {
  for declaration in claim["declarations"].as_array().ok_or("invalid planned declarations")?{
   let d=declaration.as_str().ok_or("invalid planned declaration")?;
   document.push_str(&format!("#check @{d}\n"));
  }
 }
 document.push_str("end ResearchCommons.Generated.ClaimExports\n");
 if document.len()>262144{return Err("claim export document limit".into());}
 Ok(json!({"schema":1,"claims":claims,"unbound_claims":unbound,
  "imports":imports,"document":document,
  "scope":"Exact declaration names/types in the actual current Lean package. Integration states and scientific scopes are retained; this is not a native physical provider, solver or upgraded scientific theorem."}))
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
 #[test]fn declarations_cannot_inject_source_or_escape_the_named_module(){
  let(c,mut b)=data();
  for bad in ["ResearchCommons.Claims.A.endpoint\naxiom forged : False","Other.endpoint"]{
   b["claims"][0]["lean"]["declarations"]=json!([bad]);assert!(plan(&c,&b).is_err());
  }
 }
 #[test]fn duplicate_canonical_identity_is_not_collapsed(){
  let(mut c,b)=data();c["claims"].as_array_mut().unwrap().push(json!({"id":"A"}));
  assert!(plan(&c,&b).is_err());
 }

}
