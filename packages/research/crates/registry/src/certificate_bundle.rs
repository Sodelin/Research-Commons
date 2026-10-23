//! Bounded framing for an owned proof emitter's complete public source bundle.
//! This reader grants no proof/result authority. Every document is checked by
//! Lean and the entire owned declaration audit before a caller receipt exists.
use crate::Result;
use serde_json::Value;
use std::collections::BTreeSet;
pub fn decode(bytes:&[u8],expected:&str)->Result<Vec<(String,Vec<u8>)>>{
 if bytes.len()>32*1024*1024{return Err("proof bundle wire limit".into());}
 let value:Value=serde_json::from_slice(bytes).map_err(|e|format!("proof bundle JSON: {e}"))?;
 if value["schema"]!=1 || value["kind"]!="original-natural-word-checked-cache" ||
    value["kernel_checked"]!=false || value["final_module"]!=expected {
  return Err("proof bundle identity/unchecked-origin fields".into());
 }
 let rows=value["modules"].as_array().ok_or("missing bundle modules")?;
 if rows.is_empty()||rows.len()>512{return Err("proof bundle module count".into());}
 let mut names=BTreeSet::new();let mut result=Vec::new();let mut total=0usize;
 for row in rows{
  let name=row["module"].as_str().ok_or("missing bundle module")?;
  if !name.starts_with(expected)||name.is_empty()||
   !name.bytes().all(|b|b.is_ascii_alphanumeric()||b==b'_') ||
   !name.as_bytes()[0].is_ascii_alphabetic() || !names.insert(name.to_owned()){
   return Err("unsafe/foreign/duplicate proof bundle module".into());
  }
  let source=row["source"].as_str().ok_or("missing bundle source")?;
  if source.is_empty()||source.len()>262144{return Err("proof bundle source frame".into());}
  total=total.checked_add(source.len()).ok_or("proof bundle source size overflow")?;
  if total>16*1024*1024{return Err("proof bundle aggregate source limit".into());}
  result.push((name.to_owned(),source.as_bytes().to_vec()));
 }
 if result.last().map(|r|r.0.as_str())!=Some(expected) ||
    value["total_source_bytes"].as_u64()!=Some(total as u64) {
  return Err("proof bundle final/complete byte count".into());
 }
 Ok(result)
}
#[cfg(test)]mod tests{
 use super::*;
 fn packet(rows:Value)->Value{
  let bytes=rows.as_array().unwrap().iter().map(|r|r["source"].as_str().unwrap().len()).sum::<usize>();
  serde_json::json!({"schema":1,"kind":"original-natural-word-checked-cache",
   "kernel_checked":false,"final_module":"NaturalIndependentWord","total_source_bytes":bytes,"modules":rows})
 }
 #[test]fn complete_utf8_source_is_preserved_in_order(){
  let p=packet(serde_json::json!([
   {"module":"NaturalIndependentWordContext","source":"-- λ\n"},
   {"module":"NaturalIndependentWord","source":"-- final\n"}]));
  let b=decode(&serde_json::to_vec(&p).unwrap(),"NaturalIndependentWord").unwrap();
  assert_eq!(b[0].1,"-- λ\n".as_bytes());assert_eq!(b.len(),2);
 }
 #[test]fn untrusted_producer_cannot_self_attest_a_checked_result(){
  let mut p=packet(serde_json::json!([{"module":"NaturalIndependentWord","source":"-- final"}]));
  p["kernel_checked"]=Value::Bool(true);
  assert!(decode(&serde_json::to_vec(&p).unwrap(),"NaturalIndependentWord").is_err());
 }
 #[test]fn duplicate_foreign_and_missing_final_modules_are_refused(){
  for rows in [
   serde_json::json!([{"module":"NaturalIndependentWord","source":"x"},{"module":"NaturalIndependentWord","source":"x"}]),
   serde_json::json!([{"module":"../OriginalTreeBank","source":"x"},{"module":"NaturalIndependentWord","source":"x"}]),
   serde_json::json!([{"module":"NaturalIndependentWordContext","source":"x"}])] {
    let p=packet(rows);assert!(decode(&serde_json::to_vec(&p).unwrap(),"NaturalIndependentWord").is_err());
   }
 }
 #[test]fn utf8_character_count_is_not_a_complete_byte_count(){
  let mut p=packet(serde_json::json!([{"module":"NaturalIndependentWord","source":"λ"}]));
  p["total_source_bytes"]=serde_json::json!(1);
  assert!(decode(&serde_json::to_vec(&p).unwrap(),"NaturalIndependentWord").is_err());
 }
}
