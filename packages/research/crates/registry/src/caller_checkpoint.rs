//! Durable progress for literal caller checks. A reused object is prior
//! compilation evidence, never a newly executed kernel replay.
use crate::{module_path,read_json,sha256,Result};
use serde_json::{json,Value};
use std::{collections::BTreeSet,fs,path::{Path,PathBuf}};
pub struct CallerCheckpoint {path:PathBuf,context:String,records:Vec<Value>,next:usize}
fn family(object:&Path)->Result<Value>{
 let base=object.file_name().and_then(|v|v.to_str()).ok_or("invalid object name")?;
 let mut rows=Vec::new();
 for suffix in ["",".private",".server"] {
  let p=object.with_file_name(format!("{base}{suffix}"));
  if p.exists(){let meta=fs::symlink_metadata(&p).map_err(|e|e.to_string())?;if !meta.is_file(){return Err("caller object is not a regular file".into())}rows.push(json!({"suffix":suffix,"sha256":sha256(&fs::read(p).map_err(|e|e.to_string())?)}));}
 }
 if !rows.iter().any(|r|r["suffix"]==""){return Err("caller object missing".into())}Ok(json!(rows))
}
impl CallerCheckpoint {
 pub fn open(path:PathBuf,context:String)->Result<Self>{
  let records=if path.exists(){let v=read_json(&path)?;if v["schema"]!=1||v["context_sha256"]!=context{return Err("caller checkpoint context changed; preserve old checkpoint and start a new one".into())}v["records"].as_array().ok_or("invalid caller checkpoint records")?.clone()}else{Vec::new()};
  let mut names=BTreeSet::new();for r in &records{let n=r["module"].as_str().ok_or("invalid checkpoint module")?;module_path(n)?;if !names.insert(n)||r["compiler_exit_code"]!=0{return Err("duplicate/unverified caller checkpoint".into())}}
  Ok(Self{path,context,records,next:0})
 }
 pub fn reuse(&mut self,module:&str,source:&[u8],object:&Path)->Result<bool>{
  let Some(row)=self.records.get(self.next) else{return Ok(false)};
  if row["module"]!=module||row["source_sha256"]!=sha256(source)||row["object_family"]!=family(object)?{return Err(format!("caller checkpoint source/order/object mismatch: {module}"))}
  self.next+=1;Ok(true)
 }
 pub fn capture(&mut self,module:&str,source:&[u8],object:&Path)->Result<()> {
  if self.next!=self.records.len(){return Err("caller checkpoint cursor mismatch".into())}
  self.records.push(json!({"module":module,"source_sha256":sha256(source),"object_family":family(object)?,"compiler_exit_code":0}));self.next+=1;
  let temporary=self.path.with_extension("next");fs::write(&temporary,serde_json::to_vec_pretty(&json!({"schema":1,"context_sha256":self.context,"scope":"Prior completed literal-source compiler invocations; resume is qualified object reuse, not fresh replay. Final complete caller audit is always rerun.","records":self.records})).map_err(|e|e.to_string())?).map_err(|e|e.to_string())?;fs::rename(temporary,&self.path).map_err(|e|e.to_string())
 }
 pub fn complete(&self)->Result<()>{if self.next!=self.records.len(){return Err("caller checkpoint contains an unused tail".into())}Ok(())}
}
#[cfg(test)]mod tests{
 use super::*;
 #[test]fn changed_source_order_companion_and_context_cannot_reuse(){
  let root=std::env::temp_dir().join(format!("caller-checkpoint-{}",std::process::id()));fs::create_dir_all(&root).unwrap();let object=root.join("Example.olean");fs::write(&object,b"object").unwrap();fs::write(root.join("Example.olean.private"),b"private").unwrap();let path=root.join("checkpoint.json");
  let mut c=CallerCheckpoint::open(path.clone(),"context".into()).unwrap();assert!(!c.reuse("Example",b"source",&object).unwrap());c.capture("Example",b"source",&object).unwrap();c.complete().unwrap();
  assert!(CallerCheckpoint::open(path.clone(),"different".into()).is_err());
  let mut c=CallerCheckpoint::open(path.clone(),"context".into()).unwrap();assert!(c.reuse("Example",b"changed",&object).is_err());assert!(c.reuse("Other",b"source",&object).is_err());assert!(c.reuse("Example",b"source",&object).unwrap());c.complete().unwrap();
  fs::write(root.join("Example.olean.private"),b"changed").unwrap();let mut c=CallerCheckpoint::open(path,"context".into()).unwrap();assert!(c.reuse("Example",b"source",&object).is_err());fs::remove_dir_all(root).unwrap();
 }
}
