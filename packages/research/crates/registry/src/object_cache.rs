//! Reuse only exact retained-source objects produced by this public build path.
//! No historical phone objects or newly authored modules are admitted.
//! A cache receipt is compilation provenance, not a new kernel replay.
use crate::{module_path,read_json,sha256,Result};
use serde_json::{json,Value};
use std::{collections::BTreeSet,fs,path::{Path,PathBuf}};
pub struct RetainedObjects {
    root:PathBuf,output:PathBuf,context:String,retained:BTreeSet<String>,
    hashes:Value,records:serde_json::Map<String,Value>,
}
impl RetainedObjects {
 pub fn open(root:&Path,plan:&Value)->Result<Self> {
    let mut bytes=b"ResearchCommons-retained-objects-v1\0lean -j1 -M6144 -Ddebug.skipKernelTC=false --root=.generated\0".to_vec();
    for p in ["lean/lean-toolchain","lean/lakefile.lean"] {
        bytes.extend_from_slice(&fs::read(root.join(p)).map_err(|e|format!("cache context {p}: {e}"))?);
        bytes.push(0);
    }
    bytes.extend_from_slice(plan["source_graph_sha256"].as_str().ok_or("missing graph identity")?.as_bytes());
    bytes.extend_from_slice(std::env::consts::OS.as_bytes());
    bytes.extend_from_slice(std::env::consts::ARCH.as_bytes());
    let context=sha256(&bytes);
    let directory=root.join("build/retained-objects");
    let manifest=directory.join("manifest.json");
    let records=if manifest.exists() {
        let old=read_json(&manifest)?;
        if old["context_sha256"]!=context {return Err("retained cache context mismatch; remove this cache and compile sources".into());}
        old["modules"].as_object().ok_or("invalid retained cache module map")?.clone()
    } else {serde_json::Map::new()};
    let count=plan["retained_sources"].as_u64().ok_or("missing retained source count")? as usize;
    let order=plan["order"].as_array().ok_or("missing exact source order")?;
    if count>order.len(){return Err("retained cache census mismatch".into());}
    let retained=order.iter().take(count).map(|v|v.as_str().map(str::to_owned).ok_or("invalid retained module".to_owned()))
        .collect::<Result<BTreeSet<_>>>()?;
    let hashes=plan["module_hashes"].clone();
    for name in records.keys() {
        if !retained.contains(name){return Err(format!("cache contains unretained module {name}"));}
        module_path(name)?;
    }
    Ok(Self{root:directory,output:root.join("lean/.lake/build/lib/lean"),context,retained,hashes,records})
 }
 fn relative(name:&str)->Result<PathBuf> {Ok(module_path(name)?.with_extension("olean"))}
 pub fn restore(&self,name:&str)->Result<bool> {
    if !self.retained.contains(name){return Ok(false);}
    let Some(record)=self.records.get(name) else{return Ok(false)};
    if record["source_sha256"]!=self.hashes[name] {return Err(format!("cached source identity mismatch: {name}"));}
    let relative=Self::relative(name)?;
    let parent=relative.parent().ok_or("no cached object parent")?;
    let base=relative.file_name().and_then(|v|v.to_str()).ok_or("invalid cached object filename")?;
    let files=record["files"].as_array().ok_or("missing cached object files")?;
    if !files.iter().any(|v|v["name"]==base){return Err(format!("cache lacks main object: {name}"));}
    let mut seen=BTreeSet::new();let mut checked=Vec::new();
    // Validate the entire object's file family before copying any of it.
    for item in files {
        let filename=item["name"].as_str().ok_or("invalid cached filename")?;
        if filename!=base && !filename.starts_with(&format!("{base}.")){return Err("foreign cached companion".into());}
        if filename.contains('/')||filename.contains('\\')||!seen.insert(filename.to_owned()){return Err("unsafe/duplicate cached companion".into());}
        let source=self.root.join("objects").join(parent).join(filename);
        let metadata=fs::symlink_metadata(&source).map_err(|e|e.to_string())?;
        if !metadata.file_type().is_file(){return Err("cached object is not a regular file".into());}
        let bytes=fs::read(&source).map_err(|e|e.to_string())?;
        if item["sha256"].as_str()!=Some(sha256(&bytes).as_str()){return Err(format!("cached object digest mismatch: {name}/{filename}"));}
        checked.push((filename.to_owned(),bytes));
    }
    let target=self.output.join(parent);
    fs::create_dir_all(&target).map_err(|e|e.to_string())?;
    for (filename,bytes) in checked {fs::write(target.join(filename),bytes).map_err(|e|e.to_string())?;}
    Ok(true)
 }
 pub fn capture(&mut self,name:&str)->Result<()> {
    if !self.retained.contains(name){return Ok(());}
    let relative=Self::relative(name)?;
    let parent=relative.parent().ok_or("no object parent")?;
    let base=relative.file_name().and_then(|v|v.to_str()).ok_or("invalid object filename")?;
    let destination=self.root.join("objects").join(parent);
    fs::create_dir_all(&destination).map_err(|e|e.to_string())?;
    let mut files=Vec::new();
    for entry in fs::read_dir(self.output.join(parent)).map_err(|e|e.to_string())? {
        let entry=entry.map_err(|e|e.to_string())?;
        let filename=entry.file_name().into_string().map_err(|_|"non-UTF8 object filename")?;
        if filename!=base && !filename.starts_with(&format!("{base}.")){continue;}
        if !entry.file_type().map_err(|e|e.to_string())?.is_file(){return Err("compiled object is not a regular file".into());}
        let bytes=fs::read(entry.path()).map_err(|e|e.to_string())?;
        fs::write(destination.join(&filename),&bytes).map_err(|e|e.to_string())?;
        files.push(json!({"name":filename,"sha256":sha256(&bytes)}));
    }
    if !files.iter().any(|v|v["name"]==base){return Err(format!("compiler did not produce {base}"));}
    files.sort_by(|a,b|a["name"].as_str().cmp(&b["name"].as_str()));
    self.records.insert(name.to_owned(),json!({"source_sha256":self.hashes[name],"files":files,
        "origin":{"github_run_id":std::env::var("GITHUB_RUN_ID").ok(),"source_commit":std::env::var("GITHUB_SHA").ok()},
        "scope":"Object files emitted by the exact source compiler invocation, not a fresh kernel replay on cache reuse."}));
    self.persist()
 }
 fn persist(&self)->Result<()> {
    let value=json!({"schema":1,"context_sha256":self.context,"modules":self.records});
    fs::create_dir_all(&self.root).map_err(|e|e.to_string())?;
    let temporary=self.root.join("manifest.next");
    fs::write(&temporary,serde_json::to_vec_pretty(&value).map_err(|e|e.to_string())?).map_err(|e|e.to_string())?;
    fs::rename(temporary,self.root.join("manifest.json")).map_err(|e|e.to_string())
 }
}
#[cfg(test)]mod tests {
 use super::*;
 use std::sync::atomic::{AtomicU64,Ordering};
 static SEQUENCE:AtomicU64=AtomicU64::new(0);
 struct Example(PathBuf);
 impl Drop for Example{fn drop(&mut self){let _=fs::remove_dir_all(&self.0);}}
 fn example()->(Example,Value) {
    let root=std::env::temp_dir().join(format!("commons-object-cache-{}-{}",std::process::id(),SEQUENCE.fetch_add(1,Ordering::Relaxed)));
    fs::create_dir_all(root.join("lean/.lake/build/lib/lean")).unwrap();
    fs::write(root.join("lean/lean-toolchain"),"leanprover/lean4:v4.33.1").unwrap();
    fs::write(root.join("lean/lakefile.lean"),"fixed public test Mathlib identity").unwrap();
    let plan=json!({"source_graph_sha256":"fixed-graph","retained_sources":1,
      "order":["Retained","New"],"module_hashes":{"Retained":"retained-source","New":"new-source"}});
    (Example(root),plan)
 }
 #[test]fn reuse_checks_exact_object_companions_and_source_identity(){
    let (root,plan)=example();let output=root.0.join("lean/.lake/build/lib/lean");
    fs::write(output.join("Retained.olean"),b"public synthetic object").unwrap();
    fs::write(output.join("Retained.olean.private"),b"public synthetic companion").unwrap();
    let mut cache=RetainedObjects::open(&root.0,&plan).unwrap();cache.capture("Retained").unwrap();
    fs::remove_file(output.join("Retained.olean.private")).unwrap();
    assert!(cache.restore("Retained").unwrap());
    assert_eq!(fs::read(output.join("Retained.olean.private")).unwrap(),b"public synthetic companion");
    let mut changed=plan.clone();changed["module_hashes"]["Retained"]=json!("different");
    assert!(RetainedObjects::open(&root.0,&changed).unwrap().restore("Retained").is_err());
    fs::write(root.0.join("build/retained-objects/objects/Retained.olean.private"),b"tampered").unwrap();
    assert!(cache.restore("Retained").is_err());
 }
 #[test]fn authored_modules_are_always_recompiled_and_context_changes_are_refused(){
    let (root,plan)=example();let output=root.0.join("lean/.lake/build/lib/lean");
    fs::write(output.join("Retained.olean"),b"public test").unwrap();
    fs::write(output.join("New.olean"),b"new test").unwrap();
    let mut cache=RetainedObjects::open(&root.0,&plan).unwrap();
    cache.capture("Retained").unwrap();cache.capture("New").unwrap();
    assert!(!cache.restore("New").unwrap());
    fs::write(root.0.join("lean/lakefile.lean"),"changed dependency identity").unwrap();
    assert!(RetainedObjects::open(&root.0,&plan).is_err());
 }
}
