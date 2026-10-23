use research_commons_package::{check_package,prepare_lean,read_json,Result};
use serde_json::json;
use std::{env,fs,path::PathBuf,process::{Command,Stdio}};

/// Execute the actual public Rust callers and kernel-check their literal proof
/// output against the already built retained package. No external result or
/// supplied theorem is accepted in place of these checks.
fn check_callers_at(root:&std::path::Path,project:&str,owned:&[String],scope:&str)->Result<()> {
 let root=root.canonicalize().map_err(|e|e.to_string())?;
 let lean=root.join(project);
 let generated=lean.join(".generated");
 let objects=lean.join(".lake/build/lib/lean");
 let evidence=root.join("build").join(scope).join("sources");
 fs::create_dir_all(&evidence).map_err(|e|e.to_string())?;
 let target_audit=scope=="retained-target-audit";
 let source_only=scope=="original-source-callers" || target_audit;
 let mut callers=if source_only {Vec::new()} else {vec![
    ("CMExample","cm-certificate",None),
    ("AffineSAT","affine-certificate",Some("sat")),
    ("AffineUNSAT","affine-certificate",Some("unsat"))]};
 if project=="lean" && !target_audit {
  callers.extend([("OriginalTreeBank","source-certificate",Some("tree")),
    ("OriginalParallelBank","source-certificate",Some("parallel")),
    ("OriginalCellExclusion","source-certificate",Some("infeasible"))]);
 }
 let mut records=Vec::new();
 let mut names=owned.to_vec();
 for (module,binary,argument) in callers {
  let mut command=Command::new("cargo");
  command.args(["run","--locked","-p","research-commons-runtime","--bin",binary]);
  if let Some(a)=argument {command.args(["--",a]);}
  let output=command.current_dir(&root).stdin(Stdio::null()).output().map_err(|e|e.to_string())?;
  if !output.status.success(){return Err(format!("caller {binary} refused: {}",output.status));}
  if output.stdout.len()>262144 {return Err(format!("caller {binary} exceeded source limit"));}
  std::str::from_utf8(&output.stdout).map_err(|e|e.to_string())?;
  let source=generated.join(format!("{module}.lean"));
  fs::write(&source,&output.stdout).map_err(|e|e.to_string())?;
  fs::write(evidence.join(format!("{module}.lean")),&output.stdout).map_err(|e|e.to_string())?;
  println!("LEAN CERTIFICATE {module}");
  let status=Command::new("lake").args(["env","lean","-j1","-M6144","-Ddebug.skipKernelTC=false","--root=.generated"])
      .arg("-o").arg(objects.join(format!("{module}.olean"))).arg(&source)
      .current_dir(&lean).stdin(Stdio::null()).status().map_err(|e|e.to_string())?;
  if !status.success(){return Err(format!("Lean rejected {module}: {status}"));}
  records.push(json!({"module":module,"source_sha256":research_commons_package::sha256(&output.stdout),
      "source_bytes":output.stdout.len(),"kernel_check_passed":true}));
  names.push(module.to_owned());
 }
 let lock=read_json(&root.join("source-lock.json"))?;
 let base=root.join(lock["lean_profile"]["directory"].as_str().ok_or("missing profile directory")?);
 let template=fs::read_to_string(base.join("scripts/AuditTemplate.lean")).map_err(|e|e.to_string())?;
 let placeholder=r##"#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]"##;
 if template.matches(placeholder).count()!=1{return Err("unexpected caller audit template".into());}
 let selected=serde_json::to_string(&names).map_err(|e|e.to_string())?;
 let mut imports=if source_only {String::new()} else {String::from("import ResearchCommons\n")};
 for name in &names {imports.push_str(&format!("import {name}\n"));}
 let audit=imports+&template.replace(placeholder,&format!("#{selected}"))
    .replace("\"AUDIT-OWNED.json\"",&format!("\"../build/{scope}/caller-audit.json\""));
 fs::write(generated.join("CallerAudit.lean"),audit).map_err(|e|e.to_string())?;
 let status=Command::new("lake").args(["env","lean","-j1","-M6144","-Ddebug.skipKernelTC=false","--root=.generated",".generated/CallerAudit.lean"])
    .current_dir(&lean).stdin(Stdio::null()).status().map_err(|e|e.to_string())?;
 if !status.success(){return Err(format!("caller axiom audit failed: {status}"));}
 let audit=read_json(&root.join("build").join(scope).join("caller-audit.json"))?;
 for field in ["owned_axioms","nonstandard_axiom_rows","missing_modules"] {
    if !audit[field].as_array().is_some_and(|v|v.is_empty()){return Err(format!("caller audit rejected {field}"));}
 }
 let receipt=json!({"profile":scope,"certificates":records,"owned_axiom_audit_passed":true,
    "scope":if target_audit {"Only the exact target dependency closure and owned declarations; no particular native table/input/result/word/readout is certified."} else {"Particular exact rational and source-cell certificates for this selected profile; no observation-law, universal parser/native refinement, full source coverage or full registry closure."}});
 fs::write(root.join("build").join(scope).join("caller-verification.json"),serde_json::to_vec_pretty(&receipt).map_err(|e|e.to_string())?)
    .map_err(|e|e.to_string())?;
 println!("{receipt}");
 Ok(())
}


fn build_certificates(root:&std::path::Path)->Result<()> {
 let root=root.canonicalize().map_err(|e|e.to_string())?;
 let plan=research_commons_package::prepare_certificate_profile(&root)?;
 let lean=root.join("certificates");
 let out=lean.join(".lake/build/lib/lean");
 fs::create_dir_all(&out).map_err(|e|e.to_string())?;
 let mut names=plan["order"].as_array().ok_or("no certificate order")?.iter()
    .map(|v|v.as_str().map(str::to_owned).ok_or("invalid certificate module".to_owned())).collect::<Result<Vec<_>>>()?;
 names.push("ResearchCommons".into());
 for name in &names {
    let relative=research_commons_package::module_path(name)?;
    let target=out.join(&relative).with_extension("olean");
    fs::create_dir_all(target.parent().ok_or("no certificate target parent")?).map_err(|e|e.to_string())?;
    let status=Command::new("lake").args(["env","lean","-j1","-M6144","-Ddebug.skipKernelTC=false","--root=.generated"])
        .arg("-o").arg(target).arg(lean.join(".generated").join(relative))
        .current_dir(&lean).stdin(Stdio::null()).status().map_err(|e|e.to_string())?;
    if !status.success(){return Err(format!("certificate context rejected {name}: {status}"));}
 }
 check_callers_at(&root,"certificates",&names,"isolated-certificate-callers")
}


/// Compile either the complete profile, a diagnostic prefix, or one actual
/// dependency closure. Scoped success never substitutes for full-profile PASS.
fn build_lean(root:&std::path::Path,mut args:Vec<String>)->Result<()> {
 let reuse=args.iter().any(|a|a=="--reuse-retained");
 args.retain(|a|a!="--reuse-retained");
 let plan=prepare_lean(root)?;
 let lean=root.join("lean").canonicalize().map_err(|e|e.to_string())?;
 let out=lean.join(".lake/build/lib/lean");
 fs::create_dir_all(&out).map_err(|e|e.to_string())?;
 let (cap,target)=match args.as_slice() {
  []=>(None,None),
  [flag,name] if flag=="--target" => (None,Some(name.as_str())),
  [n]=>(Some(n.parse::<usize>().map_err(|_|"invalid module cap".to_owned())?),None),
  _=>return Err("usage: build [--reuse-retained] [module-cap|--target Module]".into()),
 };
 let all=plan["order"].as_array().ok_or("missing order")?.iter()
    .map(|v|v.as_str().map(str::to_owned).ok_or("non-string module".to_owned())).collect::<Result<Vec<_>>>()?;
 let mut names=if let Some(t)=target {research_commons_package::selected_modules(&plan,t)?} else {all.clone()};
 if let Some(n)=cap {names.truncate(n);}
 let source_count=names.len();
 let complete=target.is_none()&&source_count==all.len();
 if target.is_none(){names.push("ResearchCommons.Registry".into());}
 if complete{names.push("ResearchCommons".into());}
 fs::create_dir_all(root.join("build")).map_err(|e|e.to_string())?;
 let receipt_path=root.join(if target.is_some(){"build/lean-target-build.json"}else{"build/lean-build.json"});
 let mut objects=Vec::new();
 let mut reused=0usize;
 let mut cache=if reuse {Some(research_commons_package::object_cache::RetainedObjects::open(root,&plan)?)} else {None};
 let mut receipt=json!({"status":"RUNNING","compiler_exit_success":false,"complete_profile":false,
   "target":target,"selected_source_modules":source_count,"full_profile_source_modules":all.len(),
   "source_graph_sha256":plan["source_graph_sha256"],"module_hashes":plan["module_hashes"],
   "objects":objects});
 let write_receipt=|value:&serde_json::Value|->Result<()> {
   fs::write(&receipt_path,serde_json::to_vec_pretty(value).map_err(|e|e.to_string())?).map_err(|e|e.to_string())
 };
 write_receipt(&receipt)?;
 for (i,name) in names.iter().enumerate(){
  let relative=research_commons_package::module_path(name)?;
  let object=out.join(&relative).with_extension("olean");
  fs::create_dir_all(object.parent().ok_or("no object parent")?).map_err(|e|e.to_string())?;
  println!("LEAN {}/{} {}",i+1,names.len(),name);
  let source=lean.join(".generated").join(&relative);
  let cached=cache.as_ref().map(|c|c.restore(name)).transpose()?.unwrap_or(false);
  if cached {reused+=1;println!("REUSE RETAINED {name}");} else {
  let status=Command::new("lake").args(["env","lean","-j1","-M6144","-Ddebug.skipKernelTC=false"])
    .arg("--root=.generated").arg("-o").arg(&object).arg(&source).current_dir(&lean)
    .stdin(Stdio::null()).status().map_err(|e|format!("lean spawn: {e}"))?;
  if !status.success(){
   receipt["status"]=json!("FAILED");receipt["failed_module"]=json!(name);write_receipt(&receipt)?;
   return Err(format!("Lean failed on {name}: {status}"));
  }
  if let Some(c)=cache.as_mut(){c.capture(name)?;}
  }
  objects.push(json!({"module":name,"reused_retained_object":cached,"sha256":research_commons_package::sha256(&fs::read(object).map_err(|e|e.to_string())?)}));
  receipt["objects"]=json!(objects);receipt["reused_retained_objects"]=json!(reused);write_receipt(&receipt)?;
 }
 let mut owned_audit=false;
 if complete {
  let status=Command::new("lake").args(["env","lean","-j1","-M6144","-Ddebug.skipKernelTC=false","--root=.generated",".generated/OwnedAudit.lean"])
    .current_dir(&lean).stdin(Stdio::null()).status().map_err(|e|e.to_string())?;
  if !status.success(){return Err(format!("complete owned axiom audit failed: {status}"));}
  let audit=read_json(&root.join("build/owned-audit.json"))?;
  for field in ["owned_axioms","nonstandard_axiom_rows","missing_modules"]{
   if !audit[field].as_array().is_some_and(|a|a.is_empty()){return Err(format!("audit rejected {field}"));}
  }
  owned_audit=true;
 }
 receipt["status"]=json!("COMPLETE");receipt["compiler_exit_success"]=json!(true);
 receipt["compiled_modules"]=json!(names.len()-reused);receipt["checked_or_reused_modules"]=json!(names.len());receipt["complete_profile"]=json!(complete);
 receipt["owned_axiom_audit_passed"]=json!(owned_audit);
 receipt["historical_acceptance_transferred"]=json!(false);receipt["all_claims_formalized"]=json!(false);
 write_receipt(&receipt)?;println!("{receipt}");Ok(())
}

fn checked_target(root:&std::path::Path,target:&str)->Result<Vec<String>> {
   let plan=prepare_lean(root)?;
   let selected=research_commons_package::selected_modules(&plan,target)?;
   let receipt=read_json(&root.join("build/lean-target-build.json"))?;
   if receipt["compiler_exit_success"]!=true || receipt["target"].as_str()!=Some(target) ||
       receipt["source_graph_sha256"]!=plan["source_graph_sha256"] ||
       receipt["module_hashes"]!=plan["module_hashes"] {
    return Err("no exact successful target build".into());
   }
   for entry in receipt["objects"].as_array().ok_or("missing target objects")? {
    let name=entry["module"].as_str().ok_or("invalid target object")?;
    let path=root.join("lean/.lake/build/lib/lean").join(research_commons_package::module_path(name)?).with_extension("olean");
    let bytes=fs::read(path).map_err(|e|e.to_string())?;
    if research_commons_package::sha256(&bytes)!=entry["sha256"].as_str().ok_or("missing object digest")? {
     return Err(format!("target object changed: {name}"));
    }
   }
   if receipt["objects"].as_array().ok_or("missing target objects")?.iter()
      .map(|v|v["module"].as_str().map(str::to_owned).ok_or("missing object module".to_owned()))
      .collect::<Result<Vec<_>>>()? != selected {
     return Err("incomplete target object coverage".into());
   }
   Ok(selected)
}

fn run() -> Result<()> {
 let mut args=env::args().skip(1);
 let command=args.next().unwrap_or_else(||"check".into());
 let root=PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
 match command.as_str(){
  "check"|"coverage"=>{
   let result=check_package(&root)?;println!("{}",serde_json::to_string_pretty(&result).map_err(|e|e.to_string())?);
   if args.any(|a|a=="--strict")&&result["full_package_complete"]!=true{return Err("full integration incomplete; no claim of package closure".into());}
  },
  "prepare"=>println!("{}",prepare_lean(&root)?),
  "check-callers"=>check_callers_at(&root,"lean",&[],"full-profile-callers")?,
  "prepare-certificates"=>println!("{}",research_commons_package::prepare_certificate_profile(&root)?),
  "build-certificates"=>build_certificates(&root)?,
  "build"=>build_lean(&root,args.collect())?,
  "check-source-callers"=>{
   let selected=checked_target(&root,"OriginalCodeChartReceiver")?;
   check_callers_at(&root,"lean",&selected,"original-source-callers")?;
  },
  "audit-target"=>{
   let target=args.next().ok_or("audit-target needs an exact module")?;
   if args.next().is_some(){return Err("audit-target accepts one module".into());}
   let selected=checked_target(&root,&target)?;
   check_callers_at(&root,"lean",&selected,"retained-target-audit")?;
  },
  "emit-index"=> {
    let claims=read_json(&root.join("registry/claims.json"))?;
    let rows=claims["claims"].as_array().ok_or("missing cards")?;
    println!("-- Registry metadata only; not proofs of the claims.\nnamespace ResearchCommons.Registry\ndef claimIDs : List String := [");
    for (i,c) in rows.iter().enumerate(){println!("  {:?}{}",c["id"].as_str().ok_or("missing id")?,if i+1<rows.len(){","}else{""});}
    println!("]\ntheorem claim_count : claimIDs.length = {} := by decide\nend ResearchCommons.Registry",rows.len());
  },
  _=>return Err("usage: commons [check|coverage --strict|prepare|build [module-cap|--target Module]|check-callers|check-source-callers|audit-target Module|prepare-certificates|build-certificates|emit-index]".into())
 }
 Ok(())
}
fn main(){if let Err(e)=run(){eprintln!("PACKAGE_INCOMPLETE: {e}");std::process::exit(2);}}
