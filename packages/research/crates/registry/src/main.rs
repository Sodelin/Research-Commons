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
 let callers=[
    ("CMExample","cm-certificate",None),
    ("AffineSAT","affine-certificate",Some("sat")),
    ("AffineUNSAT","affine-certificate",Some("unsat"))];
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
 let mut imports=String::from("import ResearchCommons\n");
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
    "scope":"Particular exact rational CM law and affine matrices; no physical source/parser/universal-native refinement or full registry closure."});
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
  "build"=>{
   let plan=prepare_lean(&root)?;
   let lean=root.join("lean").canonicalize().map_err(|e|e.to_string())?;
   let out=lean.join(".lake/build/lib/lean");
   fs::create_dir_all(&out).map_err(|e|e.to_string())?;
   let cap=args.next().map(|v|v.parse::<usize>().map_err(|_|"invalid module cap".to_owned())).transpose()?;
   let mut names=plan["order"].as_array().ok_or("missing order")?.iter()
      .map(|v|v.as_str().map(str::to_owned).ok_or("non-string module".to_owned())).collect::<Result<Vec<_>>>()?;
   let expected=names.len();
   if let Some(n)=cap { names.truncate(n); }
   let complete=names.len()==expected;
   names.push("ResearchCommons.Registry".into());
   if complete {names.push("ResearchCommons".into());}
   fs::create_dir_all(root.join("build")).map_err(|e|e.to_string())?;
   fs::write(root.join("build/lean-build.json"),b"{\"status\":\"RUNNING\",\"complete_profile\":false}").map_err(|e|e.to_string())?;
   for (i,name) in names.iter().enumerate(){
    let relative=research_commons_package::module_path(name)?;
    let target=out.join(&relative).with_extension("olean");
    fs::create_dir_all(target.parent().ok_or("no object parent")?).map_err(|e|e.to_string())?;
    println!("LEAN {}/{} {}",i+1,names.len(),name);
    let source=lean.join(".generated").join(&relative);
    let status=Command::new("lake").args(["env","lean","-j1","-M6144","-Ddebug.skipKernelTC=false"])
      .arg("--root=.generated").arg("-o").arg(&target).arg(&source).current_dir(&lean)
      .stdin(Stdio::null()).status().map_err(|e|format!("lean spawn: {e}"))?;
    if !status.success(){return Err(format!("Lean failed on {name}: {status}"));}
   }
   fs::create_dir_all(root.join("build")).map_err(|e|e.to_string())?;
   if complete {
    let status=Command::new("lake").args(["env","lean","-j1","-M6144","-Ddebug.skipKernelTC=false","--root=.generated",".generated/OwnedAudit.lean"])
      .current_dir(&lean).stdin(Stdio::null()).status().map_err(|e|e.to_string())?;
    if !status.success(){return Err(format!("complete owned axiom audit failed: {status}"));}
    let audit=read_json(&root.join("build/owned-audit.json"))?;
    for field in ["owned_axioms","nonstandard_axiom_rows","missing_modules"]{
     if !audit[field].as_array().is_some_and(|a|a.is_empty()){return Err(format!("audit rejected {field}"));}
    }
   }
   let receipt=json!({"compiler_exit_success":true,"selected_source_modules":expected,
      "compiled_modules":names.len(),"complete_profile":complete,"historical_acceptance_transferred":false,
      "owned_axiom_audit_passed":complete,"all_claims_formalized":false});
   fs::write(root.join("build/lean-build.json"),serde_json::to_vec_pretty(&receipt).map_err(|e|e.to_string())?).map_err(|e|e.to_string())?;
   println!("{receipt}");
  },
  "emit-index"=> {
    let claims=read_json(&root.join("registry/claims.json"))?;
    let rows=claims["claims"].as_array().ok_or("missing cards")?;
    println!("-- Registry metadata only; not proofs of the claims.\nnamespace ResearchCommons.Registry\ndef claimIDs : List String := [");
    for (i,c) in rows.iter().enumerate(){println!("  {:?}{}",c["id"].as_str().ok_or("missing id")?,if i+1<rows.len(){","}else{""});}
    println!("]\ntheorem claim_count : claimIDs.length = {} := by decide\nend ResearchCommons.Registry",rows.len());
  },
  _=>return Err("usage: commons [check|coverage --strict|prepare|build [module-cap]|check-callers|prepare-certificates|build-certificates|emit-index]".into())
 }
 Ok(())
}
fn main(){if let Err(e)=run(){eprintln!("PACKAGE_INCOMPLETE: {e}");std::process::exit(2);}}
