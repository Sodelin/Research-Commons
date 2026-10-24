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
 let population_callers=scope=="population-certificate-callers";
 let residual_callers=scope=="residual-certificate-callers";
 let epoch_callers=scope=="epoch-certificate-callers";
 let word_callers=scope=="word-certificate-callers";
 let completion_callers=scope=="completion-certificate-callers";
 let moment_callers=scope=="moment-signature-callers";
 let jc_callers=scope=="jc69-branch-callers";
 let jc_tree_callers=scope=="jc69-tree-callers";
 let alignment_callers=scope=="msci-alignment-callers";
 let calibration_callers=scope=="rare-event-calibration-callers";
 let source_only=scope=="original-source-callers" || target_audit || population_callers || residual_callers || epoch_callers || word_callers || completion_callers || moment_callers || jc_callers || jc_tree_callers || alignment_callers || calibration_callers;
 let mut callers=if source_only {Vec::new()} else {vec![
    ("CMExample","cm-certificate",None),
    ("AffineSAT","affine-certificate",Some("sat")),
    ("AffineUNSAT","affine-certificate",Some("unsat"))]};
 if project=="lean" && !target_audit && !residual_callers && !moment_callers && !jc_callers && !jc_tree_callers && !alignment_callers && !calibration_callers {
  if !word_callers { callers.push(("OriginalTreeBank","source-certificate",Some("tree"))); }
  if word_callers { callers.push(("OriginalParallelBank","source-certificate",Some("parallel"))); }
  else if !population_callers && !epoch_callers && !completion_callers {
   callers.extend([("OriginalParallelBank","source-certificate",Some("parallel")),
    ("OriginalCellExclusion","source-certificate",Some("infeasible"))]);
  }
  if population_callers || scope=="full-profile-callers" {
   callers.extend([("EdgePopulation","population-certificate",Some("edge")),
    ("AncestralPopulation","population-certificate",Some("ancestral")),
    ("PathPopulation","population-certificate",Some("path"))]);
  }
 }
 if completion_callers || scope=="full-profile-callers" {
  callers.push(("AncestralCompletion","completion-certificate",None));
 }
 if moment_callers || scope=="full-profile-callers" {
  callers.push(("PositiveMomentSignature","moment-signature-certificate",None));
 }
 if alignment_callers || scope=="full-profile-callers" {
  callers.extend([("MSCIAlignmentCoherent","alignment-certificate",Some("coherent")),
    ("MSCIAlignmentIncoherent","alignment-certificate",Some("incoherent"))]);
 }
 if jc_callers || scope=="full-profile-callers" {
  callers.push(("JC69Branch","jc69-certificate",None));
 }
 if jc_tree_callers || scope=="full-profile-callers" {
  callers.push(("JC69TreeColumn","jc69-tree-certificate",None));
 }
 if calibration_callers {
  callers.extend([("RareEventFinite","rare-event-certificate",None),
    ("RareEventEmpty","rare-event-certificate",Some("empty"))]);
 }
 if word_callers || scope=="full-profile-callers" {
  callers.extend([("NaturalIndependentWord","word-cache-certificate",Some("independent")),
    ("NaturalCommonWord","word-cache-certificate",Some("common"))]);
 }
 if epoch_callers || scope=="full-profile-callers" {
  callers.push(("MixedPopulationEpoch","epoch-certificate",None));
 }
 if residual_callers || scope=="full-profile-callers" {
  callers.push(("ResidualTopK","residual-certificate",None));
 }
 let mut records=Vec::new();
 let mut names=owned.to_vec();
 for (module,binary,argument) in callers {
  let mut command=Command::new("cargo");
  command.args(["run","--locked","-p","research-commons-runtime","--bin",binary]);
  if let Some(a)=argument {command.args(["--",a]);}
  let output=command.current_dir(&root).stdin(Stdio::null()).output().map_err(|e|e.to_string())?;
  if !output.status.success(){return Err(format!("caller {binary} refused: {}",output.status));}
  let documents=if binary=="word-cache-certificate" {
   research_commons_package::certificate_bundle::decode(&output.stdout,module)?
  }else{
   if output.stdout.len()>262144{return Err(format!("caller {binary} exceeded source limit"));}
   std::str::from_utf8(&output.stdout).map_err(|e|e.to_string())?;
   vec![(module.to_owned(),output.stdout)]
  };
  for (module,source_bytes) in documents {
  let source=generated.join(format!("{module}.lean"));
  fs::write(&source,&source_bytes).map_err(|e|e.to_string())?;
  fs::write(evidence.join(format!("{module}.lean")),&source_bytes).map_err(|e|e.to_string())?;
  println!("LEAN CERTIFICATE {module}");
  println!("LEAN CERTIFICATE INPUT {module} {} bytes SHA256 {}",source_bytes.len(),research_commons_package::sha256(&source_bytes));
  let status=Command::new("lake").args(["env","lean","-j1","-M6144","-Ddebug.skipKernelTC=false","--root=.generated"])
      .arg("-o").arg(objects.join(format!("{module}.olean"))).arg(&source)
      .current_dir(&lean).stdin(Stdio::null()).status().map_err(|e|e.to_string())?;
  if !status.success(){return Err(format!("Lean rejected {module}: {status}"));}
  records.push(json!({"module":module,"source_sha256":research_commons_package::sha256(&source_bytes),
      "source_bytes":source_bytes.len(),"kernel_check_passed":true}));
  names.push(module.to_owned());
  }
 }
 let lock=read_json(&root.join("source-lock.json"))?;
 let base=root.join(lock["lean_profile"]["directory"].as_str().ok_or("missing profile directory")?);
 let template=fs::read_to_string(base.join("scripts/AuditTemplate.lean")).map_err(|e|e.to_string())?;
 let placeholder=r##"#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]"##;
 if template.matches(placeholder).count()!=1{return Err("unexpected caller audit template".into());}
 let selected=serde_json::to_string(&names).map_err(|e|e.to_string())?;
 let mut imports=String::from("import Lean\n");
 if !source_only {imports.push_str("import ResearchCommons\n");}
 for name in &names {imports.push_str(&format!("import {name}\n"));}
 let audit=imports+&template.replace(placeholder,&format!("#{selected}"))
    .replace("\"AUDIT-OWNED.json\"",&format!("\"../build/{scope}/caller-audit.json\""));
 fs::write(evidence.join("CallerAudit.lean"),&audit).map_err(|e|e.to_string())?;
 fs::write(generated.join("CallerAudit.lean"),audit).map_err(|e|e.to_string())?;
 let status=Command::new("lake").args(["env","lean","-j1","-M6144","-Ddebug.skipKernelTC=false","--root=.generated",".generated/CallerAudit.lean"])
    .current_dir(&lean).stdin(Stdio::null()).status().map_err(|e|e.to_string())?;
 if !status.success(){return Err(format!("caller axiom audit failed: {status}"));}
 let audit=read_json(&root.join("build").join(scope).join("caller-audit.json"))?;
 for field in ["owned_axioms","nonstandard_axiom_rows","missing_modules"] {
    if !audit[field].as_array().is_some_and(|v|v.is_empty()){return Err(format!("caller audit rejected {field}"));}
 }
 let receipt=json!({"profile":scope,"certificates":records,"owned_axiom_audit_passed":true,
    "scope":if calibration_callers {"Exact rational known-rate iid Bernoulli model, SAME all-sample randomized decision, separately sharp sum/worst/equal-prior risks. Particular n=3 and n=0 outputs rechecked against the actual product law and all-rule theorem. Limits remain UNKNOWN; no dependent/unknown-rate/biological sampling admission or universal Rust semantic refinement."} else if jc_tree_callers {"Actual complete64-entry native mutation channel on ONE retained labelled tree, coherent branch bank and SAME returned chronological ages/decoded pair matrix. All-finite conditional locus product is on that SAME tree. This is not actual demographic source admission, measure-level tree/source/channel law, bounded recurrence/observation equivalence or universal native/parser refinement."} else if alignment_callers {"Complete actual native finite coherent-parameter filters on supplied rational histories, including every omitted map. One epoch renaming is shared by both adjacent matrices and initial/root names stay fixed. This is not actual canonical physical-source admission, a genealogy-law equivalence proof, observability/coverage or universal native/parser refinement."} else if jc_callers {"Actual complete sixteen-entry rational JC branch table on the literal four-base/character encoding; every probability and row normalization checked against the constructed normalized clock-JC PMF at ONE returned finite time. Whole original timed-genealogy/event/locus/source admission and universal parser/native/channel refinement remain separate."} else if moment_callers {"Actual supplied rational positive target, complete M0..M2r signature, total mass equality against EVERY finite positive atomic rival and all further moments, under the explicit matching-signature premise. The stochastic reaction/stopped-law/derivative acquisition and general native refinement joins are separate."} else if completion_callers {"Particular complete native ancestral constant table with nonempty Copy/all-copy root support, unchanged actual infinite completion law and SAME positive returned source bank. Passive selected comb event is derived on the same decoded input. No whole-word/root admission, all-cap tester grammar/tomography or universal native/observer/provider claim."} else if word_callers {"Particular complete natural word tables on the same original hybrid source and returned bank; original parent0/parent1 order, all selected endpoint/register fields, total coefficient fibres and once-drawn register retained in BOTH mode examples. No whole-calendar/readout, completion, universal parser/native/provider/action/target/QE closure."} else if epoch_callers {"Particular full mixed-population native epoch table on the same original source/shared physical bank, all selected coefficient fibres and explicit original edge-then-ancestral order. Whole word/raw completion/readout, universal native/parser, physical census/action/target/QE joins remain separate."} else if residual_callers {"Particular complete supplied finite ensemble, same raw weights/class map, strict residual top-k set and conservation. Actual RNA support/sampling/class-mass computation, simultaneous stochastic events and universal native refinement remain separate."} else if population_callers {"Particular total ordered-copy population tables on the same original source; any positive population rates/durations. Whole epoch/word, parser/native universal refinement, global label/readout, history/source/action/QE joins are separate."} else if target_audit {"Only the exact target dependency closure and owned declarations; no particular native table/input/result/word/readout is certified."} else {"Particular exact rational and source-cell certificates for this selected profile; no observation-law, universal parser/native refinement, full source coverage or full registry closure."}});
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
 let keep_going=args.iter().any(|a|a=="--keep-going");
 args.retain(|a|a!="--reuse-retained"&&a!="--keep-going");
 let plan=prepare_lean(root)?;
 let lean=root.join("lean").canonicalize().map_err(|e|e.to_string())?;
 let out=lean.join(".lake/build/lib/lean");
 fs::create_dir_all(&out).map_err(|e|e.to_string())?;
 let (cap,target)=match args.as_slice() {
  []=>(None,None),
  [flag,name] if flag=="--target" => (None,Some(name.as_str())),
  [n]=>(Some(n.parse::<usize>().map_err(|_|"invalid module cap".to_owned())?),None),
  _=>return Err("usage: build [--reuse-retained] [--keep-going] [module-cap|--target Module]".into()),
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
 let mut failures=Vec::<serde_json::Value>::new();
 let mut blocked=Vec::<serde_json::Value>::new();
 let mut unavailable=std::collections::BTreeSet::<String>::new();
 let mut cache=if reuse {Some(research_commons_package::object_cache::RetainedObjects::open(root,&plan)?)} else {None};
 let mut receipt=json!({"status":"RUNNING","compiler_exit_success":false,"complete_profile":false,
   "target":target,"keep_going":keep_going,"failed_modules":[],"blocked_modules":[],"selected_source_modules":source_count,"full_profile_source_modules":all.len(),
   "source_graph_sha256":plan["source_graph_sha256"],"module_hashes":plan["module_hashes"],
   "objects":objects});
 let write_receipt=|value:&serde_json::Value|->Result<()> {
   fs::write(&receipt_path,serde_json::to_vec_pretty(value).map_err(|e|e.to_string())?).map_err(|e|e.to_string())
 };
 write_receipt(&receipt)?;
 for (i,name) in names.iter().enumerate(){
  // Continue only across independent ORIGINAL modules. A failed import is
  // unavailable, so no dependent compiler/audit can silently use a stale object.
  let blockers=if plan["module_imports"][name].is_array() {
    research_commons_package::failed_imports(&plan,name,&unavailable)?
  } else if name=="ResearchCommons.Registry" || name=="ResearchCommons" {
    unavailable.iter().cloned().collect::<Vec<_>>()
  } else {return Err(format!("missing import metadata: {name}"));};
  if !blockers.is_empty() {
    println!("BLOCKED LEAN {name}: {}",blockers.join(", "));
    unavailable.insert(name.clone());
    blocked.push(json!({"module":name,"unavailable_imports":blockers}));
    receipt["blocked_modules"]=json!(blocked);write_receipt(&receipt)?;
    continue;
  }
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
   failures.push(json!({"module":name,"compiler_exit":status.to_string()}));
   unavailable.insert(name.clone());
   receipt["status"]=json!(if keep_going {"RUNNING_WITH_FAILURES"}else{"FAILED"});
   receipt["failed_module"]=failures[0]["module"].clone();
   receipt["failed_modules"]=json!(failures);write_receipt(&receipt)?;
   if !keep_going {return Err(format!("Lean failed on {name}: {status}"));}
   continue;
  }
  if let Some(c)=cache.as_mut(){c.capture(name)?;}
  }
  objects.push(json!({"module":name,"reused_retained_object":cached,"sha256":research_commons_package::sha256(&fs::read(object).map_err(|e|e.to_string())?)}));
  receipt["objects"]=json!(objects);receipt["reused_retained_objects"]=json!(reused);write_receipt(&receipt)?;
 }
 if !failures.is_empty() || !blocked.is_empty() {
  receipt["status"]=json!("FAILED");
  receipt["failed_modules"]=json!(failures);receipt["blocked_modules"]=json!(blocked);
  receipt["compiled_modules"]=json!(objects.len()-reused);
  receipt["checked_or_reused_modules"]=json!(objects.len());
  receipt["reused_retained_objects"]=json!(reused);
  receipt["compiler_exit_success"]=json!(false);receipt["complete_profile"]=json!(false);
  receipt["owned_axiom_audit_passed"]=json!(false);write_receipt(&receipt)?;
  println!("{receipt}");
  return Err(format!("Lean dependency build rejected {} failed modules and {} blocked consumers",failures.len(),blocked.len()));
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

/// Reuse the existing complete object/digest validator for exact target and
/// full-profile callers. A declaration string alone grants no verification.
fn checked_objects(root:&std::path::Path,receipt:&serde_json::Value,selected:&[String])->Result<()> {
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
   Ok(())
}

fn checked_full_profile(root:&std::path::Path)->Result<Vec<String>> {
 let plan=prepare_lean(root)?;
 let receipt=read_json(&root.join("build/lean-build.json"))?;
 if receipt["compiler_exit_success"]!=true || receipt["complete_profile"]!=true ||
    receipt["owned_axiom_audit_passed"]!=true ||
    receipt["source_graph_sha256"]!=plan["source_graph_sha256"] ||
    receipt["module_hashes"]!=plan["module_hashes"] {
  return Err("no exact complete audited source build for claim exports".into());
 }
 let mut selected=plan["order"].as_array().ok_or("missing complete order")?.iter()
  .map(|v|v.as_str().map(str::to_owned).ok_or("invalid complete module".to_owned())).collect::<Result<Vec<_>>>()?;
 selected.extend(["ResearchCommons.Registry".into(),"ResearchCommons".into()]);
 checked_objects(root,&receipt,&selected)?;
 Ok(selected)
}

fn check_exports(root:&std::path::Path,target:Option<&str>,claims:&[String])->Result<()> {
 research_commons_package::check_package(root)?;
 let canonical=read_json(&root.join("registry/claims.json"))?;
 let bindings=read_json(&root.join("integration/claims.json"))?;
 let mut plan=research_commons_package::exports::plan_for_claims(&canonical,&bindings,claims)?;
 let selected=if let Some(module)=target{checked_target(root,module)?}else{checked_full_profile(root)?};
 let source_plan=prepare_lean(root)?;
 for module in plan["imports"].as_array().ok_or("missing export imports")?{
  let module=module.as_str().ok_or("invalid export import")?;
  let required=research_commons_package::selected_modules(&source_plan,module)?;
  if required.iter().any(|n|!selected.contains(n)){
   return Err(format!("selected context omits an export dependency of {module}"));
  }
 }
 if target.is_some(){
  check_callers_at(root,"lean",&selected,"retained-target-audit")?;
 }
 let selection_key=if claims.is_empty(){None}else{
  Some(research_commons_package::sha256(&serde_json::to_vec(&plan["requested_claims"]).map_err(|e|e.to_string())?))
 };
 let stem=selection_key.as_ref().map(|key|format!("ClaimExportsScoped{key}")).unwrap_or_else(||"ClaimExports".into());
 let relative=format!(".generated/{stem}.lean");
 let document=plan["document"].as_str().ok_or("missing exact export document")?;
 let lean=root.join("lean");let source=lean.join(&relative);
 fs::write(&source,document).map_err(|e|e.to_string())?;
 let status=Command::new("lake").args(["env","lean","-j1","-M6144",
  "-Ddebug.skipKernelTC=false","--root=.generated"]).arg(&relative)
  .current_dir(&lean).stdin(Stdio::null()).status().map_err(|e|e.to_string())?;
 if !status.success(){return Err(format!("Lean rejected a named claim export: {status}"));}
 let hash=research_commons_package::sha256(document.as_bytes());
 plan.as_object_mut().ok_or("invalid export plan")?.remove("document");
 plan["document_sha256"]=json!(hash);
 plan["kernel_check_passed"]=json!(true);
 plan["exact_source_context_and_owned_audit_revalidated"]=json!(true);
 plan["target"]=json!(target);
 plan["complete_profile"]=json!(target.is_none());
 plan["all_claims_formalized"]=json!(false);
 let destination=if let Some(key)=selection_key {
  let directory=root.join("build").join(format!("claim-exports-{key}"));
  fs::create_dir_all(&directory).map_err(|e|e.to_string())?;
  let audit=fs::read(root.join("build/retained-target-audit/caller-audit.json")).map_err(|e|e.to_string())?;
  fs::write(directory.join("owned-audit.json"),&audit).map_err(|e|e.to_string())?;
  let audit_source=fs::read(root.join("build/retained-target-audit/sources/CallerAudit.lean")).map_err(|e|e.to_string())?;
  fs::write(directory.join("OwnedAudit.lean"),&audit_source).map_err(|e|e.to_string())?;
  plan["owned_audit_source_sha256"]=json!(research_commons_package::sha256(&audit_source));
  fs::copy(&source,directory.join("ClaimExports.lean")).map_err(|e|e.to_string())?;
  plan["owned_audit_sha256"]=json!(research_commons_package::sha256(&audit));
  plan["source_graph_sha256"]=source_plan["source_graph_sha256"].clone();
  plan["checked_modules"]=json!(&selected);
  plan["module_hashes"]=serde_json::Value::Object(selected.iter()
   .map(|name|(name.clone(),source_plan["module_hashes"][name].clone()))
   .collect::<serde_json::Map<String,serde_json::Value>>());
  plan["source_commit"]=json!(env::var("GITHUB_SHA").ok());
  plan["github_run_id"]=json!(env::var("GITHUB_RUN_ID").ok());
  plan["artifact_directory"]=json!(format!("build/claim-exports-{key}"));
  directory.join("verification.json")
 }else{root.join("build/claim-export-verification.json")};
 fs::write(destination,serde_json::to_vec_pretty(&plan).map_err(|e|e.to_string())?).map_err(|e|e.to_string())?;
 println!("{plan}");Ok(())
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
   checked_objects(root,&receipt,&selected)?;
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
  "check-exports"=>{
   let mut target=None;let mut claims=Vec::new();
   while let Some(flag)=args.next(){
    match flag.as_str(){
     "--target" if target.is_none()=>target=Some(args.next().ok_or("--target needs a module")?),
     "--claim"=>claims.push(args.next().ok_or("--claim needs an exact canonical ID")?),
     _=>return Err("usage: check-exports [--target Module] [--claim ID ...]".into()),
    }
   }
   if !claims.is_empty() && target.is_none(){return Err("selected claims require an explicit checked --target".into());}
   check_exports(&root,target.as_deref(),&claims)?;
  },
  "prepare-certificates"=>println!("{}",research_commons_package::prepare_certificate_profile(&root)?),
  "build-certificates"=>build_certificates(&root)?,
  "build"=>build_lean(&root,args.collect())?,
  "check-source-callers"=>{
   let selected=checked_target(&root,"OriginalCodeChartReceiver")?;
   check_callers_at(&root,"lean",&selected,"original-source-callers")?;
  },
  "check-population-callers"=>{
   let selected=checked_target(&root,"ResearchCommons.Integration.Population")?;
   check_callers_at(&root,"lean",&selected,"population-certificate-callers")?;
  },
  "check-alignment-callers"=>{
   let target=match args.collect::<Vec<_>>().as_slice(){
    []=>"ResearchCommons.MSCI.Alignment",
    [flag] if flag=="--in-exports"=>"ResearchCommons.Integration.Exports",
    _=>return Err("usage: check-alignment-callers [--in-exports]".into()),
   };
   let selected=checked_target(&root,target)?;
   let plan=prepare_lean(&root)?;
   let required=research_commons_package::selected_modules(&plan,"ResearchCommons.MSCI.Alignment")?;
   if required.iter().any(|n|!selected.contains(n)){
    return Err("actual coherent alignment dependencies missing from checked context".into());
   }
   check_callers_at(&root,"lean",&selected,"msci-alignment-callers")?;
  },
  "check-calibration-callers"=>{
   let target=match args.collect::<Vec<_>>().as_slice(){
    []=>"ResearchCommons.Calibration.RareEvent",
    [flag] if flag=="--in-exports"=>"ResearchCommons.Integration.Exports",
    _=>return Err("usage: check-calibration-callers [--in-exports]".into()),
   };
   let selected=checked_target(&root,target)?;
   let plan=prepare_lean(&root)?;
   let required=research_commons_package::selected_modules(&plan,"ResearchCommons.Calibration.RareEvent")?;
   if required.iter().any(|n|!selected.contains(n)){
    return Err("actual rare-event product-law dependencies missing from checked context".into());
   }
   check_callers_at(&root,"lean",&selected,"rare-event-calibration-callers")?;
  },
  "check-jc-tree-callers"=>{
   let target=match args.collect::<Vec<_>>().as_slice(){
    []=>"ResearchCommons.MSCI.JC69Tree",
    [flag] if flag=="--in-exports"=>"ResearchCommons.Integration.Exports",
    _=>return Err("usage: check-jc-tree-callers [--in-exports]".into()),
   };
   let selected=checked_target(&root,target)?;
   let plan=prepare_lean(&root)?;
   let required=research_commons_package::selected_modules(&plan,"ResearchCommons.MSCI.JC69Tree")?;
   if required.iter().any(|n|!selected.contains(n)){
    return Err("actual JC tree channel dependencies missing from checked context".into());
   }
   check_callers_at(&root,"lean",&selected,"jc69-tree-callers")?;
  },
  "check-jc-callers"=>{
   let target=match args.collect::<Vec<_>>().as_slice(){
    []=>"ResearchCommons.MSCI.JC69",
    [flag] if flag=="--in-exports"=>"ResearchCommons.Integration.Exports",
    _=>return Err("usage: check-jc-callers [--in-exports]".into()),
   };
   let selected=checked_target(&root,target)?;
   let plan=prepare_lean(&root)?;
   let required=research_commons_package::selected_modules(&plan,"ResearchCommons.MSCI.JC69")?;
   if required.iter().any(|n|!selected.contains(n)){
    return Err("actual JC branch caller dependencies missing from checked context".into());
   }
   check_callers_at(&root,"lean",&selected,"jc69-branch-callers")?;
  },
  "check-moment-callers"=>{
   let target=match args.collect::<Vec<_>>().as_slice(){
    []=>"ResearchCommons.Integration.PositiveMoments",
    [flag] if flag=="--in-exports"=>"ResearchCommons.Integration.Exports",
    _=>return Err("usage: check-moment-callers [--in-exports]".into()),
   };
   let selected=checked_target(&root,target)?;
   let plan=prepare_lean(&root)?;
   let required=research_commons_package::selected_modules(&plan,"ResearchCommons.Integration.PositiveMoments")?;
   if required.iter().any(|n|!selected.contains(n)){
    return Err("actual moment caller dependencies missing from the checked context".into());
   }
   check_callers_at(&root,"lean",&selected,"moment-signature-callers")?;
  },
  "check-residual-callers"=>{
   let selected=checked_target(&root,"ResearchCommons.Claims.RNA")?;
   check_callers_at(&root,"lean",&selected,"residual-certificate-callers")?;
  },
  "check-completion-callers"=>{
   let selected=checked_target(&root,"ResearchCommons.Integration.Completion")?;
   check_callers_at(&root,"lean",&selected,"completion-certificate-callers")?;
  },
  "check-word-callers"=>{
   let selected=checked_target(&root,"ResearchCommons.Integration.WordCache")?;
   check_callers_at(&root,"lean",&selected,"word-certificate-callers")?;
  },
  "check-epoch-callers"=>{
   let selected=checked_target(&root,"ResearchCommons.Integration.Epoch")?;
   check_callers_at(&root,"lean",&selected,"epoch-certificate-callers")?;
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
  _=>return Err("usage: commons [check|coverage --strict|prepare|build [module-cap|--target Module]|check-callers|check-source-callers|check-population-callers|check-moment-callers [--in-exports]|check-jc-callers [--in-exports]|check-jc-tree-callers [--in-exports]|check-alignment-callers [--in-exports]|check-residual-callers|check-epoch-callers|check-word-callers|check-completion-callers|check-exports|audit-target Module|prepare-certificates|build-certificates|emit-index]".into())
 }
 Ok(())
}
fn main(){if let Err(e)=run(){eprintln!("PACKAGE_INCOMPLETE: {e}");std::process::exit(2);}}
