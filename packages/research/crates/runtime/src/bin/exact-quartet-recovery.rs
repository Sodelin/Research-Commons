//! Supplied exact support -> OLD shared-cache unknown-order or supplied-circle recovery.
//! RAM stdin/stdout only. No network, daemon, source census or biological oracle.
use research_commons_runtime::exact_query::{self,Limits,Quartet};
use serde_json::{json,Value};
use std::{collections::{BTreeMap,BTreeSet},io::{self,Read,Write}};

const FRAME: usize = 1048576;
fn integers(v:&Value, length:Option<usize>) -> Result<Vec<u64>,String> {
    let xs=v.as_array().ok_or("integer array required")?;
    if length.is_some_and(|n|n!=xs.len()) { return Err("array arity".into()); }
    xs.iter().map(|x|x.as_u64().ok_or_else(||"unsigned integer required".into())).collect()
}
fn run() -> Result<Value,String> {
    let mut input=Vec::new();
    io::stdin().take((FRAME+1) as u64).read_to_end(&mut input).map_err(|e|e.to_string())?;
    if input.len()>FRAME { return Err("UNKNOWN: input frame limit".into()); }
    let request:Value=serde_json::from_slice(&input).map_err(|e|format!("JSON: {e}"))?;
    let object=request.as_object().ok_or("request object required")?;
    if object.keys().any(|k|!["circle","labels","answers"].contains(&k.as_str())) {
        return Err("unknown request field".into());
    }
    let learned=request.get("labels").is_some();
    if learned==request.get("circle").is_some() {return Err("exactly one of labels or circle required".into());}
    let circle=integers(request.get(if learned{"labels"}else{"circle"}).ok_or("labels/circle required")?,None)?;
    if circle.len()>128 { return Err("UNKNOWN: CLI taxon limit".into()); }
    let labels:BTreeSet<_>=circle.iter().copied().collect();
    let supplied=request.get("answers").and_then(Value::as_array).ok_or("answers array required")?;
    if supplied.len()>16384 { return Err("UNKNOWN: supplied answer count limit".into()); }
    let mut answers=BTreeMap::new();
    for entry in supplied {
        let entry=entry.as_object().ok_or("answer object required")?;
        if entry.keys().any(|k|!["quartet","mask"].contains(&k.as_str())) {
            return Err("unknown answer field".into());
        }
        let q:Quartet=integers(entry.get("quartet").ok_or("quartet required")?,Some(4))?
            .try_into().map_err(|_|"quartet arity")?;
        if !q.windows(2).all(|w|w[0]<w[1]) || q.iter().any(|x|!labels.contains(x)) {
            return Err("sorted distinct original-label quartet required".into());
        }
        let mask=entry.get("mask").and_then(Value::as_u64).ok_or("integer mask required")?;
        if !(1..=7).contains(&mask) { return Err("nonempty 1/2/4 support mask required".into()); }
        if answers.insert(q,mask as u8).is_some() { return Err("duplicate supplied quartet".into()); }
    }
    let limits=Limits{taxa:128,unique_queries:16384,..Limits::default()};
    let (circle,recovered,order_info)=if learned {
        let joint=exact_query::order::recover_unordered(&circle,|q|answers.get(&q).copied()
            .ok_or("missing exact support answer"),exact_query::order::OrderLimits{search:limits,tree_work:4_194_304})
            .map_err(|e|format!("UNKNOWN/REFUSED: {e:?}"))?;
        let info=json!({"order_queries":joint.order_queries,"sparse_requests":joint.sparse_requests,
            "order_predicates":joint.order_predicates,"centroid_steps":joint.centroid_steps,
            "internal_vertices":joint.internal_vertices,"retired_vertices":joint.retired_vertices,
            "tree_work":joint.tree_work});
        (joint.circle,joint.recovery,info)
    }else{
        let recovered=exact_query::recover(&circle,|q|answers.get(&q).copied()
            .ok_or("missing exact support answer"),limits)
            .map_err(|e|format!("UNKNOWN/REFUSED: {e:?}"))?;
        (circle,recovered,Value::Null)
    };
    let trace:Vec<_>=recovered.cache.iter().map(|(q,m)|json!({"quartet":q,"mask":m})).collect();
    let chronological:Vec<_>=recovered.query_trace.iter().map(|(q,m)|json!({"quartet":q,"mask":m})).collect();
    Ok(json!({"status":"conditional_recovery","circle":circle,
        "order_mode":if learned{"learned"}else{"supplied"},"order_acquisition":order_info,
        "gap_pairs":recovered.gap_pairs,"unique_queries":recovered.cache.len(),
        "rectangle_tests":recovered.rectangle_tests,
        "positive_internal_nodes":recovered.positive_internal_nodes,
        "max_search_depth":recovered.max_search_depth,"original_answer_cache":trace,
        "chronological_query_trace":chronological,
        "assumptions":[if learned{"oracle admits the original complete circular binary-family promise"}else{"supplied order is common to the complete binary displayed-tree family"},
            "every oracle mask is its COMPLETE distinct resolved topology set"],
        "not_established":["global original-source admission","universal algorithm/source/query-charge formal refinement",
            "whole asymptotic theorem formal refinement","biological data-to-oracle",
            "exact finite minimax","source/controller/result authentication"]}))
}
fn main() {
    let result=run().and_then(|v|serde_json::to_vec(&v).map_err(|e|e.to_string()));
    match result {
        Ok(mut output) if output.len()<=FRAME => {
            output.push(b'\n');
            if io::stdout().write_all(&output).is_err() { std::process::exit(2); }
        }
        Ok(_) => { eprintln!("UNKNOWN: output frame limit");std::process::exit(2); }
        Err(e) => { eprintln!("{e}");std::process::exit(2); }
    }
}
