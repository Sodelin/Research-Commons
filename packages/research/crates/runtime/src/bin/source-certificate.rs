//! Public request reader. Input and emitted proof remain in process memory;
//! the caller explicitly chooses any persistence or later Lean verification.
use std::io::Read;
fn run()->Result<String,String> {
 let args=std::env::args().skip(1).collect::<Vec<_>>();
 match args.as_slice() {
  []=>research_commons_runtime::source_certificate::example("tree").map_err(|e|format!("{e:?}")),
  [which] if matches!(which.as_str(),"tree"|"parallel"|"infeasible") =>
    research_commons_runtime::source_certificate::example(which).map_err(|e|format!("{e:?}")),
  [flag,namespace] if flag=="--stdin" => {
   let mut input=Vec::new();
   std::io::stdin().lock().take(65537).read_to_end(&mut input).map_err(|e|e.to_string())?;
   if input.len()>65536{return Err("original RC1 request exceeds65536 bytes".into());}
   research_commons_runtime::source_certificate::emit(&input,namespace,true,262144).map_err(|e|format!("{e:?}"))
  },
  _=>Err("usage: source-certificate [tree|parallel|infeasible|--stdin Namespace]".into()),
 }
}
fn main() {
 match run() {
  Ok(source)=>print!("{source}"),
  Err(error)=>{eprintln!("SOURCE_CERTIFICATE_REFUSED: {error}");std::process::exit(2);}
 }
}
