fn main() {
 let limits=research_commons_runtime::residual_certificate::Limits::default();
 let result=research_commons_runtime::residual_certificate::example().and_then(|c|c.lean_certificate(limits));
 match result {
  Ok(source)=>print!("{source}"),
  Err(error)=>{eprintln!("RESIDUAL_CERTIFICATE_REFUSED: {error:?}");std::process::exit(2);}
 }
}
