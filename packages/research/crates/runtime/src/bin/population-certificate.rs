fn main() {
 let kind=std::env::args().nth(1).unwrap_or_else(||"edge".into());
 let result=match kind.as_str() {
  "edge"=>research_commons_runtime::population_certificate::example(false),
  "ancestral"=>research_commons_runtime::population_certificate::example(true),
  "path"=>research_commons_runtime::population_certificate::path_example(),
  _=>Err(research_commons_runtime::population_certificate::Error::Invalid("example name")),
 };
 match result {
  Ok(source)=>print!("{source}"),
  Err(error)=>{eprintln!("POPULATION_CERTIFICATE_REFUSED: {error:?}");std::process::exit(2);}
 }
}
