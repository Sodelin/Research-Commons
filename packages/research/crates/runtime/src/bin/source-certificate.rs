fn main() {
 let which=std::env::args().nth(1).unwrap_or_else(||"tree".into());
 match research_commons_runtime::source_certificate::example(&which) {
  Ok(source)=>print!("{source}"),
  Err(error)=>{eprintln!("SOURCE_CERTIFICATE_REFUSED: {error:?}");std::process::exit(2);}
 }
}
