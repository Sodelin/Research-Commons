fn main() {
 let mode=std::env::args().nth(1).unwrap_or_else(||"independent".into());
 match research_commons_runtime::word_certificate::example(&mode) {
  Ok(source)=>print!("{source}"),
  Err(e)=>{eprintln!("WORD_CERTIFICATE_REFUSED: {e:?}");std::process::exit(2);}
 }
}
