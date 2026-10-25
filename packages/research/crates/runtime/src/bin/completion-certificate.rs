fn main() {
 match research_commons_runtime::completion_certificate::example() {
  Ok(source)=>print!("{source}"),
  Err(e)=>{eprintln!("COMPLETION_CERTIFICATE_REFUSED: {e:?}");std::process::exit(2);}
 }
}
