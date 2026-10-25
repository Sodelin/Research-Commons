fn main() {
 match research_commons_runtime::epoch_certificate::example() {
  Ok(source)=>print!("{source}"),
  Err(e)=>{eprintln!("EPOCH_CERTIFICATE_REFUSED: {e:?}");std::process::exit(2);}
 }
}
