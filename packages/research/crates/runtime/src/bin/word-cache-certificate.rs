fn main() {
 let mode=std::env::args().nth(1).unwrap_or_else(||"independent".into());
 match research_commons_runtime::word_cache_certificate::example(&mode).and_then(|b|b.json()) {
  Ok(source)=>println!("{source}"),
  Err(e)=>{eprintln!("WORD_CACHE_CERTIFICATE_REFUSED: {e:?}");std::process::exit(2);}
 }
}
