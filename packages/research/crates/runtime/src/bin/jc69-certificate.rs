fn main(){
 match research_commons_runtime::jc69::example(){
  Ok(source)=>println!("{source}"),
  Err(e)=>{eprintln!("JC69_CERTIFICATE_REFUSED: {e:?}");std::process::exit(2);}
 }
}
