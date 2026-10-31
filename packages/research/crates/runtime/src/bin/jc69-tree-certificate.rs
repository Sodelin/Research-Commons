fn main(){
 match research_commons_runtime::jc69_tree::example_certificate(){
  Ok(source)=>print!("{source}"),
  Err(e)=>{eprintln!("UNKNOWN: {e:?}");std::process::exit(2);}
 }
}
