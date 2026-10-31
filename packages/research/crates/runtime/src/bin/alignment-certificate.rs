fn main(){
 let incoherent=match std::env::args().nth(1).as_deref(){
  None|Some("coherent")=>false,Some("incoherent")=>true,
  _=>{eprintln!("usage: alignment-certificate [coherent|incoherent]");std::process::exit(2);}
 };
 match research_commons_runtime::alignment::example(incoherent){
  Ok(s)=>print!("{s}"),Err(e)=>{eprintln!("{e:?}");std::process::exit(2);}
 }
}
