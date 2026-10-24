fn main(){
 let input=std::env::args().skip(1).map(|x|x.parse::<usize>()).collect::<Result<Vec<_>,_>>();
 let result=match input{
  Ok(v)if v.len()==3=>research_commons_runtime::msci::observation_cutoff(v[0],v[1],v[2],
   research_commons_runtime::msci::Limits::default()).and_then(|b|b.json()),
  _=>Err(research_commons_runtime::msci::Error::Invalid("usage: msci-cutoff n J P")),
 };
 match result{Ok(document)=>println!("{document}"),Err(e)=>{
  eprintln!("MSCI_CUTOFF_REFUSED: {e:?}");std::process::exit(2);}}
}
