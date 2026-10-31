fn main(){
 let args=std::env::args().skip(1).collect::<Vec<_>>();
 let mode=match args.as_slice(){[]=>false,[s]if s=="zero"=>true,
  _=>{eprintln!("COUNT_PREFIX_REFUSED: usage count-prefix-certificate [zero]");std::process::exit(2);}};
 let limits=research_commons_runtime::count_prefix::Limits::default();
 let result=research_commons_runtime::count_prefix::example(mode,limits)
  .and_then(|c|c.lean(if mode{"CountPrefixZero"}else{"CountPrefixOrdinary"},limits));
 match result{Ok(source)=>print!("{source}"),Err(error)=>{
  eprintln!("COUNT_PREFIX_REFUSED: {error:?}");std::process::exit(2);}}
}
