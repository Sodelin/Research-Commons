use research_commons_runtime::moments::{example,lean_signature_certificate,SignatureLimits};
fn main(){
 let reference=match example(){Ok((s,_))=>s,Err(e)=>{eprintln!("CERTIFICATE_REFUSED: {e}");std::process::exit(2);}};
 match lean_signature_certificate(&reference,SignatureLimits::default()){
  Ok(source)=>print!("{source}"),
  Err(error)=>{eprintln!("CERTIFICATE_REFUSED: {error:?}");std::process::exit(2);}
 }
}
