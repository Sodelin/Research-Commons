use research_commons_runtime::moments::{example,lean_certificate,Limits};
fn main() {
    let result=example().and_then(|(s,t)|lean_certificate(&s,&t,Limits::default()));
    match result {
        Ok(source)=>print!("{source}"),
        Err(error)=>{eprintln!("CERTIFICATE_REFUSED: {error}");std::process::exit(2);}
    }
}
