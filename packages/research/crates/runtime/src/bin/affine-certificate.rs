fn main() {
    let exclusion=match std::env::args().nth(1).as_deref() {
        Some("sat")=>false, Some("unsat")=>true,
        _=>{eprintln!("usage: affine-certificate sat|unsat");std::process::exit(2);}
    };
    match research_commons_runtime::affine_certificate::example(exclusion) {
        Ok(source)=>print!("{source}"),
        Err(e)=>{eprintln!("CERTIFICATE_REFUSED: {e:?}");std::process::exit(2);}
    }
}
