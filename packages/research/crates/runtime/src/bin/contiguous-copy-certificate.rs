fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let wrapped = match args.as_slice() {
        [] => false,
        [s] if s == "wrapped" => true,
        _ => { eprintln!("usage: contiguous-copy-certificate [wrapped]"); std::process::exit(2); }
    };
    match research_commons_runtime::contiguous_copies::example_certificate(wrapped) {
        Ok(source) => print!("{source}"),
        Err(e) => { eprintln!("REFUSED/UNKNOWN: {e:?}"); std::process::exit(2); }
    }
}
