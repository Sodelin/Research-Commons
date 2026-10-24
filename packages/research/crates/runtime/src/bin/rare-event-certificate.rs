fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let empty = match args.as_slice() {
        [] => false,
        [s] if s == "empty" => true,
        _ => { eprintln!("usage: rare-event-certificate [empty]"); std::process::exit(2); }
    };
    match research_commons_runtime::calibration::example_certificate(empty) {
        Ok(source) => print!("{source}"),
        Err(error) => { eprintln!("REFUSED/UNKNOWN: {error:?}"); std::process::exit(2); }
    }
}
