use research_commons_runtime::nanuq_noise::{example, Limits};
fn main() -> Result<(), String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let cycle = match args.as_slice() {
        [] => false,
        [x] if x == "cycle" => true,
        _ => return Err("usage: nanuq-noise-certificate [cycle]".into()),
    };
    let limits = Limits::default();
    let recovery = example(cycle,limits).map_err(|e| format!("{e:?}"))?;
    let name = if cycle { "RawNoiseCycle" } else { "RawNoiseTree" };
    print!("{}",recovery.lean_certificate(name,limits).map_err(|e| format!("{e:?}"))?);
    Ok(())
}
