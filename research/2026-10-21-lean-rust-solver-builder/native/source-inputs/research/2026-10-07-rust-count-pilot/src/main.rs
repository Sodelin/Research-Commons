#![forbid(unsafe_code)]
use exact_count_certificate::{certify, parse, BigUint};
use std::env;
use std::process::ExitCode;

const HELP: &str = "Exact normalized Poisson-prefix certificate pilot\n\nUsage: count-certificate A EPSILON [--max-steps N] [--weights]\n\nA >= 0; 0 < EPSILON < 1. Exact ASCII rational/decimal/scientific inputs.\nWithout --max-steps, the cutoff search is unbounded. --max-steps 0 inspects none.\nA RESOURCE_LIMIT is not a negative source/target conclusion.\nBoth mathematical outcomes exit 0. Invalid input/usage exits 2, no JSON.\nTransport: at most 4096 bytes/token; exponent magnitude at most 4096.\n";

fn run() -> Result<(), String> {
    let mut positionals = Vec::new();
    let mut max_steps: Option<BigUint> = None;
    let mut include_weights = false;
    let mut args = env::args_os().skip(1)
        .map(|arg| arg.into_string().map_err(|_| "arguments must be UTF-8".to_owned()))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => { print!("{HELP}"); return Ok(()); }
            "--weights" => {
                if include_weights { return Err("duplicate --weights".to_owned()); }
                include_weights = true;
            }
            "--max-steps" => {
                if max_steps.is_some() { return Err("duplicate --max-steps".to_owned()); }
                let value = args.next().ok_or("--max-steps requires a value")?;
                max_steps = Some(parse::natural(&value).map_err(|e| e.to_string())?);
            }
            _ if arg.starts_with("--max-steps=") => {
                if max_steps.is_some() { return Err("duplicate --max-steps".to_owned()); }
                max_steps = Some(parse::natural(&arg[12..]).map_err(|e| e.to_string())?);
            }
            _ if arg.starts_with("--") => return Err(format!("unknown option: {arg}")),
            _ => positionals.push(arg),
        }
    }
    if positionals.len() != 2 { return Err("expected exactly A and EPSILON; use --help".to_owned()); }
    let a = parse::rational(&positionals[0]).map_err(|e| format!("A: {e}"))?;
    let epsilon = parse::rational(&positionals[1]).map_err(|e| format!("EPSILON: {e}"))?;
    let result = certify(&a, &epsilon, max_steps.as_ref()).map_err(|e| e.to_string())?;
    println!("{}", result.to_legacy_json(include_weights));
    Ok(())
}
fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => { eprintln!("count-certificate: {error}"); ExitCode::from(2) }
    }
}
