//! Standalone supplied-fit bridge; stdin/file modes use identical response bytes.
use calendar_cli::source_fit;
use parity_solver::source_fit_bank::{MAX_REQUEST_BYTES, MAX_RESULT_BYTES};
use std::{fs, io::{self, Read, Write}, path::Path};

fn read(path: &str, limit: usize) -> Result<Vec<u8>, &'static str> {
    let mut data = Vec::new();
    if path == "-" {
        io::stdin().lock().take(limit as u64 + 1).read_to_end(&mut data).map_err(|_| "SOURCE_FIT_READ")?;
    } else {
        let metadata = fs::symlink_metadata(Path::new(path)).map_err(|_| "SOURCE_FIT_FILE")?;
        if !metadata.is_file() || metadata.len() > limit as u64 { return Err("SOURCE_FIT_FILE"); }
        fs::File::open(path).map_err(|_| "SOURCE_FIT_FILE")?.take(limit as u64 + 1)
            .read_to_end(&mut data).map_err(|_| "SOURCE_FIT_READ")?;
    }
    if data.len() > limit { return Err("SOURCE_FIT_BYTES"); }
    Ok(data)
}
fn check(request: &str, response: &str, forward: bool) -> Result<source_fit::Frame, &'static str> {
    let (r, c) = (read(request, MAX_REQUEST_BYTES)?, read(response, MAX_RESULT_BYTES)?);
    let replay = if forward { calendar_cli::source_fit_forward::natural(&r) } else { source_fit::bind(&r) };
    let accepted = replay.exit_code != 1 && replay.bytes == c;
    Ok(source_fit::Frame { bytes: format!("{{\"schema\":\"source_fit_check_v1\",\"status\":\"{}\"}}\n",
        if accepted { "ACCEPT" } else { "REJECT" }).into_bytes(), exit_code: if accepted { 0 } else { 1 } })
}
fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args == ["--help"] || args == ["-h"] {
        println!("source-fit-solver bank [REQUEST|-]\nsource-fit-solver readout [REQUEST|-]\nsource-fit-solver check REQUEST RESPONSE\nsource-fit-solver check-readout REQUEST RESPONSE\n\nChecks a supplied exact assignment and sparse equation trace, then emits one symbolic physical bank.\nReadout selects natural ROOTED_UNRANKED_COMPLETE and evaluates the completed rooted law with the same bank.\nChecks replay the native computation and require identical response bytes.\nSYMBOLIC_BANK/TABLE exit0; UNKNOWN/UNSUPPORTED exit2; invalid input exits1.\nNo source-equation provenance or full solver completion is inferred.");
        return;
    }
    let result = match args.as_slice() {
        [] => read("-", MAX_REQUEST_BYTES).map(|r| source_fit::bind(&r)),
        [cmd] if cmd == "bank" => read("-", MAX_REQUEST_BYTES).map(|r| source_fit::bind(&r)),
        [cmd,path] if cmd == "bank" => read(path, MAX_REQUEST_BYTES).map(|r| source_fit::bind(&r)),
        [cmd] if cmd == "readout" => read("-", MAX_REQUEST_BYTES).map(|r| calendar_cli::source_fit_forward::natural(&r)),
        [cmd,path] if cmd == "readout" => read(path, MAX_REQUEST_BYTES).map(|r| calendar_cli::source_fit_forward::natural(&r)),
        [cmd,request,response] if cmd == "check" => check(request, response, false),
        [cmd,request,response] if cmd == "check-readout" => check(request, response, true),
        _ => Err("SOURCE_FIT_ARGUMENTS"),
    };
    let frame = result.unwrap_or_else(|code| if code == "SOURCE_FIT_ARGUMENTS" || code == "SOURCE_FIT_BYTES" {
        source_fit::error(code)
    } else { source_fit::execution_error(code) });
    if io::stdout().lock().write_all(&frame.bytes).is_err() { std::process::exit(1); }
    std::process::exit(i32::from(frame.exit_code));
}
