//! General supplied-calendar frontend; native checking is complete forward replay.
use calendar_cli::{request::MAX_REQUEST_BYTES, response::{canonical_json, ErrorKind, Frame, MAX_RESULT_BYTES}};
use serde_json::json;
use std::{ffi::OsString, fs, io::{self, Read, Write}, path::PathBuf};

enum Command { Solve(Option<PathBuf>), Check(PathBuf, PathBuf) }
fn command(args: &[OsString]) -> Result<Command, &'static str> {
    if args.is_empty() { return Ok(Command::Solve(None)); }
    if args[0] == "solve" {
        return match &args[1..] {
            [] => Ok(Command::Solve(None)),
            [flag,path] if flag == "--request" => Ok(Command::Solve(Some(PathBuf::from(path)))),
            _ => Err("SOURCE_CALENDAR_ARGUMENTS"),
        };
    }
    if args[0] == "check" && args.len() == 5 {
        let mut request = None;
        let mut certificate = None;
        for pair in args[1..].chunks_exact(2) {
            match pair[0].to_str() {
                Some("--request") if request.is_none() => request = Some(PathBuf::from(&pair[1])),
                Some("--certificate") if certificate.is_none() => certificate = Some(PathBuf::from(&pair[1])),
                _ => return Err("SOURCE_CALENDAR_ARGUMENTS"),
            }
        }
        if let (Some(request),Some(certificate)) = (request,certificate) {
            return Ok(Command::Check(request,certificate));
        }
    }
    Err("SOURCE_CALENDAR_ARGUMENTS")
}
fn read(path: Option<&PathBuf>, max_bytes: usize) -> Result<Vec<u8>, &'static str> {
    let mut bytes = Vec::new();
    if let Some(path) = path {
        let metadata = fs::symlink_metadata(path).map_err(|_| "SOURCE_CALENDAR_FILE")?;
        if !metadata.is_file() { return Err("SOURCE_CALENDAR_FILE"); }
        if metadata.len() > max_bytes as u64 { return Err("SOURCE_CALENDAR_BYTES"); }
        fs::File::open(path).map_err(|_| "SOURCE_CALENDAR_FILE")?.take(max_bytes as u64+1)
            .read_to_end(&mut bytes).map_err(|_| "SOURCE_CALENDAR_READ")?;
    } else {
        io::stdin().lock().take(max_bytes as u64+1).read_to_end(&mut bytes)
            .map_err(|_| "SOURCE_CALENDAR_READ")?;
    }
    if bytes.len() > max_bytes { return Err("SOURCE_CALENDAR_BYTES"); }
    Ok(bytes)
}
fn replay(raw: &[u8]) -> Frame {
    match std::panic::catch_unwind(|| calendar_cli::solve(raw)) {
        Ok(frame) => frame,
        Err(_) => Frame::error(ErrorKind::Internal,"SOURCE_CALENDAR_PANIC"),
    }
}
fn run(args: &[OsString]) -> (Vec<u8>,u8) {
    let check_requested = args.first().is_some_and(|arg| arg == "check");
    let action = match command(args) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("{error}");
            return if check_requested {
                (canonical_json(&json!({"schema":"source_calendar_check_v1","status":"REJECT"})),1)
            } else { (Frame::error(ErrorKind::ExecutionFailure,error).bytes(),1) };
        },
    };
    match action {
        Command::Solve(path) => {
            let frame = match read(path.as_ref(),MAX_REQUEST_BYTES) {
                Ok(raw) => replay(&raw),
                Err("SOURCE_CALENDAR_BYTES") => Frame::error(ErrorKind::InvalidRequest,"SOURCE_CALENDAR_BYTES"),
                Err(error) => Frame::error(ErrorKind::ExecutionFailure,error),
            };
            if let Some(diagnostic) = &frame.diagnostic { eprintln!("{diagnostic}"); }
            (frame.bytes(),frame.exit_code)
        },
        Command::Check(request,certificate) => {
            let accepted = match (read(Some(&request),MAX_REQUEST_BYTES),read(Some(&certificate),MAX_RESULT_BYTES)) {
                (Ok(raw),Ok(table)) => replay(&raw).bytes() == table,
                _ => false,
            };
            (canonical_json(&json!({"schema":"source_calendar_check_v1",
                "status":if accepted {"ACCEPT"} else {"REJECT"}})),if accepted {0} else {1})
        },
    }
}
fn main() {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    let (bytes,code) = run(&args);
    if let Err(error) = io::stdout().lock().write_all(&bytes) {
        eprintln!("SOURCE_CALENDAR_WRITE: {error}");
        std::process::exit(1);
    }
    std::process::exit(i32::from(code));
}
