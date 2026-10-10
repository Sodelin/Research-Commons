//! Native RC1 solver. stdin, file and fresh output modes share exact bytes.
#![forbid(unsafe_code)]
use parity_solver::protocol::{self, MAX_CERTIFICATE_BYTES, MAX_REQUEST_BYTES};
use std::{env, fs::{self, OpenOptions}, io::{self, Read, Write}, path::Path, process::ExitCode};

const HELP: &str = "Exact Research Commons RC1 solver\n\nparity-solver solve [REQUEST|-] [--output NEW_FILE]\nparity-solver check REQUEST CERTIFICATE\nparity-solver --help\n\nWithout REQUEST, solve reads stdin. All requests use canonical ASCII RC1.\nSAT/UNSAT exit 0; UNKNOWN and conditional count exit 2; invalid input exits 1.\nCheck independently verifies request-bound witness/exclusion certificates.\nNo scientific source admission or complete unrestricted registry is inferred.\n";

fn read_bounded(reader: impl Read, limit: usize) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    reader.take(limit as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > limit { return Err(io::Error::new(io::ErrorKind::InvalidData, "input byte limit")); }
    Ok(bytes)
}

fn read_path(path: &str, limit: usize) -> io::Result<Vec<u8>> {
    if path == "-" { read_bounded(io::stdin().lock(), limit) }
    else {
        let metadata = fs::symlink_metadata(path)?;
        if !metadata.file_type().is_file() { return Err(io::Error::new(io::ErrorKind::InvalidInput, "regular file required")); }
        read_bounded(fs::File::open(path)?, limit)
    }
}

fn run(args: &[String]) -> io::Result<u8> {
    if args == ["--help"] || args == ["-h"] { print!("{HELP}"); return Ok(0); }
    match args.first().map(String::as_str) {
        Some("solve") => {
            let mut path = "-";
            let mut output: Option<&str> = None;
            let mut i = 1;
            if i < args.len() && args[i] != "--output" { path = &args[i]; i += 1; }
            if i < args.len() {
                if args[i] != "--output" || args.len() != i + 2 {
                    print!("{}", protocol::INVALID); return Ok(1);
                }
                output = Some(&args[i + 1]);
            }
            let bytes = read_path(path, MAX_REQUEST_BYTES)?;
            let result = protocol::execute(&bytes);
            if let Some(path) = output {
                // Fresh-create prevents an existing receipt from being erased.
                let mut file = OpenOptions::new().write(true).create_new(true).open(Path::new(path))?;
                file.write_all(result.bytes.as_bytes())?;
                file.sync_all()?;
            }
            print!("{}", result.bytes);
            Ok(result.exit_code)
        }
        Some("check") if args.len() == 3 => {
            let request = read_path(&args[1], MAX_REQUEST_BYTES)?;
            let certificate = read_path(&args[2], MAX_CERTIFICATE_BYTES)?;
            match protocol::check(&request, &certificate) {
                Ok(()) => { println!("RC1 CHECK ACCEPT"); Ok(0) }
                Err(_) => { println!("RC1 CHECK REJECT"); Ok(1) }
            }
        }
        _ => { print!("{}", protocol::INVALID); Ok(1) },
    }
}

fn main() -> ExitCode {
    let mut args: Vec<_> = env::args().skip(1).collect();
    if args.is_empty() { args.push("solve".to_owned()); }
    match run(&args) {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            eprintln!("parity-solver: {error}");
            if error.kind() == io::ErrorKind::InvalidData {
                print!("{}", protocol::INVALID);
            } else {
                println!("RC1 ERROR EXECUTION_FAILURE");
            }
            ExitCode::from(1)
        }
    }
}
