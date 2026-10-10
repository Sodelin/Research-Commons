use rational_compression::{check, encode, solve, Check, Frame, MAX_REQUEST_BYTES, MAX_RESULT_BYTES};
use std::{fs::File, io::{self, Read, Write}, path::Path, process::ExitCode};

fn read(path: Option<&str>, cap: usize) -> io::Result<Vec<u8>> {
    let input: Box<dyn Read> = match path { Some(p) => Box::new(File::open(Path::new(p))?), None => Box::new(io::stdin()) };
    let mut result = Vec::new();
    input.take((cap + 1) as u64).read_to_end(&mut result)?;
    Ok(result)
}
fn payload<T: serde::Serialize>(value: &T, code: i32) -> (Vec<u8>, i32) {
    match encode(value) {
        Ok(data) => (data, code),
        Err(()) => (encode(&Frame::error("EXECUTION_FAILURE")).unwrap_or_default(), 1),
    }
}
fn emit<T: serde::Serialize>(value: &T, code: i32) -> ExitCode {
    let (data, code) = payload(value, code);
    if io::stdout().lock().write_all(&data).is_err() { return ExitCode::from(1); }
    ExitCode::from(code as u8)
}

#[cfg(test)]
mod tests {
    #[test]
    fn encoding_failure_has_failure_exit() {
        let too_large = "x".repeat(rational_compression::MAX_RESULT_BYTES);
        for input_code in [0, 2] {
            let (data, code) = super::payload(&too_large, input_code);
            assert_eq!(code, 1);
            assert_eq!(serde_json::from_slice::<serde_json::Value>(&data).unwrap()["error"], "EXECUTION_FAILURE");
        }
    }
}
fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        [] | ["solve"] => match read(None, MAX_REQUEST_BYTES) {
            Ok(raw) => { let result = solve(&raw); emit(&result, result.exit_code()) }
            Err(_) => emit(&Frame::error("EXECUTION_FAILURE"), 1),
        },
        ["solve", "--request", path] => match read(Some(path), MAX_REQUEST_BYTES) {
            Ok(raw) => { let result = solve(&raw); emit(&result, result.exit_code()) }
            Err(_) => emit(&Frame::error("EXECUTION_FAILURE"), 1),
        },
        ["check", "--request", request, "--certificate", certificate] => {
            let result = match (read(Some(request), MAX_REQUEST_BYTES), read(Some(certificate), MAX_RESULT_BYTES)) {
                (Ok(request), Ok(certificate)) => check(&request, &certificate),
                _ => Check::rejected(),
            };
            let code = if result.status == "ACCEPT" { 0 } else { 1 };
            emit(&result, code)
        }
        _ => emit(&Frame::error("INVALID_REQUEST"), 1),
    }
}
