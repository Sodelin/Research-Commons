//! Rust front end for the shared C/GMP exact-count kernel.
//! This component is not the complete nine-parameter practical solver.
use std::ffi::{CStr, CString};
use std::io::{self, Write};
use std::os::raw::{c_char, c_int};
use std::ptr;

extern "C" {
    fn rc_count_certificate_json(
        a: *const c_char,
        epsilon: *const c_char,
        max_steps: u64,
        has_limit: c_int,
        include_weights: c_int,
        out_json: *mut *mut c_char,
    ) -> c_int;
    fn rc_count_free(json: *mut c_char);
}

fn invalid_arguments() -> i32 {
    let result = io::stdout().lock().write_all(
        b"{\"status\":\"INVALID_INPUT\",\"error\":\"ARGUMENTS\"}\n",
    );
    if result.is_ok() { 2 } else { 3 }
}

fn run() -> i32 {
    let args: Vec<std::ffi::OsString> = std::env::args_os().collect();
    if args.len() < 3 {
        return invalid_arguments();
    }
    let mut max_steps = 0_u64;
    let mut has_limit = 0;
    let mut include_weights = 0;
    let mut i = 3;
    while i < args.len() {
        match args[i].to_str() {
            Some("--weights") if include_weights == 0 => include_weights = 1,
            Some("--max-steps") if has_limit == 0 && i + 1 < args.len() => {
                i += 1;
                let s = match args[i].to_str() {
                    Some(s) => s,
                    None => return invalid_arguments(),
                };
                if s.is_empty() || !s.bytes().all(|c| c.is_ascii_digit()) {
                    return invalid_arguments();
                }
                max_steps = match s.parse() {
                    Ok(n) => n,
                    Err(_) => {
                        return invalid_arguments();
                    }
                };
                has_limit = 1;
            }
            _ => {
                return invalid_arguments();
            }
        }
        i += 1;
    }
    let a = match CString::new(args[1].as_encoded_bytes()) {
        Ok(s) => s,
        Err(_) => return invalid_arguments(),
    };
    let epsilon = match CString::new(args[2].as_encoded_bytes()) {
        Ok(s) => s,
        Err(_) => return invalid_arguments(),
    };
    let mut out_json: *mut c_char = ptr::null_mut();
    // SAFETY: both input CStrings outlive the call; out_json is writable.
    // The C ABI returns a NUL-terminated allocation owned by its caller.
    let code = unsafe {
        rc_count_certificate_json(
            a.as_ptr(), epsilon.as_ptr(), max_steps, has_limit,
            include_weights, &mut out_json,
        )
    };
    if out_json.is_null() {
        eprintln!("Count kernel returned no complete JSON result.");
        return 3;
    }
    // SAFETY: this pointer is the allocation returned by the checked ABI.
    // It is read before its one matching rc_count_free call.
    let write_result = unsafe {
        let bytes = CStr::from_ptr(out_json).to_bytes();
        let mut stdout = io::stdout().lock();
        stdout.write_all(bytes).and_then(|_| stdout.write_all(b"\n"))
    };
    unsafe { rc_count_free(out_json) };
    if write_result.is_err() {
        eprintln!("Could not write the complete result.");
        return 3;
    }
    match code {
        0 | 2 | 3 => code,
        _ => 3,
    }
}

fn main() {
    std::process::exit(run());
}
