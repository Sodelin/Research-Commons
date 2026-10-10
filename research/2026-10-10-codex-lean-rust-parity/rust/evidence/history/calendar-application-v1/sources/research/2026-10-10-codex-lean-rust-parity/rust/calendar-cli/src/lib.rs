//! Additive request/transport entrypoint; the accepted source kernels are reused.
//! Universal native/source refinement and original source admission are separate.

#[cfg(not(target_pointer_width = "64"))]
compile_error!("The calendar request count contract requires a 64-bit target");

pub mod request;
pub mod response;

use request::parse_request;
use response::{ErrorKind, Frame};

/// One fresh general request forwarded to the preserved exact calendar kernel.
pub fn solve(raw: &[u8]) -> Frame {
    let dto = match parse_request(raw) {
        Ok(value) => value,
        Err(error) => return Frame::error(ErrorKind::InvalidRequest, error.0),
    };
    let input = match dto.to_request() {
        Ok(value) => value,
        Err(error) => return Frame::error(ErrorKind::InvalidRequest, error.0),
    };
    match parity_solver::source_calendar::calendar_row(&input) {
        Ok(decision) => response::decision(&dto, decision),
        Err(parity_solver::source_calendar::Error::InvalidInput(code)) =>
            Frame::error(ErrorKind::InvalidRequest, code),
        Err(parity_solver::source_calendar::Error::Internal(code)) =>
            Frame::error(ErrorKind::Internal, code),
        Err(parity_solver::source_calendar::Error::Unsupported(code)) =>
            Frame::error(ErrorKind::ExecutionFailure, code),
    }
}
