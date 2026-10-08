//! Narrow bounded TSV fixture probe, not a production JSON/API protocol.
#![forbid(unsafe_code)]
use signed_nine_pair_receiver::{evaluate, Config, Outcome, Request, TextBox, PYTHON_PROVIDER_SHA};
use std::io::{self, BufRead, Write};

const MAX_LINE: usize = 32768;
const MAX_FIELD: usize = 4096;
const MAX_ROWS: usize = 96;

// Consume an oversized line without ever retaining its unbounded tail.
// The bools mark overflow and a terminating LF, respectively.
fn bounded_line(reader: &mut impl BufRead) -> io::Result<Option<(Vec<u8>, bool, bool)>> {
    let mut line = Vec::with_capacity(4096);
    let mut overflow = false;
    loop {
        let buffer = reader.fill_buf()?;
        if buffer.is_empty() {
            return if line.is_empty() && !overflow { Ok(None) }
                   else { Ok(Some((line, overflow, false))) };
        }
        let newline = buffer.iter().position(|&b| b == b'\n');
        let take = newline.unwrap_or(buffer.len());
        if !overflow {
            if take <= MAX_LINE - line.len() { line.extend_from_slice(&buffer[..take]); }
            else { overflow = true; }
        }
        let consumed = take + usize::from(newline.is_some());
        reader.consume(consumed);
        if newline.is_some() { return Ok(Some((line, overflow, true))); }
    }
}

fn integer(s: &str) -> Option<i32> {
    let magnitude = s.strip_prefix('-').unwrap_or(s);
    if magnitude.is_empty() || magnitude.len() > 10 || !magnitude.bytes().all(|b| b.is_ascii_digit()) { return None; }
    s.parse().ok()
}

fn identifier(s: &str) -> bool {
    !s.is_empty() && s.len() <= 64 && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
}

fn text_box<'a>(fields: &[&'a str]) -> TextBox<'a> {
    // Called only after the entire fixed field count has been checked.
    std::array::from_fn(|i| (fields[2*i], fields[2*i+1]))
}

fn response(id: &str, outcome: Outcome) -> String {
    let status = outcome.status();
    let refusal = match &outcome.geometry { Ok(_) => "-".to_owned(), Err(e) => e.to_string() };
    let config = outcome.config;
    let mut fields = vec!["result".to_owned(), id.to_owned(), status.to_owned(), refusal,
                          outcome.scalar_exp_calls.to_string(), config.precision.to_string(),
                          config.max_bits.to_string(), config.max_exp_calls.to_string(),
                          PYTHON_PROVIDER_SHA.to_owned(), "native_exact_interval_core".to_owned()];
    // Confidence, cover, mean admission, source existence, forward calls, rows.
    fields.extend((0..6).map(|_| "0".to_owned()));
    if let Ok(geometry) = outcome.geometry {
        for value in geometry.differences { fields.push(value.lo().to_string()); fields.push(value.hi().to_string()); }
        fields.extend(geometry.normalized.into_iter().map(|q| q.to_string()));
        fields.push(geometry.maximum.to_string());
        for value in geometry.signed_residuals { fields.push(value.lo().to_string()); fields.push(value.hi().to_string()); }
    }
    fields.join("\t")
}

fn run(line: &[u8], overflow: bool, framed: bool) -> String {
    let protocol = |id: &str, code: &str| format!("protocol\t{id}\t{code}");
    if overflow { return protocol("-", "PROBE_LINE"); }
    if !framed { return protocol("-", "PROBE_FRAME"); }
    if !line.iter().all(|&b| b == b'\t' || (32..=126).contains(&b)) { return protocol("-", "PROBE_ASCII"); }
    // ASCII check makes this conversion infallible; use a guarded branch anyway.
    let line = match std::str::from_utf8(line) { Ok(v) => v, Err(_) => return protocol("-", "PROBE_ASCII") };
    let fields: Vec<_> = line.split('\t').collect();
    if fields.iter().any(|s| s.len() > MAX_FIELD) { return protocol("-", "PROBE_FIELD"); }
    if fields.len() < 6 || fields[0] != "pair" { return protocol("-", "PROBE_SHAPE"); }
    let id = fields[1];
    if !identifier(id) { return protocol("-", "PROBE_ID"); }
    let boxes = match fields[5] { "default" => false, "boxes" => true, _ => return protocol(id, "PROBE_MODE") };
    if fields.len() != if boxes { 78 } else { 42 } { return protocol(id, "PROBE_SHAPE"); }
    let config = match (integer(fields[2]), integer(fields[3]), integer(fields[4])) {
        (Some(precision), Some(max_bits), Some(max_exp_calls)) => Config { precision, max_bits, max_exp_calls },
        _ => return protocol(id, "PROBE_INTEGER"),
    };
    let m0 = text_box(&fields[6..24]); let m1 = text_box(&fields[24..42]);
    let p0 = boxes.then(|| text_box(&fields[42..60]));
    let p1 = boxes.then(|| text_box(&fields[60..78]));
    let outcome = match Request::from_ordered_text(config, &m0, &m1, p0.as_ref(), p1.as_ref()) {
        Ok(request) => evaluate(request),
        Err(error) => Outcome::refused(config, error),
    };
    response(id, outcome)
}

fn main() -> io::Result<()> {
    let stdin = io::stdin(); let stdout = io::stdout();
    let mut reader = stdin.lock(); let mut writer = io::BufWriter::new(stdout.lock());
    let mut rows = 0;
    while let Some((line, overflow, framed)) = bounded_line(&mut reader)? {
        if rows == MAX_ROWS { writeln!(writer, "protocol\t-\tPROBE_ROWS")?; break; }
        rows += 1;
        writeln!(writer, "{}", run(&line, overflow, framed))?;
    }
    writer.flush()
}
