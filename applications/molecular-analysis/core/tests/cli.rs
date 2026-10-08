use std::io::Write;
use std::process::{Command,Output,Stdio};

fn run(input:&[u8]) -> Output {
    let mut child=Command::new(env!("CARGO_BIN_EXE_molecular-haplotype-core"))
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    child.wait_with_output().unwrap()
}
fn request(sequence:&str) -> String {
    format!("molecular-haplotype-v1\nwindow\thg38\tchr1\t0\t{sequence}\tACGT\nphase\tcis\ttrue\nvariant\ta\tchr1\t1\tA\tT\nvariant\tb\tchr1\t5\tA\tT\n")
}
#[test] fn cli_success_has_version_and_scenarios() {
    let output=run(request("ACGTACGT").as_bytes());assert!(output.status.success());
    let text=String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("\"schema\":\"molecular-haplotype-result-v1\""));
    assert!(text.contains("\"AB\":{\"sequence\":\"TCGTTCGT\""));assert!(output.stderr.is_empty());
}
#[test] fn large_sequence_uses_stdin_without_argument_limit() {
    let sequence="ACGT".repeat(50_000);let output=run(request(&sequence).as_bytes());
    assert!(output.status.success());assert!(output.stdout.len()>800_000);
}
#[test] fn invalid_utf8_and_oversized_input_are_structured_refusals() {
    let output=run(&[0xff]);assert_eq!(output.status.code(),Some(2));
    assert!(String::from_utf8(output.stdout).unwrap().contains("stdin must be UTF-8"));
    let output=run(&vec![b'x';molecular_haplotype_core::MAX_INPUT_BYTES+1]);assert_eq!(output.status.code(),Some(2));
    assert!(String::from_utf8(output.stdout).unwrap().contains("RESOURCE_LIMIT"));
}
