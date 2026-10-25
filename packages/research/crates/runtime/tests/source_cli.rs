use std::io::Write;
use std::process::{Command,Stdio,Output};
fn run(bytes:&[u8])->Output {
 let mut child=Command::new(env!("CARGO_BIN_EXE_source-certificate"))
   .args(["--stdin","UserCapturedSource"]).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
   .spawn().unwrap();
 child.stdin.take().unwrap().write_all(bytes).unwrap();
 child.wait_with_output().unwrap()
}
#[test]fn stdin_captures_a_complete_original_request_and_emits_no_assumed_checker_premise(){
 let input=b"RC1 CHART 7 6 4 0 1 0 4096\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nEDGE 2 1 3\nEDGE 3 1 4\nEDGE 4 2 5\nEDGE 5 2 6\nLEAF 0 3\nLEAF 1 4\nLEAF 2 5\nLEAF 3 6\nAGE EQ V:0 Q:5/1\n";
 let result=run(input);assert!(result.status.success(),"{:?}",result.stderr);
 let source=String::from_utf8(result.stdout).unwrap();
 assert!(source.contains("namespace ResearchCommons.Generated.UserCapturedSource"));
 assert!(source.contains("def originalRequest : String :="));
 assert!(source.contains("theorem binary_valid"));
 assert!(source.contains("theorem checked"));
 assert!(source.contains("checked_original_bank_feasible"));
}
#[test]fn oversized_input_refuses_before_emitting_any_partial_proof(){
 let result=run(&vec![b' ';65537]);
 assert!(!result.status.success());assert!(result.stdout.is_empty());
 assert!(String::from_utf8(result.stderr).unwrap().contains("exceeds65536"));
}
