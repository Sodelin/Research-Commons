use serde_json::{json,Value};
use std::{io::Write,process::{Command,Stdio}};
fn run(request:Value)->std::process::Output {
    let mut p=Command::new(env!("CARGO_BIN_EXE_exact-quartet-recovery"))
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    p.stdin.take().unwrap().write_all(request.to_string().as_bytes()).unwrap();
    p.wait_with_output().unwrap()
}
#[test]
fn stdin_original_label_mask_recovers_the_expected_circle_split() {
    let p=run(json!({"circle":[40,10,30,20],
        "answers":[{"quartet":[10,20,30,40],"mask":2}]}));
    assert!(p.status.success(),"{}",String::from_utf8_lossy(&p.stderr));
    let v:Value=serde_json::from_slice(&p.stdout).unwrap();
    assert_eq!(v["status"],"conditional_recovery");
    assert_eq!(v["gap_pairs"],json!([[0,2]]));
    assert_eq!(v["unique_queries"],1);
    assert_eq!(v["rectangle_tests"],2);
    assert_eq!(v["original_answer_cache"][0]["mask"],2);
    assert!(!v["not_established"].as_array().unwrap().is_empty());
}
#[test]
fn missing_duplicate_or_crossing_support_emits_no_successful_prefix() {
    for request in [
        json!({"circle":[0,1,2,3],"answers":[]}),
        json!({"circle":[0,1,2,3],"answers":[{"quartet":[0,1,2,3],"mask":2}]}),
        json!({"circle":[0,1,2,3],"answers":[{"quartet":[0,1,2,3],"mask":1},
            {"quartet":[0,1,2,3],"mask":1}]})
    ] {
        let p=run(request);
        assert_eq!(p.status.code(),Some(2));
        assert!(p.stdout.is_empty());
        assert!(!p.stderr.is_empty());
    }
}
