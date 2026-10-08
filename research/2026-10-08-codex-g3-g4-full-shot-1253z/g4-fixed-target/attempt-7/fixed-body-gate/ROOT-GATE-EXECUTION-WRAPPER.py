"""Root-owned single reviewed gate wrapper. Exclusive evidence, 60-second wall cap."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
RUNNER = HERE / "exact_fixed_body_pad_column.py"
EXPECTED = "bc5828c4ad19b1775cc955c2f287e36337fa6e41bd4f53d620133ab6b546dbd5"
REVIEW = ROOT / "research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-impossibility/fixed-body-gate-review/PREEXECUTION-SOURCE-REVIEW.md"
REVIEW_HASH = "f4500a75adf3ba87a656047e7274179ac849a64cb8f25df45d8a418114a02798"

def identity(path):
    raw = path.read_bytes()
    return {"path": str(path.relative_to(ROOT)), "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}

def main():
    if identity(RUNNER)["sha256"] != EXPECTED or identity(REVIEW)["sha256"] != REVIEW_HASH:
        raise ValueError("frozen reviewed source identity mismatch")
    run = HERE / "root-run-20261008T161300Z"
    run.mkdir(exist_ok=False)
    output = run / "RESULT.json"
    # This byte buffer is the one compiled; the runner authenticates the same
    # on-disk identity before and after its mathematical work.
    bootstrap = (
        "import hashlib, pathlib, sys; "
        "p=pathlib.Path(sys.argv[1]); expected=sys.argv[2]; raw=p.read_bytes(); "
        "assert hashlib.sha256(raw).hexdigest()==expected; "
        "sys.argv=[str(p),'--output',sys.argv[3]]; "
        "exec(compile(raw,str(p),'exec'),{'__name__':'__main__','__file__':str(p)})"
    )
    command = [sys.executable, "-c", bootstrap, str(RUNNER), EXPECTED, str(output)]
    before = {"status": "STARTED", "root_scheduler": True, "source": identity(RUNNER),
              "independent_preexecution_review": identity(REVIEW), "wrapper": identity(Path(__file__)),
              "command_argv": command, "wall_limit_seconds": 60, "cpu_limit_seconds": 55,
              "address_space_limit_bytes": 512*1024*1024, "new_output_path": str(output.relative_to(ROOT))}
    (run / "START.json").write_text(json.dumps(before, indent=2)+"\n")
    start = time.monotonic()
    with (run / "stdout.txt").open("xb") as stdout, (run / "stderr.txt").open("xb") as stderr:
        child = subprocess.Popen(command, cwd=ROOT, stdout=stdout, stderr=stderr)
        timed_out = False
        try:
            code = child.wait(timeout=60)
        except subprocess.TimeoutExpired:
            timed_out = True
            child.terminate()
            try:
                code = child.wait(timeout=2)
            except subprocess.TimeoutExpired:
                child.kill()
                code = child.wait()
    result = {**before, "status": "PASS" if code == 0 and output.exists() and not timed_out else "FAILED",
              "exit_code": code, "wall_timeout": timed_out, "wall_seconds": time.monotonic()-start,
              "source_after": identity(RUNNER), "stdout": identity(run / "stdout.txt"),
              "stderr": identity(run / "stderr.txt"), "result": identity(output) if output.exists() else None,
              "automatic_retry": False, "original_G4_closed": False}
    (run / "EXECUTION.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ("status", "exit_code", "wall_timeout", "wall_seconds")}))
    if code != 0 or timed_out:
        raise SystemExit(1)

if __name__ == "__main__":
    main()
