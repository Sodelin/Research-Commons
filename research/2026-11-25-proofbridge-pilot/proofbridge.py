"""Replay signed Mobius pair certificates against the pinned Lean kernel."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
PIN = (ROOT / "lean-toolchain").read_text(encoding="ascii").strip()
COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
SCHEMA = "commons.goldbach-sign-pair.v1"

def digest(data):
    return hashlib.sha256(data).hexdigest()

def write_cert(file):
    signs = (-1, 0, 1)
    rows = [(h if q else 0) - (q if h else 0) for q in signs for h in signs]
    file.write_text(json.dumps({"schema": SCHEMA, "rows": rows}) + "\n", encoding="ascii")

def check(file):
    raw = file.read_bytes()
    if len(raw) > 4096:
        raise ValueError("oversized certificate")
    cert = json.loads(raw)
    if (type(cert) is not dict or set(cert) != {"schema", "rows"}
            or cert["schema"] != SCHEMA or type(cert["rows"]) is not list
            or len(cert["rows"]) != 9
            or any(type(x) is not int or not -2 <= x <= 2 for x in cert["rows"])):
        raise ValueError("unexpected schema or invalid rows")
    rows = ", ".join(str(x) for x in cert["rows"])
    base = (ROOT / "Checker.lean").read_bytes()
    module = base + f"""
namespace ProofBridge
def proposed : List Int := [{rows}]
theorem rows_replayed : proposed = actual := by decide
theorem certified_rows : proposed = normalForm := certificate_sound proposed rows_replayed
end ProofBridge
#print axioms ProofBridge.certified_rows
""".encode("ascii")
    command = ["elan", "run", PIN, "lean"]
    version = subprocess.check_output(command + ["--version"], text=True, timeout=15)
    if COMMIT not in version:
        raise ValueError("unexpected Lean compiler commit")
    with tempfile.TemporaryDirectory(prefix="commons_cert_") as work:
        (Path(work) / "Replay.lean").write_bytes(module)
        result = subprocess.run(command + ["Replay.lean"], cwd=work,
                                capture_output=True, text=True, timeout=30)
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        return 1
    expected = "'ProofBridge.certified_rows' does not depend on any axioms"
    if expected not in result.stdout:
        raise ValueError("missing axiom audit")
    print(json.dumps({"status": "kernel-checked", "lean": version.strip(),
                      "certificate_sha256": digest(raw), "checker_sha256": digest(base),
                      "module_sha256": digest(module), "theorem": "ProofBridge.certified_rows",
                      "axioms": []}, indent=2))
    return 0

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["make", "check"])
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    if args.action == "make":
        write_cert(args.certificate)
        return 0
    return check(args.certificate)

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        sys.exit(str(exc))

