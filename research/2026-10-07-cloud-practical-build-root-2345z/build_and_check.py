"""Build and differential-check the shared C/GMP, C++ and Rust count component.

This is not the complete inverse solver or a transfer of Lean verification.
All checks use public exact synthetic inputs and a pinned Python reference.
"""
from __future__ import annotations

import argparse
import ctypes
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import subprocess
import time

REFERENCE_SHA = "4708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4"
KERNEL_PINS = {
    "src/count_gmp.c": "4c15198ae726b8afb9aefab32bd46f2ee5d20833ccc2ede7375028cc289a0933",
    "src/count_cli.cpp": "6e48875c712f1ebdb73e68c5e68f67d3ca6755a523d764183d0c8779580809dd",
    "include/rc_count.h": "77910eaf3978bf2da5925a1a01c66fcb95c998cd4ce315210073104c85cff6e8",
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kernel-packet", type=Path, required=True)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--rustc", default="rustc")
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    packet = args.kernel_packet.resolve()
    own = Path(__file__).resolve().parent
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    expected_sources = {str(packet / name): pin for name, pin in KERNEL_PINS.items()}
    expected_sources[str(own / "rust_count_cli.rs")] = sha(own / "rust_count_cli.rs")
    reference = args.reference.read_bytes()
    assert hashlib.sha256(reference).hexdigest() == REFERENCE_SHA, "Reference pin mismatch"
    for name, pin in expected_sources.items():
        assert sha(Path(name)) == pin, f"Source pin mismatch: {name}"
    namespace = {"__name__": "frozen_count_reference_2345z"}
    exec(compile(reference, str(args.reference), "exec"), namespace)
    commands = []
    started = time.monotonic()

    def run(command, *, timeout=30):
        begin = time.monotonic()
        result = subprocess.run(command, capture_output=True, timeout=timeout)
        commands.append({
            "argv": [str(x) for x in command], "exit_code": result.returncode,
            "elapsed_seconds": time.monotonic() - begin,
            "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
            "stderr_sha256": hashlib.sha256(result.stderr).hexdigest(),
        })
        return result

    def build(command):
        result = run(command)
        assert result.returncode == 0, result.stderr.decode(errors="replace")
        assert not result.stderr, result.stderr.decode(errors="replace")

    obj = out / "count_gmp.o"
    archive = out / "librc_count.a"
    shared = out / "librc_count.so"
    cpp = out / "count_cpp"
    rust = out / "count_rust"
    build(["gcc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic",
           "-O2", "-fPIC", "-I", str(packet / "include"), "-c",
           str(packet / "src/count_gmp.c"), "-o", str(obj)])
    build(["ar", "rcs", str(archive), str(obj)])
    build(["gcc", "-shared", str(obj), "-lgmp", "-o", str(shared)])
    build(["g++", "-std=c++17", "-Wall", "-Wextra", "-Werror", "-pedantic",
           "-O2", "-I", str(packet / "include"),
           str(packet / "src/count_cli.cpp"), str(archive), "-lgmp", "-o", str(cpp)])
    build([args.rustc, "--edition=2021", "-D", "warnings", "-C", "opt-level=3",
           "-C", "overflow-checks=on", str(own / "rust_count_cli.rs"),
           "-L", f"native={out}", "-l", "static=rc_count", "-l", "gmp",
           "-o", str(rust)])
    versions = {"gcc": run(["gcc", "--version"]).stdout.decode().splitlines()[0],
                "g++": run(["g++", "--version"]).stdout.decode().splitlines()[0],
                "rustc": run([args.rustc, "--version", "--verbose"]).stdout.decode()}
    lib = ctypes.CDLL(str(shared))
    fn = lib.rc_count_certificate_json
    fn.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint64,
                   ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_void_p)]
    fn.restype = ctypes.c_int
    lib.rc_count_free.argtypes = [ctypes.c_void_p]
    lib.rc_count_free.restype = None

    def direct(a, epsilon, limit, weights):
        result = ctypes.c_void_p()
        status = fn(a.encode(), epsilon.encode(), limit or 0,
                    int(limit is not None), int(weights), ctypes.byref(result))
        assert result.value, "C API returned no JSON"
        try:
            decoded = json.loads(ctypes.string_at(result.value))
        finally:
            lib.rc_count_free(result)
        return status, decoded

    cases = [
        ("0", "1/2", None, True), ("-0", "1/3", 1, True),
        ("1", "1/10", None, True), ("2/3", "2/7", None, False),
        ("1", "1/100", 0, True), ("1", "1/100", 1, False),
        ("12/18", "02/003", 20, True), ("10", "1/1000", 64, True),
        (str(2**120), "1/8", 3, False), ("1/1000", f"1/{2**160}", 64, True),
    ]
    rng = random.Random(20261007)
    for _ in range(70):
        cases.append((f"{rng.randrange(60)}/{rng.randrange(1,20)}",
                      f"{rng.randrange(1,9)}/{rng.randrange(10,80)}",
                      rng.choice([0,1,2,8,32,96]), bool(rng.randrange(2))))
    details = []
    for a, epsilon, limit, weights in cases:
        expected = namespace["certify"](Fraction(a), Fraction(epsilon), max_steps=limit)
        if weights and expected["status"] == "CERTIFIED":
            expected["weights"] = [str(x) for x in namespace["weights"](Fraction(a), expected["K"])]
        cli_args = [a, epsilon]
        if limit is not None:
            cli_args += ["--max-steps", str(limit)]
        if weights:
            cli_args += ["--weights"]
        c_status, c_data = direct(a, epsilon, limit, weights)
        assert c_status == 0 and c_data == expected, (cli_args, c_data, expected)
        for executable in (cpp, rust):
            r = run([str(executable), *cli_args], timeout=3)
            assert r.returncode == 0 and json.loads(r.stdout) == expected, (executable, cli_args, r.stdout)
        details.append({"argv": cli_args, "expected": expected, "all_three_equal": True})
    invalid = [
        [], ["1"], ["1","1/2","--weights","--weights"],
        ["1","1/2","--max-steps","0","--max-steps","1"],
        ["1","1/2","--max-steps"], ["1","1/2","--max-steps","-1"],
        ["1","1/2","--max-steps",str(2**64)], ["1","1/2","--unknown"],
        ["-1","1/2"], ["1","0"], ["1","1"], ["1/0","1/2"],
        ["1/-2","1/2"], ["1e-3","1/2"], [" 1","1/2"],
        ["１","1/2"], ["1","1/2/3"], [str(2**256),"1/2"],
        ["0"*159,"1/2"], ["1","NaN"],
    ]
    for values in invalid:
        outcomes = []
        for executable in (cpp,rust):
            r = run([str(executable), *values], timeout=3)
            data = json.loads(r.stdout)
            assert r.returncode == 2 and data["status"] == "INVALID_INPUT", (values,r.stdout)
            outcomes.append(data)
        assert outcomes[0] == outcomes[1], (values,outcomes)
    byte_args = [b"\xff", b"1/2"]
    outcomes = []
    for executable in (cpp,rust):
        r = run([bytes(executable), *byte_args], timeout=3)
        data = json.loads(r.stdout)
        assert r.returncode == 2 and data["status"] == "INVALID_INPUT"
        outcomes.append(data)
    assert outcomes[0] == outcomes[1], outcomes
    for name, pin in expected_sources.items():
        assert sha(Path(name)) == pin, f"Source changed during check: {name}"
    result = {
        "status": "PASS", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "reference_sha256": REFERENCE_SHA, "source_sha256": expected_sources,
        "versions": versions, "build_and_version_commands": commands[:8],
        "valid_full_output_cases": len(cases), "interfaces": ["C ABI","C++ CLI","Rust CLI"],
        "invalid_cli_cases": len(invalid)+1, "valid_cases": details,
        "command_receipts": commands, "elapsed_seconds": time.monotonic()-started,
        "limits": "Each build has30s and each CLI test3s wall timeout; valid searches are small or bounded.",
        "scope": "Shared scalar normalized Poisson-prefix component; same C/GMP arithmetic, not independent Rust arithmetic.",
        "excluded": "Full JC inverse solver, certified interval integration, performance/speedup, Lean executable correspondence.",
    }
    (out/"RESULT.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ("status","valid_full_output_cases","invalid_cli_cases","elapsed_seconds")}))


if __name__ == "__main__":
    main()
