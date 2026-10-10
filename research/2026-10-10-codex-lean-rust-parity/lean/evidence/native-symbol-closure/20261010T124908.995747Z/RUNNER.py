#!/usr/bin/env python3
"""Compile exact generated provider C and its ordinary runtime symbol closure.

All native outputs stay in scratch. This uses the already source-built pinned
Mathlib/package C files and never starts a Lean process. Module initialization
is not stubbed or modified; --load-dynlib replay is a separate actual check.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import datetime
import json
from pathlib import Path
import re
import shutil
import subprocess
import time
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]


def symbols(path):
    body = path.read_text()
    definitions = set(re.findall(r"^[^\n;{}]*\b([A-Za-z_][A-Za-z0-9_]*)\([^;\n]*\)\s*\{", body, re.M))
    # Whole generated modules also refer to exported global values. Lazy
    # function relocation alone does not permit unresolved data relocations.
    definitions.update(re.findall(r"^(?:LEAN_EXPORT|static)\s+[^\n;(){}=]*\b([A-Za-z_][A-Za-z0-9_]*)\s*(?:;|=)", body, re.M))
    references = set(re.findall(r"\b(lp_[A-Za-z0-9_]+)\b", body))
    references.update(re.findall(r"\b((?:(?:runtime|meta)_)?initialize_[A-Za-z0-9_]+)\s*\(", body))
    return definitions, references - definitions


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("provider_work", type=Path)
    args = parser.parse_args()
    provider_work = args.provider_work.resolve()
    provider = provider_work / "FinEnum.c"
    assert provider.is_file()
    assert shutil.disk_usage(ROOT).free >= 4 * 1024**3, "Native closure requires at least4GiB free, retaining3GiB reserve."
    mathlib = Path("/workspace/dependencies/mathlib4")
    leanc = Path("/workspace/toolchains/lean-4.33.1-linux/bin/leanc")
    include_root = leanc.parent.parent / "include"
    headers = {str(p): sha(p) for p in include_root.rglob("*") if p.is_file()}
    commit = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
    assert commit == "0df444a360eaa60ab8c11dca51a86af692955474"
    generated_roots = [mathlib / ".lake/build/ir"] + sorted((mathlib / ".lake/packages").glob("*/.lake/build/ir"))
    base_receipt = json.loads((ROOT / "FINENUM-NATIVE-RESULT.json").read_bytes())
    paths = [Path(p) for p in base_receipt["lean_path"].split(":")]
    old_run = paths[0].parents[2]
    native_pins = json.loads((old_run / "NATIVE-RUNTIME-PINS.json").read_bytes())["libraries"]
    native_symbols = set()
    for path, identity in native_pins.items():
        assert sha(Path(path)) == identity["sha256"]
        with Path(path).open("rb") as stream:
            if stream.read(4) != b"\x7fELF":
                continue  # Pinned linker scripts are not dynamic symbol owners.
        listing = subprocess.check_output(["nm", "-D", "--defined-only", path], text=True, stderr=subprocess.DEVNULL)
        native_symbols.update(line.split()[-1].split("@")[0] for line in listing.splitlines() if line.split())
    owners, information = {}, {}
    for root in generated_roots:
        for path in sorted(root.rglob("*.c")):
            # Cache executables intentionally repeat helper declarations from
            # Mathlib. They are not part of the imported Mathlib library.
            if root == mathlib / ".lake/build/ir" and path.relative_to(root).parts[0] != "Mathlib":
                continue
            defs, refs = symbols(path)
            information[path] = (defs, refs, root)
            for symbol in defs:
                if symbol.startswith("lp_") or re.match(r"(?:(?:runtime|meta)_)?initialize_", symbol):
                    assert symbol not in owners or owners[symbol] == path, ("Duplicate generated definition", symbol)
                    owners[symbol] = path
    own_defs, pending = symbols(provider)
    selected, missing = set(), set()
    while pending:
        symbol = pending.pop()
        if symbol in own_defs or symbol in native_symbols:
            continue
        if symbol not in owners:
            missing.add(symbol)
            continue
        path = owners[symbol]
        if path in selected:
            continue
        selected.add(path)
        defs, refs, _ = information[path]
        own_defs.update(defs)
        pending.update(refs - own_defs)
    assert not missing, ("Generated runtime symbol owner unavailable", sorted(missing))
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    work = ROOT / ".build/native-symbol-closure" / stamp
    evidence = ROOT / "evidence/native-symbol-closure" / stamp
    (work / "objects").mkdir(parents=True)
    evidence.mkdir(parents=True)
    records = []
    for index, path in enumerate([provider] + sorted(selected)):
        source = None
        if path in information:
            generated_root = information[path][2]
            source_root = generated_root.parents[2]
            source = source_root / path.relative_to(generated_root).with_suffix(".lean")
            assert source.is_file(), ("Original generated-C source unavailable", source)
        records.append({"c_path": str(path), "c_sha256": sha(path), "c_bytes": path.stat().st_size,
                        "source_path": str(source) if source else str(provider_work / "Mathlib/Data/FinEnum.lean"),
                        "source_sha256": sha(source) if source else sha(provider_work / "Mathlib/Data/FinEnum.lean"),
                        "object_path": str(work / "objects" / (str(index) + ".o"))})
    preparation = {"status": "PREPARED_EXACT_GENERATED_C_RUNTIME_SYMBOL_CLOSURE", "work": str(work),
                   "evidence": str(evidence.relative_to(ROOT)), "mathlib_commit": commit,
                   "leanc_sha256": sha(leanc), "generated_modules": len(records), "records": records,
                   "no_lean_compiler_process_started": True,
                   "global_function_and_initializer_symbols_included": True,
                   "existing_native_symbol_provider_identities": native_pins,
                   "toolchain_header_identities": headers,
                   "job_ceiling": 1024, "C_workers": 2, "seconds_per_C_job": 180,
                   "scratch_output_byte_ceiling": 2 * 1024**3, "free_space_reserve_bytes": 3 * 1024**3,
                   "initializer_or_original_source_bodies_modified": False,
                   "initialization": "Whole original generated module bodies and their original global/function/initializer dependencies retained. No initializer is stubbed or modified."}
    save(work / "PREPARATION.json", preparation)
    save(evidence / "PREPARATION.json", preparation)
    save(ROOT / "NATIVE-SYMBOL-CLOSURE-PREPARATION.json", preparation)
    (evidence / "RUNNER.py").write_bytes(Path(__file__).read_bytes())
    print(json.dumps({k: preparation[k] for k in ["status", "generated_modules", "evidence"]}), flush=True)
    assert len(records) <= 1024, "Generated closure exceeds this bounded two-C-compiler lane."
    flags = [str(leanc), "-O2", "-fPIC", "-DLEAN_EXPORTING"]
    def compile_row(row):
        index = Path(row["object_path"]).stem
        assert sha(Path(row["c_path"])) == row["c_sha256"]
        assert shutil.disk_usage(ROOT).free >= 3 * 1024**3, "Native closure stops before reserve is consumed."
        command = flags + ["-c", "-o", row["object_path"], row["c_path"]]
        start = time.monotonic()
        with (evidence / (index + ".stdout")).open("wb") as out, (evidence / (index + ".stderr")).open("wb") as err:
            try:
                code = subprocess.run(command, stdout=out, stderr=err, timeout=180).returncode
            except subprocess.TimeoutExpired:
                code = 124
        assert sha(Path(row["c_path"])) == row["c_sha256"]
        rec = {"command": command, "exit_code": code, "elapsed_seconds": time.monotonic() - start,
               "generated_c_sha256": row["c_sha256"], "source_sha256": row["source_sha256"],
               "stderr_sha256": sha(evidence / (index + ".stderr")), "stdout_sha256": sha(evidence / (index + ".stdout"))}
        if code == 0:
            rec["object_sha256"] = sha(Path(row["object_path"]))
        assert sum(p.stat().st_size for p in (work / "objects").glob("*.o")) <= 2 * 1024**3, "Native scratch output exceeds explicit ceiling."
        save(evidence / (index + ".receipt.json"), rec)
        return rec
    with ThreadPoolExecutor(max_workers=2) as workers:
        compiled = list(workers.map(compile_row, records))
    assert all(r["exit_code"] == 0 for r in compiled), "Native compilation failures preserved."
    plugin = work / "libOriginalFinEnumRuntime.so"
    command = [str(leanc), "-shared", "-o", str(plugin)] + [r["object_path"] for r in records]
    with (evidence / "link.stdout").open("wb") as out, (evidence / "link.stderr").open("wb") as err:
        code = subprocess.run(command, stdout=out, stderr=err, timeout=180).returncode
    result = {"status": "PASS_EXACT_GENERATED_C_RUNTIME_LINK" if code == 0 else "FAILED_LINK_PRESERVED",
              "preparation_sha256": sha(work / "PREPARATION.json"), "compile_records": compiled,
              "plugin_path": str(plugin), "plugin_sha256": sha(plugin) if code == 0 else None,
              "link_command": command, "link_exit_code": code,
              "link_stdout_sha256": sha(evidence / "link.stdout"), "link_stderr_sha256": sha(evidence / "link.stderr"),
              "leanc_identity_stable": sha(leanc) == preparation["leanc_sha256"],
              "source_and_generated_c_identities_stable": all(sha(Path(r["c_path"])) == r["c_sha256"] and sha(Path(r["source_path"])) == r["source_sha256"] for r in records),
              "toolchain_header_identities_final_stable": all(sha(Path(p)) == digest for p, digest in headers.items()),
              "actual_lean_smoke_execution_or_kernel_audit_claimed": False, "evidence": str(evidence.relative_to(ROOT))}
    save(evidence / "RECEIPT.json", result)
    save(ROOT / "NATIVE-SYMBOL-CLOSURE-RESULT.json", result)
    print(json.dumps({k: result[k] for k in ["status", "plugin_sha256", "evidence"]}))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
