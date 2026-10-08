"""Static exact source-DAG preparation for owned draft files; no Lean/Actions.

Usage: python plan_extension.py <module-name> <draft-repository-path> <output-name>
The draft's exact captured hash is a preparation only, not author freeze/review.
Existing providers are read from immutable accepted181 input916e02a1.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
COMMIT = "916e02a1d51d79cdffd300b9d8313df2608b08bc"
PACKET = "research/2026-10-07-cloud-g6-sol-ultra-1601z"
BASELINE = "research/2026-10-04-dot-verified-lean-825-0203z/package/baseline"

def frozen(path):
    return subprocess.check_output(["git", "show", f"{COMMIT}:{path}"], cwd=REPO)

def imports(source):
    clean, depth, i = [], 0, 0
    while i < len(source):
        if source[i:i+2] == "/-": depth += 1; i += 2
        elif depth and source[i:i+2] == "-/": depth -= 1; i += 2
        elif depth:
            if source[i] == "\n": clean.append("\n")
            i += 1
        else: clean.append(source[i]); i += 1
    assert depth == 0
    result = []
    for line in "".join(clean).splitlines():
        match = re.match(r"\s*(?:public\s+)?import\s+(.+)", line)
        if match: result.extend(match[1].split("--")[0].split())
    return result

target, draft_path, output_name = sys.argv[1:]
assert "/" not in output_name and output_name.endswith(".json")
draft = REPO / draft_path
assert draft.is_file() and draft.resolve().is_relative_to(REPO / "research/2026-10-08-codex-integration-0825z")
draft_bytes = draft.read_bytes()
owned_siblings = {p.stem: p for p in draft.parent.glob("*.lean")}
accepted = json.loads((HERE / "terminal-37749239915/inputs-recovered.json").read_text())
accepted_plan = json.loads(frozen(PACKET + "/verification/freeze-plans/finite-corruption-direction-repair-static.json"))
provider_paths = {m: r["repository_path"] for m, r in accepted_plan["modules"].items()}
baseline_files = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", COMMIT, BASELINE], cwd=REPO, text=True).splitlines()
for path in baseline_files:
    if not path.endswith(".lean"): continue
    relative = path[len(BASELINE)+1:-5]
    for prefix in ["Imported/", "HistoricalCore/", "HistoricalNanuq/", "HistoricalBiological/"]:
        if relative.startswith(prefix): relative = relative[len(prefix):]; break
    provider_paths.setdefault(relative.replace("/", "."), path)
modules, external, order, visiting = {}, set(), [], set()

def visit(name):
    if name.startswith(("Mathlib.", "Lean.", "Std.", "Init.")):
        external.add(name); return
    if name in modules: return
    assert name not in visiting, "cycle:" + name
    visiting.add(name)
    if name in owned_siblings:
        local = owned_siblings[name]
        data, path, origin = local.read_bytes(), str(local.relative_to(REPO)), "owned local draft, compiler UNCHECKED"
    else:
        assert name in provider_paths, "Missing provider:" + name
        path = provider_paths[name]
        data, origin = frozen(path), COMMIT
    record = {"repository_path": path, "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data),
              "imports": imports(data.decode()), "source_version": origin,
              "in_accepted181": name in accepted["modules"]}
    if name in accepted["modules"]:
        assert record["sha256"] == accepted["modules"][name]["sha256"]
        assert record["imports"] == accepted["modules"][name]["imports"]
    for dependency in record["imports"]: visit(dependency)
    modules[name] = record
    visiting.remove(name)
    order.append(name)

visit(target)
incremental = [m for m in order if m not in accepted["modules"]]
external_roots = sorted(m for m in external if m.startswith("Mathlib."))
result = {
    "status": "STATIC DAG only; author freeze, source/API/selection review and fresh root gate pending; no compiler authorization",
    "target": target, "draft_path": draft_path, "draft_sha256": hashlib.sha256(draft_bytes).hexdigest(),
    "provider_commit": COMMIT, "accepted_run": 37749239915, "accepted_custom": 181,
    "smallest_independent_stage_custom": len(modules), "stage_mathlib_roots": external_roots,
    "stage_lean_std_init_roots": sorted(external - set(external_roots)),
    "accepted181_provider_intersection": len(modules)-len(incremental),
    "incremental_custom_modules_vs181": incremental, "incremental_custom_count": len(incremental),
    "additional_mathlib_roots_vs181": sorted(set(external_roots)-set(accepted["mathlib_roots"])),
    "modules": modules, "topological_order": order,
    "runtime_budget": "Unestimated: new-provider actual timings and scoped owner proposal required; existing181 times are observations, not upper bounds",
    "axiom_audit_requirement": "All successful modules, including generated/type/body/transitive-axiom rows; compare inherited rows and expose generated additions",
    "controls": "No controls, workflows, formal sources or target lists edited",
    "compiler_invoked": False, "actions_dispatched": False,
    "scope": "This dependency selection records source identities and import closure; it proves no new theorem or source/application bridge",
}
(HERE / output_name).write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: result[k] for k in ["status", "target", "draft_sha256", "smallest_independent_stage_custom", "accepted181_provider_intersection", "incremental_custom_count", "incremental_custom_modules_vs181", "additional_mathlib_roots_vs181"]}, indent=2))
