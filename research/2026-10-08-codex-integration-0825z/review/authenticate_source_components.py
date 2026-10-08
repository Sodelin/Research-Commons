"""Static check of owner source pins/results; no owner code is imported or run."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PACKET = HERE.parent
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_bytes())
def save(name, obj):
    (HERE / name).write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")

c = PACKET / "correspondence"
pins = read(c / "SOURCE-PINS.json")
for identity in pins["source_pins"]:
    raw = (REPO / identity["path"]).read_bytes()
    assert sha(raw) == identity["sha256"] and len(raw) == identity["bytes"]
    if identity.get("git_blob"):
        blob = subprocess.check_output(["git", "hash-object", "--stdin"], input=raw, cwd=REPO).decode().strip()
        assert blob == identity["git_blob"]
receipt = read(c / "test-receipt.json")
assert receipt["status"] == "PASS" and receipt["total_checks"] == sum(receipt["checks"].values()) == 4226
assert receipt["checks"]["actual-python-boundary-v-native-definition"] == 192
assert sum(v for k, v in receipt["checks"].items() if k.startswith("refusal:")) == 39
assert receipt["checks"]["refusal:silent-Copy-loss-or-uppercap-substitution"] == 1
for name, digest in receipt["source_files"].items():
    assert sha((c / name).read_bytes()) == digest
assert receipt["reference_sha256"] == sha((REPO / receipt["reference_path"]).read_bytes())
for table in read(c / "boundary-tables.json"):
    assert table["gamma_native"] == ["1", "3"] and table["gamma_python"] == ["2", "3"]
    actual = {(r["parent0_roots"], r["parent1_roots"]): Q(*map(int, r["mass"])) for r in table["rows"]}
    wanted = ({(0, 2): Q(1)} if table["stored_h_bit"] else {(2, 0): Q(1)}) if table["common"] else {(2, 0): Q(4, 9), (1, 1): Q(4, 9), (0, 2): Q(1, 9)}
    assert actual == wanted
wire_raw = (c / "sample-residual-law.json").read_bytes()
wire = json.loads(wire_raw)
assert sha(wire_raw) == receipt["epoch"]["wire_sha256"]
assert json.dumps(wire, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False).encode() == wire_raw
assert wire["source_admission"] == "NOT_CERTIFIED_BY_ADAPTER" and len(wire["rows"]) == 7
assert sum((Q(*map(int, r["mass"])) for r in wire["rows"]), Q(0)) == 1
assert sha(json.dumps(wire["contract"], sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()) == wire["contract_sha256"]
save("CORRESPONDENCE-STATIC-AUTHENTICATION.json", {"status": "HAND/CODE + INSPECTED AUTHOR RECEIPT ACCEPT", "reviewer_called_reference_or_native": False,
    "source_pin_count": len(pins["source_pins"]), "source_files": receipt["source_files"], "checks": 4226, "boundary_cases": 192, "refusals": 39,
    "original_full_Copy_cardinality_guard": "exact equality; an upper cap or missing original copies refuses",
    "boundary_table_binomial_and_common_mass_recount": True, "sample_states": 7, "sample_exact_total_mass": "1", "wire_sha256": sha(wire_raw),
    "former_loader": "first4220receipt source hash/reopen identity not accepted; earlier source and receipt retained",
    "scope": "local compound original child-exit/pulse; same parent IDs/Bool with gamma complement; finite exact rational representation; no native binary/Lean/full calendar/source admission"})

g = PACKET / "g6"
doc, results = read(g / "FIXED-CHART-EXAMPLE.json"), read(g / "BANK-CONTROL-RESULTS.json")
assert len(results["cases"]) == 12 and results["lean_builds"] == 0 and not results["empirical_claim"]
bank_receipt = read(g / "BANK-EXECUTION-RECEIPT.json")
assert bank_receipt["exit_code"] == 0 and bank_receipt["lean_builds"] == 0
assert bank_receipt["source_sha256"] == sha((g / "check_bank_controls.py").read_bytes())
assert bank_receipt["gate_sha256"] == sha((g / "shared_bank_gate.py").read_bytes())
assert bank_receipt["results_sha256"] == sha((g / "BANK-CONTROL-RESULTS.json").read_bytes())
bank = results["cases"][0]["result"]["bank"]
ages = {v: Q(t) for v, t in doc["ages"].items()}
exposures = {}
for profile in doc["profiles"]:
    points = sorted(set(ages.values()) | {Q(t) for t in profile["cuts"]})
    for a, b in zip(points, points[1:]):
        for e, (parent, child) in doc["edges"].items():
            if ages[child] <= a < b <= ages[parent]:
                exposures[profile["id"], e, str(a), str(b)] = b - a
        if ages[doc["root"]] <= a < b:
            exposures[profile["id"], "ANCESTRAL", str(a), str(b)] = b - a
assert len(exposures) == 42
def member(x, interval):
    lo, hi = Q(interval["lo"]), None if interval["hi"] is None else Q(interval["hi"])
    return (x > lo or x == lo and interval["lo_closed"]) and (hi is None or x < hi or x == hi and interval["hi_closed"])
assert set(bank["rates"]) == {*doc["edges"], "ANCESTRAL"}
assert all(Q(r) > 0 for r in bank["rates"].values())
assert set(bank["gamma_native"]) == set(doc["hybrids"])
assert all(0 < Q(r) < 1 for r in bank["gamma_native"].values())
for cell in doc["hazard_cells"]:
    key = cell["profile"], cell["population"], cell["young"], cell["old"]
    assert member(Q(bank["rates"][cell["population"]]) * exposures.pop(key), cell["cell"])
assert not exposures
expected_inheritance = {(p["id"], h) for p in doc["profiles"] for h in doc["hybrids"]}
for cell in doc["inheritance_cells"]:
    expected_inheritance.remove((cell["profile"], cell["hybrid"]))
    assert member(Q(bank["gamma_native"][cell["hybrid"]]), cell["cell"])
assert not expected_inheritance
save("G6-FIXED-BANK-STATIC-AUTHENTICATION.json", {"status": "HAND/CODE scoped ACCEPT; inspected authored controls", "reviewer_executed_solver": False,
    "gate_sha256": sha((g / "shared_bank_gate.py").read_bytes()), "lean_sha256": sha((g / "G6FixedCalendarSharedBank.lean").read_bytes()),
    "controls": 12, "fixture_exposures": 42, "independent_primitive_product_recount": True,
    "execution_receipt_sha256": sha((g / "BANK-EXECUTION-RECEIPT.json").read_bytes()),
    "corrected_replay_coverage": "shared inheritance validator now checks exact coverage, duplicate cells/hybrid IDs in both solve and replay; first v1 retained",
    "scope": "fixed rational already-admitted chart bank only; no law/net/G6 biological source certification; sixLean bodies uncompiled"})

comparison = read(g / "CWU-RUNS/COMPARISON.json")
metadata = read(g / "DRYAD-DATASET-METADATA.json")
assert metadata["identifier"] == "doi:10.5061/dryad.2r12j"
assert comparison["source"]["metadata_sha256"] == sha((g / "DRYAD-DATASET-METADATA.json").read_bytes())
assert not comparison["plant_alphagenome_use"] and not comparison["professor_contact_or_endorsement"]
assert not comparison["comparison"]["empirical_capture_identified"]
for control in comparison["original_solver_controls"]:
    folder = g / "CWU-RUNS" / control["name"]
    receipt = read(folder / "EXECUTION-RECEIPT.json")
    assert sha((folder / "REQUEST.json").read_bytes()) == receipt["input_sha256"]
    assert sha((folder / "RESULT.json").read_bytes()) == receipt["result_sha256"]
    for command in receipt["commands"]:
        assert sha((folder / (command["stage"] + ".stdout")).read_bytes()) == command["stdout_sha256"]
        assert sha((folder / (command["stage"] + ".stderr")).read_bytes()) == command["stderr_sha256"]
    assert read(folder / "checker.stdout") == control["checker"]
save("CWU-STATIC-AUTHENTICATION.json", {"status": "SOURCE/SCOPE + INSPECTED ACTUAL RECEIPTS ACCEPT", "reviewer_reran_solver": False,
    "dataset_doi": metadata["identifier"], "metadata_sha256": comparison["source"]["metadata_sha256"],
    "controls": {c["name"]: {"status": c["status"], "checker": c["checker"]} for c in comparison["original_solver_controls"]},
    "scope": "hand-transcribed abstract topology incompatibility; two synthetic known-registry laws; empirical NOT_ADMITTED refusal; no chloroplast capture causal conclusion/plantAlphaGenome/professor endorsement"})
print(json.dumps({"correspondence": "4226/192/39, corrected source identity and exact Copy carrier", "g6_fixed_chart": "42 primitive exposures/12controls", "cwu": "synthetic2+empiricalrefusal scope"}))
