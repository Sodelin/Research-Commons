"""Read-only text identities and bounded static checks; executes no reviewed code."""
from pathlib import Path
from datetime import datetime, timezone
import ast
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[5]
PACKET = ROOT / "research/2026-10-10-codex-lean-rust-parity"
OUT = Path(__file__).resolve().parent
NOTE = PACKET / "rust/notes/HISTORY-RUNTIME-ASSEMBLY-AUDIT-20261010T2043Z.md"
RECOVERY = "research/2026-10-04-dot-practical-solver-recovery-1803z"

groups = {
    "instructions_and_scope": [
        "AGENTS.md", "START-HERE.md", "applications/AGENTS.md",
        "docs/RESEARCH-COMPLETION-STANDARD.md",
        "research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md",
        "handoffs/2026-10-09-goal-oriented-finish-lines/FINISH-LINES.md",
        "research/2026-10-09-codex-conditional-bridge-1630z/OBLIGATIONS.md",
        "research/2026-10-09-codex-conditional-bridge-1630z/bounded/README.md",
    ],
    "current_application_body_or_scope": [
        "applications/practical-solver/run.py", "applications/practical-solver/README.md",
        "applications/practical-solver/SOURCE-IDENTITIES.json",
        "applications/practical-solver/certified-bounds-sources.json",
        "applications/practical-solver/certified_bounds.py",
        "applications/practical-solver/forest_baseline.py",
        "applications/practical-solver/diagnostic.py",
        "applications/practical-solver-biology/offline.py",
    ],
    "old_numerical_confidence_and_source_bodies": [
        "research/2026-09-30-robust-statistical-recovery/cf_confidence.py",
        "research/2026-09-30-robust-statistical-recovery/robust_support.py",
        "research/2026-09-30-astra-statistical-bridge/confidence_support.py",
        "research/2026-10-01-sol61-g3-interior-2025z/closure_bounds.py",
        "research/2026-10-01-g7-continuous-design/source_census.py",
        "research/2026-10-01-g7-continuous-design/law_compiler.py",
        "research/2026-10-01-g7-continuous-design/README.md",
        "research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md",
        "research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py",
        "research/2026-10-07-dot-typed-jc-source-supplement-0803z/README.md",
        "research/2026-10-07-dot-typed-jc-source-supplement-0803z/layout/practical-typed-jc-adapter-20261007-0532z/jc_history_adapter.py",
    ],
    "recovered_policy_source_excerpts": [
        RECOVERY + "/README.md",
        RECOVERY + "/01-exact-source-solver/package/solver.py",
        RECOVERY + "/01-exact-source-solver/package/verify_certificate.py",
        RECOVERY + "/01-exact-source-solver/package/bounded_search.py",
        RECOVERY + "/01-exact-source-solver/package/export_design.py",
        RECOVERY + "/02-forced-pair-policy/package/execute_forced_pair_policy.py",
        RECOVERY + "/02-forced-pair-policy/package/check_forced_pair_policy.py",
        RECOVERY + "/03-terminal-33-pairs/package/experimental_last_call_solver.py",
        RECOVERY + "/04-terminal-adapter/package/terminal_g7.py",
        RECOVERY + "/04-terminal-adapter/package/terminal_engine.py",
        RECOVERY + "/05-recursive-execution/package/recursive_g7.py",
        RECOVERY + "/05-recursive-execution/package/recursive_engine.py",
        RECOVERY + "/06-passive-whole-policy/package/whole-policy-instance.wl",
        RECOVERY + "/06-passive-whole-policy/package/README.md",
        RECOVERY + "/08-supplied-policy-verifier/package/verify_actual_policy.py",
        RECOVERY + "/08-supplied-policy-verifier/package/execute_actual_policy.py",
        RECOVERY + "/08-supplied-policy-verifier/package/verify_policy.py",
        RECOVERY + "/08-supplied-policy-verifier/package/README.md",
        RECOVERY + "/09-affine-word-decoder/package/compile_leaves.py",
        RECOVERY + "/10-algebraic-sections/package/README.md",
        RECOVERY + "/13-private-common-moments/package/common_moment_slots.py",
        RECOVERY + "/13-private-common-moments/package/COMMON-MOMENT-REFINEMENT.md",
        RECOVERY + "/13-private-common-moments/package/INTEGRATION-CONTRACT.md",
    ],
    "later_policy_derivative_bodies_and_review": [
        "research/2026-10-04-dot-principal-root-cad-policy-2347z/package/verify_algebraic_policy.py",
        "research/2026-10-04-dot-principal-root-cad-policy-2347z/package/assemble_cad_terminal_policy.py",
        "research/2026-10-04-dot-principal-root-cad-policy-2347z/package/README.md",
        "research/2026-10-04-dot-principal-root-cad-policy-2347z/independent-review/REVIEW.md",
        "research/2026-10-04-dot-terminal-cad-policy-integration-2224z/independent-review/REVIEW.md",
    ],
    "old_rust_body_or_dated_status": [
        "research/2026-10-07-rust-count-pilot/src/lib.rs",
        "research/2026-10-08-cloud-rust-interval-root-0000z/src/lib.rs",
        "research/2026-10-08-cloud-rust-signed-nine-0008z/src/lib.rs",
        "research/2026-10-08-cloud-rust-signed-nine-0008z/README.md",
        "research/2026-10-08-cloud-rust-signed-probe-0122z/README.md",
        "research/2026-10-08-cloud-rust-signed-nine-review-sol-0119z/README.md",
        "research/2026-10-07-cloud-practical-native-rust-transfer-2358z/README.md",
        "research/2026-10-07-rust-solver-architecture/README.md",
    ],
    "current_native_interface_excerpts": [
        "research/2026-10-10-codex-lean-rust-parity/rust/Cargo.toml",
        "research/2026-10-10-codex-lean-rust-parity/rust/INHERITED-SOURCES.json",
        "research/2026-10-10-codex-lean-rust-parity/rust/calendar-cli/src/lib.rs",
        "research/2026-10-10-codex-lean-rust-parity/rust/calendar-cli/src/request.rs",
        "research/2026-10-10-codex-lean-rust-parity/rust/src/source_population.rs",
        "research/2026-10-10-codex-lean-rust-parity/rust/src/source_calendar.rs",
        "research/2026-10-10-codex-lean-rust-parity/rust/src/natural_cell.rs",
        "research/2026-10-10-codex-lean-rust-parity/rust/native_calendar_component.py",
        "research/2026-10-10-codex-lean-rust-parity/design/calendar_check.py",
        "research/2026-10-10-codex-lean-rust-parity/design/CALENDAR-APPLICATION-CONTRACT-20261010T1458Z.md",
    ],
    "typed_provider_body_and_scope_excerpts": [
        "research/2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/FiniteSourceSnapshot.lean",
        "research/2026-10-09-dot-g7-original-registry-admission-1908z/sources/G7OriginalAdmission.lean",
        "research/2026-10-10-dot-g2-current-source-verification-0042z/COMPLETE-CURRENT-G2-CERTIFICATE-SCOPE.md",
        "research/2026-10-10-dot-g2-current-source-verification-0042z/RUNTIME-COMPANION-CRITERION-ADDENDUM.md",
        "research/2026-10-10-codex-lean-rust-parity/reuse/sources/G7NamedCalendarSourceAdmission.lean",
        "research/2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveWordCoefficients.lean",
        "research/2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveCompletedWordCoefficients.lean",
        "research/2026-10-10-codex-lean-rust-parity/design/lean/G7OriginalCompletedCalendarLaw.lean",
        "research/2026-10-10-codex-lean-rust-parity/design/GOAL-STATUS.md",
        "research/2026-10-10-codex-lean-rust-parity/design/G6-G7-REUSE-STATUS.md",
    ],
    "preserved_receipt_metadata_not_reexecuted": [
        RECOVERY + "/05-recursive-execution/package/REPORTS.json",
        RECOVERY + "/08-supplied-policy-verifier/package/TEST-RECEIPT.json",
        RECOVERY + "/08-supplied-policy-verifier/package/ACTUAL-WORKFLOW-RECEIPT.json",
        RECOVERY + "/08-supplied-policy-verifier/package/VERIFIED-POLICY-RECEIPT.json",
        RECOVERY + "/08-supplied-policy-verifier/package/ADVERSARIAL-CONTROLS.json",
        "research/2026-10-10-codex-lean-rust-parity/quality/evidence/application-calendar-integration-20261010T1505Z/RECEIPT.json",
        "research/2026-10-10-codex-lean-rust-parity/design/evidence/calendar-general-frontend-review-1/RECEIPT.json",
        "research/2026-10-10-codex-lean-rust-parity/rust/evidence/calendar-completed-application-1/RECEIPT.json",
        "research/2026-10-10-codex-lean-rust-parity/lean/ORIGINAL-CALENDAR-LAW-CERTIFICATE.json",
        "research/2026-10-10-codex-lean-rust-parity/lean/EFFECTIVE-WORD-CERTIFICATE.json",
        "research/2026-10-10-codex-lean-rust-parity/lean/EFFECTIVE-COMPLETED-WORD-CERTIFICATE.json",
        "research/2026-10-10-codex-lean-rust-parity/lean/NAMED-CALENDAR-SOURCE-ADMISSION-CERTIFICATE.json",
        "research/2026-10-10-codex-lean-rust-parity/lean/RATIONAL-COMPRESSION-CERTIFICATE.json",
    ],
}

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

captured = {}
rows = []
for role, names in groups.items():
    for name in names:
        path = ROOT / name
        assert path.is_file() and not path.is_symlink(), name
        raw = path.read_bytes()
        raw.decode("utf-8")  # Never copy/read a compiled ELF as audit evidence.
        captured[name] = raw
        rows.append({"path": name, "sha256": digest(raw), "bytes": len(raw), "inspection": role})

checks = []
def require(name, condition):
    checks.append({"name": name, "pass": bool(condition)})
    if not condition:
        raise AssertionError(name)

launcher = captured["applications/practical-solver/run.py"]
tree = ast.parse(launcher)
commands = {node.args[0].value for node in ast.walk(tree)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
    and node.func.attr == "add_parser" and node.args
    and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str)}
# Four current native commands share a literal (name, help_text) tuple loop.
# Resolve only this statically visible data, without importing the launcher.
for node in ast.walk(tree):
    if isinstance(node, ast.For) and isinstance(node.target, ast.Tuple) \
            and [v.id for v in node.target.elts if isinstance(v, ast.Name)] == ["name", "help_text"]:
        require("launcher_native_command_loop_is_literal_tuple", isinstance(node.iter, ast.Tuple))
        commands.update(pair[0] for pair in ast.literal_eval(node.iter))
cli = sorted(commands)
require("current_public_command_set", cli == sorted([
    "run", "show", "check", "molecular", "certified-bounds", "forest-baseline",
    "affine-cell", "natural-cell", "genealogy-law", "calendar-law"]))
old_census = captured["research/2026-10-01-g7-continuous-design/source_census.py"]
old_law = captured["research/2026-10-01-g7-continuous-design/law_compiler.py"]
require("old_census_exact_current_pin", digest(old_census) ==
        "d004c3730d26ebffa9ec19d842adc0b86bcaac46e216228c15b295b0c5f94396")
require("old_law_exact_current_pin", digest(old_law) ==
        "eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7")
manifest = captured["applications/practical-solver/certified-bounds-sources.json"].decode()
require("public_source_backend_already_pins_census_and_law",
        digest(old_census) in manifest and digest(old_law) in manifest)
app_receipt = json.loads(captured[
    "research/2026-10-10-codex-lean-rust-parity/quality/evidence/application-calendar-integration-20261010T1505Z/RECEIPT.json"])
require("current_launcher_matches_preserved_final_app_receipt",
        app_receipt["application_current_launcher"]["sha256"] == digest(launcher))
require("final_app_receipt_retains_18_checks", app_receipt["current_launcher_checks"] == 18)
front = json.loads(captured[
    "research/2026-10-10-codex-lean-rust-parity/design/evidence/calendar-general-frontend-review-1/RECEIPT.json"])
require("saved_general_frontend_pass", front["pass"] is True and front["cases_passed"] == 34
        and front["full_view_rows"] == 259)
completed = json.loads(captured[
    "research/2026-10-10-codex-lean-rust-parity/rust/evidence/calendar-completed-application-1/RECEIPT.json"])
require("saved_completed_app_three_38", completed["status"] == "PASS"
        and completed["cases_passed"] == 3 and completed["full_view_rows"] == 38)
for name in groups["preserved_receipt_metadata_not_reexecuted"]:
    if "/lean/" in name and name.endswith("CERTIFICATE.json"):
        cert = json.loads(captured[name])
        require("saved_kernel_certificate_status:" + Path(name).name,
                cert["status"] == "PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS")

files = subprocess.check_output(["rg", "--files", "research", "-g", "*.py", "-g", "*.wl"],
                                cwd=ROOT, text=True).splitlines()
census_paths = sorted(name for name in files if Path(name).name == "source_census.py")
copy_groups = {}
for name in census_paths:
    raw = (ROOT / name).read_bytes()
    raw.decode("utf-8")
    copy_groups.setdefault(digest(raw), []).append(name)
require("census_copy_group_contains_current_pinned_upstream",
        "research/2026-10-01-g7-continuous-design/source_census.py" in copy_groups[digest(old_census)])
rust_roots = sorted(p.name for p in (ROOT / "research").iterdir()
    if p.is_dir() and p.name < "2026-10-10" and ("rust" in p.name or any(p.glob("Cargo.toml"))))
package_roots = sorted(p.name for p in (ROOT / RECOVERY).iterdir()
                       if p.is_dir() and (p / "package").is_dir())
require("historical_recovered_component_index_13", len(package_roots) == 13)

unchanged = all((ROOT / name).read_bytes() == raw for name, raw in captured.items())
require("all_selected_text_inputs_stable_during_static_review", unchanged)
receipt = {
    "schema": "history_runtime_assembly_readonly_audit_v1",
    "status": "PASS_STATIC_SOURCE_AND_RECEIPT_BINDINGS",
    "reviewer": "Codex / rust_implementation",
    "ended_utc": datetime.now(timezone.utc).isoformat(),
    "note": str(NOTE.relative_to(ROOT)), "note_sha256": digest(NOTE.read_bytes()),
    "reviewer_sha256": digest(Path(__file__).read_bytes()),
    "preserved_preparatory_attempt": {
        "path": str((OUT / "ATTEMPT-1.json").relative_to(ROOT)),
        "sha256": digest((OUT / "ATTEMPT-1.json").read_bytes()),
        "qualification": "Reviewer-only literal-loop discovery corrected; no product defect inferred"},
    "inspected_artifacts": len(rows), "files": rows, "static_checks": checks,
    "public_commands": cli,
    "discovery": {"searchable_research_python_wolfram_paths": len(files),
        "filename_screen_only_not_all_bodies_reviewed": True,
        "historical_rust_roots_name_or_direct_cargo": rust_roots,
        "recovered_component_package_roots": package_roots,
        "source_census_copy_groups": copy_groups,
        "root_owns_separate_git_historical_inventory": True},
    "execution": {"reviewed_code_imported_or_executed": False, "native_solver_execution": False,
        "application_execution": False, "Lean_execution": False, "builds": False,
        "old_suites_rerun": False, "policy_backends_run": False, "ELF_copies": 0,
        "git_operations": False, "code_or_runtime_edits": False,
        "writes": "New owned audit note/reviewer/receipt only"},
    "claim_limits": ["Static bodies and preserved evidence, not new numerical/kernel evidence",
        "Bounded historical source audit, not exhaustive all-commit/all-file inspection",
        "No generic parser/producer refinement or full source-admission promotion",
        "No empirical confidence, timed observer or general G6/G7 practical closure",
        "Existing G1/G2/G5 mathematics not reopened; G3/G4 obligations kept separate"]}
with (OUT / "RECEIPT.json").open("x") as handle:
    json.dump(receipt, handle, indent=2, sort_keys=True)
    handle.write("\n")
print(json.dumps({"status": receipt["status"], "artifacts": len(rows),
    "static_checks": len(checks), "note_sha256": receipt["note_sha256"],
    "receipt_sha256": digest((OUT / "RECEIPT.json").read_bytes())}, sort_keys=True))
