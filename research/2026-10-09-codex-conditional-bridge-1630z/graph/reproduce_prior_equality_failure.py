"""Compare the prior recursive expression with the final iterative equality.

The two earlier failure-seeking probes did not reproduce a crash. This final
check does not require or claim a failure in the previous expression.
"""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "applications/practical-solver"))
from forest_baseline import ForestGraph

m = 2000
tree = 1
for label in range(2, m + 1):
    tree = (tree, label)
graph = ForestGraph(m)
forest = (tree,)
decoded = graph.decode(graph.encode(forest))
try:
    previous_expression_result = forest == decoded
    failure = {"observed": False, "previous_expression_result": previous_expression_result}
except RecursionError as error:
    failure = {"observed": True, "exception": type(error).__name__, "message": str(error)}
corrected_entry = graph.generator_entry(forest, decoded)
print(json.dumps({"status": "PASS_DEEP_EQUALITY_COMPARISON" if corrected_entry == 0 else "FAIL",
                  "evidence_tier": "authored_execution", "m": m, "depth": m - 1,
                  "prior_module_sha256": "44b13e8cc1b90a789880f07a974cb3c4c89ba546b5c55b24f6e20780ef054598",
                  "scope": "Direct comparison of prior f==g expression and final iterative generator_entry on independently decoded deep tuples. No prior crash or whole former-module replay claimed.",
                  "failure": failure, "corrected_generator_entry": corrected_entry}, indent=2))
raise SystemExit(corrected_entry != 0)
