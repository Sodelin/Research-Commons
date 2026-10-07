"""Executed rational controls; not a substitute for Lean or all-source proofs."""
from __future__ import annotations
import hashlib
import json
import platform
import time
from dataclasses import FrozenInstanceError, replace
from datetime import datetime, timezone
from fractions import Fraction as Q
from pathlib import Path

from finite_source_prefix import (Leaf, PrefixCertificate, SourceParameters, SourceState,
    bind, contains, graft, hybrid_boundary, joint_readout, leaves, poisson_prefix,
    source_epoch, source_step, tv)

START = datetime.now(timezone.utc).isoformat()
T0 = time.monotonic()
checks = 0
families: dict[str, int] = {}

def check(ok: bool, family: str) -> None:
    global checks
    if not ok:
        raise AssertionError(f"Failed exact control in {family}")
    checks += 1
    families[family] = families.get(family, 0) + 1

def raises(fn, exception, family: str) -> None:
    try:
        fn()
    except exception:
        check(True, family)
    else:
        check(False, family)

def qstr(x: Q) -> str:
    return f"{x.numerator}/{x.denominator}"

# An actual positive four-species rooted binary cut-child source with a bigon.
EDGES = {
    "r-u": ("r", "u"), "r-cd": ("r", "cd"),
    "arm0": ("u", "h"), "arm1": ("u", "h"),
    "h-ab": ("h", "ab"), "ab-a": ("ab", "a"),
    "ab-b": ("ab", "b"), "cd-c": ("cd", "c"), "cd-d": ("cd", "d")}
AGES = {"r": 4, "u": 3, "h": 2, "ab": 1, "cd": 1,
        "a": 0, "b": 0, "c": 0, "d": 0}
TIPS = {"a", "b", "c", "d"}
for v in AGES:
    indeg = sum(b == v for a, b in EDGES.values())
    outdeg = sum(a == v for a, b in EDGES.values())
    expected = (0, 2) if v == "r" else (2, 1) if v == "h" else \
               (1, 0) if v in TIPS else (1, 2)
    check((indeg, outdeg) == expected, "admitted-source-fixture")
for a, b in EDGES.values():
    check(AGES[a] > AGES[b], "admitted-source-fixture")
def reach(exclude_node=None, exclude_edge=None):
    seen, todo = set(), ["r"]
    while todo:
        v = todo.pop()
        if v in seen or v == exclude_node:
            continue
        seen.add(v)
        todo += [b for e, (a, b) in EDGES.items() if a == v and e != exclude_edge]
    return seen
check(reach() == set(AGES), "admitted-source-fixture")
for v in set(AGES) - {"r"}:
    check(bool(TIPS.intersection(reach(exclude_node=v))), "admitted-source-fixture")
check(not {"a", "b"}.intersection(reach(exclude_edge="h-ab")), "admitted-source-fixture")
# An undirected bridge test respects parallel edges as different original IDs.
seen, todo = set(), ["h"]
while todo:
    v = todo.pop()
    if v in seen:
        continue
    seen.add(v)
    for e, (a, b) in EDGES.items():
        if e != "h-ab" and v in (a, b):
            todo.append(b if v == a else a)
check("ab" not in seen, "admitted-source-fixture")

cert_rows = []
for mean in (Q(0), Q(1, 100), Q(1, 3), Q(1), Q(7, 2), Q(20), Q(100)):
    for eps in (Q(1, 10), Q(1, 1000), Q(1, 10**8)):
        c = poisson_prefix(mean, eps)
        c.validate()
        check(sum(c.weights, Q(0)) == 1, "rational-count-certificates")
        check(all(w >= 0 for w in c.weights), "rational-count-certificates")
        check(0 <= c.deficit <= eps, "rational-count-certificates")
        check(c.degree + 2 >= 2 * mean, "rational-count-certificates")
        for k, w in enumerate(c.retained):
            check(w == c.terms[k] / c.upper_exp, "rational-count-coefficients")
        cert_rows.append({"mean": qstr(mean), "epsilon": qstr(eps),
                          "degree": c.degree, "deficit": qstr(c.deficit)})

raises(lambda: poisson_prefix(-1, "1/10"), ValueError, "reject-invalid-inputs")
raises(lambda: poisson_prefix(1, 0), ValueError, "reject-invalid-inputs")
raises(lambda: poisson_prefix(1.0, "1/10"), TypeError, "reject-invalid-inputs")
raises(lambda: poisson_prefix(1, "1/10", max_degree=True), ValueError, "reject-invalid-inputs")
raises(lambda: poisson_prefix(20, "1/1000", max_degree=1), RuntimeError, "resource-not-exclusion")
raises(lambda: replace(poisson_prefix(1, "1/1000"), upper_exp=Q(1)).validate(),
       ValueError, "forged-certificate-rejection")
raises(lambda: PrefixCertificate(Q(10), Q(1, 10), 0, (Q(1),), Q(21)).validate(),
       ValueError, "forged-certificate-rejection")

rates = tuple(sorted([(e, Q(1)) for e in EDGES] + [("ROOT", Q(1))]))
parameters = SourceParameters(rates, 4)
check(parameters.global_bound == (1 + 10) * 17, "pinned-source-rate-bound")
raises(lambda: SourceParameters(rates, 2.5), ValueError, "reject-invalid-inputs")
initial = SourceState.make({"ROOT": [Leaf(x) for x in sorted(TIPS)]}, {"h": False})
step = source_step(parameters, initial, 9)
check(len(step) == 7, "actual-current-pair-step")
check(step[initial] == 1 - Q(6, 1) / parameters.global_bound, "actual-current-pair-step")
for s, mass in step.items():
    s.validate()
    if s != initial:
        check(mass == 1 / parameters.global_bound, "actual-current-pair-step")
    check(s.registers == initial.registers, "original-register-preservation")

forest_rows = []
for duration in (Q(0), Q(1, 200), Q(1, 50)):
    law, c = source_epoch(parameters, initial, duration, 9, Q(1, 10**7))
    check(sum(law.values(), Q(0)) == 1, "whole-forest-law")
    check(all(p > 0 for p in law.values()), "whole-forest-law")
    exact_no_merge = poisson_prefix(6 * duration, Q(1, 10**15))
    lo, hi = exact_no_merge.lower_exp_minus, 1 / exact_no_merge.partial
    # A narrower rigorous scalar interval is contained in the claimed error box.
    check(law[initial] - c.deficit <= lo, "exact-scalar-crosscheck")
    check(hi <= law[initial] + c.deficit, "exact-scalar-crosscheck")
    for s in law:
        check(set().union(*(leaves(t) for _, ts in s.populations for t in ts)) == TIPS,
              "label-preservation")
        check(s.registers == initial.registers, "original-register-preservation")
    panels = (frozenset({"a", "b"}), frozenset({"a", "b"}))
    joint = joint_readout(law, panels)
    check(sum(joint.values(), Q(0)) == 1, "same-locus-joint-record")
    check(all(a == b for a, b in joint), "same-locus-joint-record")
    if duration:
        marg = {a: mass for (a, b), mass in joint.items()}
        false_off_diagonal = sum((p * q for a, p in marg.items()
                                 for b, q in marg.items() if a != b), Q(0))
        check(false_off_diagonal > 0, "reject-independent-same-locus-product")
        check(sum(c.retained, Q(0)) < 1, "reject-silent-tail-loss")
    forest_rows.append({"duration": qstr(duration), "states": len(law),
                        "degree": c.degree, "error_bound": qstr(c.deficit)})

# A whole OLD subtree counts as ONE live root, not one coin/clock per old leaf.
old = graft(Leaf("a:1"), Leaf("a:2"), 7)
entering = SourceState.make({"h-ab": [old, Leaf("b:1")],
                            "r-cd": [Leaf("c:1"), Leaf("d:1")]}, {"h": False})
parameters5 = SourceParameters(rates, 5)
entered_step = source_step(parameters5, entering, 9)
check(entered_step[entering] == 1 - Q(2) / parameters5.global_bound,
      "current-root-not-original-tip-count")
for s in entered_step:
    check(any(contains(t, old) for _, ts in s.populations for t in ts), "old-subtree-bin-preservation")

args = dict(child="h-ab", parent0="arm0", parent1="arm1", original_id="h", gamma=Q(1, 3))
independent = hybrid_boundary(entering, common=False, **args)
check(len(independent) == 4, "independent-current-root-routing")
check(sum(independent.values(), Q(0)) == 1, "independent-current-root-routing")
check(sorted(independent.values()) == sorted((Q(1, 9), Q(2, 9), Q(2, 9), Q(4, 9))),
      "independent-current-root-routing")
common0 = hybrid_boundary(entering, common=True, **args)
common1 = hybrid_boundary(replace(entering, registers=(("h", True),)), common=True, **args)
check(len(common0) == len(common1) == 1, "common-register-not-resampled")
check(dict(next(iter(common0)).populations)["arm0"] == dict(entering.populations)["h-ab"],
      "common-register-not-resampled")
check(dict(next(iter(common1)).populations)["arm1"] == dict(entering.populations)["h-ab"],
      "common-register-not-resampled")
for s in independent.keys() | common0.keys() | common1.keys():
    check(any(contains(t, old) for _, ts in s.populations for t in ts), "old-subtree-bin-preservation")
raises(lambda: hybrid_boundary(replace(entering, registers=()), common=True, **args),
       ValueError, "missing-original-register-rejection")
raises(lambda: source_step(parameters, SourceState.make({"INVENTED": [Leaf("a")]}), 0),
       ValueError, "unknown-physical-ID-rejection")
raises(lambda: source_step(parameters, SourceState.make({"ROOT": [Leaf("a"), Leaf("a")]}), 0),
       ValueError, "duplicate-copy-rejection")
raises(lambda: source_step(parameters, initial, -1), ValueError, "reject-invalid-inputs")
raises(lambda: setattr(parameters, "rates", ()), FrozenInstanceError, "shared-rate-bank-immutable")

# Two numerical epochs reuse ONE source/rate bank; no rate refit at their boundary.
p1, c1 = source_epoch(parameters, initial, Q(1, 400), 9, Q(1, 10**6))
c2 = poisson_prefix(parameters.global_bound / 400, Q(1, 10**6))
p12 = bind(p1, lambda s: source_epoch(parameters, s, Q(1, 400), 9, Q(1, 10**6))[0])
pwhole, cwhole = source_epoch(parameters, initial, Q(1, 200), 9, Q(1, 10**6))
check(tv(p12, pwhole) <= c1.deficit + c2.deficit + cwhole.deficit,
      "shared-rate-epoch-composition-crosscheck")
check(tv(joint_readout(p12, (frozenset({"a", "b"}),)),
         joint_readout(pwhole, (frozenset({"a", "b"}),))) <= tv(p12, pwhole),
      "joint-observer-contraction-crosscheck")

HERE = Path(__file__).parent
out = {"status": "PASS_REFERENCE_CONTROLS_NOT_LEAN", "started_utc": START,
       "finished_utc": datetime.now(timezone.utc).isoformat(),
       "seconds": round(time.monotonic() - T0, 6), "python": platform.python_version(),
       "checks": checks, "families": families, "count_certificates": cert_rows,
       "whole_forest_fixtures": forest_rows,
       "source_sha256": hashlib.sha256((HERE / "finite_source_prefix.py").read_bytes()).hexdigest(),
       "test_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       "scope": "Exact rational finite controls and scalar interval crosschecks; no Lean execution, "
                "global source catalogue, graph-to-calendar compiler, unbounded-source closure "
                "or statistical master execution."}
(HERE / "evidence" / "reference-tests.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({k: out[k] for k in ("status", "checks", "families", "seconds", "python")}, indent=2))
