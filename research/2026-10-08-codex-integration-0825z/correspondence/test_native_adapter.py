"""Independent source-definition oracle versus actual pinned Python calls.

No native binary/Lean theorem is executed. Native probabilities below are a
literal finite enumeration of inspected original measure/router definitions.
"""
from collections import defaultdict
from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
import hashlib
import json
import importlib.util
import os
from pathlib import Path
import platform
import py_compile
import sys
from datetime import datetime, timezone
from unittest.mock import patch

import native_adapter as a

checks = defaultdict(int)


def check(condition, name):
    if not condition:
        raise AssertionError(name)
    checks[name] += 1


def refuses(fn, name):
    try:
        fn()
    except (ValueError, TypeError, RuntimeError):
        checks["refusal:" + name] += 1
    else:
        raise AssertionError("Accepted invalid input: " + name)


def contract(gamma=Q(1, 3), common=False):
    return a.Contract(("h", "k", "outside", "root"),
                      tuple(sorted((p, Q(i + 1, 7)) for i, p in enumerate(
                          ("child:h", "parent:h:0", "parent:h:1", "child:k",
                           "parent:k:0", "parent:k:1", "root-population")))),
                      12,
                      (a.Hybrid("h", "child:h", "parent:h:0", "parent:h:1", gamma, common),
                       a.Hybrid("k", "child:k", "parent:k:0", "parent:k:1", Q(2, 5), True)),
                      ((Q(1), (("exit", "child:h"), ("exit", "child:k"),
                               ("node", "h"), ("node", "k"))),),
                      (Q(1, 4), Q(1, 2)))


def record(c, m, bit, old=False):
    roots = tuple(a.Leaf(f"a:{i}") for i in range(m))
    if old and m:
        roots = (a.ref.graft(a.Leaf("old:left"), a.Leaf("old:right"), 2),) + roots[1:]
    populations = {"parent:h:0": [a.Leaf("already:0")],
                   "parent:h:1": [a.Leaf("already:1")], "child:h": roots}
    registers = {v: False for v in c.vertices}
    registers["h"] = bit
    active_labels = sum(len(a.ref.leaves(t)) for ts in populations.values() for t in ts)
    outside = [a.Leaf("outside:retained")]
    outside += [a.Leaf(f"outside:filler:{i}") for i in range(c.copy_cap - active_labels - 1)]
    return a.FullRecord(a.SourceState.make(populations, registers),
                        (("outside", tuple(sorted(outside, key=a.ref.tree_key))),))


def native_definition_oracle(r, c, h):
    """Defined product TRUE gamma + actual same-parent deterministic router.

    The guarded child exit sends all child roots to AtNode h, then the native
    pulse routes precisely those current roots. The quotient forgets only
    current survivor identity and binary child order; all payload stays.
    """
    roots = dict(r.physical.populations).get(h.child, ())
    regs = dict(r.physical.registers)
    choices = [(tuple(regs[h.original_id] for _ in roots), Q(1))] if h.common else [
        (bits, h.gamma_native ** sum(bits) * (1 - h.gamma_native) ** (len(bits) - sum(bits)))
        for bits in product((False, True), repeat=len(roots))]
    out = defaultdict(Q)
    for bits, mass in choices:
        physical = {p: list(ts) for p, ts in r.physical.populations if p != h.child}
        for root, b in zip(roots, bits):
            physical.setdefault(h.parent1 if b else h.parent0, []).append(root)
        d = a.FullRecord(a.SourceState.make(physical, regs), r.outside_nodes)
        out[d] += mass
    return dict(out)


def projected_parent_counts(law, h):
    out = defaultdict(Q)
    for r, mass in law.items():
        pops = dict(r.physical.populations)
        # Existing one root on each parent stays and is subtracted here.
        out[(len(pops.get(h.parent0, ())) - 1, len(pops.get(h.parent1, ())) - 1)] += mass
    return [{"parent0_roots": x, "parent1_roots": y, "mass": a.qwire(mass)}
            for (x, y), mass in sorted(out.items())]


def execute():
    start = datetime.now(timezone.utc).isoformat()
    # Challenge the actual additive loader with a timestamp/size-valid hostile
    # pyc and a path reread substitution. Only own scratch files are changed.
    scratch = Path("/workspace/scratch/integration-correspondence/loader-controls")
    scratch.mkdir(parents=True, exist_ok=True)
    original_bytes = (a.ROOT / a.REFERENCE_PATH).read_bytes()
    fake_source = scratch / "finite_source_prefix.py"
    malicious = b"raise RuntimeError('HOSTILE_PYC_EXECUTED')\n"
    malicious += b" " * (len(original_bytes) - len(malicious))
    fake_source.write_bytes(malicious)
    stamp = fake_source.stat()
    py_compile.compile(str(fake_source), doraise=True)
    fake_source.write_bytes(original_bytes)
    os.utime(fake_source, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
    spec = importlib.util.spec_from_file_location("hostile_control", fake_source)
    try:
        spec.loader.exec_module(importlib.util.module_from_spec(spec))
    except RuntimeError as error:
        check(str(error) == "HOSTILE_PYC_EXECUTED", "hostile-timestamp-valid-pyc-standard-loader-countercontrol")
    else:
        raise AssertionError("Hostile-pyc fixture was not effective.")
    exact_module = a.load_reference(fake_source)
    check(exact_module.hybrid_boundary.__code__.co_filename == str(fake_source),
          "captured-source-loader-bypasses-hostile-pyc")
    # Substitution occurs after the read returns but before execution. This
    # simulates the historical hash/reopen gap without mutating inherited code.
    substituted = scratch / "read-substitution.py"
    substituted.write_bytes(original_bytes)
    original_read = Path.read_bytes
    def capture_then_replace(path):
        data = original_read(path)
        if path == substituted:
            substituted.write_bytes(malicious)
        return data
    with patch.object(Path, "read_bytes", capture_then_replace):
        module = a.load_reference(substituted)
    check(module.hybrid_boundary.__code__.co_filename == str(substituted),
          "captured-source-loader-ignores-after-read-substitution")
    check(substituted.read_bytes() == malicious, "read-substitution-fixture-effective")
    refuses(lambda: a.load_reference(substituted), "altered-source-identity")
    sys.modules["correspondence_frozen_reference"] = a.ref
    boundary_tables = []
    for g in (Q(1, 7), Q(1, 3), Q(1, 2), Q(5, 6)):
        for common in (False, True):
            c = contract(g, common)
            for m, bit, old in product(range(6), (False, True), (False, True)):
                r = record(c, m, bit, old)
                actual = a.adapted_child_boundary(r, c, "h")
                expected = native_definition_oracle(r, c, c.hybrids[0])
                check(actual == expected, "actual-python-boundary-v-native-definition")
                check(sum(actual.values(), Q(0)) == 1, "boundary-exact-normalization")
                for d in actual:
                    check(d.physical.registers == r.physical.registers,
                          "same-stored-total-register")
                    check(d.outside_nodes == r.outside_nodes, "outside-node-payload-preserved")
                    check(all(any(a.ref.contains(t, oldtree) for _, ts in d.physical.populations for t in ts)
                              for _, trees in r.physical.populations for oldtree in trees),
                          "all-old-subtrees-labels-tags-preserved")
                if g == Q(1, 3) and m == 2 and not old:
                    boundary_tables.append({"gamma_native": a.qwire(g),
                                            "gamma_python": a.qwire(c.hybrids[0].gamma_python),
                                            "common": common, "stored_h_bit": bit,
                                            "parent0": c.hybrids[0].parent0,
                                            "parent1": c.hybrids[0].parent1,
                                            "rows": projected_parent_counts(actual, c.hybrids[0])})
                wire = a.serialize_law(actual, c)
                restored = a.deserialize_law(wire, c)
                check(restored == actual, "lossless-state-law-wire-roundtrip")
                check(a.serialize_law(dict(reversed(list(actual.items()))), c) == wire,
                      "canonical-wire-independent-of-dictionary-insertion")

    # Same Bool + fixed parents: unchanged gamma has an exact nonzero failure.
    c = contract(Q(1, 3), False)
    r = record(c, 1, False)
    h = c.hybrids[0]
    wrong = {a.FullRecord(s, r.outside_nodes): p for s, p in a.ref.hybrid_boundary(
        r.physical, child=h.child, parent0=h.parent0, parent1=h.parent1,
        original_id=h.original_id, gamma=h.gamma_native, common=False).items()}
    right = a.adapted_child_boundary(r, c, "h")
    check(a.ref.tv(wrong, right) == Q(1, 3), "unchanged-gamma-countercontrol-TV-one-third")

    # The same parameter bug in a hypothetical Python COMMON initializer is
    # visible BEFORE routing: True mass 1-g rather than g with unchanged eta.
    native_init = {(False,): 1 - h.gamma_native, (True,): h.gamma_native}
    wrong_init = {(False,): h.gamma_native, (True,): 1 - h.gamma_native}
    check(a.ref.tv(native_init, wrong_init) == Q(1, 3), "unchanged-gamma-COMMON-init-countercontrol")

    # Natural original initializer draws every actual hybrid, then sets all
    # nonhybrid V slots false. COMMON reads that law once, not fresh per pulse.
    for g in (Q(1, 7), Q(1, 3), Q(1, 2), Q(5, 6)):
        for common in (False, True):
            c = contract(g, common)
            initial = a.original_register_law(c)
            check(sum(initial.values(), Q(0)) == 1, "initializer-normalization")
            for regs, mass in initial.items():
                register = dict(regs)
                direct_mass = Q(1)
                for hybrid in c.hybrids:
                    direct_mass *= hybrid.gamma_native if register[hybrid.original_id] else 1 - hybrid.gamma_native
                check(mass == direct_mass, "initializer-native-product-at-every-original-hybrid")
                check(not register["outside"] and not register["root"], "initializer-inert-nonhybrid-false")
            marginal = sum((m for reg, m in initial.items() if dict(reg)["h"]), Q(0))
            check(marginal == g, "initializer-native-true-gamma")
            mixture = {}
            for regs, mass in initial.items():
                base = record(c, 2, False)
                state = replace(base, physical=replace(base.physical, registers=regs))
                mixture[state] = mass
            actual = a.adapted_law(mixture, c, "h")
            expected = defaultdict(Q)
            for state, mass in mixture.items():
                for d, p in native_definition_oracle(state, c, c.hybrids[0]).items():
                    expected[d] += mass * p
            check(actual == dict(expected), "same-initial-register-boundary-mixture")

    # A correlated past/register is carried, not manufactured as independent.
    c = contract(Q(1, 3), True)
    correlated = {}
    for bit, mass in ((False, Q(2, 3)), (True, Q(1, 3))):
        base = record(c, 1, bit)
        old = a.ref.graft(a.Leaf("past:L"), a.Leaf("past:R"), int(bit))
        retained = [t for _, ts in base.outside_nodes for t in ts
                    if t.label not in ("outside:retained", "outside:filler:0")]
        correlated[replace(base, outside_nodes=(("outside", tuple(sorted([old] + retained, key=a.ref.tree_key))),))] = mass
    transported = a.adapted_law(correlated, c, "h")
    for d, mass in transported.items():
        bit = dict(d.physical.registers)["h"]
        tag = d.outside_nodes[0][1][0].bin_tag
        populations = dict(d.physical.populations)
        check(tag == int(bit), "COMMON-correlated-past-retained")
        check(any(a.Leaf("a:0") in ts for p, ts in populations.items()
                  if p == ("parent:h:1" if bit else "parent:h:0")), "COMMON-retained-bit-actual-parent")
    proper = {(dict(d.physical.registers)["h"], d.outside_nodes[0][1][0].bin_tag): mass
              for d, mass in transported.items()}
    redraw = {(newbit, int(oldbit)): oldmass * newmass
              for oldbit, oldmass in ((False, Q(2, 3)), (True, Q(1, 3)))
              for newbit, newmass in ((False, Q(2, 3)), (True, Q(1, 3)))}
    check(a.ref.tv(proper, redraw) == Q(4, 9), "COMMON-redraw-destroys-joint-past-countercontrol")

    # Execute the literal JOINT reader, preserving same-locus dependence.
    joint_input = {}
    for tag, mass in ((0, Q(2, 3)), (1, Q(1, 3))):
        trees = [a.ref.graft(a.Leaf("A"), a.Leaf("B"), tag),
                 a.ref.graft(a.Leaf("C"), a.Leaf("D"), tag)]
        joint_input[a.SourceState.make({"root-population": trees}, {v: False for v in c.vertices})] = mass
    joint = a.ref.joint_readout(joint_input, (frozenset(("A", "B")), frozenset(("C", "D"))))
    check(len(joint) == 2, "actual-joint-reader-two-correlated-outcomes")
    first, second = defaultdict(Q), defaultdict(Q)
    for pair, mass in joint.items():
        first[pair[0]] += mass
        second[pair[1]] += mass
    independent = {(x, y): p * q for x, p in first.items() for y, q in second.items()}
    check(len(independent) == 4 and a.ref.tv(joint, independent) == Q(4, 9),
          "panel-marginal-product-countercontrol-TV-four-ninths")

    # Actual rational residual source_epoch table roundtrips through the SAME
    # total register and outside payload. No normalized-prefix substitution.
    c = contract(Q(1, 3), False)
    initial = record(c, 3, False, True)
    params = a.ref.SourceParameters(c.rates, c.copy_cap)
    result, cert = a.ref.source_epoch(params, initial.physical, Q(1, 500), 3, Q(1, 100))
    cert.validate()
    epoch = {a.FullRecord(s, initial.outside_nodes): p for s, p in result.items()}
    wire = a.serialize_law(epoch, c)
    check(a.deserialize_law(wire, c) == epoch, "actual-residual-source-epoch-wire-roundtrip")
    check(cert.weights[0] == cert.retained[0] + cert.deficit,
          "actual-residual-count-zero-deficit-retained")

    # Equal bin tags retain two internal nodes and JSON-sensitive leaf strings
    # remain exact; no repr parser or eval is involved in the wire protocol.
    repeated = a.ref.graft(a.ref.graft(a.Leaf('copy:"\\\nλ'), a.Leaf("copy:二"), 3),
                           a.Leaf("copy:last"), 3)
    special = a.FullRecord(a.SourceState.make({"root-population": [repeated]},
                                            {v: False for v in c.vertices}))
    special_contract = replace(c, copy_cap=3)
    special_wire = a.serialize_law({special: Q(1)}, special_contract)
    check(a.deserialize_law(special_wire, special_contract) == {special: Q(1)}, "repeated-tags-and-escaped-labels-lossless")
    check(a.unwire_tree(a.treewire(repeated)) == repeated, "repeated-tags-retain-entire-binary-graft")

    # Public physical domain refuses zero/one; algebra endpoints are merely
    # identities outside physical admission, not executable physical calls.
    for g in (Q(0), Q(1), 0.3, True, "1/3"):
        refuses(lambda g=g: contract(g).validate(), "nonphysical-gamma:" + repr(g))
    for g in (Q(0), Q(1)):
        check(Q(1) - (Q(1) - g) == g, "algebra-only-gamma-endpoints")
    refuses(lambda: replace(c, copy_cap=True).validate(), "Bool-cap")
    refuses(lambda: replace(c, hybrids=list(c.hybrids)).validate(), "mutable-shared-hybrid-bank")
    refuses(lambda: replace(c, calendar=[*c.calendar]).validate(), "mutable-calendar-agenda")
    refuses(lambda: replace(c, hybrids=(replace(c.hybrids[0], parent1=c.hybrids[0].parent0),)).validate(), "parallel-parent-ID-collision")
    refuses(lambda: replace(c, rates=c.rates + (c.rates[0],)).validate(), "duplicate-rate-ID")
    refuses(lambda: replace(c, calendar=((Q(1), (("node", "h"), ("exit", "child:h"))),)).validate(), "wrong-calendar-exit-node-order")
    refuses(lambda: replace(c, bin_cuts=(Q(1, 2), Q(1, 4))).validate(), "unsorted-bin-cuts")
    refuses(lambda: a.validate_record(replace(initial, outside_nodes=()), c), "silent-Copy-loss-or-uppercap-substitution")
    refuses(lambda: a.adapted_child_boundary(initial, c, "unknown"), "unknown-original-hybrid")
    refuses(lambda: a.adapted_child_boundary(replace(initial, outside_nodes=(("h", (a.Leaf("preexisting:h"),)),)), c, "h"), "preexisting-focal-node-outside-contract")
    refuses(lambda: a.validate_record(replace(initial, physical=replace(initial.physical, registers=(("h", False),))), c), "missing-total-register")
    badregs = tuple((v, 1 if v == "h" else b) for v, b in initial.physical.registers)
    refuses(lambda: a.validate_record(replace(initial, physical=replace(initial.physical, registers=badregs)), c), "integer-stored-register")
    badregs = tuple((v, True if v == "root" else b) for v, b in initial.physical.registers)
    refuses(lambda: a.validate_record(replace(initial, physical=replace(initial.physical, registers=badregs)), c), "nonhybrid-true-register")
    refuses(lambda: a.validate_record(replace(initial, outside_nodes=(("outside", (a.Leaf("old:left"),)),)), c), "duplicate-leaf-across-outside")
    refuses(lambda: a.validate_tree(a.Join(True, a.Leaf("a"), a.Leaf("b"))), "Bool-bin-tag")
    canonical = a.ref.graft(a.Leaf("a"), a.Leaf("b"), 3)
    refuses(lambda: a.validate_tree(a.Join(3, canonical.right, canonical.left)), "noncanonical-tree-child-order")
    refuses(lambda: a.ref.poisson_prefix(Q(100), Q(1, 100), max_degree=0), "resource-limit-is-refusal")
    original = json.loads(wire)
    def corrupt(mutator):
        x = json.loads(wire)
        mutator(x)
        return a.canonical_json(x)
    cases = {
        "duplicate-state-row": lambda x: x["rows"].append(x["rows"][0]),
        "unknown-wire-field": lambda x: x.update({"confidence": 0}),
        "negative-row": lambda x: x["rows"][0].update({"mass": ["-1", "1"]}),
        "zero-row": lambda x: x["rows"][0].update({"mass": ["0", "1"]}),
        "unreduced-rational": lambda x: x["rows"][0].update({"mass": ["2", "2"]}),
        "rational-leading-zero": lambda x: x["rows"][0].update({"mass": ["01", "1"]}),
        "contract-rate-change": lambda x: x["contract"]["rates"][0].__setitem__(1, ["1", "1"]),
        "contract-parent-swap": lambda x: x["contract"]["hybrids"][0].update({"parent1": "parent:h:0"}),
        "contract-cut-change": lambda x: x["contract"]["bin_cuts"].__setitem__(0, ["1", "3"]),
        "reference-identity-change": lambda x: x.update({"reference_sha256": "0" * 64}),
        "source-admission-promotion": lambda x: x.update({"source_admission": "CERTIFIED"}),
        "mass-tail-discard": lambda x: x["rows"].pop(),
        "wire-row-order-change": lambda x: x["rows"].reverse(),
    }
    for name, mutator in cases.items():
        refuses(lambda mutator=mutator: a.deserialize_law(corrupt(mutator), c), name)
    refuses(lambda: a.deserialize_law(wire.replace('"schema":', '"schema":"duplicate","schema":', 1), c), "duplicate-json-object-key")
    refuses(lambda: a.deserialize_law(wire.replace('"copy_cap":12', '"copy_cap":12.0'), c), "JSON-float")
    refuses(lambda: a.deserialize_law(wire + "\n", c), "noncanonical-wire-whitespace")

    here = Path(__file__).resolve().parent
    (here / "boundary-tables.json").write_text(json.dumps(boundary_tables, indent=2) + "\n")
    (here / "sample-residual-law.json").write_text(wire)
    receipt = {"status": "PASS", "started_utc": start,
               "finished_utc": datetime.now(timezone.utc).isoformat(),
               "python": sys.version, "platform": platform.platform(),
               "reference_path": a.REFERENCE_PATH, "reference_sha256": a.REFERENCE_SHA256,
               "evidence_scope": "actual pinned Python calls versus independent finite native-definition oracle; no native binary/Lean execution",
               "checks": dict(sorted(checks.items())), "total_checks": sum(checks.values()),
               "epoch": {"degree": cert.degree, "deficit": a.qwire(cert.deficit),
                         "states": len(epoch), "wire_sha256": hashlib.sha256(wire.encode()).hexdigest()},
               "source_files": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in (here / "native_adapter.py", Path(__file__).resolve())}}
    (here / "test-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "total_checks": receipt["total_checks"],
                      "boundary_cases": checks["actual-python-boundary-v-native-definition"],
                      "refusals": sum(v for k, v in checks.items() if k.startswith("refusal:")),
                      "epoch_states": len(epoch), "epoch_degree": cert.degree}, sort_keys=True))


if __name__ == "__main__":
    execute()
