"""PREPARED, UNEXECUTED exact fixed-body physical-pad gate.

Use the preserved lossless original full-forest/color engines. No inherited
file is modified. This one n=9 source column cannot establish a source return
or original G4. Root alone schedules execution after independent source review.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import argparse
import json
import resource
import sys
import time
import types


ROOT = Path(__file__).resolve().parents[5]
ARCHIVE = "research/2026-10-06-dot-g4-strict-leading-chronological-obstruction-0404z/source"
CORE = ARCHIVE + "/g4-lossless-resonance-20261005-2042z/lossless_resonance.py"
COLOR = ARCHIVE + "/g4-coherent-sixth-jet-20261005-2058z/source_coefficients.py"
CERT = ARCHIVE + "/g4-sixth-chronological-test-20261006-0350z/attempt1/RESULT.json"
GUARD = ARCHIVE + "/g4-sixth-chronological-test-20261006-0350z/INTEGER-GUARD-CHECK.json"
LABELLED = "research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py"
PINS = {
    CORE: "3bbbbe54d4c28abe2515c14143e9d83629e650ba0ac0df411457dec7fa17c9be",
    COLOR: "aed745dd0d3fc37a8b5eef838f000675ad3fb6c37a66116f14eacfe01192f998",
    CERT: "035b6f894216e91aad0fb8a3b24aabecbe3791675742f5688cbeebbd492821f1",
    GUARD: "4f120aa5c7ed1e3c667481f59fd4bcd02451a65fd5a3b9f91fcc6c430e4859b6",
    LABELLED: "850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884",
}


def read_pinned(path):
    full = ROOT / path
    if full.is_symlink():
        raise ValueError("provider symlink: " + path)
    raw = full.read_bytes()
    if sha256(raw).hexdigest() != PINS[path]:
        raise ValueError("provider identity: " + path)
    return raw


def captured(raw, path, name):
    module = types.ModuleType(name)
    module.__file__ = str(ROOT / path)
    sys.modules[name] = module
    exec(compile(raw, str(ROOT / path), "exec"), module.__dict__)
    return module


def newton_coefficients(x, n):
    # f(-lambda_j)=x**lambda_j. Repeated zero (empty/singleton) is isolated;
    # lambda_1=0 represents both, with identical value one.
    nodes = tuple(-comb(j, 2) for j in range(1, n + 1))
    divided = [x ** (-node) for node in nodes]
    coefficients = [divided[0]]
    for width in range(1, n):
        divided = [(divided[j + 1] - divided[j]) /
                   (nodes[j + width] - nodes[j])
                   for j in range(n - width)]
        coefficients.append(divided[0])
    return nodes, tuple(coefficients)


class ActualContext:
    def __init__(self, n, core, color):
        self.n, self.m, self.c = n, core, color
        self.states, self.ids, self.q, self.r = core.build(n)
        self.colors, self.cids, self.ql, self.qr = color.coloured(n)
        if len(self.states) > 2000 or len(self.colors) > 4096:
            raise ValueError("predeclared inherited state ceiling")
        self.arm_polynomials = {}
        self.bigons_applied = 0

    def edge(self, row, q, x):
        if x not in self.arm_polynomials:
            self.arm_polynomials[x] = newton_coefficients(x, self.n)
        nodes, coefficients = self.arm_polynomials[x]
        out = [coefficients[-1] * v for v in row]
        for j in range(len(coefficients) - 2, -1, -1):
            applied = self.m.apply(out, q)
            out = [a - nodes[j] * v + coefficients[j] * w
                   for a, v, w in zip(applied, out, row)]
        return out

    def split(self, row, g):
        out = [F(0)] * len(self.colors)
        for value, forest in zip(row, self.states):
            if value:
                # One choice per CURRENT ROOT OCCURRENCE, not descendant leaf.
                for bits in product((0, 1), repeat=len(forest)):
                    aa = tuple(t for t, bit in zip(forest, bits) if bit == 0)
                    bb = tuple(t for t, bit in zip(forest, bits) if bit == 1)
                    out[self.cids[aa, bb]] += value * g ** len(aa) * (1-g) ** len(bb)
        return out

    def bigon(self, row, x, y, g):
        self.bigons_applied += 1
        colored = self.split(row, g)
        colored = self.edge(colored, self.ql, x)
        colored = self.edge(colored, self.qr, y)
        out = [F(0)] * len(self.states)
        for value, (aa, bb) in zip(colored, self.colors):
            if value:
                out[self.ids[tuple(sorted(aa + bb))]] += value
        if sum(out, F(0)) != sum(row, F(0)):
            raise AssertionError("actual bigon row mass")
        return out

    def beta(self, k, x, y, g):
        return sum((F(comb(k, j)) * g**j * (1-g)**(k-j) *
                    x**comb(j, 2) * y**comb(k-j, 2)
                    for j in range(k+1)), F(0))

    def right_inverse_at_least_four(self, rhs, x, y, g):
        # Descending current-root blocks are scalar beta_k. Rows below four
        # can never reach four and P4 annihilates them. No full matrix inverse.
        residual = list(rhs)
        answer = [F(0)] * len(rhs)
        stages = []
        for k in range(self.n, 3, -1):
            beta = self.beta(k, x, y, g)
            if beta <= 0:
                raise AssertionError("strict current-root no-merger diagonal")
            step = [v / beta if len(f) == k else F(0)
                    for v, f in zip(residual, self.states)]
            applied = self.bigon(step, x, y, g)
            if any(v for v, f in zip(applied, self.states) if len(f) > k):
                raise AssertionError("bigon increased current roots")
            if any(v != beta*w for v, w, f in zip(applied, step, self.states)
                   if len(f) == k):
                raise AssertionError("non-scalar diagonal block")
            answer = [v+w for v, w in zip(answer, step)]
            residual = [v-w for v, w in zip(residual, applied)]
            if any(v for v, f in zip(residual, self.states) if len(f) >= k):
                raise AssertionError("exact triangular inverse stage")
            stages.append({"current_roots": k, "beta": str(beta),
                           "all_residual_coordinates_at_or_above_grade_zero": True})
        return answer, residual, stages


def shape_of_labelled(tree, core):
    if isinstance(tree, int):
        return "x"
    return core.tree(shape_of_labelled(tree[0], core), shape_of_labelled(tree[1], core))


def labelled_representative(shapes, core, labelled):
    next_leaf = 0
    def convert(tree):
        nonlocal next_leaf
        if tree == "x":
            leaf = next_leaf
            next_leaf += 1
            return leaf
        left, right = core.children(tree)
        return labelled.tree(convert(left), convert(right))
    return labelled.forest(convert(tree) for tree in shapes)


def mandatory_controls(core, color, labelled):
    checks = 0
    for n in range(1, 5):
        ctx = ActualContext(n, core, color)
        for i, shapes in enumerate(ctx.states):
            row = [F(j == i) for j in range(len(ctx.states))]
            if ctx.split(row, F(1, 2)) != color.split(row, ctx.states, ctx.cids):
                raise AssertionError("original fair split binding")
            original = labelled_representative(shapes, core, labelled)
            for x, y, g in ((F(1, 2), F(1, 2), F(2, 3)),
                            (F(1, 4), F(5, 6), F(1, 5))):
                expected = [F(0)] * len(ctx.states)
                for forest, value in labelled.bigon_law(len(original), x, y, g, "independent").items():
                    grafted = labelled.graft(original, forest)
                    shape = tuple(sorted(shape_of_labelled(tree, core) for tree in grafted))
                    expected[ctx.ids[shape]] += value
                actual = ctx.bigon(row, x, y, g)
                if actual != expected or any(v < 0 for v in actual):
                    raise AssertionError("original labelled opaque-graft bigon binding")
                checks += len(actual)
            checks += len(ctx.colors)
    return checks


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("refusing to overwrite evidence")
    resource.setrlimit(resource.RLIMIT_CPU, (55, 55))
    resource.setrlimit(resource.RLIMIT_AS, (512*1024*1024, 512*1024*1024))
    resource.setrlimit(resource.RLIMIT_FSIZE, (8*1024*1024, 8*1024*1024))
    start = time.monotonic()
    own_raw = Path(__file__).read_bytes()
    raws = {path: read_pinned(path) for path in PINS}
    color = captured(raws[COLOR], COLOR, "_fixed_body_original_color")
    # Preserved COLOR source authenticates and compiles CORE's exact byte buffer;
    # it never imports the core through a pyc-capable SourceFileLoader.
    core = color.m
    labelled = captured(raws[LABELLED], LABELLED, "_fixed_body_original_labelled")
    certificate = json.loads(raws[CERT])
    guard = json.loads(raws[GUARD])
    controls = mandatory_controls(core, color, labelled)
    print(json.dumps({"phase": "mandatory_original_labelled_controls_pass", "checks": controls}), flush=True)

    ctx = ActualContext(9, core, color)
    if len(ctx.states) != 152 or sum(core.orbit_size(f) for f in ctx.states) != 5329837:
        raise AssertionError("preserved complete nine-root row dimensions")
    top = [i for i, f in enumerate(ctx.states) if len(f) == 4]
    if len(top) != 15:
        raise AssertionError("ALL complete four-current-root top shapes")
    if [list(ctx.states[i]) for i in top] != [v["shape"] for v in certificate["coordinates"]]:
        raise AssertionError("preserved full guard row ordering")
    weights = [F(0)] * len(top)
    for term in guard["nonzero_coordinates"]:
        j = term["index"]
        if term["shape"] != list(ctx.states[top[j]]) or term["multiplicity"] != core.orbit_size(ctx.states[top[j]]):
            raise AssertionError("per-labelled guard orbit identity")
        weights[j] = F(term["integer_weight"])

    seed = [F(f == ("x",)*9) for f in ctx.states]
    left = core.project(seed, 9, ctx.q, 9)
    if core.apply(left, ctx.q) != [-36*v for v in left]:
        raise AssertionError("P9 ordinary eigenrow")
    first_r = core.apply(left, ctx.r)
    vk = {}
    for k in range(4, 10):
        row = core.project(core.apply(core.project(first_r, k, ctx.q, 9), ctx.r), 4, ctx.q, 9)
        values = [row[i]/core.orbit_size(ctx.states[i]) for i in top]
        if list(map(str, values)) != certificate["intermediate_products"][str(k)]:
            raise AssertionError("ALL preserved source guard Vk coordinates")
        vk[str(k)] = str(sum((w*v for w, v in zip(weights, values)), F(0)))
    if vk != {"4": "0", "5": "0", "6": "2/9", "7": "-2/9", "8": "0", "9": "0"}:
        raise AssertionError("preserved exact guard functional")
    print(json.dumps({"phase": "full_original_guard_binding_pass", "Vk": vk}), flush=True)

    x, y, g = F(1, 2), F(1, 2), F(2, 3)
    after_b = ctx.bigon(left, x, y, g)
    after_q = core.apply(after_b, ctx.q)
    inverse_row, inverse_residual, stages = ctx.right_inverse_at_least_four(after_q, x, y, g)
    reapplied = ctx.bigon(inverse_row, x, y, g)
    difference = [a-b for a, b in zip(reapplied, after_q)]
    if any(v for v, f in zip(difference, ctx.states) if len(f) >= 4):
        raise AssertionError("independent final inverse reapplication")
    if any(core.project(difference, 4, ctx.q, 9)):
        raise AssertionError("FULL P4-projected inverse reapplication")
    projected = core.project(inverse_row, 4, ctx.q, 9)
    if core.apply(projected, ctx.q) != [-6*v for v in projected]:
        raise AssertionError("P4 ordinary eigenrow")
    if any(v for v, f in zip(projected, ctx.states) if len(f) > 4):
        raise AssertionError("complete ninth-to-four block support")
    top_values = [projected[i]/core.orbit_size(ctx.states[i]) for i in top]
    value = sum((w*v for w, v in zip(weights, top_values)), F(0))

    for path, raw in raws.items():
        if read_pinned(path) != raw:
            raise AssertionError("provider changed during exact invocation")
    if Path(__file__).read_bytes() != own_raw:
        raise AssertionError("own source changed during exact invocation")
    report = {
        "status": "PASS", "arithmetic": "standard-library Fraction only; no floating decisions",
        "own_source_sha256": sha256(own_raw).hexdigest(),
        "executed_and_read_dependencies": [{"path": path, "sha256": PINS[path], "bytes": len(raw)}
                                           for path, raw in raws.items()],
        "operator": "P9 B(1/2,1/2,2/3) Q B(1/2,1/2,2/3)^(-1) P4",
        "physical_column": "RIGHT-relative trailing ordinary DURATION derivative; bare B held fixed; leading E(a) multiplies guard by a^30",
        "g_convention": "first/x arm probability g per CURRENT opaque root occurrence; identical to original labelled source",
        "all_full_nine_forest_orbits": len(ctx.states), "all_labelled_nine_forests": 5329837,
        "two_color_states": len(ctx.colors), "mandatory_original_labelled_control_checks": controls,
        "original_all_top_Vk_guard_values": vk, "actual_bigon_row_applications_at_nine": ctx.bigons_applied,
        "inverse_grade_stages": stages, "inverse_reapplication_at_roots_at_least_four_exact": True,
        "FULL_P4_inverse_reapplication_exact": True,
        "guard_value_exact": str(value), "guard_nonzero": bool(value),
        "all_complete_top_coordinates": [{"shape": list(ctx.states[i]), "labelled_multiplicity": core.orbit_size(ctx.states[i]),
                                          "orbit_mass": str(projected[i]), "per_labelled_coefficient": str(v),
                                          "integer_guard_weight": str(w)} for i, v, w in zip(top, top_values, weights)],
        "full_projected_fresh_nine_row": [{"shape": list(f), "current_roots": len(f),
                                           "labelled_multiplicity": core.orbit_size(f), "orbit_mass": str(v)}
                                          for f, v in zip(ctx.states, projected)],
        "inverse_residual_below_four_only": [{"shape": list(f), "value": str(v)}
                                             for f, v in zip(ctx.states, inverse_residual) if v],
        "runtime_seconds": time.monotonic()-start,
        "claim_limits": ["Only this actual fixed-body physical-pad column was evaluated",
                         "No complete cap-four-forced feedback or source cancellation established",
                         "No all-cap return, actual target interior, arbitrary presentation exclusion or original G4 closure"],
    }
    with args.output.open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print(json.dumps({key: report[key] for key in ("status", "guard_value_exact", "guard_nonzero", "runtime_seconds")}), flush=True)


if __name__ == "__main__":
    main()
