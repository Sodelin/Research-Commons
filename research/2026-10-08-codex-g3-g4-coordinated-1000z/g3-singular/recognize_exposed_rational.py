"""Bounded original rational-input slice recognizer; see RANK-THREE-EXPOSED-SLICE.md.

This is not a general G3 solver. It uses exact Fractions and exact quadratic
root encodings, with the inherited all-core calibrated marginal correspondence.
Run: python -B recognize_exposed_rational.py input.json [--output result.json]
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import math
import sys

CONTRACT = "G3-COMMON-CALIBRATED-EXPOSED-CAP10-V1"
NAMES = ["B2", "B3", "Q1", "Q3", "QP"]
ATOMS = [F(1, 8), F(1, 4), F(1, 2)]
PROOF = Path(__file__).with_name("RANK-THREE-EXPOSED-SLICE.md")
CHANNELS = Path(__file__).with_name("RANK-THREE-EXPOSED-ARITHMETIC.json")

def rat(value):
    value = F(value)
    return str(value.numerator) if value.denominator == 1 else str(value)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rational_value(value):
    return {"type": "rational", "value": rat(value)}

def quadratic_pair(weights):
    low, middle, high = weights
    total = middle + 2 * low
    delta = middle ** 2 - 4 * low * high
    assert delta >= 0 and low > 0 and middle > 0 and high > 0
    square_numerator = math.isqrt(delta.numerator)
    square_denominator = math.isqrt(delta.denominator)
    if square_numerator ** 2 == delta.numerator and square_denominator ** 2 == delta.denominator:
        square_root = F(square_numerator, square_denominator)
        return [rational_value((total - square_root) / 2),
                rational_value((total + square_root) / 2)]
    # P(0)>0, P(total/2)<0, P(1)>0: these open intervals isolate
    # precisely one strictly interior root each. No floating sqrt is used.
    coefficients = [low, -total, F(1)]
    denominator = math.lcm(*(c.denominator for c in coefficients))
    integers = [int(c * denominator) for c in coefficients]
    divisor = math.gcd(*integers)
    integers = [c // divisor for c in integers]
    assert low > 0 and high > 0 and 0 < total / 2 < 1
    return [{"type": "real_algebraic", "polynomial_coefficients_ascending": integers,
             "isolating_interval": [rat(a), rat(b)], "interval_open": True}
            for a, b in [(F(0), total / 2), (total / 2, F(1))]]

def make_source(atoms, masses):
    root = "r"
    arcs = []
    inheritance = []

    def edge(identifier, parent, child, survival):
        assert 0 < survival < 1
        arcs.append({"id": identifier, "parent": parent, "child": child,
                     "survival": rat(survival), "length": "-log(survival)"})

    edge("rv", "r", "v", F(1, 2))
    edge("rw", "r", "w", F(1, 2))
    edge("vB", "v", "B", F(1, 2))
    edge("wC", "w", "C", F(1, 2))
    edge("wD", "w", "D", F(1, 2))
    if len(atoms) == 1:
        edge("vA", "v", "A", atoms[0])
    elif len(atoms) == 2:
        alpha, beta = atoms
        c = 1 - (1 - beta) / 5
        z = beta / c ** 2
        x, y, a = c * alpha / beta, c, c
        edge("vp1", "v", "p1", z)
        edge("h1A", "h1", "A", a)
        edge("h1lower", "p1", "h1", x)
        edge("h1upper", "p1", "h1", y)
        inheritance.append({"hybrid": "h1", "lower_parent_arc": "h1lower",
                            "upper_parent_arc": "h1upper", "lower_weight": rational_value(masses[0])})
        assert z * x * a == alpha and z * y * a == beta
    else:
        assert atoms == ATOMS
        c = F(15, 16)
        z = F(1, 2) / c ** 4
        edge("vp1", "v", "p1", z)
        edge("h1p2", "h1", "p2", c)
        edge("h2A", "h2", "A", c)
        coins = quadratic_pair(masses)
        for index, coin in enumerate(coins, 1):
            edge(f"h{index}lower", f"p{index}", f"h{index}", c / 2)
            edge(f"h{index}upper", f"p{index}", f"h{index}", c)
            inheritance.append({"hybrid": f"h{index}", "lower_parent_arc": f"h{index}lower",
                                "upper_parent_arc": f"h{index}upper", "lower_weight": coin})
    vertices = sorted({v for arc in arcs for v in [arc["parent"], arc["child"]]})
    source = {"root": root, "vertices": vertices, "taxon_vertices": ["A", "B", "C", "D"],
              "arcs": arcs, "inheritance": inheritance,
              "inheritance_semantics": "one COMMON bit at each site, independent sites/fresh loci",
              "above_root": "unbounded ordinary ancestral population",
              "original_actuator_ids": [], "protected_internal_parameters": [],
              "survival_law_atoms": list(map(rat, atoms)), "survival_law_masses": list(map(rat, masses))}
    static_source_checks(source)
    return source

def static_source_checks(source):
    arcs, vertices = source["arcs"], source["vertices"]
    hybrids = {h["hybrid"] for h in source["inheritance"]}
    leaves = set(source["taxon_vertices"])
    for vertex in vertices:
        indegree = sum(a["child"] == vertex for a in arcs)
        outdegree = sum(a["parent"] == vertex for a in arcs)
        expected = ((0, 2) if vertex == source["root"] else (1, 0) if vertex in leaves
                    else (2, 1) if vertex in hybrids else (1, 2))
        assert (indegree, outdegree) == expected
    assert len(vertices) == 2 * len(leaves) + 2 * len(hybrids) - 1
    assert len(arcs) == 2 * len(leaves) + 3 * len(hybrids) - 2
    for hybrid in hybrids:
        child_arc = next(a for a in arcs if a["parent"] == hybrid)
        # Exact undirected connectivity after deleting its individual child arc.
        reachable = {hybrid}
        changed = True
        while changed:
            changed = False
            for arc in arcs:
                if arc["id"] == child_arc["id"]:
                    continue
                a, b = arc["parent"], arc["child"]
                if a in reachable and b not in reachable:
                    reachable.add(b); changed = True
                if b in reachable and a not in reachable:
                    reachable.add(a); changed = True
        assert child_arc["child"] not in reachable
    for item in source["inheritance"]:
        weight = item["lower_weight"]
        if weight["type"] == "rational":
            assert 0 < F(weight["value"]) < 1
        else:
            lower, upper = map(F, weight["isolating_interval"])
            assert 0 <= lower < upper <= 1 and weight["interval_open"]
            coefficients = weight["polynomial_coefficients_ascending"]
            left = sum(F(c) * lower ** i for i, c in enumerate(coefficients))
            right = sum(F(c) * upper ** i for i, c in enumerate(coefficients))
            assert left * right < 0

def recognize(profile):
    evidence = {"proof_file": PROOF.name, "proof_sha256": digest(PROOF),
                "channel_file": CHANNELS.name, "channel_sha256": digest(CHANNELS),
                "claim_tier": "exact rational slice algorithm using accepted hand/source correspondence",
                "compiler_invocations": 0, "QE_invocations": 0, "gene_topology_simulations": 0}

    def result(status, reason, **extra):
        return {"contract": CONTRACT, "status": status, "reason": reason,
                "evidence": evidence, **extra}

    if not isinstance(profile, dict) or set(profile) != {"contract", "source_mode", "probabilities"}:
        return result("UNKNOWN", "Input must declare exactly this contract, mode and five supplied rows; richer/malformed contracts are not classified.")
    if profile["contract"] != CONTRACT or profile["source_mode"] != "COMMON":
        return result("UNKNOWN", "This fixed natural COMMON four-taxon channel contract is required.")
    probabilities = profile["probabilities"]
    if not isinstance(probabilities, dict) or set(probabilities) != set(NAMES):
        return result("UNKNOWN", "Exactly the five original B2,B3,Q1,Q3,QP probabilities are required.")
    try:
        # Rational strings/integers only; accepting binary floats would lose exactness.
        if any(not isinstance(v, (str, int)) or isinstance(v, bool) for v in probabilities.values()):
            raise ValueError("rational strings/integers required")
        values = {name: F(probabilities[name]) for name in NAMES}
        if any(not 0 <= v <= 1 for v in values.values()):
            raise ValueError("probability outside [0,1]")
    except (ValueError, ZeroDivisionError):
        return result("UNKNOWN", "Invalid rational probability encoding; no mathematical NO is inferred.")
    if values["B2"] != F(2, 3) or values["B3"] != F(25, 48):
        return result("UNKNOWN", "The two exact B calibration values are required for the all-core source reduction.")
    if values["QP"] < F(1, 2):
        return result("NO", "The calibrated actual survival law has P>=0, so QP cannot have probability below one half.",
                      exclusion="all admitted original COMMON cores at the declared five-row contract")
    if values["QP"] > F(1, 2):
        return result("UNKNOWN", "The exposing equality is absent; the unconstrained interior fibre is not decided.")
    u1 = 8 * (values["Q1"] - F(1, 2))
    u3 = 38 * (values["Q3"] - F(1, 2))
    weights = [F(16, 7) - F(32, 3) * u1 + F(512, 21) * u3,
               -F(10, 7) + 12 * u1 - F(256, 7) * u3,
               F(1, 7) - F(4, 3) * u1 + F(256, 21) * u3]
    assert sum(weights) == 1
    decoded = {"u1": rat(u1), "u3": rat(u3), "atoms": list(map(rat, ATOMS)),
               "unique_atomic_weights": list(map(rat, weights))}
    if any(w < 0 for w in weights):
        return result("NO", "The exposing equality forces this unique atomic law, which has a negative mass.",
                      decoded=decoded, exclusion="all admitted original COMMON cores")
    support = [(a, w) for a, w in zip(ATOMS, weights) if w > 0]
    if len(support) == 3:
        delta = weights[1] ** 2 - 4 * weights[0] * weights[2]
        decoded["bernoulli_discriminant"] = rat(delta)
        if delta < 0:
            return result("NO", "Three geometric atoms require two independent Bernoulli factors, whose middle-mass discriminant is nonnegative.",
                          decoded=decoded, exclusion="all finite admitted original COMMON cores")
    atoms, masses = map(list, zip(*support))
    source = make_source(atoms, masses)
    reconstructed = {"B2": "2/3", "B3": "25/48",
                     "Q1": rat(F(1, 2) + sum(a * w for a, w in support) / 8),
                     "Q3": rat(F(1, 2) + sum(a ** 3 * w for a, w in support) / 38), "QP": "1/2"}
    assert all(F(reconstructed[name]) == values[name] for name in NAMES)
    return result("YES", "An actual positive four-taxon source with the same tuple in all five rows is constructed.",
                  decoded=decoded, source=source, exact_original_probabilities=reconstructed,
                  minimum_total_original_hybrids=len(support) - 1,
                  source_validation="exact binary degrees, positive survivals/weight root intervals, child bridges and counts checked; root/outer-face admission follows the displayed tree with serial parallel cells",
                  correspondence_limit="These probabilities use the accepted calibrated full marginal theorem, not a newly executed genealogy compiler.")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    try:
        data = json.loads(arguments.input.read_text())
    except (OSError, json.JSONDecodeError):
        data = None
    answer = recognize(data)
    payload = json.dumps(answer, indent=2) + "\n"
    if arguments.output:
        arguments.output.write_text(payload)
    else:
        sys.stdout.write(payload)

if __name__ == "__main__":
    main()
