"""Exact normalized Poisson-prefix certificate; a numerical input-layer component.

This does not construct a biological source or restrict hidden source parameters.
The old residual-lumped reference backend defines a different count law.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction


def certify(a: Fraction, epsilon: Fraction, *, max_steps: int | None = None) -> dict:
    """Return the first rational Taylor certificate, or RESOURCE_LIMIT.

    Exact unlimited search terminates for a >= 0 and 0 < epsilon < 1 by
    the geometric ratio bound. max_steps limits inspected candidate cutoffs.
    RESOURCE_LIMIT supplies no negative source/target conclusion.
    """
    if not isinstance(a, Fraction) or not isinstance(epsilon, Fraction):
        raise TypeError("Use exact Fraction inputs.")
    if a < 0 or not 0 < epsilon < 1:
        raise ValueError("Require a >= 0 and 0 < epsilon < 1.")
    if max_steps is not None and (not isinstance(max_steps, int) or max_steps < 0):
        raise ValueError("max_steps must be a nonnegative integer or None.")
    k = 0
    term = Fraction(1)
    prefix = Fraction(1)
    inspected = 0
    while max_steps is None or inspected < max_steps:
        next_term = term * a / (k + 1)
        upper = prefix + 2 * next_term
        delta = 2 * next_term / upper
        inspected += 1
        if k + 2 >= 2 * a and delta <= epsilon:
            return {
                "status": "CERTIFIED",
                "law": "normalized_prefix",
                "a": str(a),
                "epsilon": str(epsilon),
                "K": k,
                "S": str(prefix),
                "T": str(next_term),
                "U": str(upper),
                "delta": str(delta),
                "inspected": inspected,
            }
        k += 1
        term = next_term
        prefix += term
    return {
        "status": "RESOURCE_LIMIT",
        "law": "normalized_prefix",
        "a": str(a),
        "epsilon": str(epsilon),
        "inspected": inspected,
        "next_K": k,
    }


def weights(a: Fraction, k: int) -> tuple[Fraction, ...]:
    """Exact q_k=t_k/S_K; no residual mass is moved to count zero."""
    if not isinstance(a, Fraction) or a < 0 or not isinstance(k, int) or k < 0:
        raise ValueError("Require a nonnegative Fraction and a natural cutoff.")
    terms = [Fraction(1)]
    for i in range(1, k + 1):
        terms.append(terms[-1] * a / i)
    total = sum(terms)
    return tuple(t / total for t in terms)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("a", type=Fraction)
    parser.add_argument("epsilon", type=Fraction)
    parser.add_argument("--max-steps", type=int)
    parser.add_argument("--weights", action="store_true")
    args = parser.parse_args()
    result = certify(args.a, args.epsilon, max_steps=args.max_steps)
    if args.weights and result["status"] == "CERTIFIED":
        result["weights"] = [str(q) for q in weights(args.a, result["K"])]
    print(json.dumps(result, sort_keys=True))
