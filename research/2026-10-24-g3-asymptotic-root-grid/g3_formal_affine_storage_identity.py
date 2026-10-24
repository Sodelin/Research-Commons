#!/usr/bin/env python3
"""Bounded universal affine-storage algebra; no physical/model evaluation.

Reuse the eight pinned old sparse-polynomial helpers without their main.
Every runtime intent/result is sealed by the existing one-identity writer.
This check supplies no source coercivity, index theorem or G3 completion.
"""
from pathlib import Path
from fractions import Fraction as F
import ast
import hashlib
import json
import resource
import time
import traceback
import types

ACTION = "G3-FORMAL-AFFINE-STORAGE-20261024/revision1"
ROOT = Path(__file__).resolve().parent
POLY_PATH = ROOT.parent / "2026-10-21-okay-so-without-adding-without-adding-2/count_uniform_storage_identity.py"
POLY_SHA = "a7d6a1b22972a35b45719359671f79495c16a65feedbc5451f44a565b46cfda5"
WRITER_PATH = ROOT.parent / "2026-10-21-okay-so-without-adding-without-adding-5/peer_message.py"
WRITER_SHA = "c23091999f6cdf06df6a4305f65ee1af72a992097c3df5b2d8d7bceab41dd241"
HELPERS = ("const", "var", "add", "mul", "scale", "neg", "square", "derivative")
NAMES = ("a", "b", "z", "d1", "d2", "d3", "d4", "x", "y", "v", "u", "t",
         "kappa", "la", "lb", "q12", "q13", "q24", "q34", "q14")

def seal(writer, value):
    receipt, ciphertext = writer.seal(value)
    assert hashlib.sha256(ciphertext).hexdigest() == receipt["ciphertext_sha256"]
    return receipt

def encoded(poly):
    return [{"powers": list(p), "coefficient": str(c)}
            for p, c in sorted(poly.items())]

def run():
    resource.setrlimit(resource.RLIMIT_CPU, (8, 8))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    writer_source = WRITER_PATH.read_bytes()
    if hashlib.sha256(writer_source).hexdigest() != WRITER_SHA:
        raise RuntimeError("REFUSED_WRITER_SOURCE_MISMATCH")
    writer = types.ModuleType("existing_record_adapter")
    exec(compile(writer_source, str(WRITER_PATH), "exec"), writer.__dict__)
    source = Path(__file__).read_bytes()
    intent = {
        "action": ACTION, "status": "INTENT",
        "scope": "generic formal matrix indeterminates only; no model/source evaluation",
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "polynomial_helpers_sha256": POLY_SHA, "writer_sha256": WRITER_SHA,
        "cpu_seconds": 8, "core_bytes": 0,
        "old_main_selected": False, "physical_source_evaluations": 0,
    }
    intent_receipt = seal(writer, intent)
    print(json.dumps({"action": ACTION, "intent_receipt": intent_receipt}), flush=True)
    started = time.monotonic()
    report = dict(intent)
    try:
        poly_source = POLY_PATH.read_bytes()
        assert hashlib.sha256(poly_source).hexdigest() == POLY_SHA
        tree = ast.parse(poly_source, filename=str(POLY_PATH))
        selected = [n for n in tree.body
                    if isinstance(n, ast.FunctionDef) and n.name in HELPERS]
        assert tuple(n.name for n in selected) == HELPERS
        ns = {"F": F, "NAMES": NAMES, "SIZE": len(NAMES)}
        exec(compile(ast.Module(body=selected, type_ignores=[]),
                     str(POLY_PATH), "exec"), ns)
        var, add, mul, scale, neg, sq, derivative = (
            ns[n] for n in ("var", "add", "mul", "scale", "neg", "square", "derivative"))
        (a,b,z,d1,d2,d3,d4,x,y,v,u,t,kappa,la,lb,q12,q13,q24,q34,q14) = map(var,NAMES)
        phi = add(z, scale(mul(kappa, add(sq(b), neg(sq(a)))), -F(1,2)),
                  mul(la,a), mul(lb,b))
        anum = add(mul(d2,a),x)
        bnum = add(mul(d3,b),y)
        znum = add(mul(d4,z),mul(u,a),mul(t,b),v)
        jump_left = add(
            mul(d1,znum),
            scale(mul(kappa,add(sq(bnum),neg(sq(anum)))),-F(1,2)),
            mul(la,d1,anum),mul(lb,d1,bnum),neg(mul(d4,d1,phi)))
        central = add(mul(d1,v),
                      scale(mul(kappa,add(sq(y),neg(sq(x)))),-F(1,2)),
                      mul(d1,add(mul(la,x),mul(lb,y))))
        jump_right = add(
            scale(mul(kappa,add(
                mul(add(mul(d4,d1),neg(sq(d3))),sq(b)),
                neg(mul(add(mul(d4,d1),neg(sq(d2))),sq(a))))),F(1,2)),
            mul(add(mul(d1,u),mul(kappa,d2,x),
                    mul(la,d1,add(d2,neg(d4)))),a),
            mul(add(mul(d1,t),neg(mul(kappa,d3,y)),
                    mul(lb,d1,add(d3,neg(d4)))),b),
            central)
        jump_residual = add(jump_left,neg(jump_right))
        assert not jump_residual
        drift_direct = add(
            mul(derivative(phi,"a"),add(scale(a,15),q12)),
            mul(derivative(phi,"b"),add(scale(b,21),q13)),
            mul(derivative(phi,"z"),add(scale(z,30),mul(q24,a),mul(q34,b),q14)),
            scale(phi,-30))
        drift_grouped = add(
            scale(mul(kappa,sq(b)),-6),
            mul(add(q24,mul(kappa,q12),scale(la,-15)),a),
            mul(add(q34,neg(mul(kappa,q13)),scale(lb,-9)),b),
            q14,mul(la,q12),mul(lb,q13))
        drift_residual = add(drift_direct,neg(drift_grouped))
        assert not drift_residual
        missing_central = add(jump_left,neg(add(jump_right,neg(mul(d1,v)))))
        unequal_square = scale(mul(kappa,add(sq(y),neg(sq(x)))),-F(1,2))
        missing_unequal_square = add(jump_left,neg(add(jump_right,neg(unequal_square))))
        assert missing_central and missing_unequal_square
        report.update({
            "status": "PASS_UNIVERSAL_FORMAL_AFFINE_STORAGE",
            "complete_variable_names": NAMES,
            "helpers_selected": HELPERS, "old_main_executed": False,
            "jump_residual": encoded(jump_residual),
            "drift_residual": encoded(drift_residual),
            "negative_controls": {
                "omitted_central_entry_rejected": encoded(missing_central),
                "omitted_unequal_square_rejected": encoded(missing_unequal_square)},
            "source_coercivity_or_asymptotics_checked": False,
            "index_theorem_checked": False, "original_g3_closed": False,
        })
        exit_code = 0
    except BaseException:
        report.update(status="FAIL_FORMAL_AFFINE_STORAGE", error=traceback.format_exc())
        exit_code = 1
    report["elapsed_seconds"] = time.monotonic()-started
    report["intent_receipt"] = intent_receipt
    result_receipt = seal(writer, report)
    print(json.dumps({"action": ACTION, "status": report["status"],
                      "intent_receipt": intent_receipt, "result_receipt": result_receipt,
                      "source_coercivity_checked": False, "original_g3_closed": False},
                     sort_keys=True))
    return exit_code

if __name__ == "__main__":
    raise SystemExit(run())
