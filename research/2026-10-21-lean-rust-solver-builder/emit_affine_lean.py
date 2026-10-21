"""Pure literal AFFINE proof emitter; SOURCE ONLY, UNEXECUTED.

No native child, compiler, files, model, network, or installed-import claim.
The caller must encrypt runtime-generated source before its first persistence.
"""
from affine_codec import Budget, decode, sha

MAX_SOURCE = 262144
RECEIVER_SHA256 = "62d4569e436aadb3202118a818c0ed7635c27a54b8e39b27a1e23188d80b5fc6"


def _rational(q):
    return "((" + str(q.numerator) + " : ℚ) / " + str(q.denominator) + ")"


def _vector(values):
    return "![" + ", ".join(values) + "]"


def _source_for_values(values):
    """Internal renderer; input must be the result of exact decode(), not a caller dictionary."""
    n, rows = values["dimension"], values["rows"]
    identity = sha((values["literal_request_sha256"] + ":" +
                    values["literal_certificate_sha256"]).encode("ascii"))
    namespace = "Astra.Generated.AffineCertificate_" + identity
    lines = [
        "import AffineCertificateReceiver",
        "",
        "/-! Literal finite-matrix certificate; no source/chart or native-origin premise.",
        "Request SHA256: " + values["literal_request_sha256"],
        "Certificate SHA256: " + values["literal_certificate_sha256"] + " -/",
        "namespace " + namespace,
        "",
        "open UnifiedLean.G6.StrictAffineElimination",
        "open UnifiedLean.G6.RationalAffineWitness",
        "open Astra.NativeAffineCertificates",
        "",
        "def originalRows : Fin " + str(len(rows)) + " → Row " + str(n) + " :=",
        "  " + _vector(["{ coeff := " + _vector([_rational(q) for q in row["coefficients"]]) +
                        ", bound := " + _rational(row["bound"]) +
                        ", strict := " + ("true" if row["strict"] else "false") + " }"
                       for row in rows]),
        ""
    ]
    if "point" in values:
        lines += [
            "def point : Fin " + str(n) + " → ℚ := " + _vector([_rational(q) for q in values["point"]]),
            "",
            "theorem value_checked :",
            "    checkRationalWitness (rowsSet originalRows) point = true := by",
            "  apply (checkRationalWitness_correct _ _).mpr",
            "  intro row hrow",
            "  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hrow",
            "  fin_cases a <;> norm_num [originalRows, point, Row.Holds, Row.eval,",
            "    UnifiedLean.G6.StrictAffineElimination.Rel, Fin.sum_univ_succ]",
            "",
            "theorem original_rows_hold :",
            "    ∀ a, (originalRows a).Holds (fun j => (point j : ℝ)) :=",
            "  checked_witness_real originalRows point value_checked"
        ]
        selected = ["value_checked", "original_rows_hold"]
    else:
        lines += [
            "def multipliers : Fin " + str(len(rows)) + " → ℚ := " +
            _vector([_rational(q) for q in values["weights"]]),
            "",
            "theorem value_checked : checkFarkas originalRows multipliers = true := by",
            "  norm_num [checkFarkas, originalRows, multipliers, Fin.sum_univ_succ,",
            "    Fin.forall_fin_succ, Fin.exists_fin_succ]",
            "",
            "theorem original_rows_infeasible :",
            "    ¬ ∃ x : Fin " + str(n) + " → ℝ, ∀ a, (originalRows a).Holds x :=",
            "  checked_farkas_infeasible originalRows multipliers value_checked"
        ]
        selected = ["value_checked", "original_rows_infeasible"]
    lines += ["", "end " + namespace, ""]
    source = "\n".join(lines)
    if len(source.encode("utf-8")) > MAX_SOURCE:
        raise Budget("literal AFFINE Lean source exceeds 256 KiB")
    return source, namespace, [namespace + "." + name for name in selected]


def render(request_literal, certificate_literal, *, checker):
    """Check original rows/derivation and prepare a proof, entirely in memory.

    Refused malformed/false inputs use the original checker.Refused class.
    Bounded arithmetic/source exhaustion returns UNKNOWN. No result here is a
    compiler receipt, native-origin authentication, or physical source result.
    """
    try:
        values = decode(request_literal, certificate_literal, checker)
        if not values["certificate_checked"]:
            return {"schema": "literal_affine_lean_preparation_v1", "status": "UNKNOWN",
                    "literal_request_sha256": values["literal_request_sha256"],
                    "literal_certificate_sha256": values["literal_certificate_sha256"],
                    "lean_source": None, "compiled": False, "physical_source_admission": False}
        source, namespace, selected = _source_for_values(values)
        return {"schema": "literal_affine_lean_preparation_v1",
                "status": "LITERAL_AFFINE_PROOF_PREPARED",
                "literal_request_sha256": values["literal_request_sha256"],
                "literal_certificate_sha256": values["literal_certificate_sha256"],
                "value_status": values["status"], "dimension": values["dimension"],
                "ordered_original_row_count": len(values["rows"]),
                "projection_cap": values["projection_cap"],
                "lean_namespace": namespace, "selected_declarations": selected,
                "source_sha256": sha(source.encode("utf-8")), "lean_source": source,
                "required_receiver_sha256": RECEIVER_SHA256,
                "compiled": False, "native_runtime_origin_authenticated": False,
                "native_parser_refinement_proved": False, "physical_source_admission": False}
    except Budget as error:
        return {"schema": "literal_affine_lean_preparation_v1", "status": "UNKNOWN",
                "reason": str(error), "literal_request_sha256": sha(request_literal),
                "literal_certificate_sha256": sha(certificate_literal),
                "lean_source": None, "compiled": False, "physical_source_admission": False}
