"""Exact replay of archived observation extraction and finite-band obstruction.

This audits input arithmetic. It never issues scientific data admission or a
new confidence event, and does not replace the producer or whole-journal check.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
from types import ModuleType

COMMONS = Path(__file__).resolve().parents[2]
SOURCE = COMMONS / "research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration"
ARCHIVE = COMMONS / "research/2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json"
PINS = {
    "integration_core.py": "f409f3ae1cfeb04db61f7b3b9f0aad76e18e372c57289463ad7d5622023b131e",
    "declared-model/DATASET.json": "4ae2d541515bf87d1709d3708e74af9f2c2ac2ae35ed60d38456050b3ef60e03",
    "composition-attempt1/ANALYSIS-REQUEST.json": "aebcfdfe2caa31d842f56be70387b415fc9f8677aa8f8cd4a58ea62b83c82f30",
    "composition-attempt1/prepared/EXTRACTION.json": "89619327bfe8e8fb86c0b5e0792e9361ab3824a3ed4f0567858ffe6c65bc8ec7",
    "composition-attempt1/prepared/CONFIDENCE.json": "84fa51b6961b6f0e63eb5d6aa04f54c2914532285ab1ada4f8c42952915c2926",
}
ARCHIVE_SHA = "8acf47eadbb01e220f9ebb87746b64f070a0f527bfc0a230e58b316e9f3c6931"


def authenticated_extractor():
    path = SOURCE / "integration_core.py"
    raw = path.read_bytes()
    if path.is_symlink() or hashlib.sha256(raw).hexdigest() != PINS["integration_core.py"]:
        raise ValueError("literal extractor identity changed")
    module = ModuleType("_rc_verified_literal_extractor")
    module.__file__ = str(path)
    sys.modules[module.__name__] = module
    exec(compile(raw, str(path), "exec", dont_inherit=True), module.__dict__)
    return module


def shifted_to_raw(bounds):
    """One affine projection; reject empty intersection rather than reorder it."""
    lower, upper = map(F, bounds)
    if not F(0) <= lower <= upper <= F(1):
        raise ValueError("shifted mean band must lie in [0,1]")
    raw = max(F(0), 2 * lower - 1), min(F(1), 2 * upper - 1)
    if raw[0] > raw[1]:
        raise ValueError("shifted band has empty intersection with the nonnegative clock-JC moment model")
    return [str(value) for value in raw]


def audit_archived_panel():
    extractor = authenticated_extractor()
    objects = {name: extractor.read(SOURCE / name, digest)
               for name, digest in PINS.items() if name.endswith(".json")}
    request = objects["composition-attempt1/ANALYSIS-REQUEST.json"]
    extraction = extractor.extract(objects["declared-model/DATASET.json"], request["expected_loci"], request["selection_sha256"])
    if extraction != objects["composition-attempt1/prepared/EXTRACTION.json"]:
        raise ValueError("literal extraction differs from inherited receipt")
    confidence = objects["composition-attempt1/prepared/CONFIDENCE.json"]
    radius = F(confidence["radius"])
    bands = {key: [str(max(F(0), F(count, extraction["m"]) - radius)),
                   str(min(F(1), F(count, extraction["m"]) + radius))]
             for key, count in extraction["counts"].items()}
    if radius != F(3301, 65536) or bands != confidence["shifted_mean_box"]:
        raise ValueError("fixed-block band arithmetic differs")
    raw_projection = {key: shifted_to_raw(bounds) for key, bounds in bands.items()}
    if any(raw_projection[key] != [value["lower"], value["upper"]]
           for key, value in confidence["raw_moment_projection"].items()):
        raise ValueError("once-only moment conversion differs")
    # The numerical receipt includes decimal timing fields, unlike the literal
    # observation grammar. Preserve them as text; only rational source fields
    # below participate in this exact check.
    archive_raw = ARCHIVE.read_bytes()
    if ARCHIVE.is_symlink() or len(archive_raw) > 16 * 2**20 or hashlib.sha256(archive_raw).hexdigest() != ARCHIVE_SHA:
        raise ValueError("source pair archive identity or size changed")
    def reject_constant(_):
        raise ValueError("nonfinite source receipt number")
    pair = json.loads(archive_raw, object_pairs_hook=extractor.no_duplicates,
                      parse_float=str, parse_constant=reject_constant)
    points, means = pair["source_parameter_points"], pair["source_forward_mean_boxes"]
    if len(points) != 2 or len(means) != 2:
        raise ValueError("source pair archive differs")
    admitted = all(F(request["domain"][key][0]) <= F(bounds[0]) == F(bounds[1]) <= F(request["domain"][key][1])
                   for point in points for key, bounds in point.items())
    contained = all(set(mean) == set(bands) and all(F(bands[key][0]) <= F(bounds[0]) <= F(bounds[1]) <= F(bands[key][1])
                    for key, bounds in mean.items()) for mean in means)
    separation = abs(F(points[0]["rA"][0]) - F(points[1]["rA"][0])) / (F(request["domain"]["rA"][1]) - F(request["domain"]["rA"][0]))
    if not admitted or not contained or separation != F(3, 55):
        raise ValueError("archived finite-band precision obstruction differs")
    return {
        "schema": "practical-solver-biological-input-audit-v1", "status": "PASS",
        "execution_status": "FRESH_LITERAL_EXTRACTION_AND_EXACT_CONTAINMENT_REPLAY",
        "loci": extraction["m"], "counts": extraction["counts"],
        "selection_sha256": extraction["selection_sha256"], "radius": str(radius),
        "shifted_mean_box": bands, "raw_moment_box": raw_projection, "mean_conversion_count": 1,
        "two_original_domain_points_contained": admitted and contained,
        "normalized_rA_separation": str(separation), "requested_target": "1/20",
        "fixed_band_all_nine_width_goal_impossible": separation > F(1, 20),
        "confidence_enclosures": "inherited authenticated 80-bit receipt; no new exponential calculation or confidence event",
        "source_forward_means": "inherited authenticated rigorous enclosure receipt; containment freshly checked, forward solver not rerun here",
        "scientific_confidence_admitted": False, "finite_generator_law_certified": False,
        "parameter_accuracy_released": False, "fresh_data": False,
        "input_sha256": {**PINS, "source_pair_archive": ARCHIVE_SHA},
        "scope": "this archived nine-mean band and source model; other justified estimators or new observations remain possible",
    }


if __name__ == "__main__":
    print(json.dumps(audit_archived_panel(), indent=2, sort_keys=True))
