"""Static source pins and rational cap-three identities; no provider execution."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import subprocess
import datetime

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "research/2026-10-08-codex-g3-g4-coordinated-1000z"
P = BASE / "g4-stopping/marked-nonordinary"


def read(p):
    b = p.read_bytes()
    return b, hashlib.sha256(b).hexdigest()


def add(a, b, scale=F(1)):
    c = dict(a)
    for k, v in b.items():
        c[k] = c.get(k, F()) + scale * v
    return {k: v for k, v in c.items() if v}


def mul(a, b):
    c = {}
    for i, v in a.items():
        for j, w in b.items():
            c[i + j] = c.get(i + j, F()) + v * w
    return {k: v for k, v in c.items() if v}


def scale(a, q):
    return {k: q * v for k, v in a.items() if q * v}


def main():
    providers = []
    for name in ("SOURCE-PINS.json", "CAP5-SOURCE-PINS.json"):
        data = json.loads(read(P / name)[0])
        for row in data["providers"]:
            raw, sha = read(ROOT / row["path"])
            assert sha == row["sha256"] and len(raw) == row["bytes"]
            ref = row["commit"] + ":" + row["path"]
            gitraw = subprocess.run(["git", "show", ref], cwd=ROOT, check=True, capture_output=True).stdout
            blob = subprocess.run(["git", "rev-parse", ref], cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip()
            assert gitraw == raw and blob == row["git_blob"]
            providers.append({"path": row["path"], "commit": row["commit"], "git_blob": blob,
                              "sha256": sha, "bytes": len(raw), "match": True})
    manifest_raw, msha = read(P / "MANIFEST-SUPPLIED-LENGTH-UPDATE.json")
    assert msha == "344941b44a9d2be67d747f8a9f0f197e98612905fd027ee71c690b654a6387c9"
    manifest = json.loads(manifest_raw)
    objects = []
    for row in manifest["files"]:
        raw, sha = read(P / row["path"])
        assert sha == row["sha256"] and len(raw) == row["bytes"]
        objects.append({"path": str((P / row["path"]).relative_to(ROOT)), "sha256": sha, "bytes": len(raw), "match": True})
    assert read(P / "MANIFEST.json")[1] == manifest["prior_manifest_sha256"]
    one, s = {0: F(1)}, {1: F(1)}
    beta = scale(add(one, s), F(1, 2))
    beta3 = mul(mul(beta, beta), beta)
    # Direct fair original routing after substitution s*h^2=(1-s)^3/6.
    sh2 = scale(mul(mul(add(one, s, F(-1)), add(one, s, F(-1))),
                      add(one, s, F(-1))), F(1, 6))
    s3 = mul(mul(s, s), s)
    bare3 = scale(add(add(s3, sh2, F(3)), s, F(3)), F(1, 4))
    assert bare3 == beta3
    pair = scale(add(add(add({0: F(2)}, s, F(-1)), s3, F(-1)), sh2, F(-3)), F(1, 8))
    tree = scale(add(add(add({0: F(2)}, s, F(-3)), s3), sh2, F(3)), F(1, 24))
    assert pair == scale(add(beta, beta3, F(-1)), F(1, 2))
    assert tree == add(add({0: F(1, 3)}, beta, F(-1, 2)), beta3, F(1, 6))
    assert add(add(bare3, pair, F(3)), tree, F(3)) == one
    receipt = json.loads(read(P / "EXACT-CAP-THREE-RECEIPT.json")[0])
    assert receipt["script_sha256"] == read(P / "exact_cap_three_check.py")[1]
    fixtures = []
    for row in receipt["positive_source_fixtures"]:
        q, mean = F(row["q"]), F(row["s"])
        h2 = (1 - mean) ** 3 / (6 * mean)
        beta_value = (1 + mean) / 2
        pad2 = q / beta_value
        assert 0 < h2 < min(mean ** 2, (1 - mean) ** 2) and 0 < pad2 < 1
        assert (mean ** 3 + 3 * mean * h2 + 3 * mean) / 4 == beta_value ** 3
        assert pad2 * beta_value == q and pad2 ** 3 * beta_value ** 3 == q ** 3
        fixtures.append({"q": str(q), "s": str(mean), "strict_arms_and_pads": True,
                         "complete_cap3_bare_is_ordinary_beta": True})
    result = {"schema": "reviewer-marked-ordinary-target-static-v1", "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "manifest_sha256": msha, "provider_pins": providers, "objects": objects,
              "complete_fair_bare_cap3_coefficients_match_ordinary_beta": True,
              "opaque_merged_pair_rows_use_same_pair_survival": True,
              "fixtures": fixtures, "author_symbolic_receipt_script_hash_matches": True,
              "provider_or_author_code_imported_or_executed": False,
              "scope": "Exact immutable source identities and independent rational polynomial identities for all exchangeable three-root forest categories; chain-count, cap-five existence, effective fixed-length stopping and legal tomography remain hand/reused theorem obligations."}
    dest = Path(__file__).with_name("G4-MARKED-ORDINARY-SOURCE-AUTHENTICATION.json")
    dest.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "providers": len(providers), "objects": len(objects), "fixtures": len(fixtures), "output": str(dest)}))


if __name__ == "__main__":
    main()
