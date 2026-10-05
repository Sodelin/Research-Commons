"""Inventory the exact public example; biological assumptions stay conditional."""
import collections
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
UPSTREAM = ROOT / "upstream-bpp-v4.8.7"
EXAMPLE = UPSTREAM / "examples/frogs"
RELEASE = ROOT / "runtime/bpp-4.8.7-linux-x86_64/examples/frogs"


def digest(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
            "git_blob_sha1": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()}


def admit():
    mappings = {}
    for line in (EXAMPLE / "frogs.Imap.txt").read_text().splitlines():
        if not line.strip():
            continue
        label, species = line.split()
        if label in mappings:
            raise ValueError("duplicate specimen map key")
        if species not in {"K", "C", "L", "H"}:
            raise ValueError("unexpected population")
        mappings[label] = species
    lines = [line.strip() for line in (EXAMPLE / "frogs.txt").read_text().splitlines() if line.strip()]
    loci, offset = [], 0
    while offset < len(lines):
        n, length = map(int, lines[offset].split())
        offset += 1
        labels, chars, counts = set(), collections.Counter(), collections.Counter()
        for line in lines[offset:offset+n]:
            label, seq = line.split()
            if not label.startswith("^") or label[1:] not in mappings:
                raise ValueError("unmapped input label")
            if label in labels or len(seq) != length:
                raise ValueError("duplicate label or length mismatch")
            if set(seq.upper()) - set("ACGTRYSWKMBDHVN?-"):
                raise ValueError("invalid nucleotide/IUPAC symbol")
            labels.add(label)
            chars.update(seq.upper())
            counts[mappings[label[1:]]] += 1
        if len(labels) != n:
            raise ValueError("truncated locus")
        offset += n
        loci.append({"locus_index": len(loci)+1, "sequence_count": n, "length": length,
                     "population_counts": dict(sorted(counts.items())),
                     "iupac_heterozygote_count": sum(v for k, v in chars.items() if k in "RYSWKM"),
                     "other_ambiguous_or_missing_count": sum(v for k, v in chars.items() if k in "BDHVN?-"),
                     "no_recombination_verified": False})
    if len(loci) != 5:
        raise ValueError("expected five nuclear example loci")
    names = ["frogs.txt", "frogs.Imap.txt", "A00.bpp.ctl", "A01.bpp.ctl"]
    files = {}
    for name in names:
        if (EXAMPLE/name).read_bytes() != (RELEASE/name).read_bytes():
            raise ValueError("source/release example mismatch: " + name)
        files[name] = digest(EXAMPLE/name)
    return {"schema": "official-bpp-example-local-admission-v1", "upstream_commit": "da8caf3aa00cf275cc9a044e0d806e9bbb0e1460",
            "status": "ENGINE_INPUT_VALID_UNDER_DECLARED_EXAMPLE_ASSUMPTIONS",
            "scientific_admission_claimed": False, "raw_data_public_redistribution": False,
            "files": files, "loci": loci, "map_entries": len(mappings),
            "assumptions": ["five nuclear example loci", "no within-locus recombination", "free between-locus recombination",
                            "fixed original K/C/L/H assignments", "unphased diploid phase=1,1,1,1; cleandata=0",
                            "neutral MSC genealogy; configured substitution/clock model"],
            "unresolved": ["independent biological verification of linkage/recombination/orthology", "third-party data redistribution license",
                           "model adequacy", "chain mixing", "calendar calibration"],
            "source_references": ["https://github.com/bpp/bpp/tree/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460/examples/frogs",
                                  "https://academic.oup.com/mbe/article/35/10/2585/5057515",
                                  "https://onlinelibrary.wiley.com/doi/abs/10.1111/j.1365-294X.2011.05411.x"]}


if __name__ == "__main__":
    result = admit()
    (ROOT / "LOCAL-EXAMPLE-ADMISSION.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))
