#!/usr/bin/env python3
"""Original-graph full joint LAW fixtures, copies, routing and budget controls."""
from dataclasses import dataclass
import argparse
import hashlib
import json
from pathlib import Path

from certificate_check import require
from law_check import parse_law


@dataclass(frozen=True)
class LawCase:
    name: str
    request: bytes
    expected: str = "TABLE"
    source_scope: str = "formal full joint supplied-source genealogy table; physical admission gate retained"
    expected_limit: tuple | None = None


def law_request(vertices, edges, leaves, samples, hybrids=(), mechanism="COMMON", state_cap=4096,
                term_cap=65536, history_cap=4096, root=0):
    lines = [f"RC1 LAW {vertices} {len(edges)} {len(leaves)} {len(hybrids)} {len(samples)} {state_cap} {term_cap} {history_cap}",
             f"MECHANISM {mechanism}", f"ROOT {root}"]
    lines.extend(f"EDGE {i} {a} {b}" for i, (a, b) in enumerate(edges))
    lines.extend(f"LEAF {i} {v}" for i, v in enumerate(leaves))
    lines.extend(f"HYBRID {i} {v} {a} {b}" for i, (v, a, b) in enumerate(hybrids))
    lines.extend(f"SAMPLE {i} {taxon}" for i, taxon in enumerate(samples))
    return ("\n".join(lines) + "\n").encode()


def law_cases():
    two = dict(vertices=3, edges=((0, 1), (0, 2)), leaves=(1, 2))
    three = dict(vertices=5, edges=((0, 1), (0, 2), (1, 3), (1, 4)), leaves=(2, 3, 4))
    balanced = dict(vertices=7, edges=((0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6)), leaves=(3, 4, 5, 6))
    comb = dict(vertices=7, edges=((0, 1), (0, 2), (2, 3), (2, 4), (4, 5), (4, 6)), leaves=(1, 3, 5, 6))
    parallel = dict(vertices=5, edges=((0, 1), (0, 2), (2, 3), (2, 3), (3, 4)), leaves=(1, 4), hybrids=((3, 2, 3),))
    diamond = dict(vertices=7, edges=((0, 1), (0, 2), (1, 3), (1, 4), (2, 3), (2, 5), (3, 6)),
                   leaves=(4, 5, 6), hybrids=((3, 2, 4),))
    cases = []

    def add(name, samples, graph, *, expected="TABLE", limit=None, **options):
        cases.append(LawCase(name, law_request(samples=samples, **graph, **options), expected, expected_limit=limit))

    add("law_two_tip", (0, 1), two)
    add("law_single_copy_unsampled_taxon", (1,), two)
    add("law_three_tip", (0, 1, 2), three)
    add("law_three_tip_copied_label_permutation", (2, 0, 1), three)
    add("law_four_tip_balanced", (0, 1, 2, 3), balanced)
    add("law_four_tip_comb", (0, 1, 2, 3), comb)
    add("law_four_copies_one_taxon", (1, 1, 1, 1), two)
    add("law_four_copies_two_taxa", (0, 0, 1, 1), two)
    add("law_unsampled_declared_taxa", (0, 1, 1), balanced)
    for mode in ("COMMON", "INDEPENDENT"):
        add("law_parallel_three_" + mode.lower(), (0, 1, 1), parallel, mechanism=mode)
        add("law_parallel_four_" + mode.lower(), (0, 1, 1, 1), parallel, mechanism=mode)
        add("law_nonparallel_three_" + mode.lower(), (0, 1, 2), diamond, mechanism=mode)
        reversed_parents = dict(parallel, hybrids=((3, 3, 2),))
        add("law_original_parent_order_" + mode.lower(), (0, 1, 1), reversed_parents, mechanism=mode)
    add("law_history_limit_zero", (0, 1, 1), parallel, history_cap=0,
        expected="UNKNOWN", limit=("HISTORY", 4, 1, 0))
    add("law_history_limit_nonzero", (1, 1, 1), two, history_cap=2,
        expected="UNKNOWN", limit=("HISTORY", 2, 3, 2))
    add("law_state_limit_zero", (0, 1), two, state_cap=0,
        expected="UNKNOWN", limit=("STATE", 2, 1, 0))
    add("law_state_limit_nonzero", (0, 1, 2), three, state_cap=1,
        expected="UNKNOWN", limit=("STATE", 1, 2, 1))
    add("law_term_limit_zero", (0, 1), two, term_cap=0,
        expected="UNKNOWN", limit=("TERM", 2, 1, 0))
    add("law_term_limit_nonzero", (0, 1, 2), three, term_cap=1,
        expected="UNKNOWN", limit=("TERM", 1, 3, 1))
    base, hybrid = cases[0].request, cases[9].request
    invalid = {
        "law_bad_duplicate_sample_id": base.replace(b"SAMPLE 1", b"SAMPLE 0"),
        "law_bad_sampled_taxon": base.replace(b"SAMPLE 1 1", b"SAMPLE 1 2"),
        "law_bad_sample_float": base.replace(b"SAMPLE 1 1", b"SAMPLE 1 1.0"),
        "law_bad_copy_count": base.replace(b"0 2 4096", b"0 5 4096", 1),
        "law_bad_state_cap": base.replace(b"4096 65536", b"4097 65536", 1),
        "law_bad_term_cap": base.replace(b"4096 65536", b"4096 65537", 1),
        "law_bad_history_cap": base.replace(b"65536 4096", b"65536 4097", 1),
        "law_bad_parent_alias": hybrid.replace(b"HYBRID 0 3 2 3", b"HYBRID 0 3 2 2"),
        "law_bad_mechanism": base.replace(b"MECHANISM COMMON", b"MECHANISM BOTH"),
        "law_bad_forced_route_field": hybrid+b"FORCE 0 1\n",
        "law_bad_extra_record": base+b"SAMPLE 2 0\n",
        "law_bad_loop": base.replace(b"EDGE 1 0 2", b"EDGE 1 0 0"),
        "law_bad_duplicate_edge_id": base.replace(b"EDGE 1", b"EDGE 0"),
        "law_bad_missing_lf": base[:-1],
        "law_bad_crlf": base.replace(b"\n", b"\r\n"),
        "law_bad_non_ascii": base+b"\xff",
    }
    cases.extend(LawCase(name, raw, "REFUSED", "LAW grammar/structural refusal") for name, raw in invalid.items())
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-fixtures", type=Path, required=True)
    args = parser.parse_args()
    require(not args.write_fixtures.exists(), "LAW fixture directory exists")
    args.write_fixtures.mkdir(parents=True)
    entries = []
    for case in law_cases():
        (args.write_fixtures/(case.name+".req")).write_bytes(case.request)
        try:
            parse_law(case.request)
            require(case.expected != "REFUSED", "LAW refusal fixture admitted by independent parser")
        except (ValueError, UnicodeError):
            require(case.expected == "REFUSED", "LAW valid fixture refused by independent parser")
        entries.append({"name": case.name, "expected": case.expected, "expected_limit": case.expected_limit,
                        "scope": case.source_scope, "request_sha256": hashlib.sha256(case.request).hexdigest()})
    (args.write_fixtures/"INDEX.json").write_text(json.dumps(entries, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"fixtures_written":len(entries),"directory":str(args.write_fixtures.resolve())}))


if __name__ == "__main__":
    main()
