#!/usr/bin/env python3
"""Source-rooted CHART fixtures and protocol/admission countercontrols."""
from __future__ import annotations

from dataclasses import dataclass
import argparse
import hashlib
import json
from pathlib import Path

from certificate_check import require
from chart_check import parse_chart, compile_chart, row_wire


@dataclass(frozen=True)
class ChartCase:
    name: str
    request: bytes
    expected: str | None = None
    source_scope: str = "literal shared-bank natural chart; source admission gate retained"


def chart_request(vertices, edges, leaves, hybrids=(), chronology=(), exposures=(), coins=(), cap=4096, root=0):
    require(len(coins) == len(hybrids), "fixture lacks one coin interval per original hybrid")
    lines = [f"RC1 CHART {vertices} {len(edges)} {len(leaves)} {len(hybrids)} {len(chronology)} {len(exposures)} {cap}",
             f"ROOT {root}"]
    lines.extend(f"EDGE {i} {source} {target}" for i, (source, target) in enumerate(edges))
    lines.extend(f"LEAF {i} {vertex}" for i, vertex in enumerate(leaves))
    lines.extend(f"HYBRID {i} {vertex} {incoming0} {incoming1}"
                 for i, (vertex, incoming0, incoming1) in enumerate(hybrids))
    lines.extend(f"AGE {relation} {left} {right}" for relation, left, right in chronology)
    lines.extend(f"EXPOSURE {i} {population} {younger} {older} {lower} {upper}"
                 for i, (population, younger, older, lower, upper) in enumerate(exposures))
    lines.extend(f"COIN {i} {lower} {upper}" for i, (lower, upper) in enumerate(coins))
    return ("\n".join(lines) + "\n").encode()


def chart_cases():
    ordinary = dict(vertices=3, edges=((0, 1), (0, 2)), leaves=(1, 2))
    parallel = dict(vertices=5, edges=((0, 1), (0, 2), (2, 3), (2, 3), (3, 4)),
                    leaves=(1, 4), hybrids=((3, 2, 3),), coins=(("NONE", "NONE"),))
    diamond = dict(vertices=7, edges=((0, 1), (0, 2), (1, 3), (1, 4), (2, 3), (2, 5), (3, 6)),
                   leaves=(4, 5, 6), hybrids=((3, 2, 4),), coins=(("LE:1/4", "LE:3/4"),))
    cases = []

    def add(name, expected=None, **options):
        cases.append(ChartCase(name, chart_request(**options), expected))

    add("chart_two_tip_empty", "SAT", **ordinary)
    add("chart_two_tip_typed_cells", "SAT", **ordinary,
        chronology=(("EQ", "V:0", "Q:2/1"),),
        exposures=(("E:0", "V:1", "V:0", "LE:1/1", "LE:4/1"),
                   ("E:1", "V:2", "V:0", "LE:1/1", "LE:4/1"),
                   ("A", "Q:2/1", "Q:3/1", "LE:1/1", "LE:2/1")))
    add("chart_missing_interval_ends", "SAT", **ordinary,
        exposures=(("E:0", "V:1", "V:0", "NONE", "NONE"),
                   ("A", "Q:0/1", "Q:1/1", "LE:0/1", "NONE")))
    add("chart_fixed_negative_literal_cuts", "SAT", **ordinary,
        chronology=(("LT", "Q:-1/1", "V:0"), ("LE", "V:0", "Q:2/1")),
        exposures=(("A", "Q:-3/2", "Q:-1/2", "LE:1/2", "LE:2/1"),))
    add("chart_shared_edge_contradiction", "UNSAT", **ordinary,
        exposures=(("E:0", "V:1", "V:0", "LE:1/1", "LE:1/1"),
                   ("E:0", "V:1", "V:0", "LE:2/1", "LE:2/1")))
    add("chart_shared_ancestral_contradiction", "UNSAT", **ordinary,
        exposures=(("A", "Q:0/1", "Q:1/1", "LE:1/1", "LE:1/1"),
                   ("A", "Q:0/1", "Q:2/1", "LE:1/1", "LE:1/1")))
    add("chart_calendar_strict_boundary", "UNSAT", **ordinary,
        chronology=(("EQ", "V:0", "Q:0/1"),))
    add("chart_weak_duration_singleton", "SAT", **ordinary,
        chronology=(("EQ", "V:0", "Q:2/1"),),
        exposures=(("E:0", "V:1", "V:0", "LE:1/1", "LE:1/1"),))
    add("chart_strict_duration_singleton", "UNSAT", **ordinary,
        exposures=(("E:0", "V:1", "V:0", "LT:1/1", "LE:1/1"),))
    add("chart_projection_limit", "UNKNOWN", **ordinary, cap=0)
    add("chart_parallel_original_occurrences", "SAT", **parallel)
    add("chart_parallel_shared_tie", "SAT", **parallel,
        chronology=(("EQ", "V:0", "Q:3/1"), ("EQ", "V:2", "Q:2/1"), ("EQ", "V:3", "Q:1/1")),
        exposures=(("E:2", "V:3", "V:2", "LE:1/1", "LE:4/1"),
                   ("E:3", "V:3", "V:2", "LE:1/1", "LE:4/1")))
    strict_coin = dict(parallel)
    strict_coin["coins"] = (("NONE", "LE:0/1"),)
    add("chart_hybrid_strict_coin_boundary", "UNSAT", **strict_coin)
    singleton_coin = dict(parallel)
    singleton_coin["coins"] = (("LE:1/2", "LE:1/2"),)
    add("chart_hybrid_weak_coin_singleton", "SAT", **singleton_coin)
    bad_coin_interval = dict(parallel)
    bad_coin_interval["coins"] = (("LE:3/4", "LE:1/4"),)
    add("chart_hybrid_reversed_interval", "UNSAT", **bad_coin_interval)
    add("chart_nonparallel_hybrid", "SAT", **diamond)
    base = cases[0].request
    hybrid = cases[10].request
    invalid = {
        "chart_bad_extra_line": base + b"AGE LE V:0 V:0\n",
        "chart_bad_duplicate_edge_id": base.replace(b"EDGE 1", b"EDGE 0"),
        "chart_bad_leaf_alias": base.replace(b"LEAF 1 2", b"LEAF 1 1"),
        "chart_bad_root": base.replace(b"ROOT 0", b"ROOT 1"),
        "chart_bad_vertex_ref": base.replace(b"EDGE 1 0 2", b"EDGE 1 0 3"),
        "chart_bad_loop": base.replace(b"EDGE 1 0 2", b"EDGE 1 0 0"),
        "chart_bad_hybrid_parent_alias": hybrid.replace(b"HYBRID 0 3 2 3", b"HYBRID 0 3 2 2"),
        "chart_bad_hybrid_parent_target": hybrid.replace(b"HYBRID 0 3 2 3", b"HYBRID 0 3 0 3"),
        "chart_bad_hybrid_vertex": hybrid.replace(b"HYBRID 0 3 2 3", b"HYBRID 0 2 2 3"),
        "chart_bad_coin_id": hybrid.replace(b"COIN 0", b"COIN 1"),
        "chart_bad_float_endpoint": hybrid.replace(b"COIN 0 NONE NONE", b"COIN 0 LE:0.5 NONE"),
        "chart_bad_noncanonical_endpoint": hybrid.replace(b"COIN 0 NONE NONE", b"COIN 0 LE:2/4 NONE"),
        "chart_bad_missing_final_lf": base[:-1],
        "chart_bad_crlf": base.replace(b"\n", b"\r\n"),
        "chart_bad_non_ascii": base + b"\xff",
    }
    # Degrees, root reachability and acyclicity all pass, but a nonroot
    # dominator lies below both root edge occurrences: RootedBinary rejects it.
    invalid["chart_bad_root_lsa"] = chart_request(5,
        ((0, 1), (0, 1), (1, 2), (2, 3), (2, 4)), (3, 4), ((1, 0, 1),), coins=(("NONE", "NONE"),))
    cases.extend(ChartCase(name, raw, "REFUSED", "chart grammar/structural refusal") for name, raw in invalid.items())
    return cases


def write_fixtures(directory):
    require(not directory.exists(), "chart fixture directory exists")
    directory.mkdir(parents=True)
    entries = []
    for case in chart_cases():
        (directory / (case.name + ".req")).write_bytes(case.request)
        entry = {"name": case.name, "expected": case.expected, "scope": case.source_scope,
                 "request_sha256": hashlib.sha256(case.request).hexdigest()}
        try:
            chart = parse_chart(case.request)
            require(case.expected != "REFUSED", "refusal fixture is actually accepted by reference")
            rows = compile_chart(chart)
            (directory / (case.name + ".matrix")).write_text("\n".join(map(row_wire, rows)) + "\n")
            entry.update(bank_keys=chart.bank_keys, bank_dimension=chart.dimension, compiled_rows=len(rows))
        except (ValueError, UnicodeError):
            require(case.expected == "REFUSED", "valid chart fixture rejected by reference")
        entries.append(entry)
    (directory / "INDEX.json").write_text(json.dumps(entries, indent=2, sort_keys=True) + "\n")
    return entries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-fixtures", required=True, type=Path)
    args = parser.parse_args()
    entries = write_fixtures(args.write_fixtures.resolve())
    print(json.dumps({"fixtures_written": len(entries), "directory": str(args.write_fixtures.resolve())}))


if __name__ == "__main__":
    main()
