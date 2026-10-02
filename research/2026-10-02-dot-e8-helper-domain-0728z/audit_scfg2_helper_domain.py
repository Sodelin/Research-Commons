#!/usr/bin/env python3
"""Public-source arithmetic screen, not a C++ execution or Lean proof.

Mirrors sparse_tree's parent construction and Euler traversal on balanced
round scaffolds, and checks the RMQ block/index invariant used by B and b.
The preserved public implementation is never modified or executed here.
"""
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
if len(sys.argv) != 2:
    raise SystemExit("usage: audit_scfg2_helper_domain.py PATH_TO_PINNED_CPARTY_SRC")
SRC = Path(sys.argv[1]).resolve()
PIN = "27afdd054272dbda8a74c8aad156970a44c23cd8"

def git_hash(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def source_receipt(rel):
    data = (SRC / rel).read_bytes()
    return {"path": "submodules/CParty/src/" + rel,
            "sha256": hashlib.sha256(data).hexdigest(), "git_blob_sha": git_hash(data)}

def tree_of(s):
    n = len(s)
    parent = [-1] * (n + 1)
    pair = [-2] * (n + 1)
    bases = [[] for _ in range(n + 1)]
    stack = [0]
    for i, c in enumerate(s, 1):
        if c == 'x':
            pair[i] = -1
        if c == ')':
            assert len(stack) > 1
            pair[i] = stack[-1]
            pair[stack[-1]] = i
            stack.pop()
        parent[i] = stack[-1]
        bases[stack[-1]].append(i)
        if c == '(':
            stack.append(i)
    assert stack == [0]
    # Iterative rendering of the same dfs events, avoiding Python stack limits.
    euler, depth, fai = [], [-1] * (n + 1), [-1] * (n + 1)
    todo = [(0, 0, True)]
    while todo:
        v, dep, enter = todo.pop()
        if enter:
            assert fai[v] == -1
            fai[v] = len(euler)
            depth[v] = dep
            euler.append(v)
            for child in reversed(bases[v]):
                todo.append((v, dep, False))
                todo.append((child, dep + 1, True))
        else:
            euler.append(v)
    assert len(euler) == 2 * n + 1
    assert [v for v in range(n + 1) if fai[v] < 0] == []
    assert all(fai[v] == 2 * v - depth[v] for v in range(n + 1))
    return parent, pair, depth, fai, euler

def check_table(euler, depth):
    E = len(euler)
    table = [[-1] * 14 for _ in range(E)]
    values = [depth[v] for v in euler]
    for i in range(1, E):
        table[i - 1][0] = i - 1 if values[i] > values[i - 1] else i
    for col in range(1, 14):
        offset = 1 << (col - 1)
        for i in range(E):
            if table[i][col - 1] == -1:
                break
            assert i + offset < E, (E, col, i)
            if table[i + offset][col - 1] == -1:
                break
            a, b = table[i][col - 1], table[i + offset][col - 1]
            table[i][col] = b if values[a] > values[b] else a
    for col in range(14):
        span = 1 << col
        for i in range(E):
            # Source col0 spans two positions; col k spans 2^k+1.
            assert (table[i][col] != -1) == (i + span < E)
            if table[i][col] != -1:
                selected = table[i][col]
                assert i <= selected <= i + span
                assert values[selected] == min(values[i:i + span + 1])
    return table

def scaffolds(n):
    def go(k, level, prefix):
        if k == n:
            if level == 0:
                yield prefix
            return
        yield from go(k + 1, level, prefix + '.')
        if level < n - k:
            yield from go(k + 1, level + 1, prefix + '(')
        if level:
            yield from go(k + 1, level - 1, prefix + ')')
    return go(0, 0, '')

def small_screen():
    total, queries, maxima = 0, 0, {}
    for n in range(1, 11):
        mb, ml = 0, 0
        for s in scaffolds(n):
            total += 1
            parent, pair, depth, fai, euler = tree_of(s)
            table = check_table(euler, depth)
            for l in range(1, n + 1):
                if parent[l] == 0 or pair[l] > -1:
                    continue
                assert 2 <= l <= n - 1 and depth[l] >= 2
                for j in range(l, n + 1):
                    if pair[parent[l]] > j:
                        continue
                    d = fai[j] - fai[l]
                    assert 0 <= d <= 2 * n - 3
                    mb = max(mb, d)
                    if d:
                        col = d.bit_length() - 1
                        assert table[fai[l]][col] >= 0
                        assert table[fai[j] - (1 << col)][col] >= 0
                        queries += 1
                for i in range(1, l + 1):
                    if parent[l] < i:
                        continue
                    d = fai[l] - fai[i]
                    assert 0 <= d <= 2 * n - 5
                    ml = max(ml, d)
                    if d:
                        col = d.bit_length() - 1
                        assert table[fai[i]][col] >= 0
                        assert table[fai[l] - (1 << col)][col] >= 0
                        queries += 1
        maxima[str(n)] = {"B_distance": mb, "b_distance": ml}
    return {"balanced_round_scaffolds": total, "guarded_positive_distance_queries": queries,
            "lengths": [1, 10], "maxima": maxima, "all_assertions_passed": True}

def edge_witness(n):
    # pair(1)=n-1, l=2 unpaired, j=n unpaired in root; B guard passes.
    s = '(' + '.' * (n - 3) + ').'
    parent, pair, depth, fai, euler = tree_of(s)
    l, j = 2, n
    assert parent[l] == 1 and pair[parent[l]] == n - 1 and pair[l] < 0
    assert pair[parent[l]] <= j
    d = fai[j] - fai[l]
    assert d == 2 * n - 3
    return {"n": n, "scaffold_description": "( followed by n-3 dots, then ).",
            "l": l, "j": j, "FAI_l": fai[l], "FAI_j": fai[j],
            "distance": d, "required_column": d.bit_length() - 1,
            "within_14_columns": d < 16384, "Cplusplus_executed": False}

if __name__ == '__main__':
    receipt = {
        "status": "PASS_SOURCE_ARITHMETIC_SCREEN", "attribution": "dot, E8 Lean proof worker 1",
        "repository": "TakumiOtagaki/PKProbDesign", "commit": PIN,
        "qualification": "Python mirror and hand source-domain argument; not a Lean parser proof, C++ crash test, whole-runtime memory proof, or all-accepted-input claim.",
        "source_files": [source_receipt(p) for p in ["sparse_tree.cc", "sparse_tree.hh",
            "part_func_init.cc", "part_func_energy.cc", "scfg2/api/exact.cc",
            "scfg2/deductions/generate_exact_basic.hh", "scfg2/deductions/wmb_geometry.hh",
            "scfg2/engine/basic_schedule.hh", "scfg2/replay/w_final_exact_inside.hh"]],
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "small_screen": small_screen(), "boundary_witnesses": [edge_witness(8193), edge_witness(8194)],
        "safe_RMQ_length_under_stated_helper_premises": [1, 8193],
        "preserved_source_mutated": False,
    }
    path = HERE / 'SCFG2-HELPER-DOMAIN-RECEIPT.json'
    path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({"status": receipt['status'], "screen": receipt['small_screen'],
                      "witnesses": receipt['boundary_witnesses'], "receipt": str(path)}, indent=2))
