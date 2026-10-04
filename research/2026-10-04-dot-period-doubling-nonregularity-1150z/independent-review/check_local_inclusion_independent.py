"""Independent transcription of the universal B-pattern tiling inclusion.

No author-code import. Differences: domino output is emitted on its FIRST bit;
independent-set difference is accumulated on every bit, not inferred from
parity representatives; the two rewrite rules are chosen before their second
letter; residual strings have separate source/target fields. No queue bound.
Acceptance requires literal exhaustion of all reachable states.
"""
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib, json


def cover(state, bit, parity):
    used, due = state
    if due:
        return [((used, False), "")] if bit else []
    if not bit:
        return [((False, False), "")]
    ans = [((used, True), str(parity))]
    if not used:
        ans.append(((True, False), str(1-parity)*2))
    return ans


# Rewrite state (phase, remaining literal pattern, eventual replacement).
# phase 0 copies or starts one of the two rules; 1 completes its chosen rule;
# phase 2 copies forever. Phases 0 and 2 are accepting.
READY = (0, "", "")
DONE = (2, "", "")

def rewrite(state, letter):
    phase, tail, replacement = state
    if phase == 0:
        return [(READY, letter), ((1, letter, ""), ""),
                ((1, letter*2, str(1-int(letter))), "")]
    if phase == 2:
        return [(DONE, letter)]
    if letter != tail[0]:
        return []
    if len(tail) == 1:
        return [(DONE, replacement)]
    return [((1, tail[1:], replacement), "")]


@lru_cache(None)
def through_two(a, b, string):
    current = {(a, b, "")}
    for char in string:
        following = set()
        for sa, sb, sofar in current:
            for na, middle in rewrite(sa, char):
                if middle:
                    for nb, out in rewrite(sb, middle):
                        following.add((na, nb, sofar+out))
                else:
                    following.add((na, sb, sofar))
        current = following
    return frozenset(current)


def cancel(left, right):
    upto = min(len(left), len(right))
    if left[:upto] != right[:upto]:
        return None
    return left[upto:], right[upto:]


@lru_cache(None)
def witnesses_step(w, before, parity, target_output):
    tile, a, b, left, right = w
    result = set()
    for ntile, emit in cover(tile, before, parity):
        for na, nb, source_output in through_two(a, b, emit):
            rest = cancel(left+source_output, right+target_output)
            if rest is not None:
                result.add((ntile, na, nb, *rest))
    return frozenset(result)


def bits(state, word):
    """Read paired Gray digits and update the EXACT integer I difference."""
    colour, source_run_parity, target_run_parity, delta, tile, witnesses = state
    states = {state}
    for before, after in word:
        fresh = set()
        for p, ps, pt, d, t, ws in states:
            ns = (ps ^ 1) if before else 0
            nt = (pt ^ 1) if after else 0
            nd = d + int(before and not ps) - int(after and not pt)
            for tt, output in cover(t, after, p):
                ww = frozenset(v for w in ws for v in witnesses_step(w, before, p, output))
                fresh.add((p ^ 1, ns, nt, nd, tt, ww))
        states = fresh
    return states


def next_patterns(phase):
    if phase == 0:  # arbitrary left ones, or edited x
        return [(0, ((1, 1),))] + [(1, ((x, 1-x),)) for x in (0, 1)]
    if phase == 1:
        return [(2, ((1, 1),))]
    if phase == 2:  # arbitrary PAIRS of zeroes, or edited y
        return [(2, ((0, 0), (0, 0)))] + [(3, ((y, 1-y),)) for y in (0, 1)]
    if phase == 3:
        return [(4, ((z, 1-z),)) for z in (0, 1)]
    return [(4, ((1, 1),))]


def closure(colour):
    w = ((False, False), READY, READY, "", "")
    initial = (0, (colour, 0, 0, 0, (False, False), frozenset({w})))
    seen = {initial}
    work = [initial]
    transitions = eligible = 0
    while work:
        phase, state = work.pop()
        p, ps, pt, difference, target, ws = state
        if phase == 4 and not target[1] and difference == 1:
            eligible += 1
            assert any(not tile[1] and a[0] != 1 and b[0] != 1
                       and left == right == ""
                       for tile, a, b, left, right in ws), (phase, state)
        for next_phase, paired in next_patterns(phase):
            for result in bits(state, paired):
                transitions += 1
                new = (next_phase, result)
                if new not in seen:
                    seen.add(new)
                    work.append(new)
                    if len(seen) >= 100000:
                        raise RuntimeError("RESOURCE STOP: no certificate")
    # Serialize the complete reachable inventory, preserving every unbounded
    # integer/string value actually reached. No quotient by an observed bound.
    inventory = []
    for phase, (p, ps, pt, delta, target, ws) in seen:
        inventory.append([phase, p, ps, pt, delta, target, sorted(ws, key=repr)])
    raw = json.dumps(sorted(inventory, key=repr), separators=(",", ":")).encode()
    Path(__file__).with_name(f"INDEPENDENT-LOCAL-STATES-{colour}.json").write_bytes(raw)
    return {"initial_colour": colour, "states": len(seen), "transitions": transitions,
            "eligible_ends": eligible, "maximum_queue": max(max(len(w[3]), len(w[4]))
              for _, state in seen for w in state[-1]),
            "I_difference_values": sorted({state[3] for _, state in seen}),
            "inventory_sha256": hashlib.sha256(raw).hexdigest(),
            "status": "PASS_EXHAUSTIVE_REACHABLE_CLOSURE"}


def direct_rewrites(s):
    out = {s}
    for pos in range(len(s)):
        for width in (2, 3):
            if pos+width <= len(s) and len(set(s[pos:pos+width])) == 1:
                replacement = "" if width == 2 else str(1-int(s[pos]))
                out.add(s[:pos]+replacement+s[pos+width:])
    return out


def sanity():
    # Compare streaming rewrites with literal string replacement, and streaming
    # tilings with a runwise recursive cover, on every binary word of length<=9.
    rewrite_cases = tiling_cases = 0
    def run_tilings(s, offset, p):
        if not s:
            return {""}
        if s[0] == '0':
            return run_tilings(s[1:], offset+1, p)
        j = s.find('0')
        if j < 0:
            j = len(s)
        # Unique even-run domino cover; every even-offset monomer for odd run.
        options = set()
        if j % 2 == 0:
            options.add(''.join(str((p+offset+i)%2) for i in range(0,j,2)))
        else:
            for mon in range(0,j,2):
                out = ''.join(str((p+offset+i)%2) for i in range(0,mon,2))
                out += str(1-(p+offset+mon)%2)*2
                out += ''.join(str((p+offset+i)%2) for i in range(mon+1,j,2))
                options.add(out)
        return {a+b for a in options for b in run_tilings(s[j:], offset+j, p)}
    for length in range(10):
        for chars in product('01', repeat=length):
            s = ''.join(chars)
            actual = {out for a,b,out in through_two(READY, READY, s)
                      if a[0] != 1 and b[0] != 1}
            expected = {z for t in direct_rewrites(s) for z in direct_rewrites(t)}
            assert actual == expected
            rewrite_cases += 1
            for colour in (0,1):
                paths = {((False,False), '')}
                for i, ch in enumerate(s):
                    paths = {(q, out+e) for st,out in paths
                             for q,e in cover(st, int(ch), (i+colour)%2)}
                actual = {out for st,out in paths if not st[1]}
                assert actual == run_tilings(s, 0, colour)
                tiling_cases += 1
    return {"literal_rewrite_cases": rewrite_cases, "runwise_tiling_cases": tiling_cases}


if __name__ == '__main__':
    result = {"proof_computation": [closure(0), closure(1)], "finite_sanity_controls": sanity(),
              "scope": "Universal local B-pattern inclusion, every minimum target tiling; no length, queue or I-difference bound is imposed."}
    Path(__file__).with_name('INDEPENDENT-LOCAL-INCLUSION-RECEIPT.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
