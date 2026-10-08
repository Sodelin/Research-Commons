"""Exact fixed-rational-calendar rate/inheritance witness gate.
No graph admission, law evaluation, net completeness or original-real-source restriction.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Optional


def rat(x):
    if not isinstance(x, (str, int)) or isinstance(x, bool):
        raise ValueError("expected exact rational string/integer, no float or Bool")
    return Q(x)


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Optional[Q]
    lc: bool = True
    hc: bool = True

    def contains(self, x):
        return (x > self.lo or (self.lc and x == self.lo)) and (self.hi is None or x < self.hi or (self.hc and x == self.hi))

    def meet(self, b):
        lo = max(self.lo, b.lo)
        lc = (self.lc if lo == self.lo else True) and (b.lc if lo == b.lo else True)
        if self.hi is None:
            hi, hc = b.hi, b.hc
        elif b.hi is None:
            hi, hc = self.hi, self.hc
        else:
            hi = min(self.hi, b.hi)
            hc = (self.hc if hi == self.hi else True) and (b.hc if hi == b.hi else True)
        return Interval(lo, hi, lc, hc)

    def empty(self):
        return self.hi is not None and (self.lo > self.hi or (self.lo == self.hi and not (self.lc and self.hc)))

    def witness(self):
        if self.empty():
            raise ValueError("empty interval")
        if self.hi is None:
            return self.lo + 1
        if self.lo == self.hi:
            return self.lo
        return (self.lo + self.hi) / 2

    def divided(self, d):
        if d <= 0:
            raise ValueError("positive exposure required")
        return Interval(self.lo / d, None if self.hi is None else self.hi / d, self.lc, self.hc)


def cell(a):
    if set(a) != {"lo", "hi", "lo_closed", "hi_closed"}:
        raise ValueError("unexpected/missing interval field")
    if type(a["lo_closed"]) is not bool or type(a["hi_closed"]) is not bool:
        raise ValueError("interval endpoint flags must be literal Bool")
    c = Interval(rat(a["lo"]), None if a["hi"] is None else rat(a["hi"]), a["lo_closed"], a["hi_closed"])
    if c.lo < 0 or c.empty():
        raise ValueError("negative or empty supplied cell")
    return c


def exposures(doc):
    # This parser validates a physical chart, not RootedBinary/LSA/CutChild.
    ages = {v: rat(t) for v, t in doc["ages"].items()}
    if not ages or any(t < 0 for t in ages.values()):
        raise ValueError("finite nonnegative vertex dates required")
    root = doc["root"]
    if root not in ages:
        raise ValueError("missing root date")
    edges = doc["edges"]
    if "ANCESTRAL" in edges:
        raise ValueError("ANCESTRAL is reserved separate root population")
    for e, ends in edges.items():
        if not isinstance(e, str) or len(ends) != 2 or any(v not in ages for v in ends):
            raise ValueError("literal edge occurrence/endpoints required")
        if not ages[ends[1]] < ages[ends[0]]:
            raise ValueError("each original edge needs strictly older parent")
    rows = doc["profiles"]
    if not rows or len({r["id"] for r in rows}) != len(rows):
        raise ValueError("nonempty distinct literal profiles required")
    out = {}
    for row in rows:
        cuts = [rat(x) for x in row["cuts"]]
        if cuts != sorted(set(cuts)) or any(x < 0 for x in cuts):
            raise ValueError("strictly sorted nonnegative rational cuts required")
        points = sorted(set(ages.values()) | set(cuts))
        for a, b in zip(points, points[1:]):
            for e, (parent, child) in edges.items():
                if ages[child] <= a and b <= ages[parent]:
                    out[(row["id"], e, str(a), str(b))] = b-a
            if ages[root] <= a:
                out[(row["id"], "ANCESTRAL", str(a), str(b))] = b-a
    return out


def keyed_cells(doc, ex):
    out = {}
    for c in doc["hazard_cells"]:
        key = (c["profile"], c["population"], str(rat(c["young"])), str(rat(c["old"])))
        if key in out:
            raise ValueError("duplicate hazard occurrence")
        out[key] = cell(c["cell"])
    if set(out) != set(ex):
        raise ValueError("cells must cover EXACTLY every active original finite epoch")
    return out


def inheritance_intervals(doc):
    hybrids = doc["hybrids"]
    if len(hybrids) != len(set(hybrids)) or any(h not in doc["ages"] for h in hybrids):
        raise ValueError("distinct literal original hybrid IDs required")
    out = {}
    wanted = {(r["id"], h) for r in doc["profiles"] for h in hybrids}
    for c in doc["inheritance_cells"]:
        key = (c["profile"], c["hybrid"])
        if key not in wanted or key in out:
            raise ValueError("unexpected/duplicate hybrid profile cell")
        out[key] = cell(c["cell"])
    if set(out) != wanted:
        raise ValueError("cells must cover every original hybrid in every profile")
    return out


def solve(doc):
    ex = exposures(doc)
    cs = keyed_cells(doc, ex)
    rates = {e: Interval(Q(0), None, False) for e in [*doc["edges"], "ANCESTRAL"]}
    for key, duration in ex.items():
        rates[key[1]] = rates[key[1]].meet(cs[key].divided(duration))
    inheritance = inheritance_intervals(doc)
    gs = {h: Interval(Q(0), Q(1), False, False) for h in doc["hybrids"]}
    for (_, h), c in inheritance.items():
        gs[h] = gs[h].meet(c)
    failures = ["rate:"+e for e, c in rates.items() if c.empty()] + ["gamma:"+h for h, c in gs.items() if c.empty()]
    if failures:
        return {"status": "INFEASIBLE_FIXED_CHART", "conflicts": failures, "target_exclusion_authorized": False}
    bank = {"rates": {e: str(c.witness()) for e, c in rates.items()}, "gamma_native": {h: str(c.witness()) for h, c in gs.items()}}
    replay(doc, bank)
    return {"status": "FIXED_CHART_BANK_FEASIBLE", "bank": bank, "source_admission_established": False, "law_evaluated": False, "target_exclusion_authorized": False}


def replay(doc, bank):
    # Independent certificate consumer checks literal primitive products directly.
    ex = exposures(doc)
    cs = keyed_cells(doc, ex)
    inheritance = inheritance_intervals(doc)
    if set(bank["rates"]) != {*doc["edges"], "ANCESTRAL"} or set(bank["gamma_native"]) != set(doc["hybrids"]):
        raise ValueError("bank changed/missing original occurrence IDs")
    rates = {e: rat(r) for e, r in bank["rates"].items()}
    gs = {h: rat(g) for h, g in bank["gamma_native"].items()}
    if any(r <= 0 for r in rates.values()) or any(not 0 < g < 1 for g in gs.values()):
        raise ValueError("nonpositive rate or boundary inheritance")
    for key, duration in ex.items():
        if not cs[key].contains(rates[key[1]]*duration):
            raise ValueError("shared source rate violates hazard cell")
    for (_, h), c in inheritance.items():
        if not c.contains(gs[h]):
            raise ValueError("shared original gamma violates row cell")
    return True
