"""G6 source-epoch reference backend: exact rational finite Poisson prefixes.

Contributor: GPT-6 Astra Pro, 2026-10-07.
This is NOT the G6 graph catalogue, positive-chain compressor or Lean verifier.
It evaluates a concrete source uniformization step on entire labelled forests.
The bound agrees with UniformizedSourceStep.globalRateBound. All coefficients
are fractions; leftover mass is kept explicitly at the unchanged input state.
See PROOF.md for the tail enclosure and whole-law error argument.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations, product
from typing import Callable, Hashable, Mapping, TypeVar

T = TypeVar("T", bound=Hashable)


def rational(x: int | str | Q) -> Q:
    """Reject floating-point inputs rather than silently invent exact data."""
    if isinstance(x, bool) or not isinstance(x, (int, str, Q)):
        raise TypeError("Use an integer, rational string or Fraction, not a float.")
    return Q(x)


@dataclass(frozen=True)
class PrefixCertificate:
    mean: Q
    tolerance: Q
    degree: int
    terms: tuple[Q, ...]
    upper_exp: Q

    @property
    def partial(self) -> Q:
        return sum(self.terms, Q(0))

    @property
    def next_term(self) -> Q:
        return self.terms[-1] * self.mean / (self.degree + 1)

    @property
    def lower_exp_minus(self) -> Q:
        return 1 / self.upper_exp

    @property
    def retained(self) -> tuple[Q, ...]:
        return tuple(x / self.upper_exp for x in self.terms)

    @property
    def deficit(self) -> Q:
        return 1 - self.partial / self.upper_exp

    @property
    def weights(self) -> tuple[Q, ...]:
        """A normalized finite COUNT law, with residual mass assigned to zero."""
        w = list(self.retained)
        w[0] += self.deficit
        return tuple(w)

    def validate(self) -> None:
        """Check every finite rational certificate premise, not exp numerics."""
        if self.mean < 0 or not 0 < self.tolerance < 1 or self.degree < 0:
            raise ValueError("Invalid mean, tolerance or degree.")
        if len(self.terms) != self.degree + 1 or self.terms[0] != 1:
            raise ValueError("Invalid Taylor prefix.")
        for k in range(self.degree):
            if self.terms[k + 1] != self.terms[k] * self.mean / (k + 1):
                raise ValueError("Taylor recurrence does not match.")
        if self.degree + 2 < 2 * self.mean:
            raise ValueError("The geometric tail ratio has not been certified.")
        if self.upper_exp != self.partial + 2 * self.next_term:
            raise ValueError("The exponential upper endpoint is not the certified one.")
        if not 0 <= self.deficit <= self.tolerance:
            raise ValueError("The certified missing mass exceeds the tolerance.")
        if min(self.weights) < 0 or sum(self.weights, Q(0)) != 1:
            raise ValueError("The output count law is not normalized and nonnegative.")


def poisson_prefix(mean: int | str | Q, tolerance: int | str | Q,
                   *, max_degree: int | None = None) -> PrefixCertificate:
    """Return a finite rational law within `deficit` TV of Poisson(mean).

    The mathematical procedure has no degree bound. An optional resource bound
    raises an exception; it is NEVER a no-source or no-candidate conclusion.
    """
    a, eps = rational(mean), rational(tolerance)
    if a < 0 or not 0 < eps < 1:
        raise ValueError("Require mean >= 0 and 0 < tolerance < 1.")
    if max_degree is not None and (isinstance(max_degree, bool)
                                  or not isinstance(max_degree, int) or max_degree < 0):
        raise ValueError("max_degree must be a nonnegative integer or None.")
    terms, total, m = [Q(1)], Q(1), 0
    while True:
        nxt = terms[-1] * a / (m + 1)
        upper = total + 2 * nxt
        if m + 2 >= 2 * a and 2 * nxt / upper <= eps:
            out = PrefixCertificate(a, eps, m, tuple(terms), upper)
            out.validate()
            return out
        if max_degree is not None and m >= max_degree:
            raise RuntimeError("RESOURCE_LIMIT: no mathematical exclusion is licensed.")
        terms.append(nxt)
        total += nxt
        m += 1


@dataclass(frozen=True)
class Leaf:
    label: str


@dataclass(frozen=True)
class Join:
    bin_tag: int
    left: Tree
    right: Tree


Tree = Leaf | Join


def tree_key(t: Tree) -> str:
    return repr(t)


def graft(a: Tree, b: Tree, bin_tag: int) -> Join:
    left, right = sorted((a, b), key=tree_key)
    return Join(bin_tag, left, right)


def leaves(t: Tree) -> frozenset[str]:
    if isinstance(t, Leaf):
        return frozenset((t.label,))
    return leaves(t.left) | leaves(t.right)


def contains(t: Tree, old: Tree) -> bool:
    return t == old or (isinstance(t, Join) and
                       (contains(t.left, old) or contains(t.right, old)))


@dataclass(frozen=True)
class SourceState:
    """Entire forest per original physical population, plus original registers."""
    populations: tuple[tuple[str, tuple[Tree, ...]], ...]
    registers: tuple[tuple[str, bool], ...] = ()

    @staticmethod
    def make(populations: Mapping[str, tuple[Tree, ...] | list[Tree]],
             registers: Mapping[str, bool] | None = None) -> SourceState:
        return SourceState(tuple(sorted((p, tuple(sorted(ts, key=tree_key)))
                                        for p, ts in populations.items() if ts)),
                           tuple(sorted((registers or {}).items())))

    def validate(self) -> None:
        if len(dict(self.populations)) != len(self.populations):
            raise ValueError("Duplicate original population ID.")
        if len(dict(self.registers)) != len(self.registers):
            raise ValueError("Duplicate original register ID.")
        seen: set[str] = set()
        for _, trees in self.populations:
            for t in trees:
                ls = leaves(t)
                if not ls or seen.intersection(ls):
                    raise ValueError("Source live forests must have disjoint labelled leaves.")
                def count(x: Tree) -> int:
                    return 1 if isinstance(x, Leaf) else count(x.left) + count(x.right)
                if count(t) != len(ls):
                    raise ValueError("A labelled leaf is duplicated inside a subtree.")
                seen.update(ls)


@dataclass(frozen=True)
class SourceParameters:
    """ONE immutable bank of original constant population rates for all epochs."""
    rates: tuple[tuple[str, Q], ...]
    copy_cap: int

    def __post_init__(self) -> None:
        if isinstance(self.copy_cap, bool) or not isinstance(self.copy_cap, int) or self.copy_cap < 1:
            raise ValueError("The copy cap must be positive.")
        if len(dict(self.rates)) != len(self.rates) or not self.rates:
            raise ValueError("Rates need unique physical IDs and an ancestral population.")
        if any(not isinstance(x, Q) or x <= 0 for _, x in self.rates):
            raise ValueError("Every physical rate must be an exact positive Fraction.")

    @property
    def global_bound(self) -> Q:
        # Exactly the conservative existing Lean bound, not a fitted row rate.
        return (1 + sum((v for _, v in self.rates), Q(0))) * (1 + self.copy_cap ** 2)


def source_step(parameters: SourceParameters, state: SourceState,
                bin_tag: int) -> dict[SourceState, Q]:
    """Actual current-root Kingman pair step plus its required holding mass.

    Unordered pairs use the full pair rate. This is the unranked quotient of
    the Lean provider's two ordered orientations with half rate each.
    """
    state.validate()
    if isinstance(bin_tag, bool) or not isinstance(bin_tag, int) or bin_tag < 0:
        raise ValueError("A bin tag must be a nonnegative integer.")
    rates, out = dict(parameters.rates), defaultdict(Q)
    all_leaves = set().union(*(leaves(t) for _, ts in state.populations for t in ts))
    if len(all_leaves) > parameters.copy_cap:
        raise ValueError("The actual copy carrier exceeds the declared finite cap.")
    jump_mass = Q(0)
    for p, ts in state.populations:
        if p not in rates:
            raise ValueError("Unknown original physical population ID.")
        for i, j in combinations(range(len(ts)), 2):
            pops = dict(state.populations)
            pops[p] = tuple(t for k, t in enumerate(ts) if k not in (i, j)) + \
                      (graft(ts[i], ts[j], bin_tag),)
            dest = SourceState.make(pops, dict(state.registers))
            mass = rates[p] / parameters.global_bound
            out[dest] += mass
            jump_mass += mass
    if not 0 <= jump_mass <= 1:
        raise AssertionError("The source-derived global rate bound failed.")
    out[state] += 1 - jump_mass
    return {s: w for s, w in out.items() if w}


def bind(law: Mapping[T, Q], kernel: Callable[[T], Mapping[T, Q]]) -> dict[T, Q]:
    out: defaultdict[T, Q] = defaultdict(Q)
    for s, mass in law.items():
        for d, prob in kernel(s).items():
            out[d] += mass * prob
    return {s: w for s, w in out.items() if w}


def source_epoch(parameters: SourceParameters, initial: SourceState,
                 duration: int | str | Q, bin_tag: int,
                 tolerance: int | str | Q) -> tuple[dict[SourceState, Q], PrefixCertificate]:
    """Compute the finite lower-prefix law, never silently discard its tail."""
    dt = rational(duration)
    if dt < 0:
        raise ValueError("A source epoch duration must be nonnegative.")
    initial.validate()
    cert = poisson_prefix(parameters.global_bound * dt, tolerance)
    current, out = {initial: Q(1)}, defaultdict(Q)
    cache: dict[SourceState, dict[SourceState, Q]] = {}
    def step(s: SourceState) -> dict[SourceState, Q]:
        if s not in cache:
            cache[s] = source_step(parameters, s, bin_tag)
        return cache[s]
    # Force ID/copy validation even when the certified mean is zero.
    step(initial)
    for k, weight in enumerate(cert.weights):
        for s, mass in current.items():
            out[s] += weight * mass
        if k < cert.degree:
            current = bind(current, step)
    result = {s: w for s, w in out.items() if w}
    if any(w < 0 for w in result.values()) or sum(result.values(), Q(0)) != 1:
        raise AssertionError("The full forest output law lost probability mass.")
    return result, cert


def hybrid_boundary(state: SourceState, *, child: str, parent0: str, parent1: str,
                    original_id: str, gamma: Q, common: bool) -> dict[SourceState, Q]:
    """Reference natural source pulse: CURRENT roots, or the retained register.

    IDs must come from an admitted source's actual child/parent incidence. This
    primitive does not itself prove graph admission or calendar compatibility.
    """
    if not isinstance(gamma, Q) or not 0 < gamma < 1:
        raise ValueError("Natural inheritance must be an exact interior rational.")
    if len({child, parent0, parent1}) != 3:
        raise ValueError("Distinct original edge IDs are required, including parallel arms.")
    state.validate()
    roots = dict(state.populations).get(child, ())
    registers = dict(state.registers)
    if common and original_id not in registers:
        raise ValueError("The COMMON original register must already have been drawn.")
    choices = [(tuple(registers[original_id] for _ in roots), Q(1))] if common else [
        (bits, gamma ** bits.count(False) * (1 - gamma) ** bits.count(True))
        for bits in product((False, True), repeat=len(roots))]
    out: defaultdict[SourceState, Q] = defaultdict(Q)
    for bits, mass in choices:
        pops = {p: list(ts) for p, ts in state.populations if p != child}
        for t, b in zip(roots, bits):
            pops.setdefault(parent1 if b else parent0, []).append(t)
        out[SourceState.make(pops, registers)] += mass
    return dict(out)


def project(t: Tree, keep: frozenset[str]) -> Tree | None:
    if isinstance(t, Leaf):
        return t if t.label in keep else None
    a, b = project(t.left, keep), project(t.right, keep)
    if a is None:
        return b
    if b is None:
        return a
    return graft(a, b, t.bin_tag)


def joint_readout(law: Mapping[SourceState, Q], panels: tuple[frozenset[str], ...]
                  ) -> dict[tuple[tuple[Tree, ...], ...], Q]:
    """Push ONE locus law to a JOINT record; never multiply panel marginals."""
    out: defaultdict[tuple[tuple[Tree, ...], ...], Q] = defaultdict(Q)
    for s, mass in law.items():
        record = []
        for keep in panels:
            trees = [u for _, ts in s.populations for t in ts
                     if (u := project(t, keep)) is not None]
            record.append(tuple(sorted(trees, key=tree_key)))
        out[tuple(record)] += mass
    return dict(out)


def tv(p: Mapping[T, Q], q: Mapping[T, Q]) -> Q:
    return sum((abs(p.get(k, Q(0)) - q.get(k, Q(0))) for k in p.keys() | q.keys()), Q(0)) / 2
