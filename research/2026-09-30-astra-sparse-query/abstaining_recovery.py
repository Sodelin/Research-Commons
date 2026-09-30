"""Conservative confidence-set adapter for exact circular-split recovery.

The confidence-set provider is external. This module does not manufacture a
biological classifier, a coverage guarantee, or a correct circular order.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Iterable, Literal
from sparse_quartet import Quartet, Recovery, recover

ConfidenceOracle = Callable[[Quartet], Iterable[int]]
ADMITTED_MASKS = frozenset({1, 4, 5})


@dataclass(frozen=True)
class AbstainingRecovery:
    status: Literal['complete', 'inconclusive']
    recovery: Recovery | None
    oracle_calls: int
    unresolved_quartet: Quartet | None = None
    candidate_masks: frozenset[int] | None = None
    reason: str | None = None


class _Abstain(Exception):
    def __init__(self, quartet: Quartet, masks: frozenset[int]):
        super().__init__('Complete quartet support is not uniquely determined')
        self.quartet = quartet
        self.masks = masks


def recover_with_abstention(n: int, confidence_oracle: ConfidenceOracle) -> AbstainingRecovery:
    """Return a complete answer only if every requested support is a singleton.

    The masks 1,4,5 are complete nonempty noncrossing quartet-support answers,
    not individual quartet topologies. An empty confidence SET means no retained
    admissible answer; it does not mean the quartet has empty displayed support.
    An ambiguous or empty set halts with no claimed split output. Malformed
    values raise ValueError. This is conservative, not a maximal partial solver.
    """
    calls = 0

    def answer(quartet: Quartet) -> int:
        nonlocal calls
        calls += 1
        raw = tuple(confidence_oracle(quartet))
        if any(not isinstance(x, int) or isinstance(x, bool) or x not in ADMITTED_MASKS
               for x in raw):
            raise ValueError('Confidence candidates must be complete support masks 1, 4 or 5')
        masks = frozenset(raw)
        if len(masks) != 1:
            raise _Abstain(quartet, masks)
        return next(iter(masks))

    try:
        result = recover(n, answer)
    except _Abstain as exc:
        return AbstainingRecovery('inconclusive', None, calls, exc.quartet, exc.masks,
                                 'empty confidence set' if not exc.masks else 'ambiguous support')
    return AbstainingRecovery('complete', result, calls)
