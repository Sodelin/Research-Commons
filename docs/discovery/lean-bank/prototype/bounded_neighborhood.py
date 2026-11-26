"""Bounded traversal of already acquired declaration metadata; no I/O."""
from heapq import heappop, heappush
from itertools import islice


def neighborhood(seed, goals, neighbors, *, depth=2, pulls=4, fanout=8, excluded=()):
    """Seed is pinned. Neighbors is a bounded, relevance-ranked metadata feed.

    Relevance is an explicit per-edge gain, not a similarity score inherited
    from the seed. Coverage is *routing metadata*, not a checked proof.
    """
    goals = frozenset(goals)
    actions, declined, pending, visited, expanded = [], [], [], {seed}, set()
    remaining = set(goals)
    excluded = frozenset(excluded)
    scans = 0
    depth_frontier = set()

    def expand(parent, level):
        nonlocal scans
        if level >= depth:
            depth_frontier.add(parent)
            return
        if parent in expanded:
            return
        expanded.add(parent)
        for row in islice(neighbors(parent), fanout):
            scans += 1
            ident, relation, hits = row
            useful = remaining.intersection(hits)
            if ident in excluded:
                declined.append((ident, "excluded_after_failed_check"))
                continue
            if relation not in ("uses", "used_by", "generalizes", "analogue", "same_module"):
                declined.append((ident, "unrecognized_edge"))
                continue
            if not useful:
                declined.append((ident, "no_current_goal_gain"))
                continue
            heappush(pending, (-len(useful), level + 1, ident, relation, tuple(sorted(useful))))

    expand(seed, 0)
    while pending and len(actions) < pulls and remaining:
        neg_gain, level, ident, relation, prior = heappop(pending)
        if ident in visited:
            continue
        gain = tuple(sorted(remaining.intersection(prior)))
        if not gain:
            declined.append((ident, "goal_already_covered"))
            continue
        if len(gain) != -neg_gain:
            heappush(pending, (-len(gain), level, ident, relation, gain))
            continue
        visited.add(ident)
        actions.append({"id": ident, "depth": level, "relation": relation, "covers_hints": gain})
        remaining.difference_update(gain)
        if remaining and len(actions) < pulls:
            expand(ident, level)

    stop = "no_new_relevant_edges"
    if not remaining:
        stop = "all_requested_goals_have_candidates"
    elif len(actions) >= pulls:
        stop = "candidate_budget"
    elif depth_frontier:
        stop = "depth_budget"
    return {"disposition": "metadata_only", "actions": actions, "declined": declined,
            "uncovered": sorted(remaining), "edges_examined": scans, "stop": stop,
            "depth_frontier": sorted(depth_frontier)}
