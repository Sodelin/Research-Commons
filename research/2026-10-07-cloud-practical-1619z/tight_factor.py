"""Exact clipped-quadratic extrema for the SAME predictable betting factor."""
from fractions import Fraction as Q
import joint_betting as jb


def factor(projected_value, projected_box, total, squares, n):
    if not n:
        return jb.Interval.point(1)
    average = total / n
    variance = squares / n - average * average
    if variance < 0:
        raise jb.Invalid('negative exact empirical variance')
    denominator = variance + Q(1, 16)
    left, right = projected_box.lo, projected_box.hi
    if max(abs(projected_value - left), abs(projected_value - right)) > 1:
        raise jb.Invalid('projected centered increment outside original l1 bound')
    # Breaks between constant +/-1/2 stakes and the unclipped affine stake.
    first_break = average - denominator / 2
    second_break = average + denominator / 2
    candidates = {left, right}
    for point in (first_break, second_break):
        if left <= point <= right:
            candidates.add(point)
    # On the unclipped interval the factor is a convex quadratic, whose only
    # interior stationary point is (average+current projected value)/2.
    vertex = (average + projected_value) / 2
    if max(left, first_break) <= vertex <= min(right, second_break):
        candidates.add(vertex)
    values = [1 + jb.clip((average - point) / denominator) * (projected_value - point)
              for point in candidates]
    result = jb.Interval(min(values), max(values))
    if result.lo < Q(1, 2) or result.hi > Q(3, 2):
        raise jb.Invalid('tight factor violates proved universal range')
    return result
