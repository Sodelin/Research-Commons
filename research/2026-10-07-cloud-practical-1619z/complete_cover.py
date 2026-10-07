"""Checked original-domain outer cover after one actual branch exclusion."""
from fractions import Fraction as Q
from itertools import product
import hashlib

import joint_betting as jb
import tight_rounded_betting as receiver
from source_bridge import DOMAIN, PHYSICAL

SPLIT = ('h', 'u', 'v', 'rR')
REMOVED_SIGNATURE = (0, 0, 0, 1)


def normalize_box(record):
    if not isinstance(record, dict) or set(record) != set(PHYSICAL):
        raise jb.Invalid('original nine physical coordinates required')
    result = {}
    for key in PHYSICAL:
        pair = record[key]
        if not isinstance(pair, list) or len(pair) != 2:
            raise jb.Invalid('two physical endpoints required')
        a, b = map(jb.rational, pair)
        left, right = map(jb.rational, DOMAIN[key])
        if not left <= a <= b <= right:
            raise jb.Invalid('physical box outside original domain')
        result[key] = [str(a), str(b)]
    return result


def partition(excluded_box):
    """Only the explicit lower-clock/upper-root-rate branch is admitted here."""
    removed = normalize_box(excluded_box)
    axes = {}
    for key in PHYSICAL:
        a, b = map(Q, removed[key])
        left, right = map(Q, DOMAIN[key])
        if key in ('h', 'u', 'v'):
            if a != left or not a < b < right:
                raise jb.Invalid('lower-clock positive branch required')
            axes[key] = ([str(left), str(b)], [str(b), str(right)])
        elif key == 'rR':
            if b != right or not left < a < b:
                raise jb.Invalid('upper-root-rate positive branch required')
            axes[key] = ([str(left), str(a)], [str(a), str(right)])
        elif removed[key] != DOMAIN[key]:
            raise jb.Invalid('all unsplit original ranges must remain complete')
    cells = []
    for signature in product((0, 1), repeat=4):
        box = {key: list(pair) for key, pair in DOMAIN.items()}
        for key, bit in zip(SPLIT, signature):
            box[key] = list(axes[key][bit])
        cells.append({'signature': list(signature), 'physical_box': normalize_box(box)})
    exact_removed = [cell for cell in cells if tuple(cell['signature']) == REMOVED_SIGNATURE]
    if len(cells) != 16 or len(exact_removed) != 1 or exact_removed[0]['physical_box'] != removed:
        raise jb.Invalid('removed cell/partition correspondence failed')
    return cells


def union_widths(cells):
    if not cells:
        raise jb.Invalid('empty cover is not a source witness')
    result = {}
    for key in PHYSICAL:
        low = min(Q(cell['physical_box'][key][0]) for cell in cells)
        high = max(Q(cell['physical_box'][key][1]) for cell in cells)
        left, right = map(Q, DOMAIN[key])
        result[key] = str((high - low) / (right - left))
    return result


def build(rows, excluded_box, plan, bridge, delta='1/10', precision_bits=96, max_bits=16384):
    """Recompute original forward/data evidence, never trust a PASS JSON input."""
    removed = normalize_box(excluded_box)
    means = bridge.enclose(removed)
    evidence = receiver.replay(rows, means, plan, delta, precision_bits, max_bits)
    if evidence['status'] == 'CONDITIONAL_MEAN_BOX_EXCLUDED':
        all_cells = partition(removed)
        retained = [cell for cell in all_cells if tuple(cell['signature']) != REMOVED_SIGNATURE]
        removal = True
    else:
        retained = [{'signature': None, 'physical_box': {key: list(pair) for key, pair in DOMAIN.items()}}]
        removal = False
    widths = union_widths(retained)
    met = all(Q(value) <= Q(1, 20) for value in widths.values())
    return {'schema': 'original-domain-checked-conditional-cover-v1',
            'model': jb.MODEL, 'observation_map': jb.MAP,
            'original_domain': DOMAIN,
            'attempted_removed_box': removed,
            'attempted_removed_box_sha256': hashlib.sha256(jb.canonical(removed)).hexdigest(),
            'forward_shifted_mean_enclosure': means,
            'recomputed_exclusion_evidence': evidence,
            'candidate_cell_removed': removal,
            'retained_cover': retained, 'retained_cell_count': len(retained),
            'whole_union_normalized_widths': widths,
            'original_normalized_width_targets': {key: '1/20' for key in PHYSICAL},
            'whole_union_width_goal_met': met,
            'status': 'CONDITIONAL_WIDTH_GOAL_MET' if met else 'UNKNOWN',
            'coverage_scope': 'complete outer cover of the original source set retained by the SAME conditional joint process',
            'closed_shared_boundaries_may_retain_excluded_points': True,
            'historical_plan_predeclaration_established': False,
            'finite_rng_certified': False,
            'scientific_admission_verified': False,
            'data_confidence_certificate_issued': False,
            'source_witness_certified': False,
            'old_numerical_inverse_journal_validated': False,
            'lean_kernel_checked': False}
