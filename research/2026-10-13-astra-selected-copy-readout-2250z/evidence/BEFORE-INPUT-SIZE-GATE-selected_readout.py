#!/usr/bin/env python3
"""Exact selected-copy RC1 readout; physical/source decisions remain UNKNOWN.

This adapter serializes an explicitly indexed source, then delegates parsing,
forward compilation and request-bound replay to the existing pinned executable.
It extracts only replay-checked rooted TABLE records. It does not decode graphs,
prove native refinement, refit a calendar, or compute the full padded table.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / '2026-10-13-astra-unified-solver-0645z'
PINS = {
    'certificates.py': 'ce6ba92566e5ee009ca565476744db65555160f0e4a7d32b70ee07505b57f0b3',
    'external_encoding.py': '78dfd11a8157a5102c520be85a5fc42f4b4137250846ce510df9df98a90f4d69',
    'native_bridge.py': 'b298ae551bc488aab45560434a5f9dc2bead15a4c0b0328199577e63ac808f39',
}
MAX_RESPONSE = 1024 * 1024
MAX_TERMS = 16384
MAX_POWER = 64
MAX_BITS = 4096
MAX_OPERATIONS = 500000
MAX_ROWS = 192
NAT = re.compile(r'(?:0|[1-9][0-9]*)\Z', re.ASCII)


class Unknown(ValueError):
    """Supported computation or authentication is unavailable, never NO."""


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def providers():
    for name, pin in PINS.items():
        try:
            raw = (BASE / name).read_bytes()
        except OSError as error:
            raise Unknown('selected provider unavailable: ' + name) from error
        if sha(raw) != pin:
            raise Unknown('selected Python provider identity changed: ' + name)
    sys.path.insert(0, str(BASE))
    try:
        modules = [importlib.import_module(name[:-3]) for name in PINS]
    finally:
        sys.path.pop(0)
    for module, (name, pin) in zip(modules, PINS.items()):
        if Path(module.__file__).resolve() != (BASE / name).resolve():
            raise Unknown('loaded provider origin differs')
        if sha((BASE / name).read_bytes()) != pin:
            raise Unknown('provider changed during load')
    return modules


def natural(value, maximum, label, c):
    c.require(type(value) is int and 0 <= value <= maximum, label + ' index bound')
    return value


def source_binding(source, menu, c):
    """Check explicit enumerations and occurrence maps, not physical admission."""
    c.fields(source, ['vertices', 'root', 'edges', 'taxa', 'hybrids',
                      'protected_edges', 'protected_hybrids', 'physical_context'])
    c.fields(source['physical_context'], ['calendar', 'pair_rates', 'ancestral_pair_rate', 'provenance'])
    # Context is preserved literally and hashed, not interpreted as proof. The
    # formal assignment below does not authenticate exp(-rate * duration).
    c.require(len(json.dumps(source['physical_context'])) <= 32768, 'physical context size')
    vs, es, ts, hs = (source[k] for k in ['vertices', 'edges', 'taxa', 'hybrids'])
    for rows in [vs, es, ts, hs]:
        c.require(type(rows) is list and len(rows) <= 32, 'source enumeration bound')
    c.require(len(vs) >= 3 and len(es) >= 2 and len(ts) == len(menu['taxa']), 'source dimensions')
    if len(vs) + len(es) + 1 + len(hs) > 32:
        raise Unknown('existing native source dimension profile exceeded')
    specs = [(vs, ['index', 'id']), (es, ['index', 'id', 'source', 'target', 'survival']),
             (ts, ['index', 'id', 'vertex']),
             (hs, ['index', 'id', 'vertex', 'incoming', 'original_parent_1_probability',
                   'native_parent_0_probability'])]
    for rows, keys in specs:
        for i, row in enumerate(rows):
            c.fields(row, keys)
            c.require(type(row['index']) is int and row['index'] == i, 'explicit index/order disagreement')
        c.identifiers([row['id'] for row in rows], 'typed original IDs')
    natural(source['root'], len(vs) - 1, 'root', c)
    c.require(set(x['id'] for x in ts) == set(menu['taxa']), 'complete external taxon bijection required')
    c.require(len(set(x['vertex'] for x in ts)) == len(ts), 'leaf embedding must be injective')
    for row in ts:
        natural(row['vertex'], len(vs) - 1, 'taxon vertex', c)
    values = []
    for edge in es:
        natural(edge['source'], len(vs) - 1, 'edge source', c)
        natural(edge['target'], len(vs) - 1, 'edge target', c)
        x = c.rational(edge['survival'])
        c.require(0 < x <= 1, 'formal survival assignment requires 0 < X <= 1')
        values.append(x)
    for hybrid in hs:
        vertex = natural(hybrid['vertex'], len(vs) - 1, 'hybrid vertex', c)
        incoming = hybrid['incoming']
        c.require(type(incoming) is list and len(incoming) == 2, 'two original parent occurrences required')
        for edge in incoming:
            natural(edge, len(es) - 1, 'hybrid parent occurrence', c)
        # This is the inherited edge enumeration's original parent order. Never
        # sort or swap a supplied registry to make it fit, even for parallel edges.
        c.require(incoming == [edge['index'] for edge in es if edge['target'] == vertex],
                  'ordered original-parent registry must match occurrence enumeration')
        gamma = c.rational(hybrid['original_parent_1_probability'])
        g = c.rational(hybrid['native_parent_0_probability'])
        c.require(0 < gamma < 1 and 0 < g < 1 and gamma + g == 1,
                  'explicit original Gamma/native G complement required')
        values.append(g)
    c.require(len({h['vertex'] for h in hs}) == len(hs), 'hybrid registry must be injective')
    maps = {}
    for field, labels, rows in [('protected_edges', menu['protected_edges'], es),
                                ('protected_hybrids', menu['protected_hybrids'], hs)]:
        mapping = source[field]
        c.require(type(mapping) is dict and set(mapping) == set(labels), 'complete typed protected map required')
        c.require(all(type(v) is str for v in mapping.values()), 'protected map uses original string IDs')
        c.require(len(set(mapping.values())) == len(mapping), 'protected map must be injective')
        slots = {row['id']: row['index'] for row in rows}
        c.require(all(v in slots for v in mapping.values()), 'unknown protected occurrence')
        maps[field] = {label: slots[value] for label, value in mapping.items()}
    return values, maps


def native_request(source, samples, budgets):
    """Serializer only; the existing native parser validates the graph."""
    v, e, t, h = (source[k] for k in ['vertices', 'edges', 'taxa', 'hybrids'])
    lines = [f'RC1 LAW {len(v)} {len(e)} {len(t)} {len(h)} {len(samples)} '
             f"{budgets['states']} {budgets['terms']} {budgets['histories']}",
             'MECHANISM COMMON', f"ROOT {source['root']}"]
    lines += [f"EDGE {x['index']} {x['source']} {x['target']}" for x in e]
    lines += [f"LEAF {x['index']} {x['vertex']}" for x in t]
    lines += [f"HYBRID {x['index']} {x['vertex']} {x['incoming'][0]} {x['incoming'][1]}" for x in h]
    lines += [f'SAMPLE {i} {taxon}' for i, taxon in enumerate(samples)]
    return '\n'.join(lines) + '\n'


def copy_transport(query, source, c):
    k = query['level']
    c.require(1 <= k <= 3, 'selected transport requires level 1..3')
    taxa = {x['id']: x['index'] for x in source['taxa']}
    keep = ['selected:B'] + [f'selected:A{i}' for i in range(1, k + 1)]
    c.require(query['readout']['keep'] == keep, 'fixed selected event order changed')
    records = []
    for i, label in enumerate(keep):
        tag = ['inl', 'inr', 'unit'] if i == 0 else ['inl', 'inl', i - 1]
        records.append(dict(native_copy_index=i, external_copy_id=label,
                            padded_tag=tag, selected_subtype=dict(value=tag, member_of='paddedKeep'),
                            original_taxon_id=query['allocation'][label],
                            native_leaf_index=taxa[query['allocation'][label]]))
    tree = '0'
    for i in range(1, k + 1):
        tree = f'({tree},{i})'
    # Native canonical children are ordered by least copy index. Our fixed
    # B-first comb has least 0 on every left branch, hence this literal encoding.
    return dict(full_padded_row=query, selected_bijection=records,
                inverse={r['external_copy_id']: r['native_copy_index'] for r in records},
                retained_baselines=[dict(external_copy_id=label, padded_tag=['inr', taxon],
                    original_taxon_id=taxon) for label, taxon in query['allocation'].items()
                    if label.startswith('baseline:')],
                native_rooted_comb=tree, full_padded_forward_table_generated=False,
                internal_selected_copy_computation=True,
                semantic_reduction='accepted same-source pruning/projectivity; native refinement unproved')


class Arithmetic:
    def __init__(self, operations=MAX_OPERATIONS, bits=MAX_BITS):
        self.operations = operations
        self.bits = bits
        self.used = 0

    def check(self, value):
        if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > self.bits:
            raise Unknown('exact rational size budget exhausted')
        return value

    def step(self):
        self.used += 1
        if self.used > self.operations:
            raise Unknown('exact arithmetic operation budget exhausted')

    def add(self, a, b):
        self.step(); self.check(a); self.check(b)
        # Bound temporary products before constructing a rational result.
        if max(abs(a.numerator).bit_length() + b.denominator.bit_length(),
               abs(b.numerator).bit_length() + a.denominator.bit_length(),
               a.denominator.bit_length() + b.denominator.bit_length()) + 1 > 2 * self.bits + 1:
            raise Unknown('exact arithmetic temporary budget exhausted')
        return self.check(a + b)

    def mul(self, a, b):
        self.step(); self.check(a); self.check(b)
        return self.check(a * b)  # two bounded operands: at most 2*bits temporary factors

    def power(self, value, exponent):
        if exponent > MAX_POWER:
            raise Unknown('exact exponent profile exceeded')
        self.check(value)
        result = Fraction(1)
        while exponent:
            if exponent & 1:
                result = self.mul(result, value)
            exponent >>= 1
            if exponent:
                value = self.mul(value, value)
        return result


def table_terms(raw, request, variables, c):
    """Extract the specified bounded wire ONLY after native replay succeeds.

    No graph or genealogy parser: TREE labels remain original canonical strings.
    The native producer and replay checker own their semantics and exact bytes.
    """
    if len(raw) > MAX_RESPONSE:
        raise Unknown('selected TABLE extraction response budget exceeded')
    c.require(type(raw) is bytes and raw.isascii(), 'malformed TABLE encoding')
    prefix = ('RC1 RESULT LAW\nBEGIN_REQUEST\n' + request + 'END_REQUEST\n').encode()
    c.require(raw.startswith(prefix), 'TABLE request identity mismatch')
    lines = raw[len(prefix):].decode('ascii').splitlines()
    c.require(lines[:3] == [f'VARIABLES {len(variables)} ' + ' '.join(variables),
                           'GATE SOURCE_ADMISSION_NOT_ESTABLISHED', 'STATUS TABLE'],
              'TABLE variables, admission gate or status changed')
    pos, work = 3, 0

    def number(token, maximum):
        c.require(type(token) is str and len(token) <= 10 and NAT.fullmatch(token), 'malformed TABLE natural')
        value = int(token)
        if value > maximum:
            raise Unknown('TABLE extraction numeric budget exceeded')
        return value

    def section(tag, record, cap):
        nonlocal pos, work
        c.require(pos < len(lines), 'truncated TABLE section')
        head = lines[pos].split(' '); pos += 1
        c.require(len(head) == 2 and head[0] == tag, 'malformed TABLE section')
        size = number(head[1], cap)
        result = {}
        for _ in range(size):
            c.require(pos < len(lines), 'truncated TABLE row')
            head = lines[pos].split(' '); pos += 1
            c.require(len(head) == 3 and head[0] == record and 0 < len(head[1]) <= 128,
                      'malformed TABLE record')
            c.require(head[1] not in result, 'duplicate TABLE outcome')
            count = number(head[2], MAX_TERMS)
            work += count
            if work > MAX_TERMS:
                raise Unknown('TABLE extraction total term budget exceeded')
            terms, seen = [], set()
            for _ in range(count):
                c.require(pos < len(lines), 'truncated TABLE polynomial')
                fields = lines[pos].split(' '); pos += 1
                c.require(len(fields) == len(variables) + 2 and fields[0] == 'TERM', 'TABLE polynomial dimension')
                c.require(c.GRAMMAR.fullmatch(fields[1]) is not None, 'malformed TABLE coefficient')
                if len(fields[1]) > 80:
                    raise Unknown('native coefficient exceeds selected rational input profile')
                coefficient = Fraction(fields[1])
                if max(abs(coefficient.numerator).bit_length(), coefficient.denominator.bit_length()) > c.MAX_BITS:
                    raise Unknown('native coefficient exceeds selected rational input profile')
                coefficient = c.rational(fields[1])
                c.require(fields[1] == f'{coefficient.numerator}/{coefficient.denominator}' and coefficient != 0,
                          'noncanonical native coefficient')
                powers = tuple(number(x, MAX_POWER) for x in fields[2:])
                c.require(powers not in seen, 'duplicate TABLE monomial')
                seen.add(powers); terms.append((coefficient, powers))
            result[head[1]] = terms
        return result

    rooted = section('ROOTED', 'TREE', 15)
    section('UNROOTED', 'SPLIT', 3)
    c.require(lines[pos:] == ['END'] and raw.endswith(b'\n'), 'TABLE trailing or missing data')
    return rooted


def evaluate(terms, values, arithmetic):
    total = Fraction(0)
    for coefficient, powers in terms:
        term = coefficient
        for value, exponent in zip(values, powers):
            term = arithmetic.mul(term, arithmetic.power(value, exponent))
        total = arithmetic.add(total, term)
    return total


def configuration_readouts(table, event, source, menu, values, maps, c, arithmetic):
    rows = []
    mixture = Fraction(0)
    for cfg in menu['configurations']:
        assignment = list(values)
        forcing = [None] * len(source['hybrids'])
        for label, bit in cfg['mask'].items():
            index = maps['protected_hybrids'][label]
            forcing[index] = bit
            if bit is not None:
                assignment[len(source['edges']) + index] = Fraction(1 - bit)
        weight = c.rational(cfg['weight'])
        # Retain and evaluate every whole configuration, including zero mass.
        # No independent marginal law, renormalization or private-register claim.
        probabilities = {tree: evaluate(terms, assignment, arithmetic) for tree, terms in table.items()}
        c.require(all(0 <= x <= 1 for x in probabilities.values()), 'formal assignment produced non-probability')
        total = Fraction(0)
        for value in probabilities.values():
            total = arithmetic.add(total, value)
        c.require(total == 1, 'complete native rooted table does not have exact unit mass')
        value = probabilities.get(event, Fraction(0))
        weighted = arithmetic.mul(weight, value)
        mixture = arithmetic.add(mixture, weighted)
        rows.append(dict(configuration=cfg, complete_original_mask=forcing,
                         rc1_assignment=list(map(str, assignment)),
                         formal_event_probability=str(value), weighted_probability=str(weighted),
                         rooted_total_mass=str(total)))
    return rows, mixture


def run(raw, output, binary=None, restored=None):
    out = Path(output).resolve(); out.mkdir(parents=True, exist_ok=False)
    result = dict(schema='selected_native_common_readout_result_v1', status='UNKNOWN',
        readout_complete=False, physical_source_decision='UNKNOWN', source_feasibility_certified=False,
        physical_source_admission_verified=False, native_refinement_proved=False,
        typed_mask_forcing_correspondence_proved=False, full_padded_native_table_generated=False,
        arbitrary_input_G3_resolved=False, rows=[])
    try:
        c, encoding, bridge = providers()
        c.require(type(raw) in (bytes, str), 'request must be literal JSON bytes or text')
        (out/'REQUEST.json').write_bytes(raw if isinstance(raw, bytes) else raw.encode())
        request = c.loads(raw)
        c.fields(request, ['schema', 'menu', 'source', 'budgets'])
        c.require(request['schema'] == 'selected_native_common_readout_v1', 'unsupported selected readout schema')
        menu, source, budgets = (request[k] for k in ['menu', 'source', 'budgets'])
        assessment = c.common_packet(menu)
        queries = encoding.fixed_queries(menu)
        values, maps = source_binding(source, menu, c)
        c.fields(budgets, ['states', 'terms', 'histories'])
        for name, maximum in [('states', 4096), ('terms', 65536), ('histories', 4096)]:
            natural(budgets[name], maximum, name, c)
        (out/'FIXED-EXTERNAL-QUERIES.json').write_text(json.dumps(queries, indent=2) + '\n')
        identity = dict(source_sha256=c.digest(source), configuration_sha256=c.digest(menu['configurations']),
                        parameters_sha256=c.digest(dict(values=list(map(str, values)), physical_context=source['physical_context'])),
                        protected_maps_sha256=c.digest(maps))
        result.update(original_input_bytes_sha256=sha(raw if isinstance(raw, bytes) else raw.encode()),
            canonical_request_sha256=c.digest(request), fixed_external_queries_sha256=c.digest(queries),
            same_tuple=identity, original_source=source, original_joint_configurations=menu['configurations'],
            protected_maps=maps, parameter_constraints=menu['parameter_constraints'],
            conditional_arithmetic=assessment, reused_python_sources=PINS,
            trusted_boundary='new bounded checked-TABLE extraction and rational evaluation; native/compiler/OS trusted',
            provider_justification='same-source literal pruning + controlled projectivity, not native-to-typed refinement')
        if any(row['level'] > 3 for row in queries['queries']):
            raise Unknown('complete menu exceeds existing four-copy selected profile')
        if len(queries['queries']) > MAX_ROWS:
            raise Unknown('selected menu row budget exceeded')
        if binary is None or restored is None:
            raise Unknown('configure the pinned existing native runtime and restored sources')
        # Authentication failure is availability uncertainty, not a source refutation.
        try:
            bridge.authenticate(binary, restored)
        except (ValueError, OSError) as error:
            raise Unknown('native runtime authentication unavailable: ' + str(error)) from error
        variables = [f'X:{i}' for i in range(len(source['edges']))] + [f'G:{i}' for i in range(len(source['hybrids']))]
        arithmetic = Arithmetic()
        for index, query in enumerate(queries['queries']):
            transport = copy_transport(query, source, c)
            wire = native_request(source, [r['native_leaf_index'] for r in transport['selected_bijection']], budgets)
            folder = out / f'row-{index:03d}'
            native = bridge.consume(dict(schema='native_rc1_operation_v1', operation='solve', request=wire),
                                    folder, binary, restored)
            if native['status'] == 'UNKNOWN':
                raise Unknown('native row incomplete: ' + native.get('reason', 'UNKNOWN'))
            c.require(native['status'] == 'CHECKED_SYMBOLIC_FORWARD_TABLE' and native['certificate_checked'],
                      'existing native parser or request-bound checker refused row')
            response = bridge.regular(folder/'RESPONSE.rc1', bridge.MAX_CERTIFICATE)
            table = table_terms(response, wire, variables, c)
            configurations, mixture = configuration_readouts(table, transport['native_rooted_comb'],
                source, menu, values, maps, c, arithmetic)
            coefficient = c.rational(query['comb_coefficient'])
            c.require(coefficient > 0, 'normalization coefficient must be positive')
            normalized = arithmetic.mul(mixture, 1 / coefficient)
            row = dict(row_index=index, same_tuple=identity, transport=transport, variables=variables,
                native_request_sha256=sha(wire.encode()), native_response_sha256=sha(response),
                native_result_sha256=sha((folder/'RESULT.json').read_bytes()),
                checked_selected_joint_table=True, configurations=configurations,
                formal_mixed_event_probability=str(mixture), formal_normalized_moment=str(normalized),
                matches_supplied_moment=normalized == c.rational(query['normalized_moment']),
                physical_row_equality_proved=False)
            (folder/'READOUT.json').write_text(json.dumps(row, indent=2, sort_keys=True) + '\n')
            result['rows'].append(row)
        result.update(readout_complete=True, formal_native_readouts_checked=True,
            all_supplied_moments_match=all(x['matches_supplied_moment'] for x in result['rows']),
            arithmetic_operations=arithmetic.used,
            reason='formal selected readouts complete; native-to-typed physical binding remains unproved')
    except Unknown as error:
        result.update(reason=str(error), formal_native_readouts_checked=False)
    except (ValueError, TypeError, KeyError, OSError) as error:
        result.update(status='REFUSED_REQUEST', reason=str(error), formal_native_readouts_checked=False)
    (out/'RESULT.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--request', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--parity-binary', type=Path)
    parser.add_argument('--parity-sources', type=Path)
    args = parser.parse_args()
    with args.request.open('rb') as stream:
        raw = stream.read(262145)
    result = run(raw, args.output, args.parity_binary, args.parity_sources)
    print(json.dumps({k: result[k] for k in ['status', 'readout_complete', 'physical_source_decision']}))
    return 2 if result['status'] == 'UNKNOWN' else 1


if __name__ == '__main__':
    raise SystemExit(main())
