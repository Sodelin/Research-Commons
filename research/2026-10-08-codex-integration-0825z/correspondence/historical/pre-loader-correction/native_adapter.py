"""Conditional exact-rational native/unchanged-reference boundary adapter.

This additive adapter does not certify graph admission, execute a biological
calendar, approximate arbitrary-real inputs, or turn a proxy into a source.
Original occurrence IDs, labels, tags and stored Bool values are unchanged.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from itertools import product

REFERENCE_PATH = "research/2026-10-07-astra-g6-source-poisson-prefix-124833z/finite_source_prefix.py"
REFERENCE_SHA256 = "f54e18f2f1a09c836c4905fa936956d935929b3300248fc31f87a97ca86ae0cf"
ROOT = Path(__file__).resolve().parents[3]


def load_reference():
    path = ROOT / REFERENCE_PATH
    if hashlib.sha256(path.read_bytes()).hexdigest() != REFERENCE_SHA256:
        raise ValueError("REFERENCE_IDENTITY_MISMATCH")
    spec = importlib.util.spec_from_file_location("correspondence_frozen_reference", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


ref = load_reference()
Leaf, Join, SourceState = ref.Leaf, ref.Join, ref.SourceState


def exact_string(x):
    if type(x) is not str or not x:
        raise ValueError("An original ID/label must be a nonempty string.")
    return x


def exact_q(x, *, interior=False, positive=False):
    if type(x) is not Q:
        raise ValueError("An exact Fraction is required; floats and Bool are rejected.")
    if interior and not 0 < x < 1 or positive and x <= 0:
        raise ValueError("The original positive/interior domain is required.")
    return x


@dataclass(frozen=True)
class Hybrid:
    original_id: str
    child: str
    parent0: str
    parent1: str
    gamma_native: Q
    common: bool

    def validate(self):
        for value in (self.original_id, self.child, self.parent0, self.parent1):
            exact_string(value)
        if len({self.child, self.parent0, self.parent1}) != 3:
            raise ValueError("Distinct original physical edge occurrences are required.")
        exact_q(self.gamma_native, interior=True)
        if type(self.common) is not bool:
            raise ValueError("The source mode is a literal Bool.")

    @property
    def gamma_python(self):
        self.validate()
        return 1 - self.gamma_native


@dataclass(frozen=True)
class Contract:
    """Fixed metadata, not a claim that a graph/calendar is biologically admitted.

    `vertices` is the full original V register domain, including inert slots.
    `rates` includes the original ancestral population and all physical edges.
    `calendar` preserves the caller's literal dated, ordered boundary agenda.
    Its source admissibility must be supplied by the actual original compiler.
    """
    vertices: tuple[str, ...]
    rates: tuple[tuple[str, Q], ...]
    copy_cap: int
    hybrids: tuple[Hybrid, ...]
    calendar: tuple[tuple[Q, tuple[tuple[str, str], ...]], ...] = ()
    bin_cuts: tuple[Q, ...] = ()

    def validate(self):
        if any(type(x) is not tuple for x in (self.hybrids, self.calendar, self.bin_cuts)):
            raise ValueError("The shared hybrid/calendar/cut bank must be immutable.")
        if type(self.vertices) is not tuple or self.vertices != tuple(sorted(set(self.vertices))):
            raise ValueError("Full original vertex IDs must be sorted and unique.")
        for v in self.vertices:
            exact_string(v)
        if type(self.rates) is not tuple or tuple(p for p, _ in self.rates) != tuple(sorted(set(p for p, _ in self.rates))):
            raise ValueError("Original physical occurrence IDs must be sorted and unique.")
        if any(type(row) is not tuple or len(row) != 2 for row in self.rates):
            raise ValueError("Immutable typed rate rows are required.")
        for p, r in self.rates:
            exact_string(p)
            exact_q(r, positive=True)
        if type(self.copy_cap) is not int or self.copy_cap < 1:
            raise ValueError("copy_cap must equal a declared positive original Copy cardinality.")
        if not self.rates:
            raise ValueError("The physical bank includes an ancestral population.")
        ids = []
        for h in self.hybrids:
            if type(h) is not Hybrid:
                raise ValueError("Typed original hybrid incidence is required.")
            h.validate()
            ids.append(h.original_id)
            if h.original_id not in self.vertices or any(p not in dict(self.rates) for p in (h.child, h.parent0, h.parent1)):
                raise ValueError("Hybrid/register/parent IDs must come from the same fixed bank.")
        if ids != sorted(set(ids)):
            raise ValueError("Hybrid IDs must be sorted and unique.")
        previous = None
        for batch in self.calendar:
            if type(batch) is not tuple or len(batch) != 2:
                raise ValueError("Immutable dated boundary batches are required.")
            date, operations = batch
            exact_q(date)
            if date < 0 or previous is not None and date <= previous:
                raise ValueError("Calendar batch dates must increase; tied operations share one batch.")
            previous = date
            if type(operations) is not tuple:
                raise ValueError("Every original batch has one immutable ordered operation tuple.")
            saw_node = False
            seen = set()
            for operation in operations:
                if type(operation) is not tuple or len(operation) != 2:
                    raise ValueError("Immutable original boundary operation rows are required.")
                kind, occurrence = operation
                if kind not in ("exit", "node") or type(kind) is not str:
                    raise ValueError("Only literal original exits and node operations are metadata.")
                exact_string(occurrence)
                if (kind, occurrence) in seen:
                    raise ValueError("Duplicate original boundary occurrence.")
                seen.add((kind, occurrence))
                if kind == "node":
                    saw_node = True
                    if occurrence not in self.vertices:
                        raise ValueError("Unknown original node occurrence.")
                elif saw_node or occurrence not in dict(self.rates):
                    raise ValueError("Original exits precede nodes and use physical occurrence IDs.")
        for cut in self.bin_cuts:
            exact_q(cut)
        if any(c < 0 for c in self.bin_cuts) or self.bin_cuts != tuple(sorted(set(self.bin_cuts))):
            raise ValueError("Deterministic bin cuts must be increasing nonnegative exact rationals.")
        return self


def validate_tree(t):
    if type(t) is Leaf:
        exact_string(t.label)
    elif type(t) is Join:
        if type(t.bin_tag) is not int or t.bin_tag < 0:
            raise ValueError("Bin tags must be nonnegative integers, not Bool.")
        validate_tree(t.left)
        validate_tree(t.right)
        if t != ref.graft(t.left, t.right, t.bin_tag):
            raise ValueError("Every recursive child pair must use the canonical graft.")
    else:
        raise ValueError("Only exact Leaf/Join constructors are accepted.")


@dataclass(frozen=True)
class FullRecord:
    physical: SourceState
    outside_nodes: tuple[tuple[str, tuple[object, ...]], ...] = ()


def validate_record(record, contract):
    contract.validate()
    if type(record) is not FullRecord or type(record.physical) is not SourceState:
        raise ValueError("Typed complete records are required.")
    s = record.physical
    if type(s.populations) is not tuple or type(s.registers) is not tuple:
        raise ValueError("Immutable state coordinates are required.")
    if any(type(row) is not tuple or len(row) != 2 for row in s.populations + s.registers):
        raise ValueError("Immutable typed physical/register rows are required.")
    if tuple(p for p, _ in s.populations) != tuple(sorted(set(p for p, _ in s.populations))):
        raise ValueError("Physical population coordinates must be sorted and unique.")
    if tuple(v for v, _ in s.registers) != contract.vertices:
        raise ValueError("The SAME TOTAL original V register is required, including inert slots.")
    for v, b in s.registers:
        if type(b) is not bool:
            raise ValueError("Every stored register value must be a literal Bool.")
        if v not in {h.original_id for h in contract.hybrids} and b:
            raise ValueError("Native nonhybrid register slots are inert false.")
    if type(record.outside_nodes) is not tuple or tuple(n for n, _ in record.outside_nodes) != tuple(sorted(set(n for n, _ in record.outside_nodes))):
        raise ValueError("Outside node payload coordinates must be sorted and unique.")
    if any(type(row) is not tuple or len(row) != 2 for row in record.outside_nodes):
        raise ValueError("Immutable typed outside-node rows are required.")
    labels = set()
    for populations, domain in ((s.populations, dict(contract.rates)), (record.outside_nodes, contract.vertices)):
        for p, trees in populations:
            if p not in domain or type(trees) is not tuple or not trees or trees != tuple(sorted(trees, key=ref.tree_key)):
                raise ValueError("Unknown ID, empty/noncanonical forest or mutable payload.")
            for t in trees:
                validate_tree(t)
                ls = ref.leaves(t)
                def leaf_count(u):
                    return 1 if type(u) is Leaf else leaf_count(u.left) + leaf_count(u.right)
                if len(ls) != leaf_count(t) or labels.intersection(ls):
                    raise ValueError("Immutable Copy labels must occur exactly once across the full forest.")
                labels.update(ls)
    if len(labels) > contract.copy_cap:
        raise ValueError("Full physical/outside Copy labels exceed the SAME original cap.")
    s.validate()
    return record


def original_register_law(contract):
    """Exactly the native independent Hybrid→Bool product, then inert V slots.

    Both COMMON and INDEPENDENT sites have a latent original bit, as in the
    actual initializer; only COMMON pulses read it. No epoch redraw exists.
    """
    contract.validate()
    out = {}
    for bits in product((False, True), repeat=len(contract.hybrids)):
        registers = {v: False for v in contract.vertices}
        mass = Q(1)
        for h, bit in zip(contract.hybrids, bits):
            registers[h.original_id] = bit
            # Unchanged Python convention False eta, True 1-eta.
            eta = h.gamma_python
            mass *= 1 - eta if bit else eta
        out[tuple(sorted(registers.items()))] = mass
    return out


def adapted_child_boundary(record, contract, original_id):
    """Composite child-edge exit and its original hybrid pulse.

    Guard: h has no pre-existing node forest. The sole original child-edge
    roots are exactly the AtNode h roots after exit. Other nodes are retained
    explicitly. This is not an adapter for an arbitrary node list or calendar.
    """
    validate_record(record, contract)
    matches = [h for h in contract.hybrids if h.original_id == original_id]
    if len(matches) != 1 or original_id in dict(record.outside_nodes):
        raise ValueError("Unknown hybrid or unsupported pre-existing focal node forest.")
    h = matches[0]
    result = ref.hybrid_boundary(record.physical, child=h.child, parent0=h.parent0,
                                 parent1=h.parent1, original_id=h.original_id,
                                 gamma=h.gamma_python, common=h.common)
    out = {FullRecord(s, record.outside_nodes): m for s, m in result.items() if m}
    for d in out:
        validate_record(d, contract)
    return out


def adapted_law(law, contract, original_id):
    """Bind the SAME correlated input law, without factorizing past/registers."""
    validate_law(law, contract)
    out = defaultdict(Q)
    for s, mass in law.items():
        for d, prob in adapted_child_boundary(s, contract, original_id).items():
            out[d] += mass * prob
    result = dict(out)
    validate_law(result, contract)
    return result


def validate_law(law, contract):
    if type(law) is not dict or not law:
        raise ValueError("A finite complete probability law is required.")
    for s, mass in law.items():
        validate_record(s, contract)
        exact_q(mass, positive=True)
    if sum(law.values(), Q(0)) != 1:
        raise ValueError("Mass must be exactly one; truncation/negative/duplicate rows are refused.")


def qwire(q):
    exact_q(q)
    return [str(q.numerator), str(q.denominator)]


def unwire_q(x):
    if type(x) is not list or len(x) != 2 or any(type(v) is not str for v in x):
        raise ValueError("Exact canonical rational pair required.")
    def integer(v):
        out = int(v)
        if str(out) != v:
            raise ValueError("Noncanonical integer.")
        return out
    n, d = map(integer, x)
    if d <= 0:
        raise ValueError("Positive denominator required.")
    q = Q(n, d)
    if qwire(q) != x:
        raise ValueError("Reduced canonical rational required.")
    return q


def treewire(t):
    validate_tree(t)
    return ["leaf", t.label] if type(t) is Leaf else ["join", t.bin_tag, treewire(t.left), treewire(t.right)]


def unwire_tree(x):
    if type(x) is not list or not x:
        raise ValueError("Typed recursive tree wire required.")
    if x[0] == "leaf" and len(x) == 2:
        t = Leaf(exact_string(x[1]))
    elif x[0] == "join" and len(x) == 4:
        t = Join(x[1], unwire_tree(x[2]), unwire_tree(x[3]))
    else:
        raise ValueError("Unknown or malformed tree constructor.")
    validate_tree(t)
    return t


def recordwire(record):
    s = record.physical
    return {"physical": [[p, [treewire(t) for t in ts]] for p, ts in s.populations],
            "outside_nodes": [[p, [treewire(t) for t in ts]] for p, ts in record.outside_nodes],
            "registers": [[v, b] for v, b in s.registers]}


def unwire_record(x):
    if type(x) is not dict or set(x) != {"physical", "outside_nodes", "registers"}:
        raise ValueError("Exact full-record fields are required.")
    def populations(rows):
        if type(rows) is not list:
            raise ValueError("Population rows must be a list.")
        out = []
        for row in rows:
            if type(row) is not list or len(row) != 2 or type(row[1]) is not list:
                raise ValueError("Malformed population row.")
            out.append((exact_string(row[0]), tuple(unwire_tree(t) for t in row[1])))
        return tuple(out)
    regs = x["registers"]
    if type(regs) is not list or any(type(r) is not list or len(r) != 2 for r in regs):
        raise ValueError("Malformed total-register rows.")
    return FullRecord(SourceState(populations(x["physical"]), tuple((r[0], r[1]) for r in regs)),
                      populations(x["outside_nodes"]))


def contractwire(c):
    c.validate()
    return {"vertices": list(c.vertices), "rates": [[p, qwire(q)] for p, q in c.rates],
            "copy_cap": c.copy_cap,
            "hybrids": [{"original_id": h.original_id, "child": h.child,
                         "parent0": h.parent0, "parent1": h.parent1,
                         "gamma_native": qwire(h.gamma_native), "common": h.common} for h in c.hybrids],
            "calendar": [[qwire(d), [list(op) for op in ops]] for d, ops in c.calendar],
            "bin_cuts": [qwire(d) for d in c.bin_cuts]}


def canonical_json(x):
    return json.dumps(x, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


def serialize_law(law, contract):
    validate_law(law, contract)
    metadata = contractwire(contract)
    rows = [{"state": recordwire(s), "mass": qwire(m)} for s, m in law.items()]
    rows.sort(key=lambda r: canonical_json(r["state"]))
    return canonical_json({"schema": "conditional-original-forest-law-v1",
                           "source_admission": "NOT_CERTIFIED_BY_ADAPTER",
                           "reference_sha256": REFERENCE_SHA256,
                           "contract": metadata,
                           "contract_sha256": hashlib.sha256(canonical_json(metadata).encode()).hexdigest(),
                           "rows": rows})


def deserialize_law(data, expected_contract):
    """The caller supplies one expected shared contract; mixed metadata refuses."""
    def unique(pairs):
        out = {}
        for k, v in pairs:
            if k in out:
                raise ValueError("Duplicate JSON object key.")
            out[k] = v
        return out
    def nofloat(_):
        raise ValueError("Floating-point/nonfinite JSON numbers are forbidden.")
    x = json.loads(data, object_pairs_hook=unique, parse_float=nofloat, parse_constant=nofloat)
    if type(x) is not dict or set(x) != {"schema", "source_admission", "reference_sha256", "contract", "contract_sha256", "rows"}:
        raise ValueError("Unknown or missing packet fields.")
    metadata = contractwire(expected_contract)
    if x["schema"] != "conditional-original-forest-law-v1" or x["source_admission"] != "NOT_CERTIFIED_BY_ADAPTER" or x["reference_sha256"] != REFERENCE_SHA256 or x["contract"] != metadata:
        raise ValueError("Wrong schema/source identity or mixed original bank/calendar/incidence.")
    if x["contract_sha256"] != hashlib.sha256(canonical_json(metadata).encode()).hexdigest():
        raise ValueError("Shared contract digest mismatch.")
    if type(x["rows"]) is not list:
        raise ValueError("Exact finite rows required.")
    law = {}
    for row in x["rows"]:
        if type(row) is not dict or set(row) != {"state", "mass"}:
            raise ValueError("Exact row fields required.")
        s, mass = unwire_record(row["state"]), unwire_q(row["mass"])
        if s in law:
            raise ValueError("Duplicate full state row; mass cannot be silently overwritten.")
        law[s] = mass
    validate_law(law, expected_contract)
    if serialize_law(law, expected_contract) != data:
        raise ValueError("Noncanonical wire/order/encoding refused.")
    return law
