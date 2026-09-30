"""Joint exact recovery: new adaptive order learner + unchanged Astra decoder.

Standard library research implementation. See ORDER-SPACE.md/QUERY-BOUND.md.
The exact binary-tree-family/common-circle promise is not globally validated.
"""
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable
import hashlib, importlib.util, sys
from adaptive_order import AdaptiveOrderLearner
from core import pair_bit

SPARSE_BLOB = '49933337ce26ce0d5ef58bbfa458bf5706d8e817'
REFERENCE_BLOB = 'ec037ceb66d7f68ef0c76842b78b4f751f9f63c6'


def git_blob(path: Path) -> str:
    data=path.read_bytes()
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def load_pinned(filename: str, directory: str, blob: str):
    """Prefer canonical sibling; portable packet carries unchanged snapshots."""
    here=Path(__file__).resolve().parent
    choices=(here.parent/directory/filename, here/'vendor'/filename)
    path=next((p for p in choices if p.is_file()),None)
    if path is None:raise FileNotFoundError(f'Pinned provider missing: {choices}')
    if git_blob(path)!=blob:raise ValueError(f'Provider bytes changed: {path}')
    name='exact_query_pinned_'+blob
    if name not in sys.modules:
        spec=importlib.util.spec_from_file_location(name,path)
        if spec is None or spec.loader is None:raise ImportError(str(path))
        module=importlib.util.module_from_spec(spec);sys.modules[name]=module
        spec.loader.exec_module(module)
    return sys.modules[name]


def sparse_provider():
    return load_pinned('sparse_quartet.py','2026-09-30-astra-sparse-query',SPARSE_BLOB)


def reference_provider():
    return load_pinned('order_recovery.py','2026-09-30-query-resumption',REFERENCE_BLOB)


def remap_answer(order: tuple[int,...], positions: tuple[int,int,int,int], mask: int) -> int:
    """Original-label mask -> position-label mask, preserving bipartitions."""
    original=tuple(sorted(order[i] for i in positions))
    a=positions[0]; answer=0
    for bit,b in enumerate(positions[1:]):
        if mask & pair_bit(original,(order[a],order[b])):answer |= 1<<bit
    return answer


@dataclass(frozen=True)
class JointResult:
    order: tuple[int,...]
    gap_pairs: frozenset[tuple[int,int]]
    order_queries: int
    total_queries: int
    sparse_requests: int
    internal_vertices: int
    retired_vertices: int

    def expanded_splits(self) -> frozenset[frozenset[int]]:
        """Optional O(nk) expansion; compact output itself is order+gap pairs."""
        taxa=frozenset(self.order);out=set()
        for i,j in self.gap_pairs:
            a=frozenset(self.order[i+1:j+1]);b=taxa-a
            out.add(min(a,b,key=lambda s:(len(s),tuple(sorted(s)))))
        return frozenset(out)


def order_bound(n: int) -> int:
    if type(n) is not int or n<4:raise ValueError('Need n>=4.')
    return (n-3)*(11*(n-1).bit_length()+15)


def recover_all(labels: Iterable[int], oracle: Callable[[tuple[int,int,int,int]],int]) -> JointResult:
    labels=tuple(labels)
    if len(labels)<4 or any(type(x) is not int or x<0 for x in labels) or len(set(labels))!=len(labels):
        raise ValueError('Need >=4 distinct nonnegative integer taxon labels.')
    if not callable(oracle):raise TypeError('oracle must be callable')
    learner=AdaptiveOrderLearner(labels,oracle)
    order=learner.run(); first=len(learner.cache)
    def query_positions(q):
        original=tuple(sorted(order[i] for i in q))
        return remap_answer(order,q,learner.query(original))
    recovered=sparse_provider().recover(len(order),query_positions)
    result=JointResult(order,recovered.splits,first,len(learner.cache),recovered.oracle_calls,
                       len(learner.tree.rot)-len(labels),sum(h['central_nodes'] for h in learner.history))
    assert result.order_queries<=order_bound(len(labels))
    assert result.total_queries<=order_bound(len(labels))+sparse_provider().query_bound(len(labels),len(result.gap_pairs))
    assert result.retired_vertices==len(labels)-2-result.internal_vertices
    return result
