"""Independent exact whole cap-five zero-coordinate reconstruction check.

The input is the pinned original current-root forest provider, loaded read-only.
Deletion is independently enumerated on label subsets. No numerical solver,
compiler, source search or interval source producer is invoked.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import comb
from pathlib import Path
import json
import sys
import types
import sympy as s

HELPER='research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-forest/exact_forest_layer.py'
EXPECTED='e0ced6748fd6fbe27f8165446a1c63a09bdb598fd1bdcd89115d4ae4853193b8'

def main(root,output):
    raw=(root/HELPER).read_bytes()
    assert sha256(raw).hexdigest()==EXPECTED
    h=types.ModuleType('independent_read_only_forest_helper')
    exec(compile(raw,HELPER,'exec'),h.__dict__)
    fa,source_sha=h.load_source(root)
    states=[h.representative(shape,fa) for shape in h.SHAPES5]
    def prune(t,keep):
        if isinstance(t,int):
            return t if t in keep else None
        a,b=prune(t[0],keep),prune(t[1],keep)
        return b if a is None else a if b is None else fa.tree(a,b)
    def restricted(f,keep):
        return fa.forest(v for t in f if (v:=prune(t,keep)) is not None)
    no_merger=[]
    for k in range(2,6):
        no_merger.append([F(sum(len(restricted(f,set(keep)))==k for keep in combinations(range(5),k)),comb(5,k))
                          for f in states])
    shapes4=[h.fs(*([h.LEAF]*4)),h.fs(h.T2,h.LEAF,h.LEAF),h.fs(h.T3,h.LEAF),
             h.fs(h.T2,h.T2),h.fs(h.B4),h.fs(h.C4)]
    delete4=[[F(sum(h.forest_shape(restricted(f,set(keep)))==shape for keep in combinations(range(5),4)),5)
              for f in states] for shape in shapes4]
    C=[a-(a+b)/3 for a,b in zip(delete4[3],delete4[2])]
    H=[a-(a+b)/3 for a,b in zip(delete4[4],delete4[5])]
    D=[a+b for a,b in zip(C,H)]
    rows=[[F(1)]*10,*no_merger,C,D,*[[F(int(i==j)) for j in range(10)] for i in (7,8,9)]]
    matrix=s.Matrix([[s.Rational(a.numerator,a.denominator) for a in row] for row in rows])
    assert matrix.rank()==10
    determinant=matrix.det()
    target=s.Matrix([1]*5+[0]*5)
    recovered=matrix.inv()*target
    assert recovered==s.Matrix([1]+[0]*9)
    expected4=[['1','2/5','0','0','0','0','0','0','0','0'],
               ['0','3/5','4/5','3/5','0','0','0','0','0','0'],
               ['0','0','0','2/5','2/5','4/5','4/5','0','0','0'],
               ['0','0','1/5','0','3/5','0','0','0','0','0'],
               ['0','0','0','0','0','1/5','0','1/5','0','3/5'],
               ['0','0','0','0','0','0','1/5','4/5','1','2/5']]
    assert delete4==[[F(v) for v in row] for row in expected4]
    record={'status':'PASS','scope':'Exact ten-orbit mass/projectivity/no-merger/full-forest coordinate reconstruction, retaining distinct completed five-trees.',
            'source_sha256':source_sha,'helper_sha256':EXPECTED,
            'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'ten_by_ten_rank':10,'determinant':str(determinant),
            'rows':['mass','b2','b3','b4','b5','C','D','p7','p8','p9'],
            'exact_rows':[[str(v) for v in row] for row in rows],
            'delete_four_matrix_matches_producer':True,
            'all_coordinate_zero_with_unit_diagonals_uniquely_identity':True,
            'source_projectivity_and_opaque_graft_required':True,
            'all_cap_result':False,'compiler_runs':0}
    output.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':'PASS','rank':10,'determinant':str(determinant)}))

if __name__=='__main__':
    main(Path(sys.argv[1]),Path(sys.argv[2]))
