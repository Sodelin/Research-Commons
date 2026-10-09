"""Classical all-solution interval-RHS operator on the coherent nine source equations."""
from fractions import Fraction as F
import interval_math as m
import interval_ad as ad
from base_contractors import PHYSICAL,AUXILIARY,clone,record,initial
I=m.I
MAX_LINEAR_BITS=4096
class PreconditionerRefusal(ValueError):pass

def guard(value):
    value=F(value)
    if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>MAX_LINEAR_BITS:raise PreconditionerRefusal('rational linear-algebra bit cap')
    return value

def rational_inverse(matrix):
    n=len(matrix)
    if n!=9 or any(len(row)!=n for row in matrix):raise PreconditionerRefusal('nine by nine matrix required')
    rows=[[guard(value) for value in row]+[F(int(i==j)) for j in range(n)] for i,row in enumerate(matrix)]
    for col in range(n):
        pivot=next((row for row in range(col,n) if rows[row][col]!=0),None)
        if pivot is None:raise PreconditionerRefusal('singular finite midpoint matrix')
        rows[col],rows[pivot]=rows[pivot],rows[col];scale=rows[col][col];rows[col]=[guard(x/scale) for x in rows[col]]
        for row in range(n):
            if row==col:continue
            factor=rows[row][col]
            rows[row]=[guard(x-guard(factor*y)) for x,y in zip(rows[row],rows[col])]
    inverse=tuple(tuple(row[n:]) for row in rows)
    for i in range(n):
        for j in range(n):
            value=F(0)
            for k in range(n):value=guard(value+guard(inverse[i][k]*matrix[k][j]))
            if value!=int(i==j):raise PreconditionerRefusal('exact inverse product check failed')
    return inverse

def matrix_vector(matrix,vector):
    result=[]
    for row in matrix:
        value=I.point(0)
        for coefficient,item in zip(row,vector):value=m.add(value,m.mul(I.point(coefficient),item))
        result.append(value)
    return tuple(result)
def interval_matrix_product(left,right):
    n=9;out=[]
    for i in range(n):
        row=[]
        for j in range(n):
            value=I.point(0)
            for k in range(n):value=m.add(value,m.mul(I.point(left[i][k]),right[k][j]))
            row.append(value)
        out.append(tuple(row))
    return tuple(out)
def intervals_record(vector):return [[str(value.lo),str(value.hi)] for value in vector]
def matrix_record(matrix):return [intervals_record(row) for row in matrix]
def rational_matrix_record(matrix):return [[str(value) for value in row] for row in matrix]

def operate(state,kind):
    if kind not in ('joint','joint_zero'):raise ValueError('only the frozen coherent joint operator is allowed')
    physical=state['physical'];point={key:(physical[key].lo+physical[key].hi)/2 for key in PHYSICAL}
    # Crucially, no inherited auxiliary or observed-target restriction is used here.
    value_q,jacobian_q=ad.evaluate({key:I.point(value) for key,value in point.items()})
    _,jacobian_box=ad.evaluate(physical)
    midpoint_matrix=tuple(tuple((entry.lo+entry.hi)/2 for entry in row) for row in jacobian_q)
    zero=tuple((F(0),)*9 for _ in range(9));refusal=None
    if kind=='joint_zero':preconditioner=zero;mode='DECLARED_ZERO_NOOP'
    else:
        try:preconditioner=rational_inverse(midpoint_matrix);mode='EXACT_RATIONAL_MIDPOINT_INVERSE'
        except PreconditionerRefusal as error:preconditioner=zero;mode='CONDITIONING_REFUSAL_ZERO_NOOP';refusal=str(error)
    target=tuple(state['moments'][key] for key in m.FEATURES)
    residual=tuple(m.sub(value,observed) for value,observed in zip(value_q,target))
    correction=matrix_vector(preconditioner,residual);product=interval_matrix_product(preconditioner,jacobian_box)
    deviations=tuple(m.sub(physical[key],I.point(point[key])) for key in PHYSICAL)
    K=[]
    for i,key in enumerate(PHYSICAL):
        value=m.sub(I.point(point[key]),correction[i])
        for j in range(9):value=m.add(value,m.mul(m.sub(I.point(int(i==j)),product[i][j]),deviations[j]))
        K.append(value)
    detail={'target_units':'raw_laplace_moments','feature_order':list(m.FEATURES),'physical_order':list(PHYSICAL),'point':{key:str(value) for key,value in point.items()},'full_physical_jacobian_domain':{key:[str(value.lo),str(value.hi)] for key,value in physical.items()},'point_value':intervals_record(value_q),'point_jacobian':matrix_record(jacobian_q),'full_jacobian':matrix_record(jacobian_box),'midpoint_matrix':rational_matrix_record(midpoint_matrix),'fixed_rational_Y':rational_matrix_record(preconditioner),'preconditioner_mode':mode,'preconditioner_refusal':refusal,'raw_target':intervals_record(target),'K':intervals_record(K),'arithmetic_bits':m.BITS,'linear_bit_cap':MAX_LINEAR_BITS,'auxiliary_or_target_clipping_used_for_Fq_or_J':False}
    out=clone(state)
    try:
        for key,enclosure in zip(PHYSICAL,K):out['physical'][key]=m.meet(physical[key],enclosure)
    except m.Inconsistent as error:
        error.operator_detail=detail;raise
    return out,detail
