"""Finite reviewed contractor allowlist; every test encloses all nuisance values."""
from fractions import Fraction as F
import interval_math as m
I=m.I
PHYSICAL=('h','u','v','rA','rB','rC','rAB','rR','g')
AUXILIARY=('A','T','L')
ALLOWLIST=('linear','forward','root_q','root_time','rate_C','BC_residual','AB_residual','rate_A','rate_B')

def clone(state):return {group:dict(values) for group,values in state.items()}
def record(state):return {group:{key:[str(i.lo),str(i.hi)] for key,i in values.items()} for group,values in state.items()}
def initial(physical,observations):
    p=dict(physical);A=p['h']+p['u'];T=A+p['v'];L=p['u']+p['v']
    raw={key:m.meet(value*2-1,I(0,1)) for key,value in observations.items()}
    return {'physical':p,'aux':dict(A=A,T=T,L=L),'moments':raw}
def zero_test(value,label,log):
    log[label]=[str(value.lo),str(value.hi)]
    if not value.contains(0):raise m.Inconsistent('zero excluded: '+label)
def linear(state):
    p,a=state['physical'],state['aux']
    # All arithmetic here is exact; these are interval projections of equalities.
    for total,group,x,ygroup,y in [('A',p,'h',p,'u'),('T',a,'A',p,'v'),('L',p,'u',p,'v'),('T',p,'h',a,'L')]:
        a[total]=m.meet(a[total],group[x]+ygroup[y]);group[x]=m.meet(group[x],a[total]-ygroup[y]);ygroup[y]=m.meet(ygroup[y],a[total]-group[x])

def operate(state,kind):
    if kind not in ALLOWLIST:raise ValueError('operator outside frozen allowlist')
    out=clone(state);p,a,y=out['physical'],out['aux'],out['moments'];log={};c=F(8,3)
    if kind=='linear':linear(out)
    elif kind=='forward':
        forward=m.selected(p,a)
        for key in m.FEATURES:y[key]=m.meet(y[key],forward[key])
        log['forward']={key:[str(value.lo),str(value.hi)] for key,value in forward.items()}
    elif kind=='root_q':
        r=p['rR'];a1=y['AC1'];a2=y['AC2'];one=I.point(1)
        residual=m.sub(m.mul(m.mul(a2,r),m.add(r,I.point(2*c))),m.mul(m.exact_square(a1),m.exact_square(m.add(r,I.point(c)))))
        zero_test(residual,'root_polynomial',log)
        if a1.lo<=0:log['ratio_guard']='SKIPPED_ZERO_DENOMINATOR'
        else:
            Q=m.divide(a2,m.exact_square(a1));q=lambda x:(x+c)**2/(x*(x+2*c));Q=m.meet(Q,I(q(r.hi),q(r.lo)));trial=(r.lo+r.hi)/2;value=q(trial)
            log.update(ratio_guard='POSITIVE',Q=[str(Q.lo),str(Q.hi)],trial=str(trial),trial_q=str(value))
            if value>Q.hi:p['rR']=I(trial,r.hi);log['removed']='lower_rate_slab'
            elif value<Q.lo:p['rR']=I(r.lo,trial);log['removed']='upper_rate_slab'
    elif kind=='root_time':
        T=a['T'];trial=(T.lo+T.hi)/2;bound=m.tail(c,I.point(trial),p['rR']);target=y['AC1']
        log.update(trial=str(trial),whole_nuisance_enclosure=[str(bound.lo),str(bound.hi)])
        if bound.hi<target.lo:a['T']=I(T.lo,trial);log['removed']='upper_time_slab'
        elif bound.lo>target.hi:a['T']=I(trial,T.hi);log['removed']='lower_time_slab'
    elif kind in ('rate_C','rate_A','rate_B'):
        rate,pair={'rate_C':('rC','CC1'),'rate_A':('rA','AA1'),'rate_B':('rB','BB1')}[kind]
        old=p[rate];trial=(old.lo+old.hi)/2;trial_p=dict(p);trial_p[rate]=I.point(trial)
        # The same trial B rate is used at every tied occurrence in the full formula.
        bound=m.pair_intervals(trial_p,a,c)[pair[:-1]];target=y[pair]
        log.update(active_rate=rate,trial=str(trial),whole_nuisance_enclosure=[str(bound.lo),str(bound.hi)])
        if bound.hi<target.lo:p[rate]=I(trial,old.hi);log['removed']='lower_rate_slab'
        elif bound.lo>target.hi:p[rate]=I(old.lo,trial);log['removed']='upper_rate_slab'
    elif kind=='BC_residual':
        D={};B={}
        for k in (1,2):
            z=c*k;B[k]=m.tail(z,a['T'],p['rR']);full=m.two_stage(z,p['h'],p['rC'],a['L'],a['T'],p['rR']);D[k]=m.sub(full,B[k])
            residual=m.sub(m.sub(y['BC'+str(k)],B[k]),m.mul(p['g'],D[k]));zero_test(residual,'BC'+str(k),log)
        cross=m.sub(m.mul(D[2],m.sub(y['BC1'],B[1])),m.mul(D[1],m.sub(y['BC2'],B[2])));zero_test(cross,'BC_cross',log)
        log['division_used']=False
    elif kind=='AB_residual':
        for k in (1,2):
            z=c*k;B=m.tail(z,a['T'],p['rR']);full=m.two_stage(z,a['A'],p['rAB'],p['v'],a['T'],p['rR'])
            residual=m.sub(m.sub(y['AB'+str(k)],m.mul(p['g'],B)),m.mul(m.sub(I.point(1),p['g']),full));zero_test(residual,'AB'+str(k),log)
        log['division_used']=False
    # Physical intervals must only shrink; linear projection never introduces a new parameter.
    for group in out:
        for key,new in out[group].items():
            old=state[group][key]
            if new.lo<old.lo or new.hi>old.hi:raise ArithmeticError('noncontracting state update')
    return out,log
