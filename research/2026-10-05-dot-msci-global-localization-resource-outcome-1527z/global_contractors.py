"""Whole-nuisance triangular stages under the accepted original-domain contract."""
from fractions import Fraction as F
import interval_math as m
import base_contractors as base
import joint_contractor as joint
I=m.I
PHYSICAL=base.PHYSICAL;AUXILIARY=base.AUXILIARY
clone=base.clone;record=base.record;initial=base.initial
FEATURES=m.FEATURES
Z=F(8,3)
class GuardUnavailable(ValueError):pass

def ir(value):return [str(value.lo),str(value.hi)]
def midpoint(value):return (value.lo+value.hi)/2

def scalar_bracket(state,group,key,target,evaluate,increasing,steps,log):
    """Two bounded searches; only certified strict comparisons alter a bound."""
    original=state[group][key];cur=original;entries=[]
    def comparison(trial,tag):
        try:enclosure=evaluate(trial)
        except GuardUnavailable as error:
            entries.append({'pass':tag,'trial':str(trial),'guard':'UNRESOLVED','reason':str(error)});return None
        relation='below' if enclosure.hi<target.lo else ('above' if enclosure.lo>target.hi else 'overlap')
        cut=None
        if relation=='below':cut='lower' if increasing else 'upper'
        elif relation=='above':cut='upper' if increasing else 'lower'
        entries.append({'pass':tag,'trial':str(trial),'enclosure':ir(enclosure),'relation':relation,'cut':cut,'guard':'VALID'})
        return cut
    try:
        if comparison(cur.lo,'lower_endpoint')=='upper':raise m.Inconsistent('scalar lower endpoint excludes whole range: '+key)
        if comparison(cur.hi,'upper_endpoint')=='lower':raise m.Inconsistent('scalar upper endpoint excludes whole range: '+key)
        for side in ('lower','upper'):
            search_lo,search_hi=cur.lo,cur.hi
            for _ in range(steps):
                if search_lo==search_hi:break
                trial=(search_lo+search_hi)/2;cut=comparison(trial,side)
                if cut=='lower':cur=I(max(cur.lo,trial),cur.hi)
                elif cut=='upper':cur=I(cur.lo,min(cur.hi,trial))
                state[group][key]=cur
                if side=='lower':
                    if cut=='lower':search_lo=trial
                    else:search_hi=trial
                else:
                    if cut=='upper':search_hi=trial
                    else:search_lo=trial
    finally:
        log.append({'group':group,'coordinate':key,'initial':ir(original),'final':ir(cur),'target':ir(target),'monotonicity':'increasing' if increasing else 'decreasing','comparisons':entries})
    return cur

def point_two_stage(z,onset,rate,T,R):
    if onset<0 or T<=onset or rate<=0 or R<=0:raise GuardUnavailable('invalid positive hypothetical duration')
    p=rate/(rate+z);q=R/(R+z)
    return m.mul(m.E(I.point(z*onset)),m.add(I.point(p),m.mul(m.E(I.point((rate+z)*(T-onset))),I.point(q-p))))

def rectangle_two_stage(z,onset,rate,T,R):
    """Exact extrema from monotonicity/corners on a guarded rectangular domain."""
    if onset.lo<0 or onset.hi>=T.lo:raise GuardUnavailable('onset rectangle is not strictly before root rectangle')
    low_T=T.lo if rate.lo>=R.lo else T.hi
    high_T=T.hi if rate.hi>=R.hi else T.lo
    low=point_two_stage(z,onset.hi,rate.lo,low_T,R.lo)
    high=point_two_stage(z,onset.lo,rate.hi,high_T,R.hi)
    return I(low.lo,high.hi)

def actual_two_stage(z,onset,rate,length,T,R):
    try:return rectangle_two_stage(z,onset,rate,T,R),'guarded_corners'
    except GuardUnavailable:return m.two_stage(z,onset,rate,length,T,R),'positive_physical_length_fallback'

def positive_D(z,onset,rate,length,T,R):
    if length.lo<=0:raise GuardUnavailable('positive length lower bound unavailable')
    M,method=actual_two_stage(z,onset,rate,length,T,R);B=m.tail(z,T,R)
    # Formula(P) evaluated outward with original positive source bounds.
    lower=m.mul(m.mul(1-m.E(I.point(rate.lo*length.lo)),m.E(I.point(z*T.hi))),I.point(z/(R.hi+z))).lo
    D=m.meet(m.sub(M,B),I(max(F(0),lower),1))
    return D,B,{'positive_lower':str(lower),'method':method}

def zero_test(value,label,log):
    log.append({'residual':label,'enclosure':ir(value)})
    if not value.contains(0):raise m.Inconsistent('zero excluded: '+label)

def root_stage(state,steps,log):
    p,a,y=state['physical'],state['aux'],state['moments']
    for k in (1,2):y['AC'+str(k)]=m.meet(y['AC'+str(k)],m.tail(Z*k,a['T'],p['rR']))
    R=p['rR'];a1=y['AC1'];a2=y['AC2']
    residual=m.sub(m.mul(m.mul(a2,R),m.add(R,I.point(2*Z))),m.mul(m.exact_square(a1),m.exact_square(m.add(R,I.point(Z)))))
    zero_test(residual,'root_polynomial',log)
    if a1.lo>0:
        Q=m.divide(a2,m.exact_square(a1));q=lambda r:(r+Z)**2/(r*(r+2*Z));Q=m.meet(Q,I(q(R.hi),q(R.lo)))
        scalar_bracket(state,'physical','rR',Q,lambda trial:I.point(q(trial)),False,steps,log)
    else:log.append({'root_ratio':'SKIPPED_ZERO_DENOMINATOR'})
    scalar_bracket(state,'aux','T',y['AC1'],lambda trial:m.tail(Z,I.point(trial),p['rR']),False,steps,log)
    base.linear(state)

def C_stage(state,steps,log):
    p,a,y=state['physical'],state['aux'],state['moments']
    scalar_bracket(state,'physical','rC',y['CC1'],lambda trial:rectangle_two_stage(Z,I.point(0),I.point(trial),a['T'],p['rR']),True,steps,log)

def pulse_data(state,log):
    p,a,y=state['physical'],state['aux'],state['moments'];D={};B={};N={}
    for k in (1,2):
        D[k],B[k],detail=positive_D(Z*k,p['h'],p['rC'],a['L'],a['T'],p['rR'])
        N[k]=m.meet(m.sub(y['BC'+str(k)],B[k]),m.mul(p['g'],D[k]))
        log.append({'pulse_k':k,'D':ir(D[k]),'B':ir(B[k]),'N':ir(N[k]),**detail})
        zero_test(m.sub(m.sub(y['BC'+str(k)],B[k]),m.mul(p['g'],D[k])),'BC'+str(k),log)
    zero_test(m.sub(m.mul(D[2],N[1]),m.mul(D[1],N[2])),'BC_cross',log)
    return D,B,N

def pulse_stage(state,steps,log):
    p,a,y=state['physical'],state['aux'],state['moments'];D,B,N=pulse_data(state,log)
    if D[1].lo>0 and N[1].lo>0:
        observed=m.divide(N[2],N[1])
        def trial_ratio(trial):
            if trial>=a['T'].lo:raise GuardUnavailable('pulse trial not below entire root interval')
            length=I(a['T'].lo-trial,a['T'].hi-trial);d1,_,_=positive_D(Z,I.point(trial),p['rC'],length,a['T'],p['rR']);d2,_,_=positive_D(2*Z,I.point(trial),p['rC'],length,a['T'],p['rR'])
            if d1.lo<=0:raise GuardUnavailable('positive hypothetical D denominator not certified')
            return m.divide(d2,d1)
        scalar_bracket(state,'physical','h',observed,trial_ratio,False,steps,log)
        base.linear(state);D,B,N=pulse_data(state,log)
    else:log.append({'pulse_ratio':'SKIPPED_POSITIVE_DENOMINATOR_NOT_CERTIFIED'})
    if D[1].lo>0:
        amplitude=m.divide(N[1],D[1]);old=p['g'];p['g']=m.meet(old,amplitude);log.append({'amplitude_projection':ir(amplitude),'g_before':ir(old),'g_after':ir(p['g'])})
    else:log.append({'pulse_amplitude':'SKIPPED_POSITIVE_DENOMINATOR_NOT_CERTIFIED'})
    base.linear(state)

def AB_stage(state,steps,log):
    p,a,y=state['physical'],state['aux'],state['moments'];denom=I(1-p['g'].hi,1-p['g'].lo)
    if denom.lo<=0:raise GuardUnavailable('AB demixing denominator unavailable')
    target={k:m.meet(m.divide(m.sub(y['AB'+str(k)],m.mul(p['g'],m.tail(Z*k,a['T'],p['rR']))),denom),I(0,1)) for k in (1,2)}
    for k in (1,2):
        def rate_trial(trial,k=k):return actual_two_stage(Z*k,a['A'],I.point(trial),p['v'],a['T'],p['rR'])[0]
        scalar_bracket(state,'physical','rAB',target[k],rate_trial,True,steps,log)
    for k in (1,2):
        def onset_trial(trial,k=k):
            if trial>=a['T'].lo:raise GuardUnavailable('AB onset trial not below entire root interval')
            return rectangle_two_stage(Z*k,I.point(trial),p['rAB'],a['T'],p['rR'])
        scalar_bracket(state,'aux','A',target[k],onset_trial,False,steps,log)
        base.linear(state)
    for k in (1,2):
        M,method=actual_two_stage(Z*k,a['A'],p['rAB'],p['v'],a['T'],p['rR']);B=m.tail(Z*k,a['T'],p['rR']);model=m.add(m.mul(p['g'],B),m.mul(I(1-p['g'].hi,1-p['g'].lo),M))
        log.append({'AB_k':k,'model':ir(model),'method':method});y['AB'+str(k)]=m.meet(y['AB'+str(k)],model)

def rates_stage(state,steps,log):
    p,a,y=state['physical'],state['aux'],state['moments']
    for rate,key in [('rA','AA1'),('rB','BB1')]:
        def trial(value,rate=rate,key=key):
            hypothetical=dict(p);hypothetical[rate]=I.point(value)
            return m.pair_intervals(hypothetical,a,Z)[key[:-1]]
        scalar_bracket(state,'physical',rate,y[key],trial,True,steps,log)

def operate(state,kind,steps):
    if type(steps) is not int or not 0<=steps<=32:raise ValueError('scalar bracket cap')
    out=clone(state);log=[]
    try:
        if kind=='linear':base.linear(out)
        elif kind=='root':root_stage(out,steps,log)
        elif kind=='C':C_stage(out,steps,log)
        elif kind=='pulse':pulse_stage(out,steps,log)
        elif kind=='AB':AB_stage(out,steps,log)
        elif kind=='rates':rates_stage(out,steps,log)
        elif kind=='forward':
            model=m.selected(out['physical'],out['aux'])
            for key in FEATURES:out['moments'][key]=m.meet(out['moments'][key],model[key])
            log.append({'forward':{key:ir(value) for key,value in model.items()}})
        elif kind=='joint':
            out,detail=joint.operate(out,'joint');log.append({'joint':detail})
        else:raise ValueError('operator outside frozen complete schedule')
    except m.Inconsistent as error:error.stage_detail=log;raise
    except GuardUnavailable as error:log.append({'stage_guard':'UNRESOLVED','reason':str(error)})
    for group in out:
        for key,value in out[group].items():
            old=state[group][key]
            if value.lo<old.lo or value.hi>old.hi:raise ArithmeticError('stage enlarged a state coordinate')
    return out,{'operator':kind,'scalar_steps_per_side':steps,'details':log}
