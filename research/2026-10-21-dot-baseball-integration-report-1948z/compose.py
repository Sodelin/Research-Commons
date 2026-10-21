"""Coverage-aware value ledger. No statistical estimates are invented here."""
import math, datetime as dt
COMPONENTS=('batting','baserunning','fielding','position','league','replacement','pitching')
def compose(record):
    """Return a complete total only when all disjoint components are certified.

    'not_applicable' must be explicit with reason, not inferred from absence.
    Declared zero has same provenance requirements as a nonzero component.
    Complete means declaration-complete under the supplied model, not ground truth.
    Supplied semantic disjointness declarations are trusted, not independently certified.
    """
    required=('player_id','window_start','window_end','mode','reference_id','accounting_version','components')
    if any(k not in record for k in required):raise ValueError('missing ledger metadata')
    if record['mode'] not in ('forecast','retrospective'):raise ValueError('unknown mode')
    start=dt.date.fromisoformat(record['window_start']);end=dt.date.fromisoformat(record['window_end'])
    if start>=end or record.get('window_convention')!='[start,end)':raise ValueError('invalid half-open window')
    c=record['components']
    if set(c)-set(COMPONENTS):raise ValueError('aggregate or unknown component would double count')
    missing=[];subtotal=0.;sources=[]
    for name in COMPONENTS:
        v=c.get(name)
        if not v or v.get('status')=='missing':missing.append(name);continue
        if any(v.get(k)!=record[k] for k in ('player_id','window_start','window_end','window_convention','mode','reference_id','accounting_version')):raise ValueError('component identity/window/reference mismatch')
        if not v.get('source') or not v.get('definition'):raise ValueError('missing attribution/definition')
        if v.get('status')=='not_applicable':
            if not v.get('reason'):raise ValueError('not-applicable requires a reason')
            continue
        if v.get('status') not in ('available','partial') or v.get('units')!='runs':raise ValueError('unsupported component')
        if v['status']=='partial':missing.append(name)
        if any(v.get(k)!=record[k] for k in ('mode','reference_id','accounting_version')):raise ValueError('mixed reference, mode or version')
        if not v.get('source') or not v.get('definition'):raise ValueError('missing attribution/definition')
        x=v.get('value')
        if isinstance(x,bool) or not isinstance(x,(int,float)) or not math.isfinite(x):raise ValueError('nonfinite value')
        subtotal+=x;sources.append(v['source'])
    complete=not missing
    out={'player_id':record['player_id'],'supported_subtotal_runs':subtotal,'missing_components':missing,'coverage_complete':complete,'total_runs':subtotal if complete else None,'wins':None,'interpretation':'model-dependent accounting, not identified causal value','sources':sources}
    if 'runs_per_win' in record:
        rp=record['runs_per_win']
        if isinstance(rp,bool) or not isinstance(rp,(int,float)) or not math.isfinite(rp) or rp<=0 or not record.get('conversion_source'):raise ValueError('invalid conversion')
        if complete:out['wins']=subtotal/rp
    return out
