"""Own-code finite impact models; never imports/executes Quinn's script or GDAL.
Synthetic cases establish mechanisms, not occurrence in either published study.
"""
import json
import ast
import hashlib
from math import ceil
from statistics import median


def row_model(fail=None, stale=None):
    files = dict(stale or {})
    trace = []
    errors = []
    outputs = [('viewshed','raw','fresh-binary'), ('compress','binary',None),
               ('weight','weighted-raw',None), ('compress-weighted','weighted',None)]
    dependencies = {'compress':'raw','weight':'binary','compress-weighted':'weighted-raw'}
    def stage(name, dst, value):
        src=dependencies.get(name)
        rc=1 if name==fail or (src is not None and src not in files) else 0
        if rc==0: files[dst]=value if value is not None else files[src]+('-weighted' if name=='weight' else '')
        trace.append({'stage':name,'exit':rc,'checked':False,'files_after':dict(files)})
    def remove(name):
        trace.append({'remove_in_memory_only':name})
        if name not in files: raise FileNotFoundError(name)
        del files[name]
    try:
        stage(*outputs[0]);stage(*outputs[1]);remove('raw')
        stage(*outputs[2]);stage(*outputs[3]);remove('weighted-raw')
    except FileNotFoundError as e: errors.append(str(e))
    finally: processed=1
    return dict(processed=processed,errors=errors,files=files,trace=trace)


def top_fraction(values, fraction):
    """Declared fixture rule: ceil(p*N_positive), descending values, index ties.
    The paper does not specify this rank/tie convention.
    """
    positive=[i for i,v in enumerate(values) if v>0]
    return sorted(sorted(positive,key=lambda i:(-values[i],i))[:ceil(fraction*len(positive))])


def run():
    cases={}
    for fail in [None,'viewshed','compress','weight','compress-weighted']:
        cases[str(fail)]=row_model(fail)
    assert cases['None']['files']=={'binary':'fresh-binary','weighted':'fresh-binary-weighted'}
    assert cases['viewshed']['processed']==1 and not cases['viewshed']['files']
    assert cases['compress-weighted']['errors']==[]
    assert cases['compress-weighted']['files']=={'binary':'fresh-binary'}
    assert cases['compress']['files']=={} # generated raw deleted after failed compression
    stale=row_model('compress',{'binary':'old-binary'})
    assert stale['files']['weighted']=='old-binary-weighted' and not stale['errors']
    cases['stale-binary-after-failed-compress']=stale

    # Exact finite-sum effects and independent downstream operations.
    partial=[0,1,2];missing=[1,0,1];full=[a+b for a,b in zip(partial,missing)]
    assert full==[1,1,3] and max(b-a for a,b in zip(partial,full))<=1
    max_cases=[([5,2,1],[5,3,1],False),([5,4,1],[5,6,1],True)]
    for a,b,changed in max_cases: assert (max(a)!=max(b))==changed
    median_cases=[([10,10,11],[10,10,12],False),([10,10,11],[10,11,11],True)]
    for a,b,changed in median_cases: assert (median(a)!=median(b))==changed
    # A high separation rank is stable; a near-boundary rank can change.
    a=list(range(1,19))+[152,153];b=a.copy();b[18]+=2
    assert top_fraction(a,.05)==[19] and top_fraction(b,.05)==[18]
    stable=a.copy();stable[19]=200
    assert top_fraction(stable,.05)==top_fraction([v+(1 if i%2 else 0) for i,v in enumerate(stable)],.05)
    # Nonzero-support changes can alter rank count without changing top values.
    support=list(range(1,21))+[0];new=support.copy();new[-1]=1
    assert top_fraction(support,.05)==[19] and top_fraction(new,.05)==[18,19]
    # Illustrative 1-km-grid rectangle aggregation, not ArcGIS reproduction.
    # Two 6x4 patches: 24 each, gap 5 -> no strict <5 merge; both <25 removed.
    # Add attached 1x1 cell toward other patch: area25, gap4 -> merged area >=49.
    polygon={'before':{'patch_areas':[24,24],'gap_km':5,'retained':[]},
             'after':{'patch_areas':[25,24],'gap_km':4,'minimum_merged_area':49,'retained':['combined']}}
    assert not polygon['before']['gap_km']<5 and polygon['after']['gap_km']<5
    assert all(x<25 for x in polygon['before']['patch_areas'])
    assert sum(polygon['after']['patch_areas'])>=25

    # Renaming a fit column leaves predictions untouched; replacing it may not.
    y=[1.,2.,0.];I=[0.,1.,0.];E=[0.,0.,1.];other=[1.,0.,0.]
    fitI=[x+2*t for x,t in zip(other,I)]
    renamed=fitI.copy()
    replaced=[x+2*t for x,t in zip(other,E)]
    sse=lambda z:sum((a-b)**2 for a,b in zip(y,z))
    assert sse(fitI)==sse(renamed)==0 and sse(replaced)==8
    # Even refitting E's unconstrained coefficient gives coefficient 0, SSE4.
    assert sse(other)==4
    return {'kind':'executed own-code synthetic impact controls; no historical run or paper reproduction',
            'row_cases':cases,'finite_sum':{'partial':partial,'missing':missing,'full':full},
            'max_examples':max_cases,'median_examples':median_cases,
            'rank_flip':{'partial':a,'full':b,'selected_partial':top_fraction(a,.05),'selected_full':top_fraction(b,.05)},
            'nonzero_support_change':{'partial':support,'full':new,'selected_partial':top_fraction(support,.05),'selected_full':top_fraction(new,.05)},
            'polygon_threshold_example':polygon,
            'fit_label_vs_geometry':{'rename_sse':0,'replace_fixed_coefficient_sse':8,'replace_refitted_coefficient_sse':4},
            'curvature_difference_m_using_6371000m_radius':{str(d):(.85714-.85417)*d*d/(2*6371000) for d in [10000,50000,100000,200000]},
            'all_assertions_passed':True}

def inspect_original(path):
    from pathlib import Path
    raw=Path(path).read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='7aee3ae34ee0f4fd9e6c686dde0813f0a9e29291ff0b33d2c6022d893c42ecff'
    tree=ast.parse(raw.decode())
    ignored=[n.lineno for n in ast.walk(tree) if isinstance(n,ast.Expr)
             and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute)
             and isinstance(n.value.func.value,ast.Name) and n.value.func.value.id=='os'
             and n.value.func.attr=='system']
    removes=[n.lineno for n in ast.walk(tree) if isinstance(n,ast.Call)
             and isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name)
             and n.func.value.id=='os' and n.func.attr=='remove']
    tries=[n for n in ast.walk(tree) if isinstance(n,ast.Try)]
    assert len(ignored)==4 and len(removes)==2 and len(tries)==1
    counters=[n.lineno for n in tries[0].finalbody if isinstance(n,ast.AugAssign)
              and isinstance(n.target,ast.Name) and n.target.id=='itemsProcessed']
    assert len(counters)==1
    return {'sha256':hashlib.sha256(raw).hexdigest(),'ignored_system_return_lines':ignored,
            'remove_lines':removes,'finally_counter_lines':counters,
            'original_executed':False,'original_read_as_AST_only':True}


if __name__=='__main__':
    import sys
    result=run()
    if len(sys.argv)>1: result['original_source_static_check']=inspect_original(sys.argv[1])
    print(json.dumps(result,indent=2))
