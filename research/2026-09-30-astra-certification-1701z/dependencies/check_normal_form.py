"""Reproducible exact checks. Does NOT execute the full bounded catalogue."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import ctypes as C
import ctypes.util
import hashlib
import json
import random
import sys
import platform
import sympy as sp
from cf_normal_form import *

HERE = Path(__file__).resolve().parent


def network(arcs, leaves, inheritance=None, x=F(1,2)):
    es = [Edge(a,b,x,f'e{i}') for i,(a,b) in enumerate(arcs)]
    return Network(es, {s:s for s in leaves}, inheritance or {})


def set_edges(net, replacements):
    return Network([Edge(e.parent,e.child,replacements.get(e.name,e.survival),e.name)
                    for e in net.edges],net.leaves.copy(),net.inheritance.copy())


def endpoint_values(net, mapping):
    return set_edges(net,{e.name:mapping[e.parent,e.child] for e in net.edges
                           if (e.parent,e.child) in mapping})


def add_tree(es, v, taxa, prefix, x=F(1,2)):
    if len(taxa)==1:
        es.append(Edge(v,taxa[0],x,f'{prefix}_leaf'))
        return
    mid=len(taxa)//2
    for j, group in enumerate((taxa[:mid],taxa[mid:])):
        if len(group)==1:
            child=group[0]
            es.append(Edge(v,child,x,f'{prefix}_{j}'))
        else:
            child=f'{prefix}_v{j}'
            es.append(Edge(v,child,x,f'{prefix}_{j}'))
            add_tree(es,child,group,f'{prefix}_{j}',x)


def root_fixture(kind, size=4, x=F(1,2), h=F(2,5), q=F(3,7)):
    """size genes on EACH of two root-module ports."""
    if kind=='middle':
        arcs=[('R','U'),('R','V'),('U','HA'),('V','HA'),('U','HB'),('V','HB')]
        ps=('HA','HB'); hs={'HA':h,'HB':q}
    elif kind=='arm':
        arcs=[('R','U'),('U','V'),('V','HA'),('R','HA'),('V','HB'),('U','HB')]
        ps=('HA','HB'); hs={'HA':h,'HB':q}
    elif kind=='triangle':
        arcs=[('R','U'),('U','HB'),('R','HB')]
        ps=('U','HB'); hs={'HB':q}
    else: raise ValueError(kind)
    es=[Edge(a,b,x,f'core{i}') for i,(a,b) in enumerate(arcs)]
    groups=([f'a{i}' for i in range(size)],[f'b{i}' for i in range(size)])
    for j,(port,taxa) in enumerate(zip(ps,groups)):
        es.append(Edge(port,f'P{j}',x,f'incident{j}'))
        add_tree(es,f'P{j}',taxa,f'down{j}',x)
    net=Network(es,{t:t for g in groups for t in g},hs)
    return net, ps


def core_a(net, ports, mechanism):
    """Insert four formal genes at the SAME two population boundary interfaces.

    Retain only the original core edges. Fresh two-tip trees have zero lengths;
    they are a computational boundary probe, not an admitted positive fixture.
    """
    es=[e for e in net.edges if e.name.startswith('core')]
    for i,port in enumerate(ports):
        es.extend([Edge(port,f'Z{i}',F(1),f'z{i}'),
                   Edge(f'Z{i}',f'z{i}a',F(1),f'z{i}a'),
                   Edge(f'Z{i}',f'z{i}b',F(1),f'z{i}b')])
    labels=['z0a','z0b','z1a','z1b']
    core_hybrids={h:p for h,p in net.inheritance.items() if any(e.child == h for e in es)}
    probe=Network(es,{s:s for s in labels},core_hybrids)
    return cf(probe,tuple(labels),mechanism)[0]


def replace_root(net,ports,mechanism):
    a=core_a(net,ports,mechanism)
    s=F(3,2)*(1-a)
    assert 0<s<1
    # Asymmetric split alpha=0, beta=t is permitted: both actual incident edges
    # retain strictly positive length. There is no new zero-length actual edge.
    es=[]
    for e in net.edges:
        if e.name.startswith('core'): continue
        if e.parent in ports:
            scale=s if e.parent==ports[1] else F(1)
            es.append(Edge('NEWROOT',e.child,e.survival*scale,e.name))
        else: es.append(e)
    remaining = {h:p for h,p in net.inheritance.items() if any(e.child == h for e in es)}
    return Network(es,net.leaves.copy(),remaining),s


def insert_bigon(net, edge_name, prefix, h=F(2,5), x1=F(2,3), x2=F(3,5)):
    edge=next(e for e in net.edges if e.name==edge_name)
    # Split old edge's survival into old survival and an added positive 1/2.
    # This fixture is a new original model; collapse includes both incident edges.
    es=[e for e in net.edges if e.name!=edge_name]
    U,H=prefix+'U',prefix+'H'
    es += [Edge(edge.parent,U,edge.survival,prefix+'up'),
           Edge(U,H,x1,prefix+'p0'),Edge(U,H,x2,prefix+'p1'),
           Edge(H,edge.child,F(1,2),prefix+'down')]
    hs=net.inheritance.copy();hs[H]=h
    return Network(es,net.leaves.copy(),hs)


def collapse_bigon(net,prefix,mechanism):
    U,H=prefix+'U',prefix+'H'
    ins=net.incoming(H);up=net.incoming(U)[0];down=net.outgoing(H)[0]
    h=net.inheritance[H]
    x1,x2=(e.survival for e in ins)
    s=(h*h*x1+(1-h)**2*x2+2*h*(1-h) if mechanism=='ind'
       else h*x1+(1-h)*x2)
    assert 0<s<1
    gone={e.name for e in ins}|{up.name,down.name}
    es=[e for e in net.edges if e.name not in gone]
    es.append(Edge(up.parent,down.child,up.survival*s*down.survival,prefix+'effective'))
    hs=net.inheritance.copy(); del hs[H]
    return Network(es,net.leaves.copy(),hs)


def z3_check(script, timeout_ms=10000):
    """Exact rational QF_NRA check through installed Z3 C API; unknown is retained."""
    path=ctypes.util.find_library('z3')
    if not path: return 'unavailable'
    lib=C.CDLL(path)
    lib.Z3_mk_config.restype=C.c_void_p
    lib.Z3_set_param_value.argtypes=[C.c_void_p,C.c_char_p,C.c_char_p]
    lib.Z3_mk_context.argtypes=[C.c_void_p];lib.Z3_mk_context.restype=C.c_void_p
    lib.Z3_del_config.argtypes=[C.c_void_p]
    lib.Z3_eval_smtlib2_string.argtypes=[C.c_void_p,C.c_char_p]
    lib.Z3_eval_smtlib2_string.restype=C.c_char_p
    lib.Z3_del_context.argtypes=[C.c_void_p]
    cfg=lib.Z3_mk_config()
    lib.Z3_set_param_value(cfg,b'timeout',str(timeout_ms).encode())
    ctx=lib.Z3_mk_context(cfg);lib.Z3_del_config(cfg)
    try:
        return lib.Z3_eval_smtlib2_string(ctx,script.encode()).decode().strip()
    finally: lib.Z3_del_context(ctx)


def main():
    receipt={'session':'ASTRA-BIO-PROVER-20260930-1612Z','kind':'exact finite checks; no full catalogue execution'}
    p,q,x,y=sp.symbols('p q x y')
    identities={}
    for kind in ('middle','arm','triangle'):
        net,ports=root_fixture(kind,size=2,x=F(1))
        if kind=='middle':
            net=endpoint_values(net,{('R','U'):x,('R','V'):y})
            net.inheritance={'HA':p,'HB':q}
            expected=sp.Rational(1,3)+sp.Rational(2,3)*(p-q)**2*(1-x*y)
        elif kind=='arm':
            net=endpoint_values(net,{('U','V'):x,('R','U'):y})
            net.inheritance={'HA':p,'HB':q}
            expected=sp.Rational(1,3)+sp.Rational(2,3)*((p-q)**2*(1-x)+(1-p)**2*(1-q*q*(1-x))*(1-y))
        else:
            net=endpoint_values(net,{('R','U'):x})
            net.inheritance={'HB':q}
            expected=sp.Rational(1,3)+sp.Rational(2,3)*(1-q)**2*(1-x)
        actual=core_a(net,ports,'ind')
        diff=sp.factor(actual-expected)
        assert diff==0,(kind,diff)
        identities[kind]={'difference':str(diff),'a0':str(expected)}
    receipt['root_zero_private_symbolic_identities']=identities

    # Validate all source conditions and all quartet replacements on eight taxa.
    rng=random.Random(1612)
    count=0; mixtures=0; cases=[]
    for kind in ('middle','arm','triangle'):
        for rep in range(5):
            original,ports=root_fixture(kind,size=4)
            values={e.name:F(rng.randrange(1,9),10) for e in original.edges}
            original=set_edges(original,values)
            original.inheritance={h:F(rng.randrange(1,9),10) for h in original.inheritance}
            original.source_check()
            for mech in ('ind','com'):
                reduced,s=replace_root(original,ports,mech)
                reduced.source_check()
                assert support(original)==support(reduced)
                for taxa in original.quartets():
                    a,b=cf(original,taxa,mech),cf(reduced,taxa,mech)
                    assert a==b,(kind,rep,mech,taxa,a,b)
                    assert sum(a)==1 and all(0<v<1 for v in a)
                    count+=1
                    if mech=='com':
                        assert a==common_cf_by_tree_mixture(original,taxa)
                        mixtures+=1
                cases.append({'kind':kind,'rep':rep,'mechanism':mech,'effective_survival':str(s)})
    receipt['positive_root_fixtures']=cases
    receipt['root_all_quartet_equalities']=count

    # Nonroot 4|4 split with chains, then simultaneous root and nonroot reduction.
    serial=0; allocations=set()
    for kind in ('middle','arm','triangle'):
        base,ports=root_fixture(kind,size=4)
        original=insert_bigon(base,'incident0','B0')
        original=insert_bigon(original,'B0down','B1',h=F(1,3))
        original=insert_bigon(original,'incident1','B2',h=F(3,4))
        original.source_check()
        for mech in ('ind','com'):
            reduced=original
            for pref in ('B1','B0','B2'):
                reduced=collapse_bigon(reduced,pref,mech)
            assert not any(h.startswith('B') for h in reduced.inheritance)
            reduced,_s=replace_root(reduced,ports,mech)
            reduced.source_check()
            assert support(original)==support(reduced)
            automatic, trace = normalize_two_port(original,mech)
            assert len(trace) == 4 and len(automatic.inheritance) == 0
            automatic.source_check()
            for taxa in original.quartets():
                assert cf(automatic,taxa,mech)==cf(reduced,taxa,mech)
                assert cf(original,taxa,mech)==cf(reduced,taxa,mech)
                allocations.add(sum(t.startswith('a') for t in taxa))
                serial+=1
    receipt['serial_root_nonroot_equalities']=serial
    receipt['automatic_normalizer_cross_checks']=serial
    receipt['sampled_side_allocations']=sorted(allocations)
    receipt['independent_common_tree_mixture_equalities']=mixtures

    # Recompute an inherited positive-parameter collision with a fresh implementation.
    tri=network([('R','P'),('R','D'),('P','Q'),('P','H'),('Q','C'),('Q','H'),('H','S'),('S','A'),('S','B')],
                ['A','B','C','D'],{'H':F(1,2)})
    tri=endpoint_values(tri,{('H','S'):F(45,47),('P','H'):F(9,10),('Q','H'):F(9,10),('P','Q'):F(1,10)})
    dia=network([('R','B'),('R','U'),('U','V'),('U','W'),('V','C'),('V','H'),('W','D'),('W','H'),('H','A')],
                ['A','B','C','D'],{'H':F(1,2)})
    dia=endpoint_values(dia,{('U','V'):F(3,4),('U','W'):F(3,4)})
    tri.source_check();dia.source_check()
    target=(F(1,4),F(3,8),F(3,8));taxa=('A','B','C','D')
    assert cf(tri,taxa,'ind')==cf(dia,taxa,'ind')==target
    assert support(tri)!=support(dia)
    receipt['inherited_collision']={'cf':list(map(str,target)),'different_supports':True}

    # A remaining LEVEL-TWO branching blob tests that outside reticulations survive.
    # This reuses ASTRA-OBS's admitted two-switch witness, not a new graph claim.
    lower=network([('R','D'),('R','v3'),('v3','v2'),('v3','HA'),('v2','v1'),('v2','HC'),
                   ('v1','v0'),('v1','HA'),('v0','B'),('v0','HC'),('HA','A'),('HC','C')],
                  ['A','B','C','D'],{'HA':F(2,5),'HC':F(1,3)})
    lower.source_check()
    base,ports=root_fixture('middle',size=4)
    removed=nx.descendants(base.dag(),'P0')|{'P0'}
    es=[e for e in base.edges if e.parent not in removed]
    mapping={v:('P0' if v=='R' else 'a'+str('ABCD'.index(v)) if v in 'ABCD' and len(v)==1 else 'G_'+v)
             for v in lower.dag()}
    es += [Edge(mapping[e.parent],mapping[e.child],e.survival,'G_'+e.name) for e in lower.edges]
    hs=base.inheritance.copy();hs.update({mapping[h]:p for h,p in lower.inheritance.items()})
    composed=Network(es,base.leaves.copy(),hs)
    composed=insert_bigon(composed,'incident0','I0')
    lower_entry=next(e.name for e in composed.edges if e.parent=='P0' and e.child=='G_v3')
    composed=insert_bigon(composed,lower_entry,'I1',h=F(3,5))
    composed.source_check()
    remaining_count=0
    for mech in ('ind','com'):
        normalized,trace=normalize_two_port(composed,mech)
        normalized.source_check()
        assert len(trace)==3 and set(normalized.inheritance)=={'G_HA','G_HC'}
        assert support(composed)==support(normalized)
        for q4 in composed.quartets():
            assert cf(composed,q4,mech)==cf(normalized,q4,mech)
            remaining_count+=1
    receipt['remaining_level_two_blob_interface_equalities']=remaining_count

    # Small exhaustive grammar slice for classification, not the n>=4 catalogue.
    tiny_counts={};tiny_root_counts={}
    for tiny in complete_source_catalogue(2,max_reticulations=2):
        info=tiny.source_check();r=len(tiny.inheritance)
        tiny_counts[r]=tiny_counts.get(r,0)+1
        ug=nx.Graph()
        ug.add_edges_from((e.parent,e.child) for e in tiny.edges if e.name not in info['bridges'])
        internal=set(tiny.dag())-set(tiny.leaves)
        if len(ug)>0 and set(ug)==internal and nx.is_connected(ug):
            tiny_root_counts[r]=tiny_root_counts.get(r,0)+1
            for mech in ('ind','com'):
                normalized,tr=normalize_two_port(tiny,mech)
                assert len(tr)==1 and len(normalized.inheritance)==0
                normalized.source_check()
    assert tiny_counts=={0:1,1:4,2:22}
    assert tiny_root_counts=={1:2,2:6}
    receipt['two_port_grammar_slice']={'taxa':2,'r_cap':2,'ordered_graph_counts':tiny_counts,
        'single_root_blob_counts':tiny_root_counts,'positive_normalizations':16}

    # Source-admission negative fixtures: actual zero lengths/endpoints are rejected.
    bad=network([('R','A'),('R','B')],['A','B'])
    bad=set_edges(bad,{bad.edges[0].name:F(1)})
    try: bad.source_check()
    except ValueError: pass
    else: raise AssertionError('zero population length admitted')
    bad=Network(tri.edges,tri.leaves,{'H':F(0)})
    try: bad.source_check()
    except ValueError: pass
    else: raise AssertionError('zero inheritance admitted')
    receipt['negative_parameter_admission_checks']=2

    # Complete only the r=0 slice, not the full network catalogue.
    trees=list(complete_source_catalogue(4,max_reticulations=0))
    targets={support(t) for t in trees}
    assert len(targets)==3
    receipt['complete_tree_slice']={'n':4,'r_cap':0,'labelled_ordered_graphs':len(trees),'distinct_unrooted_targets':len(targets)}

    # Exact single-image solver checks, not all-class classifications.
    tree=network([('R','U'),('R','V'),('U','A'),('U','B'),('V','C'),('V','D')],['A','B','C','D'])
    tasks={
      'positive_tree':(tree,{taxa:(F(2,3),F(1,6),F(1,6))},'ind',False,'sat'),
      'uniform_positive_tree_excluded':(tree,{taxa:(F(1,3),)*3},'ind',False,'unsat'),
      'anomalous_cf_tree_excluded':(tree,{taxa:target},'ind',False,'unsat'),
      'collision_triangle_ind':(tri,{taxa:target},'ind',False,'sat'),
      'collision_diamond_ind':(dia,{taxa:target},'ind',False,'sat'),
      'collision_triangle_com_excluded':(tri,{taxa:target},'com',False,'unsat'),
      'collision_diamond_com':(dia,{taxa:target},'com',False,'sat'),
      'positive_tree_box':(tree,{taxa:((F(3,5),F(7,10)),(F(1,10),F(1,5)),(F(1,10),F(1,5)))},'ind',True,'sat'),
      'uniform_singleton_tree_box_excluded':(tree,{taxa:((F(1,3),F(1,3)),)*3},'ind',True,'unsat'),
    }
    solver={}
    for name,(net,obs,mech,boxes,expected) in tasks.items():
        smt=model_image_smt(net,obs,mech,boxes)
        (HERE/(name+'.smt2')).write_text(smt)
        out=z3_check(smt)
        assert out==expected,(name,out,expected)
        solver[name]=out
    receipt['single_image_qfnra']=solver
    controller_cases=[]
    for description,obs,engine,budget,expected in [
      ('tree_slice_unique_not_all_class',{taxa:(F(2,3),F(1,6),F(1,6))},z3_check,None,'unique'),
      ('tree_slice_infeasible_not_all_class',{taxa:target},z3_check,None,'infeasible'),
      ('interrupted_slice_abstains',{taxa:target},z3_check,1,'incomplete'),
      ('unknown_solver_abstains',{taxa:target},lambda s:'unknown',None,'incomplete')]:
        res=classify_global_cf(taxa,obs,engine,max_reticulations=0,max_graphs=budget)
        assert res['enumerated_scope_status']==expected
        assert res['full_class_status']=='INCONCLUSIVE'
        assert res['all_class_outer_candidates']=='ALL_ADMITTED_TARGETS'
        controller_cases.append({'case':description,'visited':res['graphs_visited'],
            'scope_status':expected,'full_class_status':res['full_class_status']})
    receipt['catalogue_controller_guards']=controller_cases
    receipt['environment']={'python':sys.version.split()[0],'sympy':sp.__version__,'networkx':nx.__version__,'platform':platform.platform(),'z3_library':ctypes.util.find_library('z3')}
    receipt['not_executed']=['full r<=2n-3 catalogue','full all-target classification run','algebraic-input front end','formal proof assistant','independent human review','biological experiment']
    receipt['hashes']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in sorted(HERE.glob('*')) if p.suffix in ('.py','.smt2')}
    (HERE/'checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('positive_root_fixtures','hashes')},indent=2))


if __name__=='__main__': main()
