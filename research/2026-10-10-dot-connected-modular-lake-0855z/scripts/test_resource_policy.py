#!/usr/bin/env python3
"""Bounded policy controls; never compile mathematical sources or call the core runner."""
from pathlib import Path
import copy, hashlib, json, tempfile, time, types
from unittest.mock import patch
import build_resource_qualified as q

results = []
def control(name, fn, rejects=False):
    try:
        fn()
    except (RuntimeError, FileNotFoundError):
        if not rejects:
            raise
        results.append({'control': name, 'status': 'PASS_REJECTED'})
    else:
        if rejects:
            raise AssertionError('Failed to reject: ' + name)
        results.append({'control': name, 'status': 'PASS'})

graph, required, count = q.verify_inputs()
template = (q.ROOT / 'scripts/AuditTemplate.lean').read_text()
control('all1439_source_versions_and_exact_graph_core_template', lambda: q.require(count == 1439, 'count'))
checks = 0
for label, g in graph['targets'].items():
    hashes = q.sources_for(g, template)
    for kind in hashes:
        args = dict(label=label, g=g, template=template,
                    name='Connected_' + ''.join(c if c.isalnum() or c in '_-' else '_' for c in label)
                         if kind == 'aggregate' else 'OwnedAudit',
                    source_hash=hashes[kind], obj=kind == 'aggregate',
                    imports=g['roots'] + ([] if kind == 'aggregate' else ['Lean.Util.CollectAxioms']),
                    seconds=300 if label == 'connected/compatible' else 180, memory=4096, kind=kind)
        value = q.invocation_policy(**args)
        assert value == (6144 if label in q.EXCEPTIONS else 4096)
        checks += 1
control('all156_generated_aggregate_and_audit_contracts_only4_invocations_get_new_cap',
        lambda: q.require(checks == 156, 'count'))
component_checks = 0
for label,g in graph['targets'].items():
    for name,e in g['modules'].items():
        theta = name == 'ThetaCertificate5' and e['sha256'] == q.THETA_SHA
        assert q.invocation_policy(label,g,template,name,e['sha256'],True,e['imports'],
                                   600 if theta else 180,6144 if theta else 4096,'component') == (6144 if theta else 4096)
        component_checks += 1
control('every_component_contract_retains_its_original_resource_policy', lambda: q.require(component_checks > 10000, 'count'))
label = 'connected/compatible'; g = graph['targets'][label]
args = dict(label=label,g=g,template=template,name='Connected_connected_compatible',
            source_hash=q.sources_for(g,template)['aggregate'],obj=True,imports=g['roots'],seconds=300,memory=4096,kind='aggregate')
for key,val in [('source_hash','0'*64),('obj',False),('imports',g['roots'][:-1]),('seconds',301),
                ('memory',8192),('kind','unknown'),('name','Connected_other')]:
    control('reject_changed_'+key, lambda k=key,v=val: q.invocation_policy(**(args|{k:v})), True)
control('reject_audit_selection_placeholder_change', lambda:q.sources_for(g,template+q.PLACEHOLDER),True)
with tempfile.TemporaryDirectory() as td:
    p=Path(td);obj=p/'objects';ext=p/'external';obj.mkdir();(ext/'Mathlib/Data').mkdir(parents=True)
    (ext/'Mathlib/Data/Card.olean').write_bytes(b'official-test-artifact')
    control('literal_external_namespace_resolution',lambda:q.require(q.first_namespace_file([obj,ext],'Mathlib.Data.Card')==ext/'Mathlib/Data/Card.olean','path'))
    (obj/'Mathlib/Data').mkdir(parents=True);(obj/'Mathlib/Data/FinEnum.olean').write_bytes(b'owned-test-artifact')
    control('reject_sparse_namespace_shadow_even_when_later_file_exists',lambda:q.first_namespace_file([obj,ext],'Mathlib.Data.Card'),True)
    (obj/'Mathlib/Data/Card.olean').symlink_to(ext/'Mathlib/Data/Card.olean')
    control('literal_overlay_path_matches_resolver',lambda:q.require(q.first_namespace_file([obj,ext],'Mathlib.Data.Card')==obj/'Mathlib/Data/Card.olean','path'))
    control('reject_missing_namespace',lambda:q.first_namespace_file([obj,ext],'Absent.Module'),True)
    fake=types.SimpleNamespace(bin=Path('/not-a-compiler'),run=p,active_label='test',attempt=0,
        _core=types.SimpleNamespace(safe=lambda x:x,save=lambda path,data:path.write_text(json.dumps(data))))
    with patch.object(q,'memory_kib',return_value={'MemAvailable':7168*1024-1,'MemTotal':10*1024*1024}):
        control('reject_insufficient_initial_headroom',lambda:q.guarded_call(fake,'test',lambda:True),True)
    with patch.object(q,'memory_kib',return_value={'MemAvailable':8192*1024,'MemTotal':10*1024*1024}):
        control('stable_memory_guard_returns_exact_call_value',lambda:q.require(q.guarded_call(fake,'test',lambda:17)==17,'return'))
    values=iter([{'MemAvailable':8192*1024,'MemTotal':10*1024*1024}])
    def low_memory():
        return next(values,{'MemAvailable':1023*1024,'MemTotal':10*1024*1024})
    with patch.object(q,'memory_kib',side_effect=low_memory):
        control('reject_pressure_even_if_call_returns',lambda:q.guarded_call(fake,'test',lambda:time.sleep(.03)),True)
    values=iter([{'MemAvailable':8192*1024,'MemTotal':10*1024*1024}])
    def uncertain():
        try:return next(values)
        except StopIteration:raise OSError('synthetic observation failure')
    with patch.object(q,'memory_kib',side_effect=uncertain):
        control('reject_uncertain_memory_observation',lambda:q.guarded_call(fake,'test',lambda:time.sleep(.03)),True)
    for name in ['scripts/build_connected.py','scripts/AuditTemplate.lean','DEPENDENCY-GRAPH.json']:
        with patch.object(q,'digest',side_effect=lambda path,n=name: '0'*64 if str(path).endswith(n) else hashlib.sha256(Path(path).read_bytes()).hexdigest()):
            control('reject_modified_'+name,lambda:q.verify_inputs(),True)
# Exercise the actual wrapper dispatch against a recording core, without Lean.
class RecordingCore:
    safe = staticmethod(lambda s: ''.join(c if c.isalnum() or c in '_-' else '_' for c in s))
    class Builder:
        def invoke(self, name, source, obj, imports, context, seconds, memory, kind):
            self.dispatched = (name,source,obj,imports,context,seconds,memory,kind)
            rec = {'cap_memory_mib':memory,'cap_seconds':seconds,
                   'command':['lean','-j1','-t0','-M'+str(memory),'-Ddebug.skipKernelTC=false'],
                   'status':self.synthetic_status,'exit_code':self.synthetic_exit,
                   'source_and_imports_stable':self.synthetic_stable,
                   'native_initialized_libraries_bound':True}
            return rec, Path('object') if obj and self.synthetic_exit==0 else None
with tempfile.TemporaryDirectory() as td:
    b=q.make_builder(RecordingCore)();b.graph=graph;b.active_label='connected/compatible'
    b.run=Path(td);b.audit_template=template;b.synthetic_status='PASS_FRESH_KERNEL_CHECK'
    b.synthetic_exit=0;b.synthetic_stable=True
    context=b.run/'targets/connected_compatible/objects';source=b.run/'aggregate.lean'
    source.write_text('\n'.join('import '+m for m in g['roots'])+'\n')
    with patch.object(q,'guarded_call',side_effect=lambda builder,kind,call:call()):
        control('actual_wrapper_dispatch_changes_only_memory_for_qualified_aggregate',
                lambda:q.require(b.invoke('Connected_connected_compatible',source,True,g['roots'],context,300,4096,'aggregate')[0]['cap_memory_mib']==6144,'cap'))
        assert b.dispatched==( 'Connected_connected_compatible',source,True,g['roots'],context,300,6144,'aggregate')
        audit=b.run/'audit.lean';audit.write_text(source.read_text()+template.replace(q.PLACEHOLDER,'#'+json.dumps(g['order'])).replace('"AUDIT-OWNED.json"','"AUDIT-RESULT.json"'))
        b.synthetic_stable=False
        control('reject_exit0_audit_with_unstable_bindings',lambda:b.invoke('OwnedAudit',audit,False,g['roots']+['Lean.Util.CollectAxioms'],context,300,4096,'complete-owned-audit'),True)
        b.synthetic_stable=True;b.synthetic_status='FAILED_OR_RESOURCE';b.synthetic_exit=1
        m=g['order'][0];e=g['modules'][m]
        control('component_failure_returns_to_original_failed_key_handler',lambda:q.require(b.invoke(m,q.ROOT/'source-store'/(e['sha256']+'.lean'),True,e['imports'],context,180,4096,'component')[0]['exit_code']==1,'failure'))
report={'status':'PASS_BOUNDED_CONFIGURATION_AND_POLICY_CONTROLS','wrapper_sha256':q.digest(q.__file__),
        'test_sha256':q.digest(__file__),'controls':results,'component_context_contracts_tested':component_checks,
        'generated_aggregate_audit_contracts_tested':checks,'mathematical_compiler_invoked':False,
        'fresh_public_layout_replay_claimed':False}
(q.ROOT/'POLICY-TEST-RESULTS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'controls':len(results),'component_contexts':component_checks,'aggregate_audit_contracts':checks}))
