"""Read-only resource/progress classification. No truncated posterior summaries."""
import hashlib,json,re
from pathlib import Path
BASE=Path(__file__).resolve().parent
RUN=BASE/'runs/A00-matched-seed21101'
BENCH=BASE.parent/'bpp-sequence-pilot-20261005/runs/A00-instrumented-seed10101'
EXPECTED=[(42,489),(56,455),(56,440),(48,285),(60,457)]
def sha(data):return hashlib.sha256(data).hexdigest()
def authenticated(folder):
    tb=(folder/'TERMINAL.json').read_bytes();t=json.loads(tb);inv={x['path']:x['sha256'] for x in t['output_inventory']}
    def read(name):
        raw=(folder/name).read_bytes()
        if sha(raw)!=inv[name]:raise ValueError('output changed: '+name)
        return raw
    return t,read,sha(tb)
def phase_patterns(log):
    rows={}
    for index,n,L,ambig,patterns in re.findall(r'^\s*(\d+)\s*\|\s*JC69\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|',log,re.M):
        i=int(index);n=int(n);L=int(L)
        if 1<=i<=5 and (n,L)==EXPECTED[i-1]:
            if i in rows:raise ValueError('duplicate post-phase locus')
            rows[i]={'locus':i,'gene_copies':n,'sites':L,'engine_ambiguous_site_count':int(ambig),'phase_expanded_patterns':int(patterns)}
    if set(rows)!=set(range(1,6)):raise ValueError('missing post-phase inventory')
    return [rows[i] for i in range(1,6)]
def main():
    t,read,th=authenticated(RUN);old,readold,oldth=authenticated(BENCH)
    if t['status']!='RESOURCE_TIME_LIMIT' or not t['inputs_stable'] or old['status']!='EXECUTION_EXIT_ZERO':raise ValueError('unexpected outcome scope')
    raw=read('result.mcmc.txt');lines=raw.splitlines(keepends=True);header=lines[0].decode().split();complete=[];incomplete=0
    for line in lines[1:]:
        if not line.endswith(b'\n') or len(line.split())!=len(header):incomplete+=1;continue
        complete.append(int(line.split()[0]))
    if complete!=list(range(20,20*(len(complete)+1),20)):raise ValueError('retained-generation sequence mismatch')
    log=read('stdout.log').decode();patterns=phase_patterns(log);oldpatterns=phase_patterns(readold('stdout.log').decode())
    gene_counts={}
    for i in range(1,6):
        data=read(f'result.gtree.L{i}');parts=data.splitlines(keepends=True);gene_counts[str(i)]={'complete_newline_records':sum(x.endswith(b'\n') for x in parts),'incomplete_tail_records':sum(not x.endswith(b'\n') for x in parts)}
    return {'schema':'matched-resource-outcome-v1','status':'RESOURCE_LIMITED_NO_POSTERIOR_RESULT','terminal_sha256':th,'engine_exit_code':t['exit_code'],'elapsed_seconds':t['elapsed_seconds'],'aggregate_final_bytes':t['aggregate_final_bytes'],'cap_overshoot_final_bytes':t['cap_overshoot_final_bytes'],'watchdog_result':t['watchdog_result'],'requested_retained_samples':5000,'complete_retained_scalar_rows':len(complete),'last_retained_sampling_generation':complete[-1] if complete else None,'incomplete_scalar_tail_rows':incomplete,'genealogy_record_inventory_only':gene_counts,'synthetic_phase_expanded_inventory':patterns,'synthetic_phase_expanded_total':sum(x['phase_expanded_patterns'] for x in patterns),'benchmark_phase_expanded_inventory':oldpatterns,'benchmark_phase_expanded_total':sum(x['phase_expanded_patterns'] for x in oldpatterns),'benchmark_terminal_sha256':oldth,'second_inference_run':False,'second_inference_gate':'BLOCKED: first required complete output missing','posterior_means_computed_from_partial_trace':False,'calibration_or_convergence_claimed':False,'budget_or_data_changed':False,'interpretation':'Layout/scale matching does not imply equal phase-expansion workload or numerical difficulty. This is an execution-budget outcome, not a statistical recovery failure or software-defect finding.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
