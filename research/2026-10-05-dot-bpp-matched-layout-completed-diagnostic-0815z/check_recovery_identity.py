"""Authenticate both attempts and compare the preserved prefix; no convergence inference."""
import hashlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
ORIGINAL='A00-matched-seed21101';RECOVERY='A00-matched-recovery-seed21101'
ORIGINAL_TERMINAL_SHA='155160e2db42a91db6c8e5d393ab237554ef256999df5e9206c9f237dfbb57e8'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def authenticated(name):
    folder=BASE/'runs'/name;raw=(folder/'TERMINAL.json').read_bytes();t=json.loads(raw)
    paths=[x['path'] for x in t['output_inventory']]
    if len(paths)!=len(set(paths)):raise ValueError('duplicate inventory path')
    evidence={}
    for item in t['output_inventory']:
        path=Path(item['path'])
        if path.is_absolute() or '..' in path.parts:raise ValueError('unsafe inventory path')
        p=folder/path
        if p.is_symlink():raise ValueError('symlink inventory')
        data=p.read_bytes()
        if len(data)!=item['bytes'] or sha(data)!=item['sha256']:raise ValueError('changed inventory bytes')
        evidence[item['path']]=data
    return t,sha(raw),evidence

def main():
    a,ah,ab=authenticated(ORIGINAL);b,bh,bb=authenticated(RECOVERY)
    if ah!=ORIGINAL_TERMINAL_SHA or a['status']!='RESOURCE_TIME_LIMIT':raise ValueError('original changed')
    if b['status']!='EXECUTION_EXIT_ZERO' or not a['inputs_stable'] or not b['inputs_stable']:raise ValueError('complete stable recovery required')
    for key in ['settings','command','address_space_limit_bytes','aggregate_attempt_limit_bytes','threads','conditional_topology']:
        if a[key]!=b[key]:raise ValueError('target/profile difference: '+key)
    for key in ['binary','watchdog','projector','admission','control','alignment','map']:
        if a['input_hashes_before'][key]!=b['input_hashes_before'][key]:raise ValueError('input difference: '+key)
    if (a['wall_limit_seconds'],b['wall_limit_seconds'])!=(600,1800):raise ValueError('unexpected budgets')
    prefix={}
    for name in ['result.mcmc.txt']+[f'result.gtree.L{i}' for i in range(1,6)]:
        old=ab[name];end=old.rfind(b'\n')+1;complete=old[:end]
        prefix[name]={'complete_prefix_bytes':end,'complete_prefix_sha256':sha(complete),'matches_recovery_byte_prefix':bb[name].startswith(complete),'excluded_unterminated_tail_bytes':len(old)-end}
    return {'schema':'same-seed-recovery-identity-v1','original_terminal_sha256':ah,'recovery_terminal_sha256':bh,'identical_target_and_seed_verified':True,'different_independent_chain_claimed':False,'checkpoint_resume_claimed':False,'original_preserved':True,'prefix_comparisons':prefix,'prefix_identity_is_not_convergence_evidence':True}
if __name__=='__main__':print(json.dumps(main(),indent=2))
