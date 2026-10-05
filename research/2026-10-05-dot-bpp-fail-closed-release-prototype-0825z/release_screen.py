"""Fail-closed release decisions for two frozen reviewed research profiles.
This module does not fit data, launch an engine, certify convergence, or admit new data.
"""
import argparse,hashlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
ROOT=BASE.parent
PIN_SHA='43a0f13a583b6a33610f4e55e5e4284871182ad329e911d984688bee924b898e'
PROFILES={'frog-a01','matched-synthetic-a00'}
def digest(raw):return hashlib.sha256(raw).hexdigest()
def read_evidence():
    raw=(BASE/'EVIDENCE-PINS.json').read_bytes()
    if digest(raw)!=PIN_SHA:raise ValueError('reviewed evidence manifest changed')
    pins=json.loads(raw);evidence={}
    for key,item in pins.items():
        p=Path(item['path'])
        if p.is_absolute() or '..' in p.parts:raise ValueError('unsafe evidence locator')
        path=ROOT/p
        if path.is_symlink():raise ValueError('symlink evidence')
        data=path.read_bytes()
        if digest(data)!=item['sha256']:raise ValueError('reviewed evidence changed: '+key)
        evidence[key]=json.loads(data) if p.suffix=='.json' else data.decode()
    return pins,evidence

def base_result(profile):
    return {'schema':'fail-closed-frozen-inference-release-v1','profile':profile,'artifact_kind':'release decision over frozen reviewed evidence','ranking_released':False,'ranked_histories':None,'recommended_history':None,'fit_or_execution_performed':False,'new_dataset_admitted':False,'convergence_certified':False,'calibration_certified':False}

def _decide(profile):
    out=base_result(profile)
    if profile not in PROFILES:
        return {**out,'status':'NOT_ADMITTED','message':'This dataset/model profile has not been admitted.','gates':{'dataset_and_model':'NOT_ADMITTED'},'evidence_sha256':{}}
    try:pins,e=read_evidence()
    except (OSError,ValueError,KeyError,TypeError) as error:
        return {**out,'status':'EVIDENCE_INVALID','message':'Inference is withheld because its reviewed evidence could not be authenticated.','gates':{'provenance':'FAILED'},'error_type':type(error).__name__,'evidence_sha256':{}}
    if not isinstance(pins,dict) or not isinstance(e,dict):raise ValueError('evidence mappings required')
    frog=e['frog_diagnostics'];matched=e['matched_pair']
    if not isinstance(frog,dict) or frog.get('schema')!='bpp-a01-diagnostics-v1' or not isinstance(frog.get('runs'),list):raise ValueError('frog diagnostic schema mismatch')
    if not isinstance(matched,dict) or matched.get('schema')!='matched-completed-pair-v1' or not isinstance(matched.get('runs'),list) or not isinstance(matched.get('pair_comparison'),dict):raise ValueError('matched diagnostic schema mismatch')
    out.update(status='WITHHELD_NUMERICAL_RELIABILITY',message='inference not yet numerically reliable',evidence_sha256={k:v['sha256'] for k,v in pins.items()},gates={'provenance':'AUTHENTICATED_FROZEN_REPORTS','dataset_and_model':'LIMITED_RESEARCH_FIXTURE_ONLY','numerical_reliability':'UNRESOLVED','repeated_simulation_calibration':'NOT_ESTABLISHED','empirical_model_adequacy':'NOT_ESTABLISHED','rank_release':'WITHHELD'})
    assumptions=['Independent loci; one shared nonrecombining genealogy per locus.','Four assigned populations under the MSC, JC69, strict clock and declared gamma priors.','Unphased diploid observations use the reviewed BPP phase handling.','Time/population parameters are mutation-scaled, not calendar dates.']
    out['target_assumptions']=assumptions
    if profile=='frog-a01':
        r=e['frog_diagnostics'];runs=[x for x in r['runs'] if x['run'] in ['A01-posterior-seed5511-long-v2','A01-posterior-seed6622-long-v2']]
        if len(runs)!=2 or any(x['usedata']!=1 or x['retained_samples']!=100000 for x in runs):raise ValueError('authenticated profile mismatch')
        out.update(target='A01 posterior over rooted four-population species-tree topologies; assignments fixed',candidate_evidence={'preserved':True,'source_sha256':pins['frog_diagnostics']['sha256'],'release_as_recommendation':False,'candidate_count_per_retained_chain':[len(x['topologies']) for x in runs]},diagnostics={'reason':'Replicate/within-chain topology and conditional-parameter discrepancies remain unresolved; no accepted stationarity gate.','same_budget_long_chains':2,'additional_short_posterior_chains':2,'prior_only_controls':2,'likelihood_considered':True,'auxiliary_synthetic_success_cannot_override_this_gate':True})
    else:
        r=e['matched_pair'];comparison=r['pair_comparison']['scalars']['lnL']
        out.update(target='A00 conditional posterior at a supplied fixed true topology, on one synthetic realization',diagnostics={'log_likelihood_means':comparison['means'],'log_likelihood_mean_gap':comparison['mean_difference'],'gap_over_combined_within_chain_heuristic_mcse':comparison['difference_over_heuristic_mcse'],'heuristic_ratio_is_not_a_calibrated_test':True,'reason':'Persistent between-seed log-likelihood discrepancy and first-chain block shift despite close selected population means.','completed_independent_seeds':2,'same_seed_timeout_recovery_is_not_a_third_chain':True},candidate_evidence={'preserved':True,'topology_ranking_performed':False,'release_as_recommendation':False})
        out['gates']['rank_release']='NOT_APPLICABLE_TO_FIXED_TOPOLOGY; WITHHELD'
    out['next_required_evidence']=['Resolve numerical exploration with a reviewed targeted tactic and independent diagnostics before releasing a ranking.','Implement the predeclared multi-chain/rank-normalized diagnostics and probability-specific Monte Carlo precision checks; thresholds are screens, not proofs.','Use repeated known-truth controls with an explicit calibration design and perform empirical adequacy/sensitivity checks.','Admit each new dataset and exact requested target separately; do not substitute an easier model or fixture.']
    return out

def decide(profile):
    try:return _decide(profile)
    except (OSError,ValueError,KeyError,TypeError,IndexError,AttributeError,OverflowError) as error:
        return {**base_result(profile),'status':'EVIDENCE_INVALID','message':'Inference is withheld because its reviewed evidence could not be authenticated or interpreted.','gates':{'provenance':'FAILED'},'error_type':type(error).__name__,'evidence_sha256':{}}

def main():
    p=argparse.ArgumentParser();p.add_argument('profile');a=p.parse_args();out=decide(a.profile);print(json.dumps(out,indent=2));return 2
if __name__=='__main__':raise SystemExit(main())
