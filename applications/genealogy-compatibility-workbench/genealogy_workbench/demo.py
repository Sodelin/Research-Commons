"""Runnable synthetic end-to-end ambiguity, refinement and confidence example."""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import copy,json,random
from .core import Source,Experiment,law,law_entries,FAMILY
from .cli import run,summary
from .provenance import receipt


def source(sid,a='1/3',x='2/3',y='1/3',g='1/2',b='1/2',label='low-survival'):
    return {'source_id':sid,'family':FAMILY,'parameters':dict(zip(['leading','left','right','weight','trailing'],[a,x,y,g,b])),
        'arm_ids':['original-left','original-right'],'target_label':label}

def experiment(n,readout='full_forest'):
    return {'experiment_id':f'interface-{n}-{readout}','readout':readout,
        'entering_roots':[{'copy_id':f'A-copy-{i+1}','original_taxon_id':'A'} for i in range(n)]}

def fixtures():
    truth=source('true-source');swap=source('arm-swapped',x='1/3',y='2/3')
    pad=source('different-pad-placement',a='1/2',b='1/3')
    high=source('high-survival',a='9/10',b='9/10',x='9/10',y='9/10',g='1/2',label='high-survival')
    cat={'catalogue_id':'synthetic-one-bigon-demo','coverage':'only_listed_sources','sources':[truth,swap,pad,high]}
    def exact_job(n,kind='canonical_source'):
        e=experiment(n)
        return {'schema':'genealogy-workbench/job-v1','catalogue':copy.deepcopy(cat),'experiments':[e],'target':{'kind':kind},
            'exact_observations':[{'experiment_id':e['experiment_id'],'probabilities':law_entries(Source.read(truth),Experiment.read(e))}]}
    e=experiment(2,'root_count');dist=law(Source.read(truth),Experiment.read(e));den=lcm(*(p.denominator for p in dist.values()))
    rng=random.Random(20261002);records=[]
    for i in range(256):
        draw=rng.randrange(den);cumulative=0
        for outcome,p in sorted(dist.items()):
            cumulative+=int(p*den)
            if draw<cumulative:break
        records.append({'locus_id':f'fresh-locus-{i+1}','experiment_id':e['experiment_id'],'outcome':outcome})
    records.append(copy.deepcopy(records[0]))
    statistical={'schema':'genealogy-workbench/job-v1','catalogue':copy.deepcopy(cat),'experiments':[e],
        'target':{'kind':'catalogue_label'},'sampling':{'unit':'one_joint_outcome_per_locus','independent_fresh_loci':True,
        'fixed_row_laws':True,'row_selected_before_outcome':True,'channel':'declared_interface_readout','alpha':'1/20','eta':'0'},'records':records}
    inference_e=experiment(4)
    inference={'source_family_promise':FAMILY,'experiment':inference_e,'probabilities':law_entries(Source.read(source('nondegenerate-inference',x='1/2',y='3/4',g='1/3')),Experiment.read(inference_e))}
    return {'recover-trailing-survival':('recover-trailing-four',inference),'cap4-ambiguous':('sort-exact',exact_job(4)), 'cap5-refined':('sort-exact',exact_job(5)),
        'original-arm-abstention':('sort-exact',exact_job(5,'original_arm_assignment')),
        'fresh-loci-conditional':('sort-loci',statistical),
        'theorem-derived-equivalence':('equivalent',{'left':truth,'right':swap})}

def demo(output_dir):
    output_dir=Path(output_dir);output_dir.mkdir(parents=True,exist_ok=True);results={}
    for name,(operation,data) in fixtures().items():
        output=receipt(operation,data,run(operation,data));results[name]=output['result']
        (output_dir/(name+'.input.json')).write_text(json.dumps(data,indent=2)+'\n')
        (output_dir/(name+'.receipt.json')).write_text(json.dumps(output,indent=2)+'\n')
        (output_dir/(name+'.txt')).write_text(summary(output))
    checks={'four_root_trailing_survival_recovered':results['recover-trailing-survival']['answer']=={'trailing_survival':'1/2'},'cap4_retains_different_pads':results['cap4-ambiguous']['status']=='ABSTAIN_AMBIGUOUS',
        'cap5_refines_to_passive_orbit':results['cap5-refined']['status']=='CERTIFIED_WITHIN_CATALOGUE',
        'original_arm_assignment_abstains':results['original-arm-abstention']['status']=='ABSTAIN_AMBIGUOUS',
        'fresh_loci_conditional_target':results['fresh-loci-conditional']['status']=='CONDITIONAL_CERTIFICATE_WITHIN_CATALOGUE',
        'duplicate_locus_not_counted_twice':results['fresh-loci-conditional']['independent_observation_units']==256 and results['fresh-loci-conditional']['identical_same_locus_duplicates_ignored']==1,
        'arm_swap_theorem_relation':results['theorem-derived-equivalence']['equivalent']}
    if not all(checks.values()):raise ArithmeticError('Synthetic demo failed its expected outcomes')
    report={'status':'PASS','checks':checks,'output_dir':str(output_dir),'synthetic_input_only':True,
        'summary':{'cap4':results['cap4-ambiguous']['compatible_source_ids'],'cap5':results['cap5-refined']['compatible_source_ids'],
        'fresh_loci':results['fresh-loci-conditional']['answer'],'physical_or_biological_validation':False}}
    (output_dir/'demo-summary.json').write_text(json.dumps(report,indent=2)+'\n')
    (output_dir/'README.md').write_text('# Synthetic end-to-end example\n\nFour-root exact laws retain two different pad placements. Five-root full laws separate the pad placements in this particular catalogue, while passive arm exchange remains indistinguishable. Requesting original-arm assignments therefore abstains. A separate two-root/count experiment filters 256 synthetic fresh loci with an all-time conditional confidence contract; one copied record is ignored.\n\nNo general five-root determining cutoff, unknown-size recognition or biological validity is claimed. Input jobs, content-bound replay receipts and plain-text summaries are included.\n')
    return report
