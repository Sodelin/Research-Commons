"""Bind the one already admitted generated dataset; no sampling or feature evaluation."""
import json
from pathlib import Path
import integration_core as c
BASE=Path(__file__).resolve().parent
GENERATOR=BASE.parent/'bpp-model-semantic-execution-20261005-1748z'
DATA_SHA='4ae2d541515bf87d1709d3708e74af9f2c2ac2ae35ed60d38456050b3ef60e03'
OLD_REGISTRY_SHA='bb75317a350a2d8d24d629154da48cc6d04796dc7e2a8c787fc71a39cf1de860'

def write(path,value):
    raw=c.canonical(value)
    with Path(path).open('xb') as out:out.write(raw)
    return c.sha(raw)
def prepare(folder):
    folder=Path(folder);folder.mkdir(exist_ok=False)
    generation=c.read(BASE/'GENERATION-RECEIPT.json',c.GENERATION_RECEIPT_SHA)
    if generation['dataset_sha256']!=DATA_SHA or generation['loci']!=1024 or generation['classification']!='synthetic_model_check':raise ValueError('fixed runtime-admitted sample identity')
    if c.sha((BASE/'GENERATION-REVIEW.md').read_bytes())!=c.GENERATION_REVIEW_SHA:raise ValueError('runtime review identity')
    raw=(GENERATOR/'admission-attempt1/DATASET.json').read_bytes()
    if c.sha(raw)!=DATA_SHA:raise ValueError('generated data changed')
    with (folder/'DATASET.json').open('xb') as out:out.write(raw)
    prior=c.read(c.PROVIDER/'declared-requests/distinct.json','a73fc025632555e058b8dc6f2c1440e6f625409caefd36ae56b660f0ba79cedb')
    budget=dict(prior['budget']);budget.update(max_stages=16,max_splits=0,max_states=1,max_depth=0,wall_ms=120000,recovery_wall_ms=120000,recovery_max_stages=16)
    request={'schema':'phased-nine-feature-analysis-v1','dataset_sha256':DATA_SHA,'admission_sha256':'pending','delta':'1/10','domain':prior['box'],'normalized_width_targets':prior['normalized_width_targets'],'inverse_budget':budget,'radius_steps':16,'expected_loci':1024,'selection_sha256':generation['selection_sha256'],'provenance':{'kind':'single_predeclared_official_model_generation','seed':202610051,'new_generation_performed_by_this_adapter':False,'ideal_model_only_statistical_bound':True}}
    admission={'schema':'reviewed-phased-design-v1','model':c.MODEL,'dataset_sha256':DATA_SHA,'analysis_premises_sha256':c.premise_identity(request),'selection_sha256':generation['selection_sha256'],'locus_count':1024,'classification':'synthetic_model_check','premises':{f'A{i}':'ideal_model_semantics_reviewed_finite_rng_not_certified' for i in range(1,7)},'review_notes':'One frozen BPP 4.8.7 generated panel; ideal coalescent/current-block/JC source semantics reviewed. The finite PRNG/floating program is not certified as an exact iid sampler. No empirical or exact finite-program confidence release. Known truth and latent trees are evaluation only.','generation_receipt_sha256':c.GENERATION_RECEIPT_SHA,'generation_review_sha256':c.GENERATION_REVIEW_SHA}
    admission_sha=write(folder/'ADMISSION.json',admission);request['admission_sha256']=admission_sha;request_sha=write(folder/'REQUEST.json',request)
    registry=c.read(BASE/'declared-protocols/ADMISSION-REGISTRY.json',OLD_REGISTRY_SHA)
    registry['admissions'][admission_sha]={'classification':'synthetic_model_check','review_scope':'ideal_source_generation_with_uncertified_finite_rng'}
    registry_sha=write(folder/'ADMISSION-REGISTRY.json',registry)
    manifest={'schema':'one-predeclared-model-check-v1','dataset_sha256':DATA_SHA,'admission_sha256':admission_sha,'request_sha256':request_sha,'registry_sha256':registry_sha,'generation_receipt_sha256':c.GENERATION_RECEIPT_SHA,'generation_review_sha256':c.GENERATION_REVIEW_SHA,'one_existing_dataset_only':True,'generator_runs_added':0,'exact_finite_program_confidence_claimed':False}
    return write(folder/'CONTROL-MANIFEST.json',manifest)
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();print(prepare(a.output))
