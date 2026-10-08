"""Raubeson/Tsuga paper-summary comparison and original solver controls.
All exact law values are SYNTHETIC, not estimates from Holman et al. data.
Run from repository root with the documented pinned solver environment.
"""
from pathlib import Path
import argparse, copy, datetime, hashlib, json, platform, subprocess, sys, time, os

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[2]
ORIGINAL = REPO / 'research/2026-10-04-dot-practical-solver-recovery-1803z/01-exact-source-solver/package'


def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', default=str(BASE / 'CWU-RUNS'))
    args = parser.parse_args()
    out = Path(args.output).resolve(); out.mkdir(parents=True, exist_ok=True)
    metadata = json.loads((BASE / 'DRYAD-DATASET-METADATA.json').read_text())
    assert metadata['identifier'] == 'doi:10.5061/dryad.2r12j'
    assert metadata['license'] == 'https://spdx.org/licenses/CC0-1.0.html'
    # Hand-transcribed relationship statements from the abstract; not a full tree.
    nuc = {'Tsuga_chinensis', 'Tsuga_caroliniana'}
    cp = {'Tsuga_chinensis', 'Tsuga_sieboldii_Japan'}
    incompatible = bool(nuc & cp) and not nuc <= cp and not cp <= nuc
    assert incompatible
    summary = {
        'schema': 'raubeson-tsuga-paper-summary-control-v1',
        'question': 'What does reported nuclear/chloroplast topology disagreement establish, and what needs empirical solver admission?',
        'source': {'doi': '10.1600/036364417X696474', 'dataset_doi': metadata['identifier'], 'metadata_sha256': digest(BASE/'DRYAD-DATASET-METADATA.json'), 'license': metadata['license']},
        'baseline': {'input_kind': 'abstract reported sister clades, hand-transcribed', 'nuclear_sister_clade': sorted(nuc), 'chloroplast_sister_clade': sorted(cp), 'same_rooted_tree_clades_compatible': not incompatible, 'proof': 'Rooted-tree descendant clades are nested or disjoint; these intersect only at T.chinensis and neither contains the other.'},
        'biological_conclusion': 'UNKNOWN: incompatible reported trees do not choose chloroplast capture versus other explanations.',
        'empirical_admission': 'NOT_ADMITTED_TO_EMPIRICAL_SOLVER',
        'no_confidence_interval': 'No gene-tree count/sample design/calibrated law was admitted; strong/moderate paper support is not a numerical probability here.',
        'original_solver_controls': [],
        'plant_alphagenome_use': False,
        'professor_contact_or_endorsement': False,
    }
    req = json.loads((ORIGINAL/'examples/passive-quartet-policy.json').read_text())
    req['limits'] = {'seconds': 20, 'max_sources': 30, 'smt_milliseconds': 5000}
    req['taxa'] = ['Tsuga_chinensis','Tsuga_caroliniana','Tsuga_sieboldii_Japan','Tsuga_diversifolia']
    req['rows'][0]['samples'] = {t: ['L'+str(i)] for i,t in enumerate(req['taxa'])}
    # Fixed rational illustration only, with no paper frequency or bootstrap substitution.
    for i, item in enumerate(req['rows'][0]['law']): item['p'] = '4/5' if i == 0 else '1/10'
    requests = {'synthetic_nuclear_like': req}
    plastid = copy.deepcopy(req)
    for i, item in enumerate(plastid['rows'][0]['law']): item['p'] = '4/5' if i == 1 else '1/10'
    requests['synthetic_plastid_like'] = plastid
    refused = copy.deepcopy(req)
    refused['empirical_admission'] = {
        'status': 'NOT_ADMITTED_TO_EMPIRICAL_SOLVER',
        'certificate_sha256': '6fc8d0850973ec9a65be678773330154b99b11f3f90ac316ca438e35fac76314',
        'source_file_bytes_verified': False,
        'metadata_inventory_count': 4,
        'law_inputs_derived_from_data': False,
    }
    requests['empirical_tsuga_refusal'] = refused
    for name, request in requests.items():
        rdir = out/name; rdir.mkdir(exist_ok=True)
        rpath=rdir/'REQUEST.json';rpath.write_text(json.dumps(request,indent=2)+'\n')
        commands=[]
        for stage, command in [('producer',[sys.executable,str(ORIGINAL/'solver.py'),str(rpath),'--output',str(rdir)]),('checker',[sys.executable,str(ORIGINAL/'verify_certificate.py'),str(rdir/'RESULT.json'),'--replay-backend'])]:
            start=datetime.datetime.now(datetime.timezone.utc).isoformat(); t=time.monotonic()
            p=subprocess.run(command,cwd=ORIGINAL,text=True,capture_output=True,timeout=50,env={**os.environ,"PYTHONDONTWRITEBYTECODE":"1"})
            (rdir/(stage+'.stdout')).write_text(p.stdout);(rdir/(stage+'.stderr')).write_text(p.stderr)
            commands.append({'stage':stage,'command':command,'started_utc':start,'ended_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'exit_code':p.returncode,'stdout_sha256':digest(rdir/(stage+'.stdout')),'stderr_sha256':digest(rdir/(stage+'.stderr'))})
        result=json.loads((rdir/'RESULT.json').read_text()); checker=json.loads((rdir/'checker.stdout').read_text())
        if name=='empirical_tsuga_refusal':
            assert result['status']=='UNKNOWN_UNSUPPORTED_OR_UNADMITTED_CONTRACT'
            assert checker['status']=='PASS_HONEST_ADMISSION_REJECTION'
        else:
            assert result['status']=='IDENTIFIED_TARGET_COMPLETE_KNOWN_REGISTRY'
            assert checker['status']=='PASS_SOURCE_AND_CERTIFICATE_RECOMPUTATION'
        (rdir/'EXECUTION-RECEIPT.json').write_text(json.dumps({'commands':commands,'status':result['status'],'input_sha256':digest(rpath),'result_sha256':digest(rdir/'RESULT.json'),'python':platform.python_version(),'producer_sha256':digest(ORIGINAL/'solver.py'),'checker_sha256':digest(ORIGINAL/'verify_certificate.py')},indent=2)+'\n')
        summary['original_solver_controls'].append({'name':name,'evidence_class':'SYNTHETIC_EXACT_LAW' if name!='empirical_tsuga_refusal' else 'EMPIRICAL_ADMISSION_REFUSAL','status':result['status'],'checker':checker,'target':result.get('identified_target'),'source_count_examined':result.get('source_count_examined'),'no_unknown_registry_or_compartment_model_claim':True,'commands':commands})
        print(json.dumps({'name':name,'status':result['status'],'checker':checker['status']}),flush=True)
    summary['original_taxon_map'] = {'L'+str(i): t for i,t in enumerate(req['taxa'])}
    def decode(t):
        if isinstance(t,list):return [decode(x) for x in t]
        if t is None:return None
        return summary['original_taxon_map'][t]
    for x in summary['original_solver_controls']:x['decoded_original_taxon_target'] = decode(x['target'])
    summary['mapping_evidence'] = 'Request taxa and original-taxon→copy sampling map; species-level display categories only, no verified specimen/accession join.'
    summary['comparison']={'synthetic_tree_targets_differ': summary['original_solver_controls'][0]['target'] != summary['original_solver_controls'][1]['target'], 'empirical_capture_identified':False,'possible_under_real_input_uncertainty':'unknown; no numeric region admitted'}
    (out/'COMPARISON.json').write_text(json.dumps(summary,indent=2)+'\n')
    return 0

if __name__=='__main__':raise SystemExit(main())
