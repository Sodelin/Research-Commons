"""Independent dated documentation readback; standard-library bytes only."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,traceback
P=Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
WF=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
WN=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
W9=Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z')
Q=WF/'design-qc/scientific-scope-docs-20261011T0218Z-solver_design_recovery'
def require(test,why):
 if not test:raise AssertionError(why)
def digest(b):return hashlib.sha256(b).hexdigest()
def pin(path,expected):
 p=Path(path);d=p.read_bytes();require(digest(d)==expected,'frozen input '+str(p));return {'path':str(p),'bytes':len(d),'sha256':expected},d
def check():
 pins={}
 inputs={
 'natural_acceptance':(P/'lean/G6-NATURAL-COMMON-FOREST-FACTORIZATION-141-ACCEPTANCE-20261011T0202Z.json','4b38e92700caa3ec2bd853b119fb2aa90d5cbf49af71081a1e6cfbbbcd73514d'),
 'output_clarification':(P/'quality/NATURAL141-ERASED-REGISTER-OUTPUT-CLARIFICATION-20261011T0207Z.json','ac517709335995660c595a057b087bd552bd4254d7e4d0f19b535403c51d31fc'),
 'own_before_scope_memo':(Q/'SCIENCE-SCOPE-CLARIFICATION-MEMO.json','bedbe80c29226563b06701259c528542d02c4d75d2037557c79f185849c255a9'),
 'private_finite_acceptance':(P/'quality/PRIVATE-SELECTED-PREFIX-FIVE-TEST-ACCEPTANCE-20261011T0133Z.json','0b51469b602b32907770e61cf1518a6fb2d9da9778255b487d29f8e46aab4bd0'),
 'public_peer_saved_reader':(WF/'metadata/commons1568-readonly-review-20261011T0200Z/PUBLIC1568-SAVED-READONLY-REVIEW.json','dc9392e2b23e02b2cc5f8a6d9c2fedcec92f95a91fa9a5757020ccdf7a90a40b'),
 'empirical_source_only_budget':(WN/'metadata/union1509-source-only-feasibility-20261011T0208Z/SOURCE-ONLY-UNION1509-FEASIBILITY.json','66766e027fe4d1674a973257196522d96fce213316bea5e29d738db65abd5d61'),
 'full_natural_saved_review':(WN/'design-qc/natural141-saved-20261011T0152Z-solver_design_recovery/NATURAL141-SAVED-QC-ATTEMPT2.json','6ed6b44b114704fb39a236a126b1f2a36197a6b443d53da5a2816a7efa5a19c4'),
 'old_legal_decoder_scope_review':(WN/'design-qc/natural141-scope-challenge-20261011T0149Z-solver_design_recovery/EXISTING-LEGAL-SOURCE-AND-CALIBRATED-DECODER-SCOPE-CHALLENGE-ATTEMPT3.json','d2e030bbecbf3b29edccb99d2aed3ae9f9089929c4c8dacfc7cac86044c36008'),
 'actual_73_git_review':(WF/'design-qc/natural141-git-publication-saved-20261011T0214Z-solver_design_recovery/NATURAL141-COMPLETE73-GIT-PUBLICATION-SAVED-QC-ATTEMPT1.json','f2c5a13de4322271956739f0376ccca9b35fdfb6138956552896b02a68fd369d'),
 'constructor_provider_outline':(W9/'metadata/legal-positive-twoport-bin-constructor-map-v2-20261011T014645.303868Z/CONSTRUCTOR-PROVIDER-MAP-V2.json','a8ae28ac04e54e9fa8fb11ad9747b1d8ed667899a498b3b25aed28e4f44ef7e1'),
 'five_source_identity_delta':(W9/'metadata/integration-source-identity-delta-1509-20261011T015156.237141Z/INTEGRATION-SOURCE-IDENTITY-DELTA.json','242535f8d6748df81b5c376d5c3aa1ebe44e2cd4594f8099e240e2f4505a5e6d'),
 'exact_factor_source':(WN/'lossless-export/proof141-20261011T014055.249073Z/sources/G6NaturalCommonForestFactorization.lean','3fc98f898f705bf778fa5b2d448ae5e05ce00d262bc3048042f08c07921edac4')}
 content={}
 for name,(path,h) in inputs.items():pins[name],content[name]=pin(path,h)
 ac=json.loads(content['natural_acceptance']);cl=json.loads(content['output_clarification']);pr=json.loads(content['private_finite_acceptance']);peer=json.loads(content['public_peer_saved_reader']);budget=json.loads(content['empirical_source_only_budget'])
 require(ac['counts']['selected_modules']==141 and ac['counts']['owned_declarations']==3486 and ac['counts']['owned_theorems']==2293 and ac['counts']['components_reused']==140 and ac['counts']['fresh_factor']==1 and ac['counts']['genuinely_new_unique_names']==45,'natural exact scoped counts')
 require(ac['inherited_metadata']['qualified_exact_differences']==13 and ac['coherent_1504_acceptance_unchanged'],'qualified metadata and unchanged base')
 require(cl['natural_theorem_private_set']=='P = {h.val}' and cl['erased_register_definition']=='register v := if v in P then false else oldregister v','exact erased-selector formula')
 require(cl['clarifies_acceptance_sha256']==pins['natural_acceptance']['sha256'] and cl['source_sha256']==pins['exact_factor_source']['sha256'],'additive clarification exact proof/acceptance')
 require(pr['actual_tests_passed']==5 and pr['actual_tests_failed']==0 and pr['public_module_promoted'] is False,'finite private tests/no public promotion')
 require(peer['all_100985_inherited_full_parsed_records_equal'] and peer['all_1568_source_bytes_and_literal_imports_verified'] and len(peer['audit_transport_parts'])==8 and peer['public_owned_declarations']==101705 and peer['public_theorem_rows']==92153,'peer public complete audit/source scope')
 require(peer['peer_local_native_trace_or_companion_payloads_authenticated_by_this_reader'] is False and peer['combined1573_kernel_acceptance_claimed'] is False,'peer operational and candidate qualifications')
 resource=budget['resource_snapshot'];profile=budget['empirical_single_copy_profile']
 allocation=resource['conservative_followed']['allocated_bytes'];headroom=resource['scratch_abort_bytes']-allocation;required=profile['most_favorable_existing_full_run_profile_before_all_preparation_export_growth_QA_and_git_bytes'];deficit=required-headroom
 require((allocation,headroom,required,deficit)==(1895915520,117350400,159350784,42000384),'recomputed dated empirical42MB shortfall')
 require('not a theorem' in profile['qualification'],'empirical profile not universal lower bound')
 docs={}
 for rel,h,snapshot in [('README.md','1b63ee40cb82e1c2dc83a2d7fced19c0f2dd5974a149b516faffde2523fbe7b9','README-AFTER-FINAL-SCOPE-CLARIFICATION.md'),('design/DISCOVERY-DELTA-20261011T0210Z.md','ec6461ff61ad6595c1eeef9419322decdd4b4f425a51378f287c21404c46b114','DISCOVERY-DELTA-AFTER-FINAL-SCOPE-CLARIFICATION.md')]:
  info,data=pin(P/rel,h);dest=Q/snapshot;require(not dest.exists(),'immutable new document snapshot');dest.write_bytes(data);docs[rel]={**info,'snapshot_path':str(dest)}
 readme=(P/'README.md').read_text();brief=(P/'design/DISCOVERY-DELTA-20261011T0210Z.md').read_text()
 require(brief.splitlines()[0]=='# Checked integration checkpoint — 11 October 2026 UTC','date-only header after enrichment')
 require('Decisions API setup is canceled, with no key created or API call made.' in readme,'canceled API')
 require('private selector slot is reset to false' in readme and 'all other register slots' in readme,'README private erasure clarity')
 require('resets the private hybrid selector slot to false' in brief and 'does not retain that original private-bit distribution' in brief and 'every other original register slot' in brief,'brief exact erased output')
 for text in [readme,brief]:
  require('f8120b1e413b64303891f7f2f8007169856c03f3' in text,'corrected current peer attribution commit linked')
  require('100,985' in text and '92,153' in text,'verified complete peer count stated')
 require('all eight gzip parts' in brief and 'does not replay those private traces' in brief,'public audit versus private local traces separated')
 require('1,573' in brief and 'Neither candidate count is a new coherent kernel certificate' in brief,'1509/1573 remain source-only candidates')
 require('96 MiB' in brief and 'all 73 files' in brief and 'indexed and byte-reviewed' in brief,'actual96 source/publication QA status stated')
 require('measured single-copy' in brief and '42 MB' in brief,'dated measured profile claim qualified in text')
 require('MASTER IN PROGRESS' in brief and 'full practical source-to-optimal-policy solver remains incomplete' in readme,'master/practical completion remains open')
 require('useful remaining constructor' in brief and 'admitted inverse nonroot-bridge-to-bigon splice' in brief and 'Full approximation' in brief,'specific proposed constructor/downstream distinction')
 links=[]
 for label,target in re.findall(r'\[([^\]]+)\]\(([^)]+)\)',brief):
  if target.startswith('https://'):links.append({'label':label,'url':target,'scope':'verified frozen peer commit link; no network action'})
  else:
   path=(P/'design'/target).resolve();require(path.is_file(),'existing brief acceptance link '+target);links.append({'label':label,'path':str(path)})
 require((P/'README.md').read_bytes()==(Q/'README-AFTER-FINAL-SCOPE-CLARIFICATION.md').read_bytes() and (P/'design/DISCOVERY-DELTA-20261011T0210Z.md').read_bytes()==(Q/'DISCOVERY-DELTA-AFTER-FINAL-SCOPE-CLARIFICATION.md').read_bytes(),'current document bytes stable through review')
 return {'current_documents':docs,'accepted_evidence_and_qualified_mapping_inputs':pins,'brief_links':links,'output_statement':'P={h.val}; private slot reset false, all other original slots and complete carried forest retained, Old reads entire erased initialized endpoint vector. This is not retained original private-bit distribution.','local141_scope':'Fresh factor/aggregate/full selected audit;140reused including qualified prefix,45unique additions and13exact inherited context qualifiers; coherent1504 unchanged.','private_Rust_scope':'Five finite accepted selected-prefix cases only; public native unchanged; no source admission, literal Code/timed correspondence or universal refinement promotion.','peer_scope':'All1568 published source/import identities/eight gzip parts/full101705/92153 raw audit and all100985 inherited parsed records verified by bound public reader; peer local native traces not authenticated/replayed by it.','candidate_scope':'1509 and1573 exact source identity sets only, no new coherent certificate; two G4 drafts remain uncompiled.','empirical_budget_arithmetic':{'dated_conservative26_root_allocated':allocation,'abort_bytes':resource['scratch_abort_bytes'],'headroom_bytes':headroom,'observed_full1504_profile_bytes':required,'deficit_before_preparation_export_growth_QA_Git':deficit,'universal_output_size_lower_bound_claimed':False},'legal_constructor_scope':'Existing supplied-calendar rate-bank and supplied-word exit/context/guarded decoder providers reused. Proposed inverse bridge source/calendar/registry/physical word/deletion correspondence and full approximation remain explicit downstream gates.','original_acceptance_source_records_changed':False,'no_producer_compiler_native_reference_or_Git_commands':True,'scope_is_dated_documentation_readback_not_new_mathematical_acceptance':True,'Decisions_API_canceled':True,'historical_before_documents_and_memo_preserved':True}
report={'schema':'FINAL_SCIENTIFIC_DOCUMENTATION_READBACK_QC_V1','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':digest(Path(__file__).read_bytes())}
try:report['checks']=check();report['status']='PASS_CURRENT_DOCS_MATCH_SEPARATE_ACCEPTED_SCOPES_AND_EXPLICIT_OPEN_GATES'
except Exception as e:report['status']='FAIL_OWN_REVIEWER';report['error']=str(e);report['traceback']=traceback.format_exc()
out=Q/'FINAL-SCIENTIFIC-DOCUMENTATION-READBACK-QC-ATTEMPT1.json';require(not out.exists(),'immutable own report');out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({'status':report['status'],'path':str(out),'sha256':digest(out.read_bytes()),'bytes':out.stat().st_size,'error':report.get('error')}))
