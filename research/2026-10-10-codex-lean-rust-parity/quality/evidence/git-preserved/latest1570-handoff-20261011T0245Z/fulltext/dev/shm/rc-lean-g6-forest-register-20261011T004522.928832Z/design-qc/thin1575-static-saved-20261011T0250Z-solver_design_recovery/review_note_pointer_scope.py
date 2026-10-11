from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
Q=Path(__file__).parent
P=Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h,size=None):
 p=Path(p);b=p.read_bytes();assert sha(b)==h and (size is None or len(b)==size);return {'path':str(p),'bytes':len(b),'sha256':h},b
ni,n=pin(P/'design/INTEGRATION-STATE-20261011T0249Z.md','5194a726f1c4a8905a9812a14245b2c6b9b52b90d946263d0c9826f4fa4e2921',3699)
pi,p=pin(P/'quality/INTEGRATION-EVIDENCE-POINTER-20261011T0232Z.json','616235d1657948c81aa22f1eb5efa8f9974279c7307e8c836ae08fc1bc3410ad',6736)
j=json.loads(p);text=n.decode();assert j['status']=='FROZEN_SOURCE_AND_SAVED_EVIDENCE_REFERENCES_REMOTE_READBACK_PENDING'
assert j['publication_cutoff_main']=='62020166e3e7ef690838f50b13caa149ede419ec'
scope=j['scope'];assert (scope['accepted_connected_modules'],scope['accepted_natural_common_component_modules'],scope['private_rust_tests_passed'],scope['prospective_union_modules'])==(1570,141,5,1575)
assert scope['prospective_union_status']=='STATIC_NOT_KERNEL_ACCEPTED' and all(scope[k] for k in ['component_counts_overlap_do_not_sum','peer_private_operational_payloads_not_personally_replayed','source_constructor_g4_observation_identity_rust_refinement_general_acquisition_master_remain_open'])
refs=[]
for name,row in j['refs'].items():
 info,b=pin(row['source_path'],row['sha256'],row['bytes']);refs.append([name,info['path'],info['sha256'],info['bytes'],row['git_tree_path']])
assert len(refs)==9
assert all(t in text for t in ['STATIC_NOT_KERNEL_ACCEPTED','Private operational payloads were not personally replayed','Rust public executable remains unchanged','named private slot set to false','current selected Rust record does not retain that entire history','bounded 67-source reuse search','decoder identity remains open','still uncompiled','master closure remain open','exceeded its 16 MiB estimate by 716,839 bytes','fixed 96 MiB bound','Remaining publication requires exact compressed-object funding','not evidence of a continuing background job or peer acknowledgement'])
old,ob=pin(P/'design/INTEGRATION-STATE-20261011T0232Z.md','169205b5833dca962e35df66f0b4e3b18f271d293fd093c6f52bc5fdf49561b9',2975)
report={'status':'PASS_DATED_NOTE_AND_PENDING_REMOTE_POINTER_SCOPE_ONLY','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':sha(Path(__file__).read_bytes()),'note':ni,'pointer':pi,'old0232_note_retained':old,'all9_current_reference_source_hashes_sizes_checked':True,'reference_names':[r[0] for r in refs],'reference_source_destination_bindings_sha256':sha(json.dumps(refs,sort_keys=True,separators=(',',':')).encode()),'existing_local_indexing_and_prospective_remote_destinations_are_distinguished':True,'forthcoming_latest1570_prefix_is_pending_not_completed_publication':True,'remote_Git_blob_tree_readback_or_commit_push_verified_by_this_reader':False,'scope_1570_public_saved_141_separate_five_private_tests_1575_static_only':True,'one_named_private_slot_resetfalse_other_register_and_carried_forest_preserved':True,'arbitrary_CodeOld_selected_runtime_correspondence_constructor_calibrated_decoder_refinement_master_open':True,'actual_fetch_estimate_failure_fixedcaps_and_exact_funding_hold_retained':True,'no_source_edits_target_producers_Git_or_index_changes':True}
b=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode();assert len(b)<=4096
out=Q/'INTEGRATION0249-NOTE-AND-POINTER-SCOPE-QC.json';assert not out.exists();assert sum(x.stat().st_blocks*512 for x in Q.iterdir() if x.is_file())+4096<=65536;out.write_bytes(b)
print(json.dumps({'path':str(out),'sha256':sha(b),'bytes':len(b),'directory_allocated_bytes':sum(x.stat().st_blocks*512 for x in Q.iterdir() if x.is_file()),'status':report['status']}))
