"""Prepare and replay a tiny published-specimen GenBank sequence comparison.
No live calls. Nuclear4CL1 and plastid rbcL remain separate exploratory markers.
"""
from pathlib import Path
from io import StringIO
import argparse, datetime, hashlib, json, os, shutil, subprocess, sys, time
from Bio import SeqIO, Align, __version__ as bio_version

BASE=Path(__file__).resolve().parent
RAW_SHA='7a021f7abf24beb5a8c692b4e53ce6bd888ad1f6694380b75205a601110384dc'
TAXA={
 'Tsuga_chinensis': {'organism':'Tsuga chinensis','paper_voucher':'Holman10-02 AA233-2003','plastid':'KX256181.1','nuclear':'KX354408.1'},
 'Tsuga_caroliniana': {'organism':'Tsuga caroliniana','paper_voucher':'Holman08-03','plastid':'KX256180.1','nuclear':'KX354414.1'},
 'Tsuga_sieboldii_Japan': {'organism':'Tsuga sieboldii','paper_voucher':'Holman09-09 AA1007-80A','plastid':'KX256184.1','nuclear':'KX354398.1'},
 'Tsuga_diversifolia': {'organism':'Tsuga diversifolia','paper_voucher':'Holman09-71 AA1146-86','plastid':'KX256182.1','nuclear':'KX354404.1'},
}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def seqsha(s):return hashlib.sha256(s.encode()).hexdigest()
def fasta(rows):return ''.join('>'+k+'\n'+v+'\n' for k,v in rows.items())

def center_align(rows,reference):
    ref=rows[reference]
    aligner=Align.PairwiseAligner(mode='global',match_score=2,mismatch_score=-1,open_gap_score=-5,extend_gap_score=-1)
    columns={};details=[]
    for name,seq in rows.items():
        possibilities=aligner.align(ref,seq);a=possibilities[0]
        try:number=len(possibilities)
        except OverflowError:number='too many'
        if number != 1:raise ValueError('Ambiguous optimal global alignment; no silent tie choice: '+name)
        m={}
        for (i,j),(k,l) in zip(*a.aligned):
            if j-i != l-k:raise ValueError('invalid aligned block')
            for x,y in zip(range(int(i),int(j)),range(int(k),int(l))):m[x]=seq[y]
        columns[name]=m
        details.append({'taxon':name,'reference_taxon':reference,'source_length':len(seq),'score':a.score,'unique_optimal_alignment':True,'coordinates':a.coordinates.tolist(),'query_insertions_omitted':len(seq)-len(m),'reference_positions_without_query_base':len(ref)-len(m)})
    keep=[i for i,c in enumerate(ref) if c in 'ACGT' and all(columns[n].get(i) in 'ACGT' for n in rows)]
    if len(keep)<16:raise ValueError('Fewer than16 shared unambiguous ungapped positions')
    retained={name:''.join(columns[name][i] for i in keep) for name in rows}
    return retained,{'algorithm':'unique optimal reference-centered global alignments, Gotoh; only shared ACGT reference positions retained; query insertions omitted','scores':{'match':2,'mismatch':-1,'open_gap':-5,'extend_gap':-1},'reference':reference,'reference_length':len(ref),'retained_sites':len(keep),'excluded_reference_sites':len(ref)-len(keep),'retained_reference_zero_based_positions':keep,'pair_alignments':details}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--genbank',type=Path,default=BASE/'REAL-BASELINE/GENBANK-RAW-15.gb');p.add_argument('--workbench',type=Path,default=BASE.parents[2]/'applications/genealogy-compatibility-workbench');p.add_argument('--output',type=Path,default=BASE/'REAL-BASELINE');a=p.parse_args()
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    if sha(a.genbank)!=RAW_SHA:raise ValueError('Raw source bytes differ from the explicitly frozen published-accession retrieval')
    if bio_version!='1.88':raise ValueError('Biopython1.88 required for this recorded recipe')
    records={r.id:r for r in SeqIO.parse(a.genbank,'genbank')}
    manifest={'schema':'raubeson-tsuga-genbank-exploratory-v1','public_source':{'kind':'actual public GenBank sequence records, not synthetic and not original Dryad alignments','raw_sha256':RAW_SHA,'raw_bytes':a.genbank.stat().st_size,'paper_doi':'10.1600/036364417X696474','paper_pdf_sha256':'81d19502fe93b40f68a8a673060670fad7e0588bb9bd186018004c372dae26ab','permission':'NCBI molecular database usage policy places no NCBI reuse/distribution restrictions; depositor IP rights not assessed/transferred. No CC0 or source-code-license claim on GenBank records.'},'specimens':[],'preprocessing':{},'outputs':{},'marker_choice_status':'Author-reported before tree outcomes; no independent immutable preregistration pin.', 'marker_choice':'Author-reported fixed tiny pilot: one complete deposited nuclear4CLlocus1 record and plastid rbcL CDS/homology region, before any tree/score result; no marker selection for desired conflict. Not full-paper replication.','empirical_solver_admission':'NOT_ADMITTED_TO_EMPIRICAL_SOLVER','independent_ancestry_blocks_verified':False,'phase_orthology_and_compartment_model_verified':False,'genbank_record_versions_verified':True,'physical_specimen_identity_evidence':'Holman2017 Appendix1 same row; GenBank source organism/isolate/clone recorded; physical original specimen not independently authenticated.'}
    nuclear={};plastid={};regions={}
    reference_cp=records['KX256180.1'];rf=next(f for f in reference_cp.features if f.type=='CDS' and f.qualifiers.get('gene')==['rbcL'])
    refgene=str(rf.extract(reference_cp.seq)).upper()
    for name,info in TAXA.items():
        cp=records[info['plastid']];n=records[info['nuclear']]
        if cp.annotations.get('organism')!=info['organism'] or n.annotations.get('organism')!=info['organism']:raise ValueError('record species differs from exact published join')
        source=[f.qualifiers for f in n.features if f.type=='source']
        nuclear[name]=str(n.seq).upper()
        features=[f for f in cp.features if f.type=='CDS' and f.qualifiers.get('gene')==['rbcL']]
        if features:
            if len(features)!=1:raise ValueError('nonunique depositedrbcL CDS')
            f=features[0];seq=str(f.extract(cp.seq)).upper();region={'kind':'DEPOSITED_CDS_ANNOTATION','location':str(f.location),'start0':int(f.location.start),'end0':int(f.location.end),'strand':f.location.strand,'gene':'rbcL'}
        else:
            if name!='Tsuga_chinensis':raise ValueError('unexpected unannotated marker')
            genome=str(cp.seq).upper();hits=[]
            for offset in range(0,len(refgene)-40,40):
                seed=refgene[offset:offset+40];j=genome.find(seed)
                while j>=0:hits.append({'reference_offset0':offset,'genome_offset0':j,'candidate_start0':j-offset});j=genome.find(seed,j+1)
            reverse_genome=str(cp.seq.reverse_complement()).upper()
            reverse_hits=sum(reverse_genome.count(refgene[offset:offset+40]) for offset in range(0,len(refgene)-40,40))
            if reverse_hits:raise ValueError('Reverse-strand exact anchors require a new explicit extraction policy')
            starts={h['candidate_start0'] for h in hits}
            if len(hits)<10 or len(starts)!=1:raise ValueError('rbcL homology anchors ambiguous/insufficient')
            start=next(iter(starts));seq=genome[start:start+len(refgene)]
            if not(seq.startswith('ATG') and seq[-3:] in {'TAA','TAG','TGA'}):raise ValueError('inferred marker lacks matching coding boundary checks')
            region={'kind':'HOMOLOGY_INFERRED_NOT_DEPOSITED_ANNOTATION','start0':start,'end0':start+len(refgene),'strand':1,'gene':'rbcL candidate','reference_accession':'KX256180.1','reference_deposited_location':str(rf.location),'seed_length':40,'unique_consistent_anchor_count':len(hits),'anchors':hits,'start_stop_check':True,'no_gene_annotation_in_original_record':True,'reverse_complement_exact_anchor_count':reverse_hits}
        plastid[name]=seq;regions[name]=region
        manifest['specimens'].append({'original_taxon_id':name,**info,'nuclear_source_qualifiers':source,'nuclear_description':n.description,'plastid_description':cp.description,'nuclear_sequence_sha256':seqsha(nuclear[name]),'plastid_region_sequence_sha256':seqsha(seq),'plastid_region':region})
    for marker,rows in [('nuclear-4CL1',nuclear),('plastid-rbcL',plastid)]:
        (out/(marker+'.raw-regions.fasta')).write_text(fasta(rows))
        aligned,recipe=center_align(rows,'Tsuga_chinensis')
        fpath=out/(marker+'.aligned.fasta');fpath.write_text(fasta(aligned));manifest['preprocessing'][marker]=recipe
        inputfile=out/(marker+'.workbench-input.json');inputfile.write_text(json.dumps([{'locus_id':'Holman2017_'+marker+'_four_published_specimens','fasta':fasta(aligned)}],indent=2)+'\n')
        receipt=out/(marker+'.receipt.json');cmd=[sys.executable,'-m','genealogy_workbench','sequence',str(inputfile),'--output',str(receipt),'--text']
        t=time.monotonic();start=datetime.datetime.now(datetime.timezone.utc).isoformat();q=subprocess.run(cmd,cwd=a.workbench,text=True,capture_output=True,timeout=45,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        (out/(marker+'.stdout')).write_text(q.stdout);(out/(marker+'.stderr')).write_text(q.stderr)
        if q.returncode!=0:raise ValueError('original workbench refused pilot: '+q.stdout+q.stderr)
        checkcmd=[sys.executable,'-m','genealogy_workbench','verify-receipt',str(inputfile),str(receipt)];v=subprocess.run(checkcmd,cwd=a.workbench,text=True,capture_output=True,timeout=45,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        (out/(marker+'.verify.stdout')).write_text(v.stdout);(out/(marker+'.verify.stderr')).write_text(v.stderr)
        if v.returncode!=0:raise ValueError('original receipt reexecution failed')
        result=json.loads(receipt.read_text());r=result['result'];manifest['outputs'][marker]={'command':cmd,'checker_command':checkcmd,'started_utc':start,'ended_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds_including_replay':time.monotonic()-t,'exit_code':q.returncode,'checker_exit_code':v.returncode,'aligned_fasta':fpath.name,'aligned_fasta_sha256':sha(fpath),'input_sha256':sha(inputfile),'receipt':receipt.name,'receipt_sha256':sha(receipt),'stdout_sha256':sha(out/(marker+'.stdout')),'stderr_sha256':sha(out/(marker+'.stderr')),'checker_stdout_sha256':sha(out/(marker+'.verify.stdout')),'result':r}
        print(json.dumps({'marker':marker,'sites':recipe['retained_sites'],'original_result':r}),flush=True)
    rows=[]
    for marker,o in manifest['outputs'].items():
        r=o['result'];row=r['loci'][0];rows.append({'marker':marker,'original_taxon_ids':list(TAXA),'sites':row['sites'],'estimated_split':row['original_taxon_split'],'bootstrap_support':row['bootstrap_support'],'bootstrap_replicates':row.get('bootstrap_replicates',0),'evidence_tier':r['evidence_tier'],'biological_target':r['g6_target_certificate'],'receipt':o['receipt'],'verify_reexecution':'PASS'})
    comparison={'schema':manifest['schema'],'input_evidence':'REAL_PUBLIC_PUBLISHED_ACCESSION_SEQUENCES','question':'Tiny matched-published-specimen nuclear4CL1/plastidrbcL exploratory comparison; does not replicate complete paper alignments.','original_taxon_map':TAXA,'rows':rows,'observed_marker_summary_agreement':rows[0]['estimated_split']==rows[1]['estimated_split'],'chloroplast_capture_conclusion':'UNKNOWN','genealogy_law_or_calibrated_confidence_region':None,'uncertainty_note':'Column bootstrap is descriptive marker resampling, not calibrated species-history/capture probability or independent locus replication.','empirical_solver_admission':'NOT_ADMITTED_TO_EMPIRICAL_SOLVER','inferred_region_note':'T.chinensis rbcL candidate is unannotated in deposit;33unique exact40nt anchors to annotatedT.caroliniana span determine the inferred1428nt region, with coding-boundary and global alignment checks recorded.','source_manifest':'MANIFEST.json','repeat_command':'From repository root with Biopython1.88: python research/2026-10-08-codex-integration-0825z/g6/prepare_real_baseline.py --output /absolute/fresh-output-directory','full_original_Dryad_alignments_retrieved':False}
    (out/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');(out/'COMPARISON.json').write_text(json.dumps(comparison,indent=2)+'\n');return 0

if __name__=='__main__':raise SystemExit(main())
