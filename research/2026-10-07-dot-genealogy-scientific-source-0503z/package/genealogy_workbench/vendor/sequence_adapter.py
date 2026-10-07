"""Pilot-only aligned FASTA to estimated quartet labels, retaining locus units.

This is an observation adapter, not a certified biological G6 inference engine.
NJ and column-bootstrap support are estimators, not known error-channel bounds.
"""
from collections import Counter
from io import StringIO
from pathlib import Path
import hashlib, json, math, random, resource, time
import Bio
from Bio import AlignIO, Phylo
from Bio.Align import MultipleSeqAlignment
from Bio.Seq import Seq
from Bio.SeqRecord import SeqRecord
from Bio.Phylo.TreeConstruction import DistanceCalculator, DistanceTreeConstructor

ROOT=Path(__file__).resolve().parent
TAXA=('A','B','C','D')
ALPHABET=('AB|CD','AC|BD','AD|BC','UNRESOLVED')
CALC=DistanceCalculator('identity'); CONSTRUCTOR=DistanceTreeConstructor()

def validated_alignment(text):
    a=AlignIO.read(StringIO(text),'fasta')
    ids=[r.id for r in a]
    if len(set(ids))!=len(ids): raise ValueError('Duplicate taxon ID')
    if set(ids)!=set(TAXA): raise ValueError('Pilot needs exactly A,B,C,D')
    if a.get_alignment_length()<16: raise ValueError('Too few sites for pilot')
    if any(set(str(r.seq).upper())-set('ACGT') for r in a): raise ValueError('Unsupported ambiguous, missing or gapped bases')
    return MultipleSeqAlignment(sorted(a,key=lambda r:r.id))

def quartet_label(a):
    dm=CALC.get_distance(a)
    sums=[dm['A','B']+dm['C','D'],dm['A','C']+dm['B','D'],dm['A','D']+dm['B','C']]
    best=min(sums)
    if sum(abs(s-best)<1e-12 for s in sums)!=1:return 'UNRESOLVED'
    # Independently exercise the library's actual NJ constructor, not just parsing.
    tree=CONSTRUCTOR.nj(dm); splits=set()
    for clade in tree.find_clades():
        names=frozenset(t.name for t in clade.get_terminals())
        if len(names)==2 and clade.branch_length is not None and clade.branch_length>1e-12:
            left=''.join(sorted(names));right=''.join(sorted(set(TAXA)-set(names)))
            splits.add('|'.join(sorted([left,right])))
    label=ALPHABET[sums.index(best)]
    return label if splits=={label} else 'UNRESOLVED'

def infer(text,seed,reps=100):
    a=validated_alignment(text);label=quartet_label(a)
    if label=='UNRESOLVED':return {'label':label,'bootstrap_support':0.0,'sites':a.get_alignment_length()}
    rng=random.Random(seed);n=a.get_alignment_length();hits=0
    for _ in range(reps):
        cols=[rng.randrange(n) for _ in range(n)]
        aa=MultipleSeqAlignment([SeqRecord(Seq(''.join(str(r.seq)[i] for i in cols)),id=r.id) for r in a])
        hits+=quartet_label(aa)==label
    support=hits/reps
    return {'label':label if support>=.9 else 'UNRESOLVED','bootstrap_support':support,'sites':n,'bootstrap_replicates':reps,'warning':'Bootstrap support is not calibrated TV error beta'}

def adapt(records):
    if not records: raise ValueError('No locus records supplied')
    groups={};ignored=0
    for rec in records:
        locus=rec['locus_id'];digest=hashlib.sha256(rec['fasta'].encode()).hexdigest()
        if locus in groups:
            if groups[locus]['input_sha256']!=digest:raise ValueError('Different same-locus records need a joint-outcome schema; refusing pseudoreplication')
            ignored+=1;continue
        groups[locus]={'locus_id':locus,'input_sha256':digest,**infer(rec['fasta'],seed=20261002+len(groups))}
    counts=Counter(r['label'] for r in groups.values());n=len(groups);alpha=.05;m=len(ALPHABET)
    # Applies to the predeclared estimated-label distribution ONLY, conditional on
    # independent identically distributed loci. This is not uncertainty in true trees.
    radius=min(1.0,m/2*math.sqrt(math.log(2*m/alpha)/(2*n)))
    return {'schema':'g6-observation-pilot/v1','observation':'estimated unrooted quartet label per aligned locus',
      'alphabet':ALPHABET,'loci':list(groups.values()),'independent_observation_units':n,
      'identical_same_locus_duplicates_ignored':ignored,'estimated_label_counts':{k:counts[k] for k in ALPHABET},
      'estimated_label_tv_radius':radius,'alpha':alpha,'confidence_scope':'One prespecified profile; conditional on iid loci. Does not cover true gene-tree distribution, adaptive profiles or calendar times.',
      'known_sequence_to_topology_channel':False,'calibrated_beta':None,'calendar_time_bins':None,
      'g6_target_certificate':'ABSTAIN: observation channel/calibration and source closure compiler absent',
      'lean_kernel_checked':False,'phylogenetic_method':'Biopython NJ with uncorrected identity distances; only synthetic smoke, no validated substitution model',
      'biopython_version':Bio.__version__}

def fixture(split):
    pair=set(split.split('|')[0]);lines=[]
    for taxon in TAXA:
        # Designed fixture, not an MSC/molecular-evolution simulation.
        seq=('ACGT'*40 if taxon in pair else 'TGCA'*40)+'ACGT'*24
        lines += ['>'+taxon,seq]
    return '\n'.join(lines)+'\n'

def main():
    t=time.perf_counter();records=[]
    for j,split in enumerate(ALPHABET[:3]):
        for i in range(2):records.append({'locus_id':f'L{j}-{i}','fasta':fixture(split)})
    records.append({'locus_id':'L-star','fasta':'\n'.join('>'+x+'\n'+'A'*256 for x in TAXA)+'\n'})
    records.append(dict(records[0]))
    out=adapt(records);checks={}
    checks['all_three_resolved_splits_recovered']=all(out['estimated_label_counts'][k]==2 for k in ALPHABET[:3])
    checks['star_abstains']=out['estimated_label_counts']['UNRESOLVED']==1
    checks['duplicate_not_independent_locus']=out['independent_observation_units']==7 and out['identical_same_locus_duplicates_ignored']==1
    for name,bad in [('duplicate_taxon',records[0]['fasta'].replace('>B','>A')),('ambiguous_base',records[0]['fasta'].replace('ACGT','NCGT',1)),('missing_taxon',records[0]['fasta'].split('>D')[0])]:
        try:validated_alignment(bad);checks[name+'_rejected']=False
        except ValueError:checks[name+'_rejected']=True
    try:adapt(records+[{'locus_id':'L0-0','fasta':fixture('AD|BC')}]);checks['different_same_locus_joint_required']=False
    except ValueError:checks['different_same_locus_joint_required']=True
    try:adapt([]);checks['empty_input_rejected']=False
    except ValueError:checks['empty_input_rejected']=True
    checks['no_false_g6_target_certificate']=out['g6_target_certificate'].startswith('ABSTAIN')
    out['checks']=checks;out['all_checks_pass']=all(checks.values());out['elapsed_seconds']=time.perf_counter()-t
    out['process_maxrss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    out['input_class']='synthetic designed FASTA, no external upload or personal genomic data'
    (ROOT/'g6-adapter-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
    (ROOT/'synthetic-loci.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['loci']},indent=2))
    assert out['all_checks_pass']

if __name__=='__main__':main()
