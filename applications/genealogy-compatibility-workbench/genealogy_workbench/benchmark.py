"""Matching-contract operational tests, not a biological accuracy study."""
from fractions import Fraction as Q
from io import StringIO
from .sequence import adapt_sequence


def life_science_comparison():
    try:
        import Bio
        from Bio import AlignIO
        from Bio.Phylo.TreeConstruction import DistanceCalculator,DistanceTreeConstructor
        from .vendor.sequence_adapter import fixture,TAXA,ALPHABET
    except ImportError:
        return {'status':'UNAVAILABLE','operational_function':'Biopython alignment, identity distances and neighbor joining',
            'reason':'Optional Biopython is not installed','ngs_workbench_execution':'UNAVAILABLE: required target/catalog/execution tools not exposed in this task',
            'biological_validity_established':False}
    records=[{'locus_id':f'designed-{i}','fasta':fixture(split)} for i,split in enumerate(ALPHABET[:3])]
    records.append({'locus_id':'designed-star','fasta':'\n'.join('>'+x+'\n'+'A'*256 for x in TAXA)+'\n'})
    results=adapt_sequence(records); rows=[]; successes=0
    calc=DistanceCalculator('identity');nj=DistanceTreeConstructor()
    for rec,expected,observed in zip(records,ALPHABET,results['loci']):
        a=AlignIO.read(StringIO(rec['fasta']),'fasta')
        # Independent integer mismatch-distance/four-point implementation.
        seq={r.id:str(r.seq) for r in a};n=a.get_alignment_length()
        def distance(x,y):return Q(sum(u!=v for u,v in zip(seq[x],seq[y])),n)
        sums=[distance('A','B')+distance('C','D'),distance('A','C')+distance('B','D'),distance('A','D')+distance('B','C')]
        best=min(sums);four='UNRESOLVED' if sums.count(best)!=1 else ALPHABET[sums.index(best)]
        tree=nj.nj(calc.get_distance(a));splits=set()
        for c in tree.find_clades():
            names={t.name for t in c.get_terminals()}
            if len(names)==2 and c.branch_length is not None and c.branch_length>1e-12:
                splits.add('|'.join(sorted([''.join(sorted(names)),''.join(sorted(set(TAXA)-names))])))
        raw=next(iter(splits)) if len(splits)==1 else 'UNRESOLVED'
        passed=four==raw==observed['label']==expected;successes+=passed
        rows.append({'locus_id':rec['locus_id'],'designed_expected_quartet':expected,'independent_exact_hamming_four_point':four,
            'direct_biopython_nj':raw,'workbench_adapter':observed['label'],'match':passed})
    return {'status':'PASS' if successes==len(rows) else 'FAIL','biopython_version':Bio.__version__,
        'matching_contract':{'input':'Four-taxon synthetic designed aligned ACGT sequences','target':'Estimated unrooted quartet split or unresolved','method':'Uncorrected identity distances; Biopython neighbor joining; adapter additionally bootstraps'},
        'ground_truth':'Explicit designed split fixture, not a coalescent or calibrated molecular-evolution simulation',
        'metric':{'designed_label_accuracy':successes/len(rows),'matching_cases':successes,'total_cases':len(rows)},'cases':rows,
        'comparison_type':'Adapter/library conformance with an independent exact four-point check, not an independent biological inference suite benchmark',
        'ngs_workbench_execution':'UNAVAILABLE: no list_compute_targets, workflow catalogue or execute_plan tools exposed at this audit',
        'bibliographic_lookup_is_inference_oracle':False,'biological_validity_established':False,
        'limits':['No calibrated DNA-to-interface/calendar error bound','No real biological or personal genomic data','No supported comparison between estimated quartet labels and full forest/target certificates'],
        'primary_documentation':'https://biopython.org/docs/1.88/api/Bio.Phylo.TreeConstruction.html'}
