"""Safe exploratory reuse of the tested Biopython observation adapter."""
from collections import Counter
from hashlib import sha256
from io import StringIO
from .core import InputError, identifier, keys


def adapt_sequence(records):
    try:
        from Bio import AlignIO
        from .vendor import sequence_adapter as old
    except ImportError as exc:
        raise InputError('Sequence intake needs optional Biopython 1.88; the exact/statistical core has no third-party dependency') from exc
    if not isinstance(records,list) or not records:raise InputError('Expected nonempty locus records')
    seen={};converted=[];mapping=None;original={};duplicates=0
    for rec in records:
        keys(rec,['locus_id','fasta'],['locus_id','fasta'],'FASTA locus record')
        lid=identifier(rec['locus_id'],'locus_id')
        if not isinstance(rec['fasta'],str):raise InputError('FASTA must be text')
        digest=sha256(rec['fasta'].encode()).hexdigest()
        if lid in seen:
            if seen[lid]!=digest:raise InputError('Different same-locus alignments need a joint channel; refusing pseudoreplication')
            duplicates+=1;continue
        seen[lid]=digest
        try:a=AlignIO.read(StringIO(rec['fasta']),'fasta')
        except Exception as exc:raise InputError(f'Invalid aligned FASTA at locus {lid}: {exc}') from exc
        ids=[r.id for r in a]
        if len(ids)!=4 or len(set(ids))!=4:raise InputError('Exploratory pilot requires exactly four distinct original taxon IDs')
        newmap={v:chr(65+i) for i,v in enumerate(sorted(ids))}
        if mapping is not None and newmap!=mapping:raise InputError('Original taxon IDs must be identical across loci')
        mapping=newmap;original[lid]=digest
        fasta=''.join('>'+mapping[r.id]+'\n'+str(r.seq).upper()+'\n' for r in a)
        converted.append({'locus_id':lid,'fasta':fasta})
    try:result=old.adapt(converted)
    except (ValueError,ZeroDivisionError) as exc:raise InputError(str(exc)) from exc
    inv={v:k for k,v in mapping.items()}
    def labelled(split):
        return split if split=='UNRESOLVED' else [sorted(inv[c] for c in half) for half in split.split('|')]
    for row in result['loci']:
        row['original_input_sha256']=original[row['locus_id']]
        row['original_taxon_split']=labelled(row['label'])
    result.update(schema='genealogy-workbench/sequence-estimate-v1',evidence_tier='exploratory_sequence_estimate',
        original_taxon_id_mapping=mapping,original_labelled_alphabet={k:labelled(k) for k in result['alphabet']},
        identical_same_locus_duplicates_ignored=duplicates,experimental_unit_assumption_verified=False,
        g6_target_certificate='ABSTAIN: no calibrated sequence-to-interface-law channel or applicable full source-image compiler',
        applicable_interface_sorter=False,sequence_estimates_are_exact_calendar_laws=False)
    repeated=Counter(original.values())
    result['repeated_alignment_content_across_distinct_locus_ids']=sum(n-1 for n in repeated.values() if n>1)
    result['repeated_content_warning']='Distinct locus IDs are retained; their physical independence cannot be established from equal or unequal alignment strings'
    return result
