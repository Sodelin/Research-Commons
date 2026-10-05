"""Read-only structural design extraction from pinned official frog inputs.
No alleles are copied into synthetic data, and no simulator/inference is run.
The local alias/mask contract is not a public raw-data attachment.
"""
import collections,hashlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
SOURCE=BASE.parent/'bpp-sequence-pilot-20261005'/'upstream-bpp-v4.8.7'/'examples'/'frogs'
PINS={'frogs.txt':'0e7bd09b44b83e6cafb1ecc444535b91e1b96b19c2d10f57012d51da2b8af92b','frogs.Imap.txt':'eb7cb7cb39586ab395089b5e42cd982a9d59ca5628a9e75a9c1d643165431f31'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def prepare(source=SOURCE):
    for name,pin in PINS.items():
        if sha(source/name)!=pin:raise ValueError('unreviewed source layout')
    mapping={}
    for line in (source/'frogs.Imap.txt').read_text().splitlines():
        if not line.strip():continue
        name,pop=line.split()
        if name in mapping or pop not in 'KCLH' or len(pop)!=1:raise ValueError('bad map')
        mapping[name]=pop
    aliases={};counts={}
    for pop in 'KCLH':
        ids=sorted(name for name,p in mapping.items() if p==pop);counts[pop]=len(ids)
        for i,name in enumerate(ids,1):aliases[name]=pop+'^'+pop.lower()+str(i)
    lines=[x.strip() for x in (source/'frogs.txt').read_text().splitlines() if x.strip()];pos=0;loci=[]
    while pos<len(lines):
        n,length=map(int,lines[pos].split());pos+=1
        if n<=0 or length<=0:raise ValueError('nonpositive layout')
        rows=[];seen=set()
        for line in lines[pos:pos+n]:
            parts=line.split();label=parts[0];seq=''.join(parts[1:]).upper();identity=label.removeprefix('^')
            if not label.startswith('^') or identity not in mapping or identity in seen or len(seq)!=length:raise ValueError('bad source observation')
            seen.add(identity)
            unknown=[i for i,s in enumerate(seq,1) if s not in 'ACGTRYSWKM']
            if any(seq[i-1]!='?' for i in unknown):raise ValueError('unreviewed uncertain-site encoding')
            rows.append({'synthetic_label':aliases[identity],'population':mapping[identity],'question_mark_sites_1based':unknown})
        if len(rows)!=n:raise ValueError('truncated locus')
        pos+=n;loci.append({'locus':len(loci)+1,'length':length,'rows':rows})
    if len(loci)!=5 or counts!={'K':6,'C':10,'L':14,'H':2}:raise ValueError('unexpected complete sampling map')
    local={'schema':'proposed-matched-layout-v1','source_hashes':PINS,'simulation_individuals_per_population':counts,'maximum_simulation_locus_length':max(l['length'] for l in loci),'loci':loci,'copy_observed_alleles':False,'execute_simulation':False}
    summary={'schema':'matched-layout-aggregate-design-v1','source_hashes':PINS,'simulation_individuals_per_population':counts,'loci':[{'locus':l['locus'],'length':l['length'],'individuals':len(l['rows']),'gene_copies':2*len(l['rows']),'population_counts':dict(collections.Counter(r['population'] for r in l['rows'])),'question_mark_count':sum(len(r['question_mark_sites_1based']) for r in l['rows'])} for l in loci],'simulate_loci':5,'simulate_sites_per_locus':489,'simulate_total_individuals':32,'simulate_gene_copies_per_locus':64,'copy_observed_alleles':False,'new_simulation_or_inference':False}
    return local,summary
if __name__=='__main__':
    local,summary=prepare();(BASE/'LOCAL-ALIAS-MASK-CONTRACT.json').write_text(json.dumps(local,indent=2)+'\n')
    summary['local_alias_mask_sha256']=sha(BASE/'LOCAL-ALIAS-MASK-CONTRACT.json');(BASE/'LAYOUT-SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
