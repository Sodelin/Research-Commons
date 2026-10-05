"""Validate the declared fixed synthetic smoke; no biological-admission claim."""
import collections,hashlib,json,re
from pathlib import Path
BASE=Path(__file__).resolve().parent
FOLDER=BASE/'synthetic-runs'/'simulation-seed7001'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def admit(folder=FOLDER):
    terminal=json.loads((folder/'TERMINAL.json').read_text())
    if terminal['status']!='EXECUTION_EXIT_ZERO' or not terminal['inputs_stable']:raise ValueError('incomplete simulation')
    inventory={p['path']:p['sha256'] for p in terminal['output_inventory']}
    for name,digest in inventory.items():
        if sha(folder/name)!=digest:raise ValueError('changed simulation output')
    mapping={}
    for line in (folder/'synthetic.Imap.txt').read_text().splitlines():
        key,value=line.split()
        if key in mapping:raise ValueError('duplicate map key')
        mapping[key]=value
    expected={species.lower()+str(i):species for species in 'KCLH' for i in [1,2]}
    if mapping!=expected:raise ValueError('map does not match two individuals/population')
    lines=[x.strip() for x in (folder/'synthetic.txt').read_text().splitlines() if x.strip()]
    offset=0;loci=[]
    while offset<len(lines):
        n,length=map(int,lines[offset].split());offset+=1
        if (n,length)!=(8,500):raise ValueError('incorrect synthetic dimensions')
        labels=set();counts=collections.Counter();ambiguities=0
        for line in lines[offset:offset+n]:
            parts=line.split();label=parts[0];seq=''.join(parts[1:]).upper()
            if label in labels:raise ValueError('duplicate label')
            labels.add(label)
            if '^' not in label:raise ValueError('missing individual label')
            population,key=label.split('^')
            if mapping.get(key)!=population:raise ValueError('label-map mismatch')
            counts[population]+=1
            if len(seq)!=length or set(seq)-set('ACGTRYSWKM'):raise ValueError('invalid diploid DNA encoding')
            ambiguities+=sum(c not in 'ACGT' for c in seq)
        if counts!={x:2 for x in 'KCLH'}:raise ValueError('wrong locus population counts')
        offset+=n;loci.append({'locus':len(loci)+1,'rows':n,'length':length,'population_counts':dict(counts),'heterozygous_sites':ambiguities})
    if len(loci)!=5:raise ValueError('wrong locus number')
    trees=(folder/'truth-gene-trees.txt').read_text().splitlines()
    if len(trees)!=5:raise ValueError('wrong gene genealogy count')
    expected_haplotypes={p+'^'+p.lower()+str(i)+a for p in 'KCLH' for i in [1,2] for a in 'ab'}
    for tree in trees:
        labels=re.findall(r'([KCLH]\^[kclh][12][ab]):',tree)
        if len(labels)!=16 or set(labels)!=expected_haplotypes:raise ValueError('not four gene copies per population')
    output=(folder/'stdout.log').read_text()
    if 'Substitution model: JC69' not in output:raise ValueError('wrong substitution model')
    observed={}
    for label,tau,theta in re.findall(r'^\d+\s+(\S+)\s+[01 ]+tau = ([.\d]+)\s+theta = ([.\d]+)',output,re.M):observed[label]={'tau':float(tau),'theta':float(theta)}
    truth={label:{'tau':tau,'theta':.001} for label,tau in [('K',0),('C',0),('L',0),('H',0),('K,C,L,H',.002),('K,C',.001),('L,H',.0015)]}
    if observed!=truth:raise ValueError('runtime truth population parameters differ')
    return {'schema':'synthetic-smoke-admission-v1','status':'FIXTURE_MATCHES_PREDECLARED_MODEL','simulation_terminal_sha256':sha(folder/'TERMINAL.json'),'input_hashes':{x:sha(folder/x) for x in ['synthetic.txt','synthetic.Imap.txt','truth-gene-trees.txt','stdout.log']},'loci':loci,'genealogy_tip_count':16,'gene_copies_per_population':4,'truth_parameters':observed,'biological_admission':False,'simulation_calibration':False,'full_and_randomized_auxiliaries_used_for_inference':False,'site_rate_note':'Printed Gamma(0), K=5 header denotes default alpha=0; simulate.c skips rate heterogeneity when alpha is zero.'}
if __name__=='__main__':
    result=admit();(BASE/'synthetic-admission.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
