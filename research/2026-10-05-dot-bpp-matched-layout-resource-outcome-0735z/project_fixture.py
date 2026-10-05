"""Project newly simulated genotypes through a pinned structural mask only.
Never reads or copies the original observed nucleotide sequences.
"""
import collections,hashlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
DESIGN=BASE.parent/'bpp-matched-difficulty-design-20261005-0607z'
LAYOUT=DESIGN/'LOCAL-ALIAS-MASK-CONTRACT.json'
LAYOUT_SHA='69be93f6312f5bdba7f58baa5db7da419ccda3234e2309df34febc0594f014be'
COUNTS={'K':6,'C':10,'L':14,'H':2}
def digest(data):return hashlib.sha256(data).hexdigest()
def bounded_bytes(path,limit=2097152):
    if path.is_symlink() or not path.is_file() or path.stat().st_size>limit:raise ValueError('input file type/size rejected')
    return path.read_bytes()
def parse_alignments(data):
    lines=[x.strip() for x in data.decode().splitlines() if x.strip()];pos=0;loci=[]
    while pos<len(lines):
        n,length=map(int,lines[pos].split());pos+=1
        if n<=0 or length<=0:raise ValueError('nonpositive locus size')
        rows=[];seen=set()
        for line in lines[pos:pos+n]:
            parts=line.split();label=parts[0];seq=''.join(parts[1:]).upper()
            if label in seen or len(seq)!=length:raise ValueError('duplicated/truncated sequence')
            seen.add(label);rows.append((label,seq))
        if len(rows)!=n:raise ValueError('truncated locus')
        loci.append((length,rows));pos+=n
    return loci

def project_data(full_data,map_data,layout):
    mapping={}
    for line in map_data.decode().splitlines():
        if not line.strip():continue
        label,pop=line.split()
        if label in mapping:raise ValueError('duplicate map key')
        mapping[label]=pop
    expected_map={p.lower()+str(i):p for p,n in COUNTS.items() for i in range(1,n+1)}
    if mapping!=expected_map:raise ValueError('unexpected generated full map')
    expected_labels={p+'^'+label for label,p in mapping.items()}
    loci=parse_alignments(full_data)
    if len(loci)!=5 or len(layout['loci'])!=5 or layout['simulation_individuals_per_population']!=COUNTS:raise ValueError('incorrect layout dimensions')
    outputs=[];report=[]
    for index,((length,rows),mask) in enumerate(zip(loci,layout['loci']),1):
        full=dict(rows)
        if length!=489 or len(rows)!=32 or set(full)!=expected_labels:raise ValueError('incorrect generated full locus')
        if any(set(seq)-set('ACGTRYSWKM') for seq in full.values()):raise ValueError('unexpected generated alphabet')
        if mask['locus']!=index or mask['length'] not in range(1,length+1):raise ValueError('invalid crop specification')
        projected=[];seen=set();questions=0
        for row in mask['rows']:
            if set(row)!={'synthetic_label','population','question_mark_sites_1based'}:raise ValueError('unexpected mask payload')
            label=row['synthetic_label'];sites=row['question_mark_sites_1based']
            if label not in full or label in seen or label.split('^')[0]!=row['population']:raise ValueError('incorrect projected sample identity')
            if len(sites)!=len(set(sites)) or any(type(k) is not int or not 1<=k<=mask['length'] for k in sites):raise ValueError('invalid question-mark index')
            seen.add(label);seq=list(full[label][:mask['length']])
            for k in sites:seq[k-1]='?'
            projected.append((label,''.join(seq)));questions+=len(sites)
        outputs.append(str(len(projected))+' '+str(mask['length'])+'\n'+'\n'.join(label+'  '+seq for label,seq in projected)+'\n\n')
        report.append({'locus':index,'length':mask['length'],'rows':len(projected),'gene_copies':2*len(projected),'population_counts':dict(collections.Counter(label.split('^')[0] for label,_ in projected)),'question_marks':questions})
    if [r['rows'] for r in report]!=[21,28,28,24,30] or [r['length'] for r in report]!=[489,455,440,285,457] or [r['question_marks'] for r in report]!=[0,0,0,0,7]:raise ValueError('declared projected layout changed')
    return ''.join(outputs).encode(),map_data,report

def project(sim=None,out=None):
    sim=Path(sim) if sim is not None else BASE/'runs'/'simulation-seed21001'
    out=Path(out) if out is not None else BASE/'runs'/'projected-seed21001'
    layout_bytes=bounded_bytes(LAYOUT)
    if digest(layout_bytes)!=LAYOUT_SHA:raise ValueError('reviewed layout changed')
    terminal_bytes=bounded_bytes(sim/'TERMINAL.json');terminal=json.loads(terminal_bytes)
    if terminal['status']!='EXECUTION_EXIT_ZERO' or not terminal['inputs_stable'] or terminal['settings']['seed']!=21001:raise ValueError('simulation not admitted for projection')
    inventory={x['path']:x['sha256'] for x in terminal['output_inventory']}
    inputs={name:bounded_bytes(sim/name) for name in ['full-synthetic.txt','full-synthetic.Imap.txt']}
    for name,data in inputs.items():
        if digest(data)!=inventory[name]:raise ValueError('simulation output changed')
    data,mapping,report=project_data(inputs['full-synthetic.txt'],inputs['full-synthetic.Imap.txt'],json.loads(layout_bytes))
    out.mkdir(parents=True,exist_ok=False)
    try:
        (out/'matched-synthetic.txt').write_bytes(data);(out/'matched-synthetic.Imap.txt').write_bytes(mapping)
        after={name:digest(bounded_bytes(sim/name)) for name in inputs}
        if any(after[name]!=digest(value) for name,value in inputs.items()):raise ValueError('simulation originals changed during projection')
        receipt={'schema':'model-matched-projection-v1','status':'PROJECTED_AND_VALIDATED','simulation_terminal_sha256':digest(terminal_bytes),'layout_sha256':LAYOUT_SHA,'projector_sha256':digest(Path(__file__).read_bytes()),'simulation_inputs':{n:digest(b) for n,b in inputs.items()},'simulation_inputs_after':after,'output_inventory':[{'path':n,'bytes':(out/n).stat().st_size,'sha256':digest((out/n).read_bytes())} for n in ['matched-synthetic.txt','matched-synthetic.Imap.txt']],'loci':report,'observed_alleles_copied':False,'full_genealogies_used_as_inference_input':False,'runtime_inference_admission':False}
        (out/'PROJECTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
        return receipt
    except BaseException as error:
        (out/'PROJECTION-FAILURE.json').write_text(json.dumps({'schema':'projection-failure-v1','status':'PROJECTION_FAILURE','error_type':type(error).__name__,'error':str(error)},indent=2)+'\n')
        raise

if __name__=='__main__':print(json.dumps(project(),indent=2))
