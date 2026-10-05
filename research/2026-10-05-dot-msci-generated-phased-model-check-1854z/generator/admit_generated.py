"""Source/graph/numeric-table and complete two-site output admission, no inference."""
import hashlib,importlib.util,json,re,sys
from collections import Counter
from decimal import Decimal
from fractions import Fraction as F
from pathlib import Path
import compile_control as design
BASE=Path(__file__).resolve().parent
PARSER=BASE.parent/'bpp-allele-invariant-genealogy-20261005-0828z/compare_genealogies.py'
PARSER_SHA='a00f986e142898dbfe5c5b76cdd50d855e9a9f4c24a18205afa45814bb517436'
MAX_BYTES=16*1024**2

def no_duplicates(pairs):
    d={}
    for k,v in pairs:
        if k in d:raise ValueError('duplicate JSON field')
        d[k]=v
    return d

def read(path,expected=None):
    path=Path(path)
    if path.is_symlink() or path.stat().st_size>MAX_BYTES:raise ValueError('read cap/link')
    raw=path.read_bytes()
    if len(raw)>MAX_BYTES or expected is not None and design.sha(raw)!=expected:raise ValueError('read identity/cap')
    return raw

def load_parser():
    read(PARSER,PARSER_SHA);spec=importlib.util.spec_from_file_location('_semantic_retained_genealogy_parser',PARSER);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def extract_panels(raw,m):
    if type(m) is not int or not 1<=m<=design.M:raise ValueError('fixed positive locus count cap')
    if not raw.endswith(b'\n'):raise ValueError('incomplete alignment final line')
    lines=[line.strip() for line in raw.decode('ascii').splitlines() if line.strip()];offset=0;loci=[]
    for i in range(m):
        if offset>=len(lines) or lines[offset].split()!=['6','2']:raise ValueError('expected complete six-by-two header')
        offset+=1;calls={};seen=set()
        for _ in range(6):
            if offset>=len(lines):raise ValueError('incomplete panel')
            fields=lines[offset].split();offset+=1
            if len(fields)!=2 or fields[0] not in design.ALIASES or fields[0] in seen or not re.fullmatch('[ACGT]{2}',fields[1]):raise ValueError('haploid label/call identity')
            seen.add(fields[0]);calls[design.ALIASES[fields[0]]]=fields[1]
        if seen!=set(design.ALIASES):raise ValueError('incomplete six-copy panel')
        loci.append({'id':f'locus_{i+1:06d}','columns':[1,2],'calls':calls})
    if offset!=len(lines):raise ValueError('extra panel content')
    return {'schema':'complete-six-copy-two-site-loci-v1','loci':loci}

def table_block(text,header):
    lines=text.splitlines();positions=[i for i,line in enumerate(lines) if header(line)]
    if len(positions)!=1:raise ValueError('unique complete table header required')
    rows=[]
    for line in lines[positions[0]+1:]:
        if not line.strip():break
        rows.append(line)
    return rows

def validate_settings(text,compilation):
    if not re.search(r'\bbpp v4\.8\.7(?:_|[,\s])',text) or text.count('Substitution model: JC69')!=1:raise ValueError('vendor version/JC identity')
    species=re.findall(r'^3 species:\s*(.*?)\s*$',text,re.M)
    if len(species)!=1 or not re.fullmatch(r'[ABC] \(2\) [ABC] \(2\) [ABC] \(2\)',species[0]) or Counter(re.findall(r'([ABC]) \((\d+)\)',species[0]))!=Counter([('A','2'),('B','2'),('C','2')]):raise ValueError('three haploid sample counts')
    if len(re.findall(r'^Hybridization events:\s*1\s*$',text,re.M))!=1 or len(re.findall(r'^Bidirectional introgressions:\s*0\s*$',text,re.M))!=1:raise ValueError('single unidirectional event')
    lines=table_block(text,lambda x:x.split()==['Label','Node','Child1','Child2','Parent']);nodes={}
    row=re.compile(r'^\s*(\S+)\s+(\d+)\s+(\d+|N/A)\s+(\d+|N/A)\s+(\d+|N/A)(.*)$')
    for line in lines:
        match=row.fullmatch(line)
        if not match:raise ValueError('network row grammar')
        label,index,c1,c2,parent,tail=match.groups();index=int(index)
        if index in nodes:raise ValueError('duplicate network node')
        flag=re.search(r'\[tau = ([01]), phi = ([0-9]+\.[0-9]{6}), prop_tau = [01], has_phi = [01]\]',tail)
        nodes[index]={'label':label,'children':[int(x) for x in (c1,c2) if x!='N/A'],'parent':None if parent=='N/A' else int(parent),'mirror':'Mirrored hybridization node' in tail,'htau':None if flag is None else int(flag[1]),'phi':None if flag is None else str(F(flag[2]))}
    if set(nodes)!=set(range(8)) or Counter(n['label'] for n in nodes.values())!=Counter(['A','B','C','AB','CS','R','H','H']):raise ValueError('complete eight-node network')
    roles={}
    for i,n in nodes.items():
        role=('H_mirror' if n['mirror'] else 'H_main') if n['label']=='H' else n['label']
        if role in roles or n['label']!='H' and n['mirror']:raise ValueError('hybrid role identity')
        roles[role]=i
    reverse={i:role for role,i in roles.items()}
    for role,i in roles.items():
        n=nodes[i]
        if any(x not in reverse for x in n['children']) or n['parent'] is not None and n['parent'] not in reverse:raise ValueError('network pointer outside table')
        if sorted(reverse[x] for x in n['children'])!=sorted(compilation['graph_children'][role]) or (None if n['parent'] is None else reverse[n['parent']])!=compilation['graph_parents'][role]:raise ValueError('pulse/backbone connectivity')
        expected=compilation['expected_node_roles'][role]
        if role.startswith('H_') and (n['htau']!=expected['htau'] or n['phi']!=expected['phi']):raise ValueError('pulse phi/parent flag')
        if not role.startswith('H_') and n['htau'] is not None:raise ValueError('extra hybrid annotation')
    headers=[];all_lines=text.splitlines()
    for j,line in enumerate(all_lines):
        if line.strip()=='Map of populations and ancestors (1 in map indicates ancestor):':headers.append(j)
    if len(headers)!=1:raise ValueError('unique numeric population table')
    start=headers[0]+1
    if all_lines[start].split()!=['Species']+[str(i) for i in range(1,9)]:raise ValueError('population table index header')
    numeric={}
    for line in all_lines[start+1:]:
        if not line.strip():break
        match=re.fullmatch(r'\s*(\d+)\s+(\S+)\s+((?:[01]\s+){8})tau\s*=\s*(-?\d+\.\d{6})\s+theta\s*=\s*(-?\d+\.\d{6})\s*',line)
        if not match:raise ValueError('numeric population row grammar')
        row_id,label,bits,tau,theta=match.groups();index=int(row_id)-1
        if index in numeric or index not in nodes or label!=nodes[index]['label']:raise ValueError('numeric/network index join')
        role=reverse[index];values={'tau':str(F(tau)),'theta':str(F(theta))}
        if any(values[key]!=compilation['expected_node_roles'][role][key] for key in values):raise ValueError('runtime numeric age/theta differs from frozen truth')
        numeric[index]={'role':role,**values,'ancestor_bits':[int(x) for x in bits.split()]}
    if set(numeric)!=set(nodes):raise ValueError('incomplete numeric population table')
    return {'network_nodes':nodes,'population_rows':numeric,'node_roles':roles,'network_tau_is_flag':True,'population_tau_is_numeric_age':True,'numeric_values_exact_at_declared_six_decimal_precision':True,'backward_direction':'B_to_C','positive_duration_population_count':7}

def admit(folder,terminal_sha,compiled_folder,compilation_sha):
    folder=Path(folder);compiled_folder=Path(compiled_folder)
    def reject(_):raise ValueError('nonfinite receipt number')
    terminal=json.loads(read(folder/'TERMINAL.json',terminal_sha),object_pairs_hook=no_duplicates,parse_float=Decimal,parse_constant=reject)
    if terminal['status']!='EXECUTION_EXIT_ZERO' or not terminal['pins_stable'] or terminal['runner_failure'] or terminal['cleanup_failure'] or terminal['inventory_failure']:raise ValueError('simulation terminal not admissible')
    compilation=json.loads(read(compiled_folder/'COMPILATION.json',compilation_sha),object_pairs_hook=no_duplicates)
    control,expected=design.compile_control()
    if compilation!=expected or read(folder/'control.ctl')!=control or read(compiled_folder/'control.ctl')!=control:raise ValueError('exact compiled design/control')
    for name,item in terminal['inventory'].items():
        raw=read(folder/name,item['sha256'])
        if len(raw)!=item['bytes']:raise ValueError('inventory byte count')
    text=read(folder/'stdout.log',terminal['inventory']['stdout.log']['sha256']).decode('utf-8')
    settings=validate_settings(text,compilation);parser=load_parser()
    imap=parser.parse_map(read(folder/'generated.Imap.txt',terminal['inventory']['generated.Imap.txt']['sha256']))
    if imap!={key.split('^')[1]:value[0] for key,value in design.ALIASES.items()}:raise ValueError('haploid Imap identity')
    dataset=extract_panels(read(folder/'generated.txt',terminal['inventory']['generated.txt']['sha256']),design.M)
    tree_raw=read(folder/'generated.trees',terminal['inventory']['generated.trees']['sha256'])
    if not tree_raw.endswith(b'\n'):raise ValueError('incomplete genealogy file')
    trees=tree_raw.decode('ascii').splitlines()
    if len(trees)!=design.M:raise ValueError('all generated genealogies required')
    for line in trees:
        item=parser.Parser(line);item.parse()
        if len(item.leaves)!=6 or set(item.leaves)!=set(design.ALIASES):raise ValueError('six phased genealogy leaves required')
    canonical=design.canonical(dataset)
    selection=design.sha(design.canonical([{'id':x['id'],'columns':x['columns']} for x in dataset['loci']]))
    receipt={'schema':'synthetic-model-check-runtime-admission-v1','classification':'synthetic_model_check','generator_terminal_sha256':terminal_sha,'compilation_sha256':compilation_sha,'control_sha256':design.sha(control),'dataset_sha256':design.sha(canonical),'selection_sha256':selection,'loci':design.M,'sites_per_locus':2,'genealogies_validated':design.M,'labels':design.ALIASES,'physical_truth':design.TRUTH,'settings':settings,'binary_sha256':design.BINARY_SHA,'genealogy_parser_sha256':PARSER_SHA,'ideal_source_semantics_reviewed':True,'finite_program_law_certified':False,'iid_randomness_certified':False,'data_confidence_certificate_issued':False,'source_feasibility_or_coverage_measured':False}
    return canonical,receipt
