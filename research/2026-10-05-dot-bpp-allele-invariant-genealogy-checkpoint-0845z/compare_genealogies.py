"""Read-only complete-trace rooted-topology comparison modulo within-individual swaps.
Branch times are deliberately ignored. Clades form a multiset, not presence indicators.
"""
import collections,hashlib,importlib.util,json,math,re,time
from pathlib import Path
BASE=Path(__file__).resolve().parent;ROOT=BASE.parent
PIN_SHA='41c2f0ebb042ac0dcd8650ffae24f9a35b350845cc06ca553075e63783d75925'
HELPER=ROOT/'bpp-matched-difficulty-execution-20261005-0645z/summarize_matched.py'
HELPER_SHA='fc1458faa22872548306eff7a8f0020614ac11b043cdc17716c1fb70db941c7d'
N=5000;MAX_INPUT_BYTES=16*1024*1024;MAX_SECONDS=180

def sha(raw):return hashlib.sha256(raw).hexdigest()
def hashed(value):return sha(json.dumps(value,separators=(',',':'),ensure_ascii=True).encode())
def read_small(p,limit=MAX_INPUT_BYTES):
    if p.is_symlink() or p.stat().st_size>limit:raise ValueError('symlink/oversized input')
    return p.read_bytes()

def authenticated_input(folder,name,key,terminal):
    raw=read_small(folder/name);h=sha(raw)
    if h!=terminal['input_hashes_before'][key] or h!=terminal['input_hashes_after'][key]:raise ValueError('changed input')
    entries=[x for x in terminal['output_inventory'] if x['path']==name]
    if len(entries)>1:raise ValueError('duplicate input inventory')
    if entries and (entries[0]['sha256']!=h or entries[0]['bytes']!=len(raw)):raise ValueError('input inventory mismatch')
    return raw

def parse_map(raw):
    popmap={}
    for line in raw.decode().splitlines():
        fields=line.split()
        if not fields:continue
        if len(fields)!=2 or fields[0] in popmap:raise ValueError('invalid/duplicate map record')
        popmap[fields[0]]=fields[1]
    if not popmap:raise ValueError('empty map')
    return popmap

class Parser:
    def __init__(self,text):
        if len(text)>32768:raise ValueError('oversized genealogy line')
        self.s=text;self.i=0;self.leaves=[]
    def branch(self):
        if self.i>=len(self.s) or self.s[self.i]!=':':raise ValueError('missing branch length')
        self.i+=1;m=re.match(r'(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?',self.s[self.i:])
        if not m:raise ValueError('invalid nonnegative branch length')
        value=float(m.group());self.i+=len(m.group())
        if not math.isfinite(value):raise ValueError('nonfinite branch length')
    def node(self,depth=0):
        if depth>128 or self.i>=len(self.s):raise ValueError('invalid tree depth/end')
        if self.s[self.i]=='(':
            self.i+=1;a=self.node(depth+1)
            if self.i>=len(self.s) or self.s[self.i]!=',':raise ValueError('binary comma required')
            self.i+=1;b=self.node(depth+1)
            if self.i>=len(self.s) or self.s[self.i]!=')':raise ValueError('binary closing node required')
            self.i+=1;node=(a,b)
        else:
            m=re.match(r'[^\s(),:;\[\]]+',self.s[self.i:])
            if not m:raise ValueError('leaf required')
            node=m.group();self.i+=len(node);self.leaves.append(node)
        self.branch();return node
    def parse(self):
        node=self.node()
        if self.i>=len(self.s) or self.s[self.i]!=';':raise ValueError('missing final semicolon')
        tail=self.s[self.i+1:]
        m=re.fullmatch(r' \[TH=(\d+(?:\.\d+)?), TL=(\d+(?:\.\d+)?)\]',tail)
        if not m or any(not math.isfinite(float(x)) for x in m.groups()):raise ValueError('invalid genealogy metadata/tail')
        return node

def canonical(node,colors):
    if isinstance(node,str):return ('L',colors[node])
    return ('I',*sorted([canonical(node[0],colors),canonical(node[1],colors)]))

def clade_vectors(node,index):
    """Every internal node except root contributes one occurrence, including duplicates."""
    vectors=[]
    def walk(x,is_root=False):
        if isinstance(x,str):return collections.Counter({index[x]:1})
        c=walk(x[0])+walk(x[1])
        if not is_root:vectors.append(tuple(sorted(c.items())))
        return c
    walk(node,True);return vectors

def total_variation(a,b):
    na=sum(a.values());nb=sum(b.values())
    if not na or not nb:raise ValueError('empty occurrence law')
    return .5*sum(abs(a[k]/na-b[k]/nb) for k in a.keys()|b.keys())

def inspect_trace(raw,expected,popmap):
    lines=raw.decode().splitlines()
    if len(lines)!=N or not raw.endswith(b'\n'):raise ValueError('all5000 complete rows required')
    individuals={x.rsplit('.',1)[0] for x in expected}
    if len(expected)!=2*len(individuals) or expected!={x+'.'+a for x in individuals for a in ['1','2']}:raise ValueError('exact diploid pairs required')
    if not 4<=len(expected)<=64:raise ValueError('outside declared tip bound')
    identity={x:(x,popmap[x.rsplit('^',1)[1]]) for x in individuals}
    colors={x:identity[x.rsplit('.',1)[0]] for x in expected}
    ordered=sorted(identity.values());identity_hash=hashed(ordered);lookup={v:i for i,v in enumerate(ordered)};index={x:lookup[colors[x]] for x in expected}
    full=collections.Counter();colored=collections.Counter();clades=collections.Counter();halves=[collections.Counter(),collections.Counter()];sizes={}
    for j,line in enumerate(lines):
        parser=Parser(line);node=parser.parse()
        if len(parser.leaves)!=len(expected) or set(parser.leaves)!=expected:raise ValueError('wrong or duplicate leaf multiset')
        full[hashed(canonical(node,{x:x for x in expected}))]+=1;colored[hashed(canonical(node,colors))]+=1
        vectors=clade_vectors(node,index)
        if len(vectors)!=len(expected)-2:raise ValueError('wrong binary internal clade count')
        for vector in vectors:
            key=hashed((identity_hash,vector));clades[key]+=1;halves[int(j>=N//2)][key]+=1;sizes[key]=sum(x[1] for x in vector)
        if j%100==0 and time.monotonic()>DEADLINE:raise TimeoutError('read-only comparison wall budget exceeded')
    return {'full':full,'colored':colored,'clades':clades,'halves':halves,'sizes':sizes,'tip_count':len(expected),'individual_count':len(individuals),'identity_map_sha256':identity_hash,'genealogy_sha256':sha(raw)}

def compare_locus(a,b):
    if any(a[k]!=b[k] for k in ['tip_count','individual_count','identity_map_sha256']):raise ValueError('different biological identities')
    n=sum(a['clades'].values());m=sum(b['clades'].values());union=a['clades'].keys()|b['clades'].keys()
    largest=sorted(union,key=lambda k:(-abs(a['clades'][k]/n-b['clades'][k]/m),k))[:10]
    return {'tips':a['tip_count'],'individuals':a['individual_count'],'identity_map_sha256':a['identity_map_sha256'],'genealogy_sha256':[a['genealogy_sha256'],b['genealogy_sha256']],'samples_per_chain':N,'clade_occurrences_per_tree':a['tip_count']-2,'clade_occurrences_per_chain':[n,m],'labelled_topology_unique':[len(a['full']),len(b['full'])],'allele_swap_orbit_unique':[len(a['colored']),len(b['colored'])],'labelled_topology_support_intersection':len(a['full'].keys()&b['full'].keys()),'allele_swap_orbit_support_intersection':len(a['colored'].keys()&b['colored'].keys()),'labelled_empirical_topology_tv':total_variation(a['full'],b['full']),'orbit_empirical_topology_tv':total_variation(a['colored'],b['colored']),'normalized_clade_occurrence_tv':total_variation(a['clades'],b['clades']),'within_chain_half_clade_occurrence_tv':[total_variation(*a['halves']),total_variation(*b['halves'])],'largest_ten_descriptive_clade_occurrence_differences':[{'clade_vector_sha256':k,'gene_copies_in_clade':a['sizes'].get(k,b['sizes'].get(k)),'counts':[a['clades'][k],b['clades'][k]],'occurrence_probabilities':[a['clades'][k]/n,b['clades'][k]/m]} for k in largest]}

DEADLINE=float('inf')
def main():
    global DEADLINE
    DEADLINE=time.monotonic()+MAX_SECONDS
    pinraw=read_small(BASE/'INPUT-PINS.json')
    if sha(pinraw)!=PIN_SHA or sha(read_small(HELPER))!=HELPER_SHA:raise ValueError('reviewed source/pin changed')
    spec=importlib.util.spec_from_file_location('reviewed_labels',HELPER);helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    pins=json.loads(pinraw);out={}
    for dataset,records in pins.items():
        sources=[]
        for rec in records:
            folder=ROOT/rec['path'];traw=read_small(folder/'TERMINAL.json');t=json.loads(traw)
            if sha(traw)!=rec['terminal_sha256'] or t['status']!='EXECUTION_EXIT_ZERO' or not t['inputs_stable'] or t['settings']['nsample']!=N:raise ValueError('stable complete admitted terminal required')
            inv={x['path']:x for x in t['output_inventory']}
            def auth(name,folder=folder,inv=inv):
                raw=read_small(folder/name)
                if sha(raw)!=inv[name]['sha256'] or len(raw)!=inv[name]['bytes']:raise ValueError('changed inventoried output')
                return raw
            alignment='frogs.txt' if dataset=='frog' else 'matched-synthetic.txt';mapname='frogs.Imap.txt' if dataset=='frog' else 'matched-synthetic.Imap.txt'
            al=authenticated_input(folder,alignment,'alignment',t);mp=authenticated_input(folder,mapname,'map',t)
            if sha(al)!=t['input_hashes_before']['alignment'] or sha(mp)!=t['input_hashes_before']['map']:raise ValueError('changed input')
            popmap=parse_map(mp)
            labels=helper.expected_locus_labels(al)
            if len(labels)!=5:raise ValueError('five loci required')
            sources.append((auth,labels,popmap,t))
        if len(sources)!=2:raise ValueError('declared pair required')
        if sources[0][3]['input_hashes_before']['alignment']!=sources[1][3]['input_hashes_before']['alignment'] or sources[0][3]['input_hashes_before']['map']!=sources[1][3]['input_hashes_before']['map']:raise ValueError('different input target')
        loci=[]
        for i in range(5):
            pair=[inspect_trace(auth(f'result.gtree.L{i+1}'),labels[i],popmap) for auth,labels,popmap,t in sources]
            loci.append({'locus':i+1,**compare_locus(*pair)})
        out[dataset]={'terminal_sha256':[r['terminal_sha256'] for r in records],'loci':loci}
    return {'schema':'allele-swap-invariant-genealogy-diagnostic-v1','datasets':out,'source_sha256':sha(Path(__file__).read_bytes()),'input_manifest_sha256':PIN_SHA,'label_helper_sha256':HELPER_SHA,'all_predeclared_rows_used':True,'branch_times_discarded':True,'clade_law':'Choose a retained tree uniformly, then a nonroot internal node uniformly. Count-vector multiplicities retained; not a per-tree presence probability.','interpretation':'Descriptive empirical marginal comparisons only. High-dimensional topology support can be disjoint even under well-mixed draws. Within-individual allele swaps are quotiented; other individuals/populations stay distinct. Clade vectors intentionally lose topology information. Neither TV nor overlap certifies convergence or identifies the likelihood discrepancy cause.','posterior_reliability_released':False,'new_engine_run':False}
if __name__=='__main__':print(json.dumps(main(),indent=2))
