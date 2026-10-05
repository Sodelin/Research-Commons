"""Static fixed-design compiler only. It never invokes BPP or samples data."""
import hashlib,json
from fractions import Fraction as F
from pathlib import Path
BASE=Path(__file__).resolve().parent
BINARY=BASE.parent/'bpp-sequence-pilot-20261005/runtime/bpp-4.8.7-linux-x86_64/bin/bpp'
BINARY_SHA='6c8828704e1037788e02d6943cc6cbb61d05d6aadbdd976095b71fc965e8e90e'
DESIGN_SHA='6e157ef710722c0dac8ed51ffcd5206037ffebf6dc24997f67e3ef11f5e3c6e4'
SEED=202610051;M=1024
TRUTH={'h':'1/16','u':'1/16','v':'1/16','rA':'1','rB':'2','rC':'4','rAB':'1','rR':'2','g':'1/4'}
ALIASES={'A^a1':'A1','A^a2':'A2','B^b1':'B1','B^b2':'B2','C^c1':'C1','C^c2':'C2'}
def sha(raw):return hashlib.sha256(raw).hexdigest()
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def exact_decimal(value):
    q=F(value);d=q.denominator
    if d&(d-1):raise ValueError('only exact dyadic control parameters admitted')
    k=d.bit_length()-1;negative=q<0;n=abs(q.numerator)*5**k
    if not k:s=str(n)
    else:
        digits=str(n).rjust(k+1,'0');s=(digits[:-k]+'.'+digits[-k:]).rstrip('0').rstrip('.')
    return ('-' if negative else '')+s

def compile_control():
    x={key:F(value) for key,value in TRUTH.items()};h=x['h'];A=h+x['u'];T=A+x['v'];g=x['g'];theta={key:2/x['r'+key] for key in ('A','B','C','AB','R')};D=exact_decimal
    tree=f"((A #{D(theta['A'])}, (B #{D(theta['B'])})H[&phi={D(1-g)},&tau-parent=yes]:{D(h)} #{D(theta['B'])})AB:{D(A)} #{D(theta['AB'])}, (H[&phi={D(g)},&tau-parent=no], C #{D(theta['C'])})CS:{D(h)} #{D(theta['C'])})R:{D(T)} #{D(theta['R'])};"
    control=f"seed = {SEED}\nseqfile = generated.txt\ntreefile = generated.trees\nImapfile = generated.Imap.txt\nspecies&tree = 3 A B C\n  2 2 2\n  {tree}\nphase = 0 0 0\nloci&length = {M} 2\nclock = 1\nlocusrate = 0\nmodel = 0\nalpha_siterate = 1 0\n".encode()
    roles={'A':{'tau':'0','theta':str(theta['A'])},'B':{'tau':'0','theta':str(theta['B'])},'C':{'tau':'0','theta':str(theta['C'])},'AB':{'tau':str(A),'theta':str(theta['AB'])},'CS':{'tau':str(h),'theta':str(theta['C'])},'R':{'tau':str(T),'theta':str(theta['R'])},'H_main':{'tau':str(h),'theta':str(theta['B']),'htau':1,'phi':str(1-g)},'H_mirror':{'tau':str(h),'theta':'-1','htau':0,'phi':str(g)}}
    receipt={'schema':'fixed-msci-simulation-compilation-v1','design_sha256':DESIGN_SHA,'binary_sha256':BINARY_SHA,'control_sha256':sha(control),'seed':SEED,'loci':M,'sites_per_locus':2,'copies_per_population':2,'physical_truth':TRUTH,'expected_node_roles':roles,'label_aliases':ALIASES,'graph_children':{'R':['AB','CS'],'AB':['A','H_main'],'CS':['C','H_mirror'],'H_main':['B'],'H_mirror':[],'A':[],'B':[],'C':[]},'graph_parents':{'R':None,'AB':'R','CS':'R','H_main':'AB','H_mirror':'CS','A':'AB','B':'H_main','C':'CS'},'backward_pulse_direction':'B_to_C','class':'synthetic_model_check','ideal_algorithm_source_reviewed':True,'finite_rng_distribution_certified':False,'iid_randomness_certified':False,'new_biological_data':False,'no_generator_invocation':True,'thread_count':1,'thread_count_basis':'pinned simulation source default and thread-index-zero draw path','numeric_table_index_offset':1,'network_tau_field_is_flag':True,'population_table_tau_field_is_age':True}
    return control,receipt

def prepare(folder):
    folder=Path(folder);folder.mkdir(exist_ok=False);control,receipt=compile_control()
    (folder/'control.ctl').write_bytes(control);(folder/'COMPILATION.json').write_bytes(canonical(receipt))
    return {'control_sha256':sha(control),'compilation_sha256':sha(canonical(receipt))}
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();print(json.dumps(prepare(a.output)))
