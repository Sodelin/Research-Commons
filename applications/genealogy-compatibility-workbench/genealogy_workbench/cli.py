from pathlib import Path
import argparse,json,sys
from . import __version__
from .core import InputError,Source,Experiment,law_entries,exact_sort,equivalence,keys
from .statistics import statistical_sort
from .provenance import receipt,verify_receipt,registry,verify_vendor


def run(operation,data):
    if operation=='sort-exact':return exact_sort(data)
    if operation=='sort-loci':return statistical_sort(data)
    if operation=='law':
        keys(data,['source','experiment'],['source','experiment'],'law input')
        s=Source.read(data['source']);e=Experiment.read(data['experiment'])
        return {'evidence_tier':'exact_finite_source_forward','source_id':s.source_id,'experiment_id':e.experiment_id,
            'probabilities':law_entries(s,e),'source_model':data['source'],'experiment':data['experiment'],
            'arithmetic':'exact rational','lean_kernel_checked':False,
            'observation_boundary':'Entering interface roots are declared, not inferred from specimen count or FASTA'}
    if operation=='equivalent':
        keys(data,['left','right'],['left','right'],'equivalence input')
        return equivalence(Source.read(data['left']),Source.read(data['right']))
    if operation=='recover-trailing-four':
        from .inference import recover_trailing_four
        return recover_trailing_four(data)
    if operation=='sequence':
        from .sequence import adapt_sequence
        return adapt_sequence(data)
    raise InputError(f'Unknown replay operation: {operation}')


def summary(output):
    r=output.get('result',output)
    lines=['Genealogy compatibility workbench '+__version__]
    for k in ['status','evidence_tier','coverage','confidence_scope','g6_target_certificate']:
        if k in r:lines.append(k.replace('_',' ').capitalize()+': '+str(r[k]))
    if 'compatible_source_ids' in r:lines.append('Compatible sources: '+', '.join(r['compatible_source_ids']))
    if r.get('answer') is not None:lines.append('Answer: '+json.dumps(r['answer'],sort_keys=True))
    if len(r.get('target_answers',[]))>1:
        lines.append('Alternatives: '+json.dumps(r['target_answers'],sort_keys=True))
    if 'probabilities' in r:lines.append('Exact output coordinates: '+str(len(r['probabilities'])))
    lines.append('Whole-program Lean certification: no')
    return '\n'.join(lines)+'\n'


def load_json(path):
    def object_pairs(pairs):
        out={}
        for key,value in pairs:
            if key in out:raise InputError(f'Duplicate JSON object key: {key}')
            out[key]=value
        return out
    return json.loads(path.read_text(),object_pairs_hook=object_pairs)


def main(argv=None):
    parser=argparse.ArgumentParser(description='Private exact/conditional/exploratory genealogy compatibility workbench')
    parser.add_argument('--version',action='version',version=__version__)
    sub=parser.add_subparsers(dest='command',required=True)
    for name in ['law','sort-exact','sort-loci','equivalent','recover-trailing-four','sequence']:
        p=sub.add_parser(name);p.add_argument('input',type=Path);p.add_argument('--output',type=Path);p.add_argument('--text',action='store_true')
    p=sub.add_parser('verify-receipt');p.add_argument('input',type=Path);p.add_argument('receipt',type=Path)
    p=sub.add_parser('unsupported');p.add_argument('feature',choices=['general-g3-recognition','unknown-size-g4-stopping','full-g5-target','whole-program-lean'])
    sub.add_parser('provenance');sub.add_parser('compare-life-science')
    p=sub.add_parser('demo');p.add_argument('--output-dir',type=Path,default=Path('demo-output'))
    args=parser.parse_args(argv)
    try:
        verify_vendor()
        if args.command=='demo':
            from .demo import demo
            output=demo(args.output_dir)
        elif args.command=='verify-receipt':output=verify_receipt(load_json(args.input),load_json(args.receipt),run)
        elif args.command=='provenance':output=registry()
        elif args.command=='compare-life-science':
            from .benchmark import life_science_comparison
            output=life_science_comparison()
        elif args.command=='unsupported':output={'status':'UNSUPPORTED_ABSTAIN','feature':args.feature,
            'reason':{'general-g3-recognition':'Unrestricted finite-input recognition remains open; no implemented oracle',
                      'unknown-size-g4-stopping':'No unrestricted passive unknown-size stopping algorithm is available',
                      'full-g5-target':'The whole original-label calendar-law source-image compiler is not implemented',
                      'whole-program-lean':'Formal components are separate; this package is not whole-program Lean certified'}[args.feature]}
        else:
            data=load_json(args.input);output=receipt(args.command,data,run(args.command,data))
        text=json.dumps(output,indent=2,sort_keys=True,ensure_ascii=False)+'\n'
        if getattr(args,'output',None):args.output.write_text(text)
        print(summary(output) if getattr(args,'text',False) else text,end='')
        return 0
    except (InputError,OSError,json.JSONDecodeError) as exc:
        print(json.dumps({'status':'INVALID_INPUT_OR_BLOCKED','error':str(exc)}),file=sys.stderr);return 2

if __name__=='__main__':sys.exit(main())
