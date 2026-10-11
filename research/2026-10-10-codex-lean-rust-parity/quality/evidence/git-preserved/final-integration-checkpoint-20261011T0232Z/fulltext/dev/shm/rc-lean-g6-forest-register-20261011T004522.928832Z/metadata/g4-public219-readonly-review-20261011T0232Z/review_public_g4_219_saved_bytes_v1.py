"""Fixed-commit public G4-219 byte/record audit. No Lean/native/target calls."""
from pathlib import Path
import ast,collections,datetime,gzip,hashlib,io,json,os,re,resource,subprocess,traceback
resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
ROOT=Path('/workspace/Research-Commons')
OUT=Path(__file__).parent
COMMIT='de4d8fa1b3c56997df1b2a2e07b4ebc6e237ef6d'
BASE_COMMIT='3972858d5c896171f80d7bc5a32f3ed1e95a6583'
PACKET='research/2026-10-11-dot-g4-compiled-actual-span-0205z'
BASE_PACKET='research/2026-10-11-dot-accepted-connected-union1568-0133z'
PARSER=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/scripts/compare_natural141_owned_20261011_v2.py')
OLD_READER=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/commons1568-readonly-review-20261011T0200Z/review_public1568_saved_bytes.py')
OLD_REVIEW=OLD_READER.parent/'PUBLIC1568-SAVED-READONLY-REVIEW.json'
GIT=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-C',str(ROOT)]
ENV=dict(os.environ,GIT_OPTIONAL_LOCKS='0',GIT_OBJECT_DIRECTORY='/tmp/rc-cloud-git-objects-20261010T223739.438030Z',GIT_ALTERNATE_OBJECT_DIRECTORIES=str(ROOT/'.git/objects'))
STANDARD_AXIOMS={'propext','Classical.choice','Quot.sound'}
NEW_MODULES={'G4ActualOriginalSpanDiagonal':'8d90261bcb35833d982d3b1913563ce1d97b766cd54eefbf856613df0a1597ed','G4ActualOriginalSpanNaturalAverage':'e1be8c6d18e12db2d11df8ea74355b4bf7fabeaf530b629174fe4e9e1e39ccdd'}
OUTPUT_LIMIT=256*2**10


def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def file_pin(path):
    path = Path(path)
    h = hashlib.sha256()
    size = 0
    with path.open('rb') as f:
        while part := f.read(65536):
            size += len(part)
            h.update(part)
    return {'path': str(path), 'bytes': size, 'sha256': h.hexdigest()}

def record_hash(row):
    return hashlib.sha256(json.dumps(row, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()).digest()

def literal_imports(text):
    """Remove nested Lean block/line comments before reading import lines."""
    out = []
    depth = 0
    i = 0
    quoted = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                i += 1
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - i))
            i = end
        else:
            out.append(text[i])
            if text[i] == '"':
                quoted = True
            i += 1
    require(depth == 0, 'Unclosed source block comment')
    imports = []
    for line in ''.join(out).splitlines():
        stripped = line.strip()
        if stripped.startswith('public '):
            stripped = stripped[7:].lstrip()
        if stripped.startswith('import '):
            imports.extend(stripped[7:].split())
    return imports

class HashedRaw(io.RawIOBase):
    def __init__(self, raw):
        self.raw = raw
        self.sha = hashlib.sha256()
        self.size = 0
        super().__init__()

    def readable(self):
        return True

    def readinto(self, target):
        data = self.raw.read(len(target))
        if not data:
            return 0
        self.sha.update(data)
        self.size += len(data)
        target[:len(data)] = data
        return len(data)

    def close(self):
        if not self.closed:
            self.raw.close()
        super().close()

class AuditInput:
    def __init__(self, raw, label):
        self.raw = raw
        self.label = label
        self.metadata = None

    def open(self, encoding):
        return io.TextIOWrapper(io.BufferedReader(self.raw, 65536), encoding=encoding)

def get_record_parser():
    source = PARSER.read_text()
    require(digest(source.encode()) == '163f91e0f3ba1a140b853989493908bf88d7da8ca0667026ad7fc570de630f4a', 'Existing parser source changed')
    tree = ast.parse(source)
    selected = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'records']
    require(len(selected) == 1, 'Existing record parser not uniquely found')
    record_node = selected[0]
    require(sum(isinstance(n, ast.Return) for n in ast.walk(record_node)) == 1, 'Record parser return shape changed')

    class ExposeMetadata(ast.NodeTransformer):
        def visit_Return(self, node):
            call = ast.Expr(ast.Call(func=ast.Name(id='_capture', ctx=ast.Load()), args=[ast.Name(id='p', ctx=ast.Load()), ast.Name(id='prefix', ctx=ast.Load()), ast.Name(id='tail', ctx=ast.Load())], keywords=[]))
            return [call, node]

    record_node = ExposeMetadata().visit(record_node)
    module = ast.fix_missing_locations(ast.Module(body=[record_node], type_ignores=[]))

    def capture(p, prefix, tail):
        p.metadata = json.loads(prefix + '"declarations":[]' + tail)

    namespace = {'json': json, 're': re, '_capture': capture}
    exec(compile(module, str(PARSER) + ':records-only-metadata-hook', 'exec'), namespace)
    return namespace['records']


def git(*args):
    return subprocess.check_output(GIT+list(args),env=ENV)

def public(name,base=False):
    return git('show',(BASE_COMMIT+':'+BASE_PACKET if base else COMMIT+':'+PACKET)+'/'+name)

def pin_blob(path,body,oid):
    require(hashlib.sha1(('blob '+str(len(body))+'\0').encode()+body).hexdigest()==oid,'Git blob identity '+path)
    return {'path':path,'bytes':len(body),'sha256':digest(body),'git_blob':oid}

def no_module(row):
    return {key:value for key,value in row.items() if key!='module'}

def validate_metadata(metadata,modules,count,theorems):
    require(metadata['declaration_count']==count and metadata['theorem_declaration_count']==theorems,'Audit metadata counts')
    selected=metadata['selected_modules']
    require(len(selected)==len(set(selected))==len(modules) and set(selected)==set(modules),'Selected modules mismatch/duplicate')
    require(not metadata['owned_axioms'] and not metadata['nonstandard_axiom_rows'] and not metadata['missing_modules'],'Audit footer exclusions')

def review():
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    require(file_pin(OLD_READER)['sha256']=='1e44d1acec98e30bfe2f6331f97415d11f9c8ba74918f202ed21c2a88db9f930','Prior reader pin')
    require(file_pin(OLD_REVIEW)['sha256']=='dc9392e2b23e02b2cc5f8a6d9c2fedcec92f95a91fa9a5757020ccdf7a90a40b','Accepted1568 reviewer pin')
    require(git('cat-file','-t',COMMIT)==b'commit\n' and git('cat-file','-t',BASE_COMMIT)==b'commit\n','Fixed commit object type')
    manifest_raw=public('MANIFEST.json');manifest=json.loads(manifest_raw)
    rows=manifest['files'];expected={x['path']:x for x in rows}
    require(len(rows)==len(expected)==288 and manifest['source_modules']==219 and manifest['local_only_loader_payloads'] is True,'Packet manifest selection')
    tree={}
    for item in git('ls-tree','-r','-z',COMMIT,'--',PACKET).split(b'\0'):
        if not item:continue
        head,path=item.split(b'\t',1);mode,kind,oid=head.split()
        require(mode==b'100644' and kind==b'blob','Nonregular public artifact')
        rel=path.decode()[len(PACKET)+1:];tree[rel]=oid.decode()
    require(set(tree)==set(expected)|{'MANIFEST.json'},'Manifest/tree completeness')
    manifest_pin=pin_blob('MANIFEST.json',manifest_raw,tree['MANIFEST.json'])
    for path,row in expected.items():require(row['git_blob']==tree[path],'Manifest Git OID '+path)
    graph_raw=public('DEPENDENCY-GRAPH.json');graph=json.loads(graph_raw)
    require(digest(graph_raw)=='d6c850c7460c836610812b0f14ca3e12aebad9ad4d11c22e713855638c9f7cae','G4 graph known pin')
    profile=graph['targets']['candidate/g4-actual-span'];modules=profile['modules']
    require(len(modules)==219 and profile['roots']==['G4ActualOriginalSpanNaturalAverage'],'Exact profile')
    base_graph_raw=public('DEPENDENCY-GRAPH.json',True)
    require(digest(base_graph_raw)=='1a82a47a20257e9fa83bc88c786a55ca82d4dd245952cf4779a646f84a83d825','Prior public graph pin')
    base_modules=json.loads(base_graph_raw)['targets']['current/connected']['modules']
    require(len(base_modules)==1568,'Prior graph module count')
    require(set(modules)-set(base_modules)==set(NEW_MODULES),'Source additions not exactly two consumers')
    inherited_modules={name:row for name,row in modules.items() if name not in NEW_MODULES}
    require(len(inherited_modules)==217 and all(base_modules[name]==row for name,row in inherited_modules.items()),'Prerequisite graph/source/import changed')
    require(all(modules[name]['sha256']==sha for name,sha in NEW_MODULES.items()),'New source identity')
    seen=set()
    for name in profile['order']:
        require(name in modules and name not in seen,'Profile order duplicate/name')
        require(all(parent not in modules or parent in seen for parent in modules[name]['imports']),'Profile order not topological')
        seen.add(name)
    require(seen==set(modules) and not any(x.startswith('Mathlib.') for x in modules),'Complete profile/no owned Mathlib')
    projection_raw=public('PUBLIC-PROJECTIONS.json');projections=json.loads(projection_raw)
    projected={x['path']:x for x in projections}
    require(len(projections)==len(projected)==48,'Public projection inventory')
    bysha={}
    for name,row in modules.items():bysha.setdefault(row['sha256'],[]).append(name)
    source_verified=set();projection_verified=[];capture={};verified=[]
    batch=subprocess.Popen(GIT+['cat-file','--batch'],env=ENV,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    try:
        for path,row in expected.items():
            batch.stdin.write((row['git_blob']+'\n').encode());batch.stdin.flush()
            header=batch.stdout.readline().decode().strip().split()
            require(len(header)==3 and header[:2]==[row['git_blob'],'blob'],'Batch header '+path)
            size=int(header[2]);require(size==row['bytes'] and size<=2*2**20,'Blob size/bound '+path)
            body=batch.stdout.read(size);require(len(body)==size and batch.stdout.read(1)==b'\n','Truncated batch '+path)
            require(digest(body)==row['sha256'],'Manifest SHA '+path)
            verified.append(pin_blob(path,body,row['git_blob']))
            if path in projected:
                decoded=gzip.decompress(body) if path.endswith('.gz') else body
                require(digest(decoded)==projected[path]['projected_sha256'],'Projection decoded SHA '+path)
                if projected[path]['exact_raw_public']:require(digest(decoded)==projected[path]['raw_sha256'],'Exact raw public projection '+path)
                projection_verified.append(dict(projected[path],decoded_bytes=len(decoded)))
            if path.startswith('source-store/') and path.endswith('.lean'):
                sha=path.rsplit('/',1)[1][:-5];require(digest(body)==sha and sha in bysha,'Source-store name SHA')
                imports=literal_imports(body.decode())
                for module in bysha[sha]:
                    require(imports==modules[module]['imports'],'Source literal import '+module);source_verified.add(module)
            elif path in ('ACCEPTANCE.json','README.md','PUBLIC-PROJECTIONS.json','evidence/AUDIT-RESULT.json.gz','evidence/FINAL-RECEIPT.projected.json','evidence/RESULT.projected.json.gz','evidence/LAKE-ATTEMPT4-TERMINAL.json.projected','evidence/LOCAL-ONLY-TRACE-INDEX.json','reviews/FINAL-G4-219-REVIEW.json.projected','reviews/FULL-CONTEXT-MODULE-ATTRIBUTION-DELTA.json.projected','evidence/INHERITED-RECORD-COMPARISON.json.projected'):
                capture[path]=body
        batch.stdin.close();err=batch.stderr.read()
        require(batch.wait()==0 and not err,'Read-only Git batch error')
    finally:
        if batch.poll() is None:batch.kill();batch.wait()
        batch.stdout.close();batch.stderr.close()
    require(source_verified==set(modules) and len(projection_verified)==48,'Complete source/projection coverage')
    for module,sha in NEW_MODULES.items():
        require(expected['source-revisions/'+module+'.lean']['sha256']==sha,'Final revision SHA')
    parser=get_record_parser()
    gz=capture['evidence/AUDIT-RESULT.json.gz']
    require(digest(gz)=='f7325fdbecfc7e252a695decec1e247b3e4f7f90459a5e51073be12acd74e605','G4 compressed audit known pin')
    raw=HashedRaw(gzip.GzipFile(fileobj=io.BytesIO(gz),mode='rb'));audit=AuditInput(raw,'public219')
    records={};kinds=collections.Counter();attributed=collections.Counter()
    for row in parser(audit):
        name=row['name'];require(name not in records,'Duplicate219 declaration '+name)
        require(row['module'] in modules,'Audit owner outside profile')
        require(set(row['axioms']).issubset(STANDARD_AXIOMS) and row['kind']!='axiom','219 nonstandard/owned axiom')
        records[name]=row;kinds[row['kind']]+=1
        if row['module'] in NEW_MODULES:attributed[row['kind']]+=1
    require(len(records)==4381 and kinds['theorem']==2878,'Actual219 counts')
    require(raw.sha.hexdigest()=='964136ed38c4dbd2dc5f11b9c6fd9fd48ca0cd31627baa63db56002520c0e807','Exact decompressed219 audit identity')
    validate_metadata(audit.metadata,modules,4381,2878)
    require(sum(attributed.values())==45 and attributed['theorem']==30,'New source attribution counts')
    # Existing1568 is streamed directly from the fixed public gzip parts. No raw file.
    transport=json.loads(public('AUDIT-TRANSPORT.json',True));pieces=[];compressed=hashlib.sha256();base_parts=[]
    for part in transport['parts']:
        body=public(part['path'],True)
        require(len(body)==part['bytes'] and digest(body)==part['sha256'],'1568 transport part identity')
        compressed.update(body);pieces.append(body);base_parts.append(part)
    require(len(pieces)==8 and compressed.hexdigest()==transport['gzip_sha256']=='ce96f4d2380cfeac0fe2c2becc30e18c6ac25b561708ad9478d125ebefac0f55','1568 complete ordered gzip identity')
    base_gz=b''.join(pieces);pieces.clear()
    base_raw=HashedRaw(gzip.GzipFile(fileobj=io.BytesIO(base_gz),mode='rb'));base_audit=AuditInput(base_raw,'verified1568')
    base_seen=set();base_kinds=collections.Counter();shared=set();changed=[];module_only=[];identical=[]
    for old in parser(base_audit):
        name=old['name'];require(name not in base_seen,'Duplicate prior declaration');base_seen.add(name);base_kinds[old['kind']]+=1
        require(set(old['axioms']).issubset(STANDARD_AXIOMS) and old['kind']!='axiom','Prior axiom scope')
        if name not in records:continue
        new=records[name];shared.add(name)
        require(no_module(old)==no_module(new),'Shared non-module fields differ '+name)
        if old['module']!=new['module']:
            module_only.append({'name':name,'old_module':old['module'],'new_module':new['module'],'nonmodule_record_sha256':record_hash(no_module(old)).hex(),'all_nonmodule_fields_identical':True})
        else:identical.append(name)
    require(base_raw.sha.hexdigest()==transport['raw_sha256']=='ee29bc1196c22fb27dd024e8593b0208aba5f4195edbf4895871235ee6e42e53','1568 full raw identity')
    require(len(base_seen)==101705 and base_kinds['theorem']==92153,'1568 actual count')
    validate_metadata(base_audit.metadata,base_modules,101705,92153)
    require(len(shared)==4337 and len(identical)==4333 and len(module_only)==4,'Shared/full/attribution count')
    expected_delta=json.loads(capture['reviews/FULL-CONTEXT-MODULE-ATTRIBUTION-DELTA.json.projected'])
    delta_sort=lambda a:sorted(a,key=lambda x:x['name'])
    simplified=[{k:x[k] for k in ('name','old_module','new_module','all_nonmodule_fields_identical')}for x in module_only]
    require(delta_sort(simplified)==delta_sort(expected_delta),'Published full module-only delta')
    new_names=sorted(set(records)-base_seen);new_kinds=collections.Counter(records[x]['kind'] for x in new_names)
    require(len(new_names)==44 and new_kinds['theorem']==29 and all(records[x]['module'] in NEW_MODULES for x in new_names),'Genuinely new declaration count/owner')
    acceptance=json.loads(capture['ACCEPTANCE.json']);final=json.loads(capture['evidence/FINAL-RECEIPT.projected.json']);qualified=json.loads(gzip.decompress(capture['evidence/RESULT.projected.json.gz']))
    independent=json.loads(capture['reviews/FINAL-G4-219-REVIEW.json.projected']);terminal=json.loads(capture['evidence/LAKE-ATTEMPT4-TERMINAL.json.projected'])
    require(acceptance['status']=='ACCEPTED_SEPARATE_219_PROFILE_AFTER_INDEPENDENT_AGENT_REVIEW' and acceptance['modules']==219 and acceptance['coherent1570_acceptance'] is False and acceptance['master_closure'] is False,'Acceptance scope')
    require(final['status']=='PASS_ALL_REQUESTED_TARGETS' and final['counts']=={'cache_reuse':218,'fresh_components':1} and final['targets_passed']==['candidate/g4-actual-span'],'Projected terminal/freshness')
    require(qualified['status']=='PASS' and qualified['closure_modules']==219 and qualified['declarations']==4381 and qualified['theorems']==2878,'Projected result counts')
    require(independent['status']=='PASS_INDEPENDENT_SEPARATE_G4_219_CONTEXT' and independent['audit_sha256']==raw.sha.hexdigest(),'Independent public review status/audit')
    require(acceptance['review_raw_sha256']=='2f71b471407fbf5e1cf8f83ddc74604301c9964d8c9319cb562342008ab84751','Independent raw review binding')
    require(any(x['path']=='reviews/INDEPENDENT-FINAL-G4-219-REVIEW.md.projected' and x['exact_raw_public'] and x['raw_sha256']==acceptance['review_raw_sha256'] for x in projection_verified),'Independent raw review public bytes not exact')
    trace=json.loads(capture['evidence/LOCAL-ONLY-TRACE-INDEX.json'])
    require(not any('trace-transport/' in row['path'] or 'NATIVE-LOADER.' in row['path'] for row in verified),'Compiled/private trace payload unexpectedly public')
    require(file_pin(OLD_REVIEW)['sha256']=='dc9392e2b23e02b2cc5f8a6d9c2fedcec92f95a91fa9a5757020ccdf7a90a40b','Prior acceptance input drift')
    return {
      'schema':'public_g4_219_fixed_commit_independent_saved_byte_review_v1','reviewer':'Codex Rust implementation role',
      'status':'PASS_EXACT_PUBLIC_BLOBS_SOURCES_COMPLETE_AUDIT_SHARED_NONMODULE_RECORDS',
      'started_utc':started,'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'source':file_pin(__file__),'source_helper_origin':file_pin(OLD_READER),'bounded_record_parser':file_pin(PARSER),'prior_public_review':file_pin(OLD_REVIEW),
      'fixed_new_commit':COMMIT,'fixed_verified_base_commit':BASE_COMMIT,'public_packet':PACKET,
      'git_read_commands':['cat-file -t','show fixed-commit:path','ls-tree fixed-commit','cat-file --batch'],
      'git_read_env':{k:ENV[k] for k in ['GIT_OPTIONAL_LOCKS','GIT_OBJECT_DIRECTORY','GIT_ALTERNATE_OBJECT_DIRECTORIES']},
      'manifest':manifest_pin,'authenticated_manifest_files':verified,'manifest_payload_bytes':sum(x['bytes']for x in verified),
      'source_modules_verified':len(source_verified),'unchanged1568_prerequisite_modules':217,
      'module_source_identities':[[name,modules[name]['sha256']]for name in profile['order']],
      'literal_imports_match_graph':True,'selected_profile_order_topological':True,'owned_mathlib_modules':0,
      'g4_graph_sha256':digest(graph_raw),'base1568_graph_sha256':digest(base_graph_raw),'new_source_pins':NEW_MODULES,
      'public_projections':projection_verified,'projection_count':len(projection_verified),'exact_raw_projection_count':sum(x['exact_raw_public']for x in projection_verified),
      'complete219_audit':{'compressed_bytes':len(gz),'compressed_sha256':digest(gz),'decompressed_bytes':raw.size,'decompressed_sha256':raw.sha.hexdigest(),'declarations':len(records),'theorems':kinds['theorem'],'kinds':dict(kinds),'duplicate_names':0,'owned_axioms':0,'nonstandard_axiom_rows':0,'missing_modules':[]},
      'verified1568_stream':{'gzip_bytes':len(base_gz),'gzip_sha256':compressed.hexdigest(),'raw_bytes':base_raw.size,'raw_sha256':base_raw.sha.hexdigest(),'declarations':len(base_seen),'theorems':base_kinds['theorem'],'parts':base_parts},
      'shared_records':{'names':len(shared),'identical_full_fields':len(identical),'identical_nonmodule_fields':len(shared),'module_attribution_only':module_only},
      'new_module_attributed':{'records':sum(attributed.values()),'theorems':attributed['theorem']},
      'globally_new_records':[{'name':name,'module':records[name]['module'],'kind':records[name]['kind'],'full_parsed_record_sha256':record_hash(records[name]).hex()}for name in new_names],
      'globally_new_counts':{'names':len(new_names),'theorems':new_kinds['theorem'],'kinds':dict(new_kinds)},
      'public_operational_result':{'terminal':terminal,'final_receipt_sha256':digest(capture['evidence/FINAL-RECEIPT.projected.json']),'projected_result_sha256':digest(gzip.decompress(capture['evidence/RESULT.projected.json.gz'])),'actual_fresh_components':1,'authenticated_reused_components':218,'independently_replayed':False},
      'local_only_trace_index':{'sha256':digest(capture['evidence/LOCAL-ONLY-TRACE-INDEX.json']),'entries':len(trace['entries']),'raw_bytes_reported':sum(x['raw_bytes']for x in trace['entries']),'private_payload_authentication_performed':False},
      'source_scope':['Supplied endpoint-typed OriginalSpan on one original graph/calendar/rate/mode bank','Conditional scalar no-loss product preserves actual entering register and co-location premises','Arbitrary entrance PMF weights retained; natural averaging uses a separately constructed once-drawn natural entrance','Equal actual COMMON arm survivals imply register independence only for this scalar marginal','Complete unnormalized root-forest law has this count marginal; not a full forest law from scalar equality'],
      'not_claimed':['Coherent1570 or1575 accepted union','General G4 finite stopping or master closure','Rival-prefix/chronology reconstruction or legal observation admission','Generic native/Rust refinement or controlled/timed policy implementation','Personal authentication of unavailable private loader/compiler/cache payloads'],
      'no_compiler_cache_context_native_reference_or_git_index_mutation':True,'raw_audit_artifact_materialized':False,
      'reader_address_space_limit_bytes':256*2**20,'reader_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }

if __name__=='__main__':
    path=OUT/'PUBLIC-G4-219-READONLY-REVIEW-ATTEMPT1.json'
    try:
        result=review()
        encoded=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
        require(sum(p.stat().st_size for p in OUT.iterdir() if p.is_file())+len(encoded)<OUTPUT_LIMIT-16*2**10,'Support artifact budget reserve')
        with path.open('xb')as f:f.write(encoded)
        print(json.dumps({'status':result['status'],'review':file_pin(path),'manifest_files':len(result['authenticated_manifest_files']),'audit':result['complete219_audit'],'shared':{'nonmodule':result['shared_records']['identical_nonmodule_fields'],'full':result['shared_records']['identical_full_fields'],'module_only':len(result['shared_records']['module_attribution_only'])},'globally_new':result['globally_new_counts'],'maxrss_kib':result['reader_maxrss_kib']},sort_keys=True))
    except BaseException as exc:
        failure={'schema':'public_g4_219_reader_failure_v1','status':'FAILED_PRESERVED_NO_PRODUCER','source':file_pin(__file__),'exception':repr(exc),'traceback':traceback.format_exc(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiler_or_native_called':False}
        with path.open('xb')as f:f.write((json.dumps(failure,indent=2,sort_keys=True)+'\n').encode())
        raise
