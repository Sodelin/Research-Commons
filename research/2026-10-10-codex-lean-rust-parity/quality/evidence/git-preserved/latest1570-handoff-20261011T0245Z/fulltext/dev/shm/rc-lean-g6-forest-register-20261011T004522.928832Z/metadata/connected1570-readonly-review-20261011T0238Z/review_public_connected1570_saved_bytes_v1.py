"""Fixed-commit connected1570 public byte/record audit. No Lean/native/target calls."""
from pathlib import Path
import ast,collections,datetime,gzip,hashlib,io,json,os,re,resource,subprocess,traceback
resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
ROOT=Path('/workspace/Research-Commons')
OUT=Path(__file__).parent
COMMIT='62020166e3e7ef690838f50b13caa149ede419ec'
BASE_COMMIT='3972858d5c896171f80d7bc5a32f3ed1e95a6583'
PACKET='research/2026-10-11-dot-accepted-connected-union1570-g4span-0225z'
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

G4_COMMIT='de4d8fa1b3c56997df1b2a2e07b4ebc6e237ef6d'
G4_PACKET='research/2026-10-11-dot-g4-compiled-actual-span-0205z'
G4_READER=OUT.parent/'g4-public219-readonly-review-20261011T0232Z/review_public_g4_219_saved_bytes_v1.py'
G4_REVIEW=G4_READER.parent/'PUBLIC-G4-219-READONLY-REVIEW-ATTEMPT1.json'
DELTA=Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z/metadata/integration-source-identity-delta-1509-20261011T015156.237141Z/INTEGRATION-SOURCE-IDENTITY-DELTA.json')


def g4public(path):
    return git('show',G4_COMMIT+':'+G4_PACKET+'/'+path)


def compressed_stream(transport,fetch,known_gzip,known_raw):
    pieces=[];sha=hashlib.sha256();pins=[]
    require(len(transport['parts'])==8,'Eight compressed audit parts required')
    for item in transport['parts']:
        body=fetch(item['path'])
        require(len(body)==item['bytes'] and digest(body)==item['sha256'],'Compressed audit part identity '+item['path'])
        sha.update(body);pieces.append(body);pins.append(item)
    require(sha.hexdigest()==transport['gzip_sha256']==known_gzip,'Concatenated compressed identity')
    require(transport['raw_sha256']==known_raw,'Transport expected raw identity')
    gz=b''.join(pieces);pieces.clear()
    raw=HashedRaw(gzip.GzipFile(fileobj=io.BytesIO(gz),mode='rb'))
    return raw,AuditInput(raw,known_raw),{'gzip_bytes':len(gz),'gzip_sha256':sha.hexdigest(),'raw_sha256':known_raw,'parts':pins}


def match_projection(path,body,item):
    decoded=gzip.decompress(body) if path.endswith('.gz') else body
    sha=item.get('projected_uncompressed_sha256',item.get('projected_sha256'))
    require(sha is not None and digest(decoded)==sha,'Public projection decoded identity '+path)
    if 'projected_bytes'in item:require(len(decoded)==item['projected_bytes'],'Public projection decoded length '+path)
    if item['exact_raw_public']:
        require(digest(decoded)==item['raw_sha256'],'Exact public raw identity '+path)
        if 'raw_bytes'in item:require(len(decoded)==item['raw_bytes'],'Exact public raw length '+path)
    return dict(item,decoded_bytes=len(decoded))


def review():
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    require(file_pin(OLD_READER)['sha256']=='1e44d1acec98e30bfe2f6331f97415d11f9c8ba74918f202ed21c2a88db9f930','1568 reader source pin')
    require(file_pin(OLD_REVIEW)['sha256']=='dc9392e2b23e02b2cc5f8a6d9c2fedcec92f95a91fa9a5757020ccdf7a90a40b','Accepted public1568 review pin')
    require(file_pin(G4_READER)['sha256']=='937cfb67172ac5175f2de43751e7a59ac0e82e36e36dd71a3878bd0170295a55','G4 reader source pin')
    require(file_pin(G4_REVIEW)['sha256']=='88c72abf675f477538a1885175168806c5a4428fdeb1547c0c2fef6791dcd118','Accepted public219 review pin')
    require(file_pin(DELTA)['sha256']=='242535f8d6748df81b5c376d5c3aa1ebe44e2cd4594f8099e240e2f4505a5e6d','Five outside consumers input pin')
    require(all(git('cat-file','-t',c)==b'commit\n'for c in [COMMIT,BASE_COMMIT,G4_COMMIT]),'Fixed commit object type')
    manifest_raw=public('MANIFEST.json');manifest=json.loads(manifest_raw)
    require(digest(manifest_raw)=='ddeb64940618cf3253971c47380c807145fdc2e9b2516e06d5bd3942a3f41587','Known new manifest SHA')
    rows=manifest['files'];expected={x['path']:x for x in rows}
    require(len(rows)==len(expected)==1639,'Exact manifest count/no duplicates')
    tree={}
    for item in git('ls-tree','-r','-z',COMMIT,'--',PACKET).split(b'\0'):
        if not item:continue
        head,path=item.split(b'\t',1);mode,kind,oid=head.split()
        require(mode==b'100644' and kind==b'blob','Nonregular public artifact')
        rel=path.decode()[len(PACKET)+1:];require(rel not in tree,'Tree duplicate');tree[rel]=oid.decode()
    require(set(tree)==set(expected)|{'MANIFEST.json'},'Complete manifest/tree equality')
    manifest_pin=pin_blob('MANIFEST.json',manifest_raw,tree['MANIFEST.json'])
    require(all(row['git_blob']==tree[path]for path,row in expected.items()),'Every manifest tree Git OID')
    graph_raw=public('DEPENDENCY-GRAPH.json');graph=json.loads(graph_raw)
    require(digest(graph_raw)=='ba9148757fda063c86b40db0d453a3eccd85c224800a8b98ebd12f6ffe31f367','Connected1570 graph identity')
    profile=graph['targets']['current/connected'];modules=profile['modules']
    base_graph_raw=public('DEPENDENCY-GRAPH.json',True)
    require(digest(base_graph_raw)=='1a82a47a20257e9fa83bc88c786a55ca82d4dd245952cf4779a646f84a83d825','1568 graph identity')
    base_modules=json.loads(base_graph_raw)['targets']['current/connected']['modules']
    require(len(modules)==1570 and len(base_modules)==1568,'Exact source module counts')
    require(set(modules)-set(base_modules)==set(NEW_MODULES),'Exactly two G4 source additions')
    require(all(modules.get(name)==row for name,row in base_modules.items()),'Inherited whole module/source/import record changed')
    require(all(modules[name]['sha256']==sha for name,sha in NEW_MODULES.items()),'New consumers equal verified219 source bytes')
    seen=set()
    for name in profile['order']:
        require(name in modules and name not in seen,'Graph order name/duplicate')
        require(all(parent not in modules or parent in seen for parent in modules[name]['imports']),'Source import order not topological')
        seen.add(name)
    require(seen==set(modules),'Source order incomplete')
    owned_mathlib=sorted(x for x in modules if x.startswith('Mathlib.'))
    require(len(owned_mathlib)==4 and owned_mathlib==sorted(x for x in base_modules if x.startswith('Mathlib.')),'Unchanged accepted four-owned-Mathlib namespace wrappers')
    projections=json.loads(public('PUBLIC-PROJECTIONS.json'))
    projected={x.get('path',x.get('public_path')):x for x in projections}
    require(len(projections)==len(projected)==39 and set(projected)<=set(expected),'Projection complete selection')
    capture_names={'ACCEPTANCE.json','AUDIT-TRANSPORT.json','evidence/FINAL-RECEIPT.json.projected','evidence/LAKE-ATTEMPT2-TERMINAL.json.projected','evidence/LOCAL-ONLY-TRACE-INDEX.json','reviews/FINAL-UNION-REVIEW.json.projected.gz','reviews/EXACT-NEW-DECLARATION-RECORDS.json.projected.gz','reviews/FINAL-MODULE-ATTRIBUTION-DELTA.json.projected.gz','evidence/AUTHOR-INHERITED-RECORD-CHECK.json'}
    bysha={}
    for name,row in modules.items():bysha.setdefault(row['sha256'],[]).append(name)
    source_verified=set();projection_verified=[];capture={};part_bytes={};payload_bytes=0;inventory_sha=hashlib.sha256()
    batch=subprocess.Popen(GIT+['cat-file','--batch'],env=ENV,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    try:
        for path,row in expected.items():
            batch.stdin.write((row['git_blob']+'\n').encode());batch.stdin.flush()
            header=batch.stdout.readline().decode().strip().split()
            require(len(header)==3 and header[:2]==[row['git_blob'],'blob'],'Batch blob header '+path)
            size=int(header[2]);require(size==row['bytes'] and size<=8*2**20,'Blob size/bound '+path)
            body=batch.stdout.read(size);require(len(body)==size and batch.stdout.read(1)==b'\n','Truncated blob '+path)
            require(digest(body)==row['sha256'],'Manifest byte SHA '+path)
            pin_blob(path,body,row['git_blob'])
            inventory_sha.update((json.dumps([path,size,row['sha256'],row['git_blob']],separators=(',',':'))+'\n').encode())
            payload_bytes+=size
            if path in projected:projection_verified.append(match_projection(path,body,projected[path]))
            if path.startswith('source-store/') and path.endswith('.lean'):
                sha=path.rsplit('/',1)[1][:-5];require(digest(body)==sha and sha in bysha,'Source-store filename identity')
                imports=literal_imports(body.decode())
                for module in bysha[sha]:
                    require(imports==modules[module]['imports'],'Literal imports do not match '+module);source_verified.add(module)
            elif path.startswith('evidence/audit-parts/'):part_bytes[path]=body
            elif path in capture_names:capture[path]=body
        batch.stdin.close();err=batch.stderr.read()
        require(batch.wait()==0 and not err,'Read-only Git batch error')
    finally:
        if batch.poll() is None:batch.kill();batch.wait()
        batch.stdout.close();batch.stderr.close()
    require(source_verified==set(modules) and len(projection_verified)==39,'Complete source/projection verification')
    require(set(capture)==capture_names,'Operational capture completeness')
    parser=get_record_parser()
    g4_review=json.loads(G4_REVIEW.read_bytes())
    g4_gzip=g4public('evidence/AUDIT-RESULT.json.gz')
    require(digest(g4_gzip)=='f7325fdbecfc7e252a695decec1e247b3e4f7f90459a5e51073be12acd74e605','Prior219 compressed identity')
    g4_raw=HashedRaw(gzip.GzipFile(fileobj=io.BytesIO(g4_gzip),mode='rb'));g4_input=AuditInput(g4_raw,'accepted219')
    g4_expected={};g4_kinds=collections.Counter()
    for row in parser(g4_input):
        require(row['name']not in g4_expected,'219 duplicate declaration')
        require(row['kind']!='axiom'and set(row['axioms'])<=STANDARD_AXIOMS,'219 axiom scope')
        g4_expected[row['name']]=record_hash(no_module(row));g4_kinds[row['kind']]+=1
    require(g4_raw.sha.hexdigest()=='964136ed38c4dbd2dc5f11b9c6fd9fd48ca0cd31627baa63db56002520c0e807'and len(g4_expected)==4381 and g4_kinds['theorem']==2878,'219 complete audit identity/counts')
    expected_new={x['name']:x for x in g4_review['globally_new_records']}
    require(len(expected_new)==44,'Prior globally new inventory')
    base_transport=json.loads(public('AUDIT-TRANSPORT.json',True))
    base_raw,base_input,base_transport_result=compressed_stream(base_transport,lambda p:public(p,True),'ce96f4d2380cfeac0fe2c2becc30e18c6ac25b561708ad9478d125ebefac0f55','ee29bc1196c22fb27dd024e8593b0208aba5f4195edbf4895871235ee6e42e53')
    inherited={};base_kinds=collections.Counter()
    for row in parser(base_input):
        require(row['name']not in inherited,'1568 duplicate declaration')
        require(row['module']in base_modules and row['kind']!='axiom'and set(row['axioms'])<=STANDARD_AXIOMS,'1568 owner/axiom scope')
        inherited[row['name']]=record_hash(row);base_kinds[row['kind']]+=1
    require(base_raw.sha.hexdigest()==base_transport['raw_sha256'] and base_raw.size==115073144 and len(inherited)==101705 and base_kinds['theorem']==92153,'1568 full audit/count equality')
    validate_metadata(base_input.metadata,base_modules,101705,92153)
    transport=json.loads(capture['AUDIT-TRANSPORT.json'])
    raw,audit,transport_result=compressed_stream(transport,lambda p:part_bytes.pop(p),'b2c5714a8c57bc9ec04b253217d091e00f9796e8e260c1844f5e51829ec30933','026783d9a4476842d9403b041b112fa08373b250885672163e3a47bcf17686ab')
    require(not part_bytes,'No leftover public compressed parts')
    names=set();kinds=collections.Counter();new_kinds=collections.Counter();matched=0;g4matched=set();new_rows=[]
    for row in parser(audit):
        name=row['name'];require(name not in names,'1570 duplicate declaration');names.add(name);kinds[row['kind']]+=1
        require(row['module']in modules and row['kind']!='axiom'and set(row['axioms'])<=STANDARD_AXIOMS,'1570 owner/axiom scope')
        full_sha=record_hash(row)
        if name in inherited:
            require(full_sha==inherited.pop(name),'Inherited full parsed record changed '+name);matched+=1
        else:
            require(name in expected_new and row['module']in NEW_MODULES,'Unexpected globally new name/owner '+name)
            expected_row=expected_new[name]
            require(row['module']==expected_row['module'] and row['kind']==expected_row['kind'] and full_sha.hex()==expected_row['full_parsed_record_sha256'],'New declaration full fields differ from219 '+name)
            new_rows.append({'name':name,'module':row['module'],'kind':row['kind'],'full_parsed_record_sha256':full_sha.hex()});new_kinds[row['kind']]+=1
        if name in g4_expected:
            require(record_hash(no_module(row))==g4_expected[name],'219 shared nonmodule record changed '+name);g4matched.add(name)
    require(raw.sha.hexdigest()==transport['raw_sha256'],'Connected1570 exact entire decompressed audit SHA')
    require(len(names)==101749 and kinds['theorem']==92182,'Actual connected1570 declaration/theorem count')
    validate_metadata(audit.metadata,modules,101749,92182)
    require(not inherited and matched==101705 and len(new_rows)==44 and new_kinds['theorem']==29 and g4matched==set(g4_expected),'Whole prior inventory/G4 comparison coverage')
    published_new=json.loads(gzip.decompress(capture['reviews/EXACT-NEW-DECLARATION-RECORDS.json.projected.gz']))
    require(len(published_new)==44 and len({x['name']for x in published_new})==44,'Published exact new records duplicate/count')
    require({x['name']:record_hash(x).hex()for x in published_new}=={x['name']:x['full_parsed_record_sha256']for x in new_rows},'Published new record bodies differ')
    attribution=json.loads(gzip.decompress(capture['reviews/FINAL-MODULE-ATTRIBUTION-DELTA.json.projected.gz']))
    require(attribution==[],'Full union attribution delta is not empty')
    acceptance=json.loads(capture['ACCEPTANCE.json']);final=json.loads(capture['evidence/FINAL-RECEIPT.json.projected'])
    independent=json.loads(gzip.decompress(capture['reviews/FINAL-UNION-REVIEW.json.projected.gz']))
    terminal=json.loads(capture['evidence/LAKE-ATTEMPT2-TERMINAL.json.projected']);trace=json.loads(capture['evidence/LOCAL-ONLY-TRACE-INDEX.json'])
    author=json.loads(capture['evidence/AUTHOR-INHERITED-RECORD-CHECK.json'])
    require(acceptance['status']=='ACCEPTED_EXACT_CONNECTED_1570_AFTER_INDEPENDENT_AGENT_REVIEW'and acceptance['modules']==1570 and acceptance['owned_declarations']==101749 and acceptance['theorem_rows']==92182,'Acceptance explicit connected1570 scope')
    require(acceptance['graph_sha256']==digest(graph_raw)and acceptance['audit_sha256']==raw.sha.hexdigest()and acceptance['all_101705_prior_records_exactly_preserved']is True and acceptance['module_attribution_changes']==[],'Acceptance graph/audit/prior-record bindings')
    require(acceptance['general_master_closure']is False and acceptance['local_loader_payloads_public']is False,'No master/private payload claim')
    require(final['status']=='PASS_ALL_REQUESTED_TARGETS'and final['counts']=={'cache_reuse':1570}and final['targets_passed']==['current/connected']and terminal['exit_code']==0,'Projected final terminal/freshness')
    require(independent['status']=='PASS_INDEPENDENT_EXACT_1570_CONTEXT_REVIEW'and independent['audit_sha256']==raw.sha.hexdigest()and independent['fresh_components']==0 and independent['authenticated_component_reuse']==1570 and independent['fresh_aggregate']is True and independent['fresh_complete_audit']is True,'Published independent exact context review')
    require(acceptance['independent_raw_review_sha256']=='0c0477e30a10dcffa95eb87dee10200d5c51f35f1a5cec03fa5f128b299cf31e','Known independent review raw identity')
    require(any(x['path']=='reviews/INDEPENDENT-FINAL-UNION-REVIEW.md.projected'and x['exact_raw_public']and x['raw_sha256']==acceptance['independent_raw_review_sha256']for x in projection_verified),'Independent raw review actual public bytes')
    require(author['old_record_count']==matched and author['new_record_count']==44 and author['all_old_fields_identical']is True and author['module_attribution_changes']==[],'Author comparison report actual corroboration')
    require(len(trace['entries'])==2 and not any('trace-transport/'in p or 'NATIVE-LOADER.'in p for p in expected),'Local-only loader index separated from public payload')
    delta=json.loads(DELTA.read_bytes());five=delta['genuinely_new_modules']
    require(len(five)==5 and all(x['module']not in modules for x in five),'Five later native-source consumers remain outside1570')
    combined=dict(modules)
    for item in five:
        require(file_pin(item['path'])['sha256']==item['sha256'] and Path(item['path']).stat().st_size==item['bytes'],'Outside consumer source changed')
        require(literal_imports(Path(item['path']).read_text())==item['imports'],'Outside consumer imports changed')
        combined[item['module']]={k:item[k]for k in ['module','sha256','imports']}
    combined_seen=set()
    for name in list(profile['order'])+delta['safe_new_only_topological_order']:
        require(name not in combined_seen and name in combined and all(x not in combined or x in combined_seen for x in combined[name]['imports']),'Prospective1575 static topological order')
        combined_seen.add(name)
    require(len(combined_seen)==len(combined)==1575,'Prospective1575 exact static identity count')
    return {
      'schema':'research_commons_public_connected1570_readonly_saved_review_v1','reviewer':'Codex Rust implementation role',
      'status':'PASS_EXACT_PUBLIC_GRAPH_SOURCES_IMPORTS_FULL_AUDIT_AND_ALL_1568_RECORDS',
      'started_utc':started,'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'source':file_pin(__file__),'records_parser_origin':file_pin(PARSER),'prior1568_source':file_pin(OLD_READER),'prior1568_review':file_pin(OLD_REVIEW),'prior219_source':file_pin(G4_READER),'prior219_review':file_pin(G4_REVIEW),
      'fixed_current_commit':COMMIT,'fixed1568_commit':BASE_COMMIT,'fixed219_commit':G4_COMMIT,'public_packet':PACKET,
      'Git_read_commands':['cat-file -t','show fixed-commit:path','ls-tree fixed-commit','cat-file --batch'],
      'Git_read_environment':{k:ENV[k]for k in ['GIT_OPTIONAL_LOCKS','GIT_OBJECT_DIRECTORY','GIT_ALTERNATE_OBJECT_DIRECTORIES']},
      'manifest':manifest_pin,'manifest_files_verified':len(expected),'manifest_payload_bytes_verified':payload_bytes,
      'every_literal_sha_length_and_recomputed_git_blob_sha1_matches_manifest':True,
      'verified_inventory_sha256':inventory_sha.hexdigest(),'verified_inventory_encoding':'Manifest-order ASCII compact JSON array [relative path, bytes, SHA256, Git blob SHA1], LF per item; immutable manifest pins every underlying row without duplicate bulky inventory here.',
      'source_graph':{'bytes':len(graph_raw),'sha256':digest(graph_raw),'target':'current/connected','modules':len(modules),'literal_source_imports_verified':len(source_verified),'all1568_module_sha_import_records_exact':True,'source_order_topological':True,'owned_mathlib_wrappers':owned_mathlib,'new_module_sha256':NEW_MODULES},
      'prior1568_graph_sha256':digest(base_graph_raw),
      'complete1570_audit':dict(transport_result,raw_bytes=raw.size,declarations=len(names),theorems=kinds['theorem'],kinds=dict(kinds),owned_axioms=0,nonstandard_axiom_rows=0,missing_modules=[],duplicate_names=0),
      'complete1568_audit_restreamed':dict(base_transport_result,raw_bytes=base_raw.size,declarations=101705,theorems=base_kinds['theorem']),
      'whole_inherited_record_equality':{'matched_names':matched,'all_parsed_fields_including_module_identical':True,'unmatched_prior_names':0,'module_attribution_changes':0,'method':'Canonical ASCII compact sorted-key JSON SHA256 for every parsed declaration field, including kind/module/ordered axiom/reference lists; exact prior name coverage once.'},
      'separate219_comparison':{'raw_bytes':g4_raw.size,'raw_sha256':g4_raw.sha.hexdigest(),'all4381_nonmodule_records_identical':True,'all44_globally_new_full_records_identical':True,'four_prior_attribution_differences_resolved_to1568':g4_review['shared_records']['module_attribution_only']},
      'globally_new_counts':{'records':len(new_rows),'theorems':new_kinds['theorem'],'kinds':dict(new_kinds)},'globally_new_records':sorted(new_rows,key=lambda x:x['name']),
      'public_projection_count':len(projection_verified),'public_exact_raw_projection_count':sum(x['exact_raw_public']for x in projection_verified),'public_projections':projection_verified,
      'public_operational_acceptance':{'acceptance':acceptance,'final_projected_sha256':digest(capture['evidence/FINAL-RECEIPT.json.projected']),'terminal':terminal,'fresh_components_reported':0,'authenticated_exact_context_component_reuse_reported':1570,'fresh_aggregate_and_complete_audit_reported':True,'independent_raw_review_sha256':acceptance['independent_raw_review_sha256'],'private_import_compiler_cache_trace_authentication_personally_performed':False},
      'local_only_loader_index':{'sha256':digest(capture['evidence/LOCAL-ONLY-TRACE-INDEX.json']),'entries':len(trace['entries']),'raw_bytes_reported':sum(x['raw_bytes']for x in trace['entries']),'payloads_public_or_personally_authenticated':False},
      'later_five_consumers':{'static_input':file_pin(DELTA),'sources':[{k:x[k]for k in ['module','path','bytes','sha256','imports']}for x in five],'compatible_identity_count':1575,'no_combined1575_graph_context_kernel_or_audit_constructed':True},
      'scientific_boundaries':['Accepted public connected1570 source/audit record evidence; no personal compiler replay','The actual supplied OriginalSpan scalar no-loss and fresh natural-register entrance averages retain their typed support and physical premises','Equal COMMON arm survival scalar equality does not imply a full forest/Old-history law','No passive topology decoder, general finite forcing, master closure, generic Rust/source refinement or timed policy promotion'],
      'raw_audit_copy_created':False,'compiler_cache_context_native_reference_or_Git_mutation':False,'all_output_inside_existing_counted_WF_metadata':True,
      'reader_AS_limit_bytes':256*2**20,'observed_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }


if __name__=='__main__':
    path=OUT/'PUBLIC-CONNECTED1570-READONLY-REVIEW-ATTEMPT1.json'
    try:
        result=review();encoded=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
        require(sum(p.stat().st_size for p in OUT.iterdir()if p.is_file())+len(encoded)<OUTPUT_LIMIT-16*2**10,'Support artifact 256KiB cap/reserve')
        with path.open('xb')as f:f.write(encoded)
        print(json.dumps({'status':result['status'],'receipt':file_pin(path),'manifest_files':result['manifest_files_verified'],'payload_bytes':result['manifest_payload_bytes_verified'],'audit':{k:result['complete1570_audit'][k]for k in ['raw_bytes','raw_sha256','declarations','theorems','owned_axioms','nonstandard_axiom_rows','duplicate_names']},'inherited_exact':result['whole_inherited_record_equality']['matched_names'],'new':result['globally_new_counts'],'maxrss_kib':result['observed_maxrss_kib']},sort_keys=True))
    except BaseException as exc:
        failure={'schema':'public_connected1570_reader_failure_v1','status':'FAILED_PRESERVED_NO_PRODUCER','source':file_pin(__file__),'exception':repr(exc),'traceback':traceback.format_exc(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiler_or_native_called':False}
        with path.open('xb')as f:f.write((json.dumps(failure,indent=2,sort_keys=True)+'\n').encode())
        raise
