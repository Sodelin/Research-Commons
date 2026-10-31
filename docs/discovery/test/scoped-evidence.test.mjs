import test from 'node:test';import assert from 'node:assert/strict';
import {mkdtemp,writeFile,rm} from 'node:fs/promises';import {tmpdir} from 'node:os';import {join} from 'node:path';
import {spawnSync} from 'node:child_process';import {fileURLToPath} from 'node:url';
import {identity} from '../tools/source-cache.mjs';import {loadScopedEvidence,searchScopedEvidence} from '../tools/scoped-evidence.mjs';
async function fixture(t){
 const root=await mkdtemp(join(tmpdir(),'scoped-evidence-'));t.after(()=>rm(root,{recursive:true,force:true}));
 const source=Buffer.from('namespace Example\ntheorem sample : True := True.intro\nend Example\n');
 const log=Buffer.from("Example.sample : True\n'Example.sample' does not depend on any axioms\n");
 const audit={selected_modules:['Example'],declaration_count:1,theorem_declaration_count:1,owned_axioms:[],nonstandard_axiom_rows:[],missing_modules:[],declarations:[{name:'Example.sample',module:'Example',kind:'theorem',axioms:[]}]};
 const owned=Buffer.from(JSON.stringify(audit));await writeFile(join(root,'source.lean'),source);await writeFile(join(root,'named.log'),log);await writeFile(join(root,'owned.json'),owned);
 const m={schema:1,kind:'local_scoped_lean_audit',id:'ExampleEvidence',scope:'A single synthetic theorem.',limitations:['No claim acceptance.'],sources:[{module:'Example',path:'source.lean',sha256:identity(source).sha256}],named_declarations:[{module:'Example',name:'Example.sample'}],selected_module_count:1,named_audit:{path:'named.log',sha256:identity(log).sha256},owned_audit:{path:'owned.json',sha256:identity(owned).sha256}};
 const manifest=join(root,'evidence.json');await writeFile(manifest,JSON.stringify(m));return {root,manifest,m,audit};
}
test('explicit scoped receipt is searchable by source and declaration without claim promotion',async t=>{
 const {manifest}=await fixture(t);const records=await loadScopedEvidence([manifest]);const hits=searchScopedEvidence(records,'Example.sample');assert.equal(hits.length,1);assert.equal(hits[0].id,'ExampleEvidence');assert.equal(hits[0].named_declarations[0].module,'Example');assert.match(hits[0].trust,/not independently authenticated/);assert.equal(hits[0].claim_id,undefined);assert.equal(searchScopedEvidence(records,'namespace Example').length,1);
});
test('changed source, missing ownership, duplicate context and escaping paths are refused',async t=>{
 const {root,manifest,m,audit}=await fixture(t);await writeFile(join(root,'source.lean'),'tampered');await assert.rejects(loadScopedEvidence([manifest]),/hash mismatch/);
 const body=Buffer.from('namespace Example\ntheorem sample : True := True.intro\nend Example\n');await writeFile(join(root,'source.lean'),body);
 audit.declarations[0].module='Other';let b=Buffer.from(JSON.stringify(audit));await writeFile(join(root,'owned.json'),b);m.owned_audit.sha256=identity(b).sha256;await writeFile(manifest,JSON.stringify(m));await assert.rejects(loadScopedEvidence([manifest]),/Invalid owned|absent from owned/);
 audit.declarations[0].module='Example';audit.selected_modules=['Example','Example'];b=Buffer.from(JSON.stringify(audit));await writeFile(join(root,'owned.json'),b);m.owned_audit.sha256=identity(b).sha256;m.selected_module_count=2;await writeFile(manifest,JSON.stringify(m));await assert.rejects(loadScopedEvidence([manifest]),/incomplete/);
 m.sources[0].path='../outside';await writeFile(manifest,JSON.stringify(m));await assert.rejects(loadScopedEvidence([manifest]),/escapes/);
});

test('CLI returns the exact local evidence and refuses transferred claim facets',async t=>{
 const {manifest}=await fixture(t);const cli=fileURLToPath(new URL('../tools/query.mjs',import.meta.url));
 const run=spawnSync(process.execPath,[cli,'--scoped-evidence',manifest,'--query','Example.sample'],{encoding:'utf8'});assert.equal(run.status,0,run.stderr);const result=JSON.parse(run.stdout);assert.equal(result.view,'explicit_local_scoped_evidence_not_claim_acceptance');assert.equal(result.results[0].named_declarations[0].name,'Example.sample');
 const invalid=spawnSync(process.execPath,[cli,'--scoped-evidence',manifest,'--status','complete'],{encoding:'utf8'});assert.notEqual(invalid.status,0);assert.equal(invalid.stdout,'');
});
