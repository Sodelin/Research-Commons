#!/usr/bin/env node
// Bounded adapter around the EXISTING Rust -> Lean checker; no theorem engine.
import {spawn,spawnSync} from 'node:child_process';
import {readFile,open} from 'node:fs/promises';
import {loadPackage,solverBinding} from './solver-bindings.mjs';
import {classifyCheck} from './check-result.mjs';
const args=process.argv.slice(2);let directory,claim,output,execute=false;
for(let i=0;i<args.length;i++){
 const key=args[i];if(key==='--execute'){execute=true;continue;}
 if(!['--package-root','--claim','--receipt'].includes(key)||!args[i+1])throw Error('Usage: check-claim.mjs --package-root PATH --claim ID [--execute] [--receipt NEW_FILE]');
 const value=args[++i];if(key==='--package-root')directory=value;else if(key==='--claim')claim=value;else output=value;
}
if(!directory||!claim)throw Error('Exact package and claim required');
const pkg=await loadPackage(directory),card=pkg.cards.get(claim);if(!card)throw Error('Unknown canonical package claim');
const binding=solverBinding(card,pkg);
// Reserve before any execution: an existing result must refuse before a check
// can run, rather than discard a newly executed result at the final write.
const receiptFile=output?await open(output,'wx'):null;
const observation={schema:1,record_kind:'bounded_declaration_check_observation',claim_id:claim,observed_utc:new Date().toISOString(),
 package_source:pkg.identity,command:binding.check,outcome:'NOT_EXECUTED',executed:false,
 scope:'Named Lean declaration/type/owner and existing audited target context only; no new mathematical, native refinement, novelty, whole-package or master-question acceptance.'};
if(execute){
 const pinnedRust=String(await readFile(`${pkg.root}/rust-toolchain.toml`)).match(/channel\s*=\s*"([^"]+)"/)?.[1];
 const pinnedLean=String(await readFile(`${pkg.root}/lean/lean-toolchain`)).trim();
 const probeEnv={...process.env,RUSTUP_TOOLCHAIN:pinnedRust,ELAN_TOOLCHAIN:pinnedLean};
 // Official CI uses the verified Lean release archive directly, without elan.
 // Inspect actual compiler versions instead of requiring one installer manager.
 const rust=spawnSync('rustc',['--version'],{cwd:pkg.root,env:probeEnv,encoding:'utf8',timeout:5000});
 const lean=spawnSync('lean',['--version'],{cwd:pkg.root,env:probeEnv,encoding:'utf8',timeout:5000});
 observation.toolchain_preflight={expected_rust:pinnedRust,expected_lean:pinnedLean,rustc:rust.stdout?.trim()??'',lean:lean.stdout?.trim()??''};
 const missing=[];
 if(rust.status!==0||!rust.stdout.startsWith(`rustc ${pinnedRust} `))missing.push(`usable Rust ${pinnedRust}`);
 if(lean.status!==0||!lean.stdout.startsWith(`Lean (version ${pinnedLean.split(':v')[1]},`))missing.push(`usable Lean ${pinnedLean}`);
 if(!binding.check)missing.push('named Lean binding');
 if(missing.length){observation.outcome='UNKNOWN';observation.blockers=missing;}
 else{
  const result=await new Promise(resolve=>{
   const child=spawn(binding.check.program,binding.check.args,{cwd:pkg.root,stdio:['ignore','pipe','pipe'],detached:true,
    env:{...process.env,RUSTUP_TOOLCHAIN:pinnedRust,ELAN_TOOLCHAIN:pinnedLean,CARGO_NET_OFFLINE:'true'}});
   let stdout='',stderr='',failure=null,size=0;
   const kill=reason=>{failure=reason;try{process.kill(-child.pid,'SIGKILL');}catch{child.kill('SIGKILL');}};
   const timer=setTimeout(()=>kill('45 second execution bound reached'),45000);
   for(const [stream,key]of [[child.stdout,'stdout'],[child.stderr,'stderr']])stream.on('data',chunk=>{
    size+=chunk.length;if(size>4*1024*1024){kill('4 MiB output bound reached');return;}
    if(key==='stdout')stdout+=chunk;else stderr+=chunk;
   });
   child.on('error',e=>{failure=e.message;});
   child.on('close',(exit_code,signal)=>{clearTimeout(timer);resolve({stdout,stderr,exit_code,signal,failure});});
  });
  observation.executed=true;observation.process=result;
  Object.assign(observation,classifyCheck(result,binding,pkg));
 }
}
if(receiptFile){await receiptFile.writeFile(JSON.stringify(observation,null,2)+'\n');await receiptFile.close();}
console.log(JSON.stringify(observation,null,2));
if(execute&&observation.outcome!=='CHECKED_SCOPED_DECLARATIONS')process.exitCode=2;
