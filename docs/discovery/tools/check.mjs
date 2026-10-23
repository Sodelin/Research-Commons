// Explicit suite paths prevent an unrelated cwd/glob from reporting zero tests.
import {readdir} from 'node:fs/promises';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
const root=fileURLToPath(new URL('../',import.meta.url));
const testDir=new URL('../test/',import.meta.url);
const files=(await readdir(testDir)).filter(name=>name.endsWith('.test.mjs')).sort();
if(!files.length)throw Error('No reader suites found: verification refused.');
console.log(`Reader verification scope: ${files.length} explicit test modules.`);
const result=spawnSync(process.execPath,['--test',...files.map(name=>fileURLToPath(new URL(name,testDir)))],{cwd:root,stdio:'inherit',timeout:45000});
if(result.error)throw result.error;
if(result.signal)throw Error(`Reader verification interrupted: ${result.signal}`);
process.exitCode=result.status??1;
