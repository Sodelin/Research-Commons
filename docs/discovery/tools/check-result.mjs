// Pinned provider namespaces recognized by the existing Rust package assembler.
// A missing project row must never be silently reclassified as an external.
export function compilerSuppliedImport(name){
 return ['Mathlib','Std','Init','Lean'].some(root=>name===root||name.startsWith(root+'.'));
}
// Mirrors selected_modules' project-import traversal, with its assembler's
// explicit compiler/Mathlib provider boundary applied to absent import rows.
export function requiredContext(pkg,roots){
 const selected=new Set(),todo=[...roots];
 while(todo.length){const name=todo.pop();if(selected.has(name))continue;
  const source=pkg.modules.get(name);if(!source||!Array.isArray(source.imports))throw Error('Missing exact project import manifest');
  selected.add(name);for(const dep of source.imports){if(pkg.modules.has(dep))todo.push(dep);else if(!compilerSuppliedImport(dep))throw Error('Unknown missing project import');}
 }
 return selected;
}
export function classifyCheck(result,binding,pkg){
 const unknown=reason=>({outcome:'UNKNOWN',blockers:[reason]});
 if(result.exit_code!==0||result.signal||result.failure)return unknown(result.failure??`Checker exit ${result.exit_code}; signal ${result.signal??'none'}`);
 // Existing checker prints its complete JSON plan as the final line, after Lean.
 let receipt;try{receipt=JSON.parse(result.stdout.trim().split('\n').at(-1));}catch{return unknown('No complete actual checker receipt');}
 if(receipt.kernel_check_passed!==true||receipt.exact_source_context_and_owned_audit_revalidated!==true||receipt.all_claims_formalized!==false)return unknown('Required checker evidence absent');
 if(receipt.target!==binding.lean.module||receipt.claims?.length!==1||receipt.claims[0].claim_id!==binding.claim_id)return unknown('Wrong check target or claim');
 if(JSON.stringify(receipt.claims[0].declarations)!==JSON.stringify(binding.lean.declarations))return unknown('Declaration selection differs');
 if(!Array.isArray(receipt.checked_modules)||!receipt.checked_modules.length)return unknown('Missing checked source context');
 const checked=new Set(receipt.checked_modules);
 if(checked.size!==receipt.checked_modules.length)return unknown('Duplicate checked context module');
 // The producer computes the target closure, then requires every export import
 // closure to be contained in it. Accept a larger explicit audited context only
 // when it still contains all required modules and is itself dependency-closed.
 let required;try{required=requiredContext(pkg,[receipt.target,...binding.declarations.map(d=>d.owner),...receipt.checked_modules]);}
 catch(e){return unknown(e.message);}
 if([...required].some(module=>!checked.has(module)))return unknown('Incomplete checked dependency context');
 for(const module of receipt.checked_modules){if(!pkg.modules.has(module)||receipt.module_hashes?.[module]!==pkg.modules.get(module).sha256)return unknown('Checked source identity differs');}
 for(const d of binding.declarations){if(!receipt.checked_modules.includes(d.owner)||receipt.claims[0].declaration_modules?.[d.name]!==d.owner)return unknown('Declaration owner differs');}
 return {outcome:'CHECKED_SCOPED_DECLARATIONS',actual_checker_receipt:receipt,blockers:[],whole_package_acceptance:false};
}
