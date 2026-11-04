"""Read-only integrity of a prepared SOURCE context, without compiler or writers.

The caller owns encryption before any runtime-result persistence. This module
has no CLI, subprocess, network, key, record or output writer.
"""
import hashlib
import json
from pathlib import Path
import re


def verify_context(root, previous=None, expected_outer_sha256=None):
    root=Path(root)
    graph_raw=(root/'DEPENDENCY-GRAPH.json').read_bytes()
    selection_raw=(root/'SOURCE-SELECTION.json').read_bytes()
    graph=json.loads(graph_raw)
    selection=json.loads(selection_raw)
    if len(graph['targets']) != 1:
        raise ValueError('ONE_SOURCE_TARGET_REQUIRED')
    target=next(iter(graph['targets'].values()))
    modules,order,rows=target['modules'],target['order'],selection['sources']
    names=[row['module'] for row in rows]
    if (len(modules)!=len(order) or len(set(order))!=len(order)
            or len(set(names))!=len(names) or set(names)!=set(order)
            or set(order)!=set(modules)):
        raise ValueError('SOURCE_MODULE_INVENTORY_MISMATCH')
    positions={name:i for i,name in enumerate(order)}
    aliases={};hits=[];total=0
    syntax=re.compile(r'\bIO\.FS\.(?:writeFile|writeBinFile|withFile|Handle\.mk)|\brun_cmd\b|^\s*#eval\b')
    for row in rows:
        name,digest=row['module'],row['sha256']
        body=(root/'source-store'/(digest+'.lean')).read_bytes()
        if (hashlib.sha256(body).hexdigest()!=digest or len(body)!=row['bytes']
                or modules[name]['sha256']!=digest):
            raise ValueError('SOURCE_BODY_CHANGED: '+name)
        aliases.setdefault(digest,[]).append(name)
        total+=len(body)
        for dep in modules[name]['imports']:
            if dep in modules and positions[dep]>=positions[name]:
                raise ValueError('SOURCE_IMPORT_ORDER_CHANGED: '+name)
        for lineno,line in enumerate(body.decode().splitlines(),1):
            if syntax.search(line):
                hits.append({'module':name,'line':lineno,'syntax':line.strip()[:240]})
    aliases={key:values for key,values in aliases.items() if len(values)>1}
    if 'CMSparseSupplier' in modules or any('CMSparseSupplier' in x['imports'] for x in modules.values()):
        raise ValueError('DUPLICATE_EXTRACTED_SPARSE_SUPPLIER')
    if selection['native_compiler_invoked'] or selection['full_import_elaboration_run']:
        raise ValueError('SOURCE_ONLY_DISPOSITION_CHANGED')
    old_count=None;added=None
    if previous is not None:
        old_graph=json.loads((Path(previous)/'DEPENDENCY-GRAPH.json').read_bytes())
        old=next(iter(old_graph['targets'].values()))
        if any(modules.get(name)!=entry for name,entry in old['modules'].items()):
            raise ValueError('PREVIOUS_SOURCE_ENTRY_CHANGED')
        if [name for name in order if name in old['modules']]!=old['order']:
            raise ValueError('PREVIOUS_SOURCE_RELATIVE_ORDER_CHANGED')
        old_count=len(old['modules']);added=sorted(set(modules)-set(old['modules']))
    outer_sha=hashlib.sha256((root/'start_new_context.sh').read_bytes()).hexdigest()
    if expected_outer_sha256 is not None and outer_sha!=expected_outer_sha256:
        raise ValueError('OUTER_REFUSAL_SOURCE_CHANGED')
    return {'modules':len(modules),'source_bytes':total,
        'original_modules':sum(row['source']=='original/current/connected' for row in rows),
        'all_source_hashes_and_bytes_verified':True,'internal_dependency_order_verified':True,
        'source_hash_aliases':aliases,'direct_writer_or_evaluation_syntax_hits':hits,
        'prior_entries_unchanged':old_count,'added_modules':added,
        'graph_bytes':len(graph_raw),'graph_sha256':hashlib.sha256(graph_raw).hexdigest(),
        'selection_bytes':len(selection_raw),'selection_sha256':hashlib.sha256(selection_raw).hexdigest(),
        'outer_source_sha256':outer_sha,'compiler_invoked':False,
        'scope':'Source identity/order/lexical inventory only; not full imports, objects, runtime writer enforcement or execution admission.'}
