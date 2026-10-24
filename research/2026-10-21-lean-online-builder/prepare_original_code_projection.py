#!/usr/bin/env python3
"""Prepare a complete admitted-source component with layout-preserving compaction.

No compiler or native process is run. Original bodies remain pinned; only
standalone block comments and line-comment tails are removed. Imports are
hoisted and each original module gets a section boundary to retain local scope.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
UNSELECTED_STRING = re.compile(r'(?:s!|m!|f!|r#+|r)"')
CHARACTER_LITERAL = re.compile(r"'(?:\\.|[^'\\\n])'")


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def compact(text):
    out, signature = [], hashlib.sha256()
    i, line, column = 0, 1, 0

    def advance(segment, code=False, literal=False):
        nonlocal line, column
        for c in segment:
            if code and (literal or not c.isspace()):
                signature.update((str(line)+':'+str(column)+':'+c+'\0').encode())
            if c == '\n':
                line, column = line+1, 0
            else:
                column += 1

    while i < len(text):
        if text.startswith('/-', i):
            start, depth, j = i, 1, i+2
            while j < len(text) and depth:
                if text.startswith('/-',j): depth, j = depth+1, j+2
                elif text.startswith('-/',j): depth, j = depth-1, j+2
                else: j += 1
            if depth: raise ValueError('UNTERMINATED_BLOCK_COMMENT')
            before = text[text.rfind('\n',0,start)+1:start]
            end = text.find('\n',j)
            after = text[j:len(text) if end < 0 else end]
            segment = text[start:j]
            standalone = not before.strip() and not after.strip()
            # Keep original copyright/licence notices in the artifact.
            licence = re.search(r'Copyright|SPDX|[Ll]icens',segment) is not None
            out.append('\n'*segment.count('\n') if standalone and not licence else segment)
            advance(segment)
            i = j
        elif text.startswith('--',i):
            j = text.find('\n',i)
            if j < 0: j = len(text)
            advance(text[i:j])
            i = j
        elif UNSELECTED_STRING.match(text,i):
            raise ValueError('INTERPOLATED_OR_RAW_STRING_COMPACTION_NOT_SELECTED')
        elif text[i] == '"':
            j = i+1
            while j < len(text):
                if text[j] == '\\': j += 2
                elif text[j] == '"': j += 1; break
                else: j += 1
            else: raise ValueError('UNTERMINATED_STRING')
            segment = text[i:j]
            out.append(segment); advance(segment,True,True); i = j
        elif text[i] == "'" and (m := CHARACTER_LITERAL.match(text,i)):
            segment = m.group()
            out.append(segment); advance(segment,True,True); i += len(segment)
        else:
            out.append(text[i]); advance(text[i],True); i += 1
    return ''.join(out), signature.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,required=True)
    args = parser.parse_args()
    project = args.project.resolve()
    graph = json.loads((project/'DEPENDENCY-GRAPH.json').read_bytes())
    modules = graph['targets']['physical-pmf-certificate-new-context']['modules']
    order, seen = [], set()

    def visit(name):
        if name in seen:return
        for dependency in modules[name]['imports']:
            if dependency in modules:visit(dependency)
        seen.add(name);order.append(name)

    visit('G7OriginalAdmission')
    inputs=[];original_identity={}
    for name in order:
        raw=(project/'source-store'/(modules[name]['sha256']+'.lean')).read_bytes()
        if digest(raw)!=modules[name]['sha256']:raise ValueError('ORIGINAL_SOURCE_CHANGED')
        original_identity[name]={'bytes':len(raw),'sha256':digest(raw)}
        if name in ('G5FairSelectorMoments','G4PathResolvedMeasurement'):
            variants=json.loads((ROOT/'lean/hosted435/SOURCE-VARIANTS.json').read_bytes())['variants']
            raw=(ROOT/variants[name]['path']).read_bytes()
            if digest(raw)!=variants[name]['sha256'] or len(raw)!=variants[name]['bytes']:
                raise ValueError('HOSTED_API_VARIANT_CHANGED')
        inputs.append((name,raw))
    for name in ('NativeOrderedBankLayout','OriginalCodeBankLayout'):
        inputs.append((name,(ROOT/'lean'/(name+'.lean')).read_bytes()))
    names={name for name,_ in inputs}
    external, parts, mapping=[],[],[]
    for number,(name,raw) in enumerate(inputs):
        text=raw.decode()
        if re.search(r'(?m)^\s*(?:#eval|run_cmd|initialize)\b|\bIO\.(?:FS|Process)\b',text):
            raise ValueError('UNSELECTED_RUNTIME_WRITER_OR_EVALUATION')
        imports=[]; body=[]; omitted_prints=[]
        for line_number,line in enumerate(text.splitlines(keepends=True),1):
            if line.startswith('import '):
                imports.extend(line.strip().split()[1:])
                body.append('\n' if line.endswith('\n') else '')
            elif re.fullmatch(r'\s*#print axioms [^\s]+\s*',line):
                omitted_prints.append({'line':line_number,'command':line.strip()})
                body.append('\n' if line.endswith('\n') else '')
            else:body.append(line)
        if name in modules and name not in ('NativeOrderedBankLayout','OriginalCodeBankLayout'):
            expected=modules[name]['imports']
            if name=='G5FairSelectorMoments':
                expected=expected+['Mathlib.Probability.ProbabilityMassFunction.Constructions']
            if imports!=expected:raise ValueError('IMPORT_MAP_CHANGED')
        for dependency in imports:
            if dependency not in names and dependency not in external:external.append(dependency)
        unimported=''.join(body)
        compressed,signature=compact(unimported)
        _,verified=compact(compressed)
        if signature!=verified:raise ValueError('CODE_TOKEN_OR_LAYOUT_CHANGED')
        label='OriginalComponent'+str(number)
        styles=('set_option linter.unusedSectionVars false\n'
                'set_option linter.unusedSimpArgs false\n') if name in original_identity else ''
        parts.append('section '+label+'\n'+styles+compressed+'\nend '+label+'\n')
        mapping.append({'module':name,
            'original_bytes':original_identity.get(name,{'bytes':len(raw)})['bytes'],
            'original_sha256':original_identity.get(name,{'sha256':digest(raw)})['sha256'],
            'selected_source_bytes':len(raw),'selected_source_sha256':digest(raw),
            'projected_body_bytes':len(compressed.encode()),
            'projected_body_sha256':digest(compressed.encode()),
            'omitted_unselected_informational_commands':omitted_prints,
            'code_character_layout_sha256':signature})
    document='\n'.join('import '+name for name in external)+'\n\n'+'\n'.join(parts)
    raw=document.encode()
    if len(raw)>258000:raise ValueError('COMPLETE_COMPONENT_EXCEEDS_EXISTING_LANE')
    destination=ROOT/'lean/OnlineOriginalCodeBankLayout.lean'
    destination.write_bytes(raw)
    mapping={'kind':'complete_original_admission_component_projection',
        'original_root':'G7OriginalAdmission','original_module_count':len(order),
        'original_bytes':sum(row['bytes'] for row in original_identity.values()),
        'owned_modules':['NativeOrderedBankLayout','OriginalCodeBankLayout'],
        'external_imports':external,'sources':mapping,'virtual_bytes':len(raw),
        'virtual_sha256':digest(raw),'compaction':'Only standalone block comments/line-comment tails; imports hoisted, unselected informational axiom prints omitted, section scopes retained; remaining non-comment code character positions unchanged per selected source module.',
        'explicit_hosted_variants':['G5FairSelectorMoments: old PMF uniform API replaced by a four-point PMF with identical atom masses.','G4PathResolvedMeasurement: the two real-product lemmas use their renamed zero-aware versions.'],
        'suppressed_style_linter_options':['linter.unusedSectionVars','linter.unusedSimpArgs'],
        'unsafe_sorry_or_error_diagnostics_suppressed':False,
        'compiler_invoked':False,'native_Lake_or_object_acceptance':False}
    (ROOT/'lean/OriginalCodeBankLayout-SOURCE-MAP.json').write_text(json.dumps(mapping,indent=2)+'\n')
    print(json.dumps({'source_only_component_modules':len(inputs),'virtual_bytes':len(raw),
        'virtual_sha256':digest(raw),'original_code_layout_preserved':True,'compiler_invoked':False}))


if __name__=='__main__':main()
