"""Read/AST-only source-contract analysis. Never import/execute analyzed source."""
import ast,hashlib,re
ORIGINAL_SHA256='7aee3ae34ee0f4fd9e6c686dde0813f0a9e29291ff0b33d2c6022d893c42ecff'
ARCHIVE_SHA256='e113cc88105a34d66f8c13371a71619e20633d68125856a78f1e65cf27957e20'
PAPER_CURVATURE='0.85417'

def inspect_python(raw,expected_sha256):
    """Hash-bind bytes and parse only; accepting a source never executes it."""
    digest=hashlib.sha256(raw).hexdigest()
    if digest!=expected_sha256:raise ValueError('Source bytes do not match the selected immutable pin')
    text=raw.decode('utf-8');tree=ast.parse(text,filename='READ_ONLY_SOURCE_CONTRACT')
    parent={child:node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}
    calls=[];removals=[];fields=[];curvatures=[];finally_counters=[];pre_try_row_fields=[]
    for node in ast.walk(tree):
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute):
            f=node.func
            if isinstance(f.value,ast.Name) and f.value.id=='os' and f.attr=='system':
                calls.append({'line':node.lineno,'return_ignored':isinstance(parent.get(node),ast.Expr),
                              'argument':ast.get_source_segment(text,node.args[0]) if node.args else None})
            if isinstance(f.value,ast.Name) and f.value.id=='os' and f.attr=='remove':
                removals.append({'line':node.lineno,'argument':ast.get_source_segment(text,node.args[0])})
            if isinstance(f.value,ast.Name) and f.value.id=='header' and f.attr=='index' and node.args and isinstance(node.args[0],ast.Constant):
                fields.append(node.args[0].value)
        if isinstance(node,ast.Constant) and isinstance(node.value,str):
            curvatures.extend(re.findall(r'(?:^|\s)-cc\s+([0-9]+(?:\.[0-9]+)?)',node.value))
        if isinstance(node,ast.Try):
            for part in node.finalbody:
                if isinstance(part,ast.AugAssign) and isinstance(part.target,ast.Name):
                    finally_counters.append({'line':part.lineno,'name':part.target.id,
                        'operator':type(part.op).__name__,'literal_increment':part.value.value if isinstance(part.value,ast.Constant) else None})
        if isinstance(node,ast.For) and isinstance(node.target,ast.Name) and node.target.id=='row':
            for part in node.body:
                if isinstance(part,ast.Try):break
                if isinstance(part,ast.Assign) and isinstance(part.value,ast.Subscript) and isinstance(part.value.value,ast.Name) and part.value.value.id=='row':
                    pre_try_row_fields.extend({'line':part.lineno,'name':target.id} for target in part.targets if isinstance(target,ast.Name))
    return {'sha256':digest,'bytes':len(raw),'CRLF_count':raw.count(b'\r\n'),'LF_count':raw.count(b'\n'),
            'AST_only':True,'analyzed_source_executed':False,'system_calls':sorted(calls,key=lambda x:x['line']),
            'ignored_system_return_count':sum(c['return_ignored'] for c in calls),
            'remove_calls':sorted(removals,key=lambda x:x['line']),'CSV_fields':fields,
            'source_curvature_literals':curvatures,'finally_counters':finally_counters,
            'row_extractions_before_try':pre_try_row_fields}

def inspect_pinned_quinn(raw):
    report=inspect_python(raw,ORIGINAL_SHA256)
    if report['ignored_system_return_count']!=4 or len(report['remove_calls'])!=2:
        raise ValueError('Pinned-source contract differs from the selected four-stage/two-remove source')
    report.update(paper_curvature_literal=PAPER_CURVATURE,curvatures_equivalent_claim=False,
        processed_counter_is_validated_output_certificate=False,
        published_run_failure_established=False,statewide_certificate=False,
        original_processed_CSV_supplied=False,original_DEM_supplied=False,
        finally_counter_scope='Rows that enter the try/finally; row extraction before try can fail without increment',
        external_stage_return_codes_checked_in_source=False)
    return report
