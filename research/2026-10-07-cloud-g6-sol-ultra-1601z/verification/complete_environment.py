"""Prepared complete custom ownership inventory; not a compiler by itself.

Derivative of dot's complete AuditTemplate and the actual successful timed G5
takeover payload recovery. Call only inside the sole bounded serial runner.
"""
import base64
import gzip
import hashlib
import json


def prepare(root, evidence, repository, modules):
    template_path = repository / (
        'research/2026-10-05-dot-connected-modular-lean-workspace-2252z/'
        'package/scripts/AuditTemplate.lean')
    template = template_path.read_text()
    old = '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
    if template.count(old) != 1:
        raise RuntimeError('Unexpected attributed complete inventory template')
    template = template.replace(old, '#[' + ', '.join(json.dumps(n) for n in modules) + ']')
    audit = evidence / 'CompleteEnvironmentAudit.lean'
    audit.write_text('\n'.join('import ' + n for n in modules) + '\n' + template)
    (root / 'AUDIT-OWNED.json').unlink(missing_ok=True)
    return audit


def recover(root, evidence, modules):
    data = (root / 'AUDIT-OWNED.json').read_bytes()
    report = json.loads(data)
    if (report['owned_axioms'] or report['nonstandard_axiom_rows'] or report['missing_modules'] or
            set(report['selected_modules']) != set(modules)):
        raise RuntimeError('Rejected complete selected custom environment inventory')
    if any(row['module'] not in modules or
           set(row['axioms']) - {'propext', 'Classical.choice', 'Quot.sound'}
           for row in report['declarations']):
        raise RuntimeError('Unexpected declaration ownership or transitive axiom')
    rows = report['declarations']
    if (report['declaration_count'] != len(rows) or
            report['theorem_declaration_count'] != sum(row['kind'] == 'theorem' for row in rows) or
            len({row['name'] for row in rows}) != len(rows) or
            any('type_references' not in row or 'body_references' not in row for row in rows)):
        raise RuntimeError('Incomplete generated/type/body declaration inventory')
    (evidence / 'complete-environment-inventory.json').write_bytes(data)
    receipt = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
               'encoding': 'gzip+base64', 'selected_custom_modules': len(modules),
               'declaration_count': report['declaration_count'],
               'theorem_declaration_count': report['theorem_declaration_count'],
               'audit_source_sha256': hashlib.sha256(
                   (evidence / 'CompleteEnvironmentAudit.lean').read_bytes()).hexdigest()}
    print('G6_COMPLETE_ENVIRONMENT_PAYLOAD ' + json.dumps(receipt), flush=True)
    encoded = base64.b64encode(gzip.compress(data, mtime=0)).decode()
    print('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN', flush=True)
    for index in range(0, len(encoded), 4096):
        print(encoded[index:index + 4096], flush=True)
    print('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END', flush=True)
    print('G6_COMPLETE_ENVIRONMENT_PASSED ' + json.dumps(receipt), flush=True)
    return receipt
