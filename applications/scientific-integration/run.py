"""One offline entry point for recovered research applications."""
import argparse
import hashlib
import html
import json
import os
from pathlib import Path
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
PROJECTS = BASE.parent
DEFAULT_COMMONS = PROJECTS.parent if (PROJECTS.parent / 'research').is_dir() else PROJECTS.parent.parent / 'Research-Commons'
PACKET = Path('research/2026-10-08-codex-integration-0825z')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def call(command, cwd, directory, name, timeout=120):
    env = dict(os.environ)
    env.pop('ALPHAGENOME_API_KEY', None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['PYTHONNOUSERSITE'] = '1'
    start = time.monotonic()
    try:
        proc = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                              text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {'name': name, 'status': 'RESOURCE_LIMIT', 'timeout': True}
    except OSError:
        return {'name': name, 'status': 'EXECUTION_FAILURE',
                'reason': 'EXECUTABLE_UNAVAILABLE', 'command': command,
                'exit_code': None}
    output = directory / (name + '.stdout')
    output.write_text(proc.stdout)
    receipt = {'name': name, 'command': command, 'exit_code': proc.returncode,
               'wall_seconds': time.monotonic() - start,
               'stdout_sha256': sha(output),
               'stderr_bytes': len(proc.stderr.encode()),
               'stderr_sha256': hashlib.sha256(proc.stderr.encode()).hexdigest()}
    # Raw exception/debug output is not forwarded or logged by this wrapper.
    try:
        receipt['result'] = json.loads(proc.stdout)
    except ValueError:
        receipt['status'] = 'EXECUTION_FAILURE' if proc.returncode else 'TEXT_OUTPUT'
    return receipt


def write_report(directory, result):
    (directory / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    explanation = result['explanation']
    baseline = result.get('real_sequence_baseline', {})
    table = ''
    if baseline.get('rows'):
        table = ('<h2>Public marker comparison</h2><p>This small baseline uses '
                 'the published specimen/accession joins. Each split separates '
                 'the four sampled taxa into two pairs.</p><table><thead><tr>'
                 '<th>Marker</th><th>Sites</th><th>Estimated split</th>'
                 '<th>Column bootstrap</th></tr></thead><tbody>')
        for row in baseline['rows']:
            split = ' | '.join(' + '.join(part) for part in row['estimated_split'])
            support = f"{row['bootstrap_support']:.0%} of {row['bootstrap_replicates']} replicates"
            cells = [row['marker'], str(row['sites']), split, support]
            table += '<tr>' + ''.join('<td>' + html.escape(cell) + '</td>' for cell in cells) + '</tr>'
        table += ('</tbody></table><p>' + html.escape(baseline['uncertainty_note'])
                  + '</p><p>' + html.escape(baseline['inferred_region_note']) + '</p>')
    page = ('<!doctype html><html lang="en"><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<title>Research application result</title><style>body{font:18px/1.5 system-ui;'
            'max-width:900px;margin:2rem auto;padding:1rem}pre{white-space:pre-wrap;'
            'overflow-wrap:anywhere;background:#f4f6f4;padding:1rem}'
            'table{border-collapse:collapse;width:100%;font-size:15px}'
            'th,td{text-align:left;border-bottom:1px solid #bbb;padding:.6rem;overflow-wrap:anywhere}</style>'
            '<h1>' + html.escape(result['title']) + '</h1><p>'
            + html.escape(explanation) + '</p><p><b>Biological conclusion: '
            + html.escape(result['biological_conclusion']) + '</b></p>'
            '<p><b>Execution status: ' + html.escape(result.get('status', 'UNKNOWN')) + '</b></p>'
            + table +
            '<p><a href="RESULT.json">Full evidence and command receipts</a></p>'
            '<details><summary>Technical evidence</summary><pre>'
            + html.escape(json.dumps(result, indent=2)) + '</pre></details></html>')
    (directory / 'REPORT.html').write_text(page)


def execute(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    result = {'schema': 'research-integration/offline-v1', 'operation': args.mode,
              'title': 'Research Commons application', 'receipts': [],
              'biological_conclusion': 'NOT_ESTABLISHED',
              'live_model_calls': 0, 'professor_contact_or_endorsement': False,
              'whole_application_lean_verified': False}
    if args.mode == 'cwu':
        packet = args.commons.resolve() / PACKET / 'g6'
        if args.replay:
            receipt = call([args.solver_python, '-B', str(packet / 'run_cwu_demo.py'),
                            '--output', str(output / 'source-controls')], packet,
                           output, 'source-controls', timeout=180)
            result['receipts'].append(receipt)
            if receipt.get('exit_code') != 0:
                result.update(title='Hemlock comparison could not be replayed',
                              status='EXECUTION_FAILURE',
                              explanation='The source-control replay failed or exceeded its bound. No result is promoted.')
                write_report(output, result)
                return 3
            comparison = json.loads((output / 'source-controls/COMPARISON.json').read_text())
            result['control_execution'] = 'REPLAYED_NOW'
        else:
            comparison = json.loads((packet / 'CWU-RUNS/COMPARISON.json').read_text())
            result['control_execution'] = 'RECOVERED_SAVED_RECEIPTS'
        result.update(title='Raubeson: nuclear and chloroplast hemlock relationships',
                      explanation='The paper reports two crossing sister clades. They cannot both be clades of one rooted tree. The original solver and checker distinguish two explicitly synthetic laws and reject the unadmitted empirical case. This does not identify chloroplast capture; original alignments and the sequence-to-source uncertainty contract remain missing.',
                      comparison=comparison,
                      status='INSPECTABLE_COMPARISON_EMPIRICAL_ADMISSION_OPEN')
        real = packet / 'REAL-BASELINE/COMPARISON.json'
        if args.replay_sequences:
            target = output / 'real-sequence-baseline'
            receipt = call([args.python, '-B', str(packet / 'prepare_real_baseline.py'),
                            '--workbench', str(PROJECTS / 'genealogy-compatibility-workbench'),
                            '--output', str(target)], packet, output, 'real-sequence-baseline', timeout=180)
            result['receipts'].append(receipt)
            if receipt.get('exit_code') == 0:
                real = target / 'COMPARISON.json'
        if real.is_file():
            result['real_sequence_baseline'] = json.loads(real.read_text())
            result['real_sequence_execution'] = ('REPLAYED_NOW' if args.replay_sequences and
                                                result['receipts'][-1].get('exit_code') == 0 else
                                                'RECOVERED_SAVED_PUBLIC_DATA_RECEIPTS')
            result['explanation'] = ('The published nuclear/chloroplast disagreement is compared with an exploratory baseline on public GenBank sequences linked to the paper specimens. The baseline has its own marker choices and preprocessing; it is not a replay of the complete published analysis. Separate synthetic exact laws exercise our source solver and checker. Empirical source admission is still missing, so neither baseline nor solver establishes chloroplast capture.')
    elif args.mode == 'workbench':
        project = PROJECTS / 'genealogy-compatibility-workbench'
        result['receipts'].append(call([args.python, '-B', '-m', 'genealogy_workbench',
                                      'demo', '--output-dir', str(output / 'demo')],
                                     project, output, 'workbench-demo'))
        result.update(title='Exact and conditional genealogy workbench',
                      explanation='Recovered source-preserving demonstrations show finite-catalogue compatibility, ambiguity and abstention. Their declared source and observation promises do not establish membership of empirical hemlock data.',
                      status='RECOVERED_APPLICATION_DEMO')
    elif args.mode == 'molecular':
        project = PROJECTS / 'molecular-analysis'
        jobs = [('tert-rna', ['rna', 'examples/tert-rna-public-reference-mock.json']),
                ('synthetic-rna-pas', ['rna', 'examples/synthetic-rna-processing.json'])]
        if args.core_binary:
            jobs.append(('tert-haplotype', ['haplotype', 'examples/tert-public-reference-mock.json',
                                          '--core-binary', str(args.core_binary.resolve())]))
        else:
            result['haplotype'] = 'UNAVAILABLE: provide the verified native core binary'
        for name, command in jobs:
            result['receipts'].append(call([args.python, '-B', '-m', 'molecular_apps',
                                          *command, '--provider', 'mock'], project, output, name))
        result.update(title='Recovered molecular applications: offline mocks',
                      explanation='The existing RNA and haplotype services are reused with their synthetic provider. Expression, splice usage and derived PAS remain separate. Four matched sequences are required for predicted haplotype nonadditivity. These results are software fixtures, not measured biology or plant-hemlock predictions.',
                      status='MOCK_SYNTHETIC')
    else:
        project = PROJECTS / 'genealogy-compatibility-workbench'
        manifest = json.loads(args.public_manifest.read_text())
        expected = {'source_url', 'license', 'nuclear_json_sha256', 'plastid_json_sha256'}
        if set(manifest) != expected or manifest['license'] != 'CC0-1.0' or manifest['source_url'] != 'https://datadryad.org/dataset/doi:10.5061/dryad.2r12j':
            raise ValueError('The paired input needs the declared public Tsuga source manifest')
        mappings = []
        for compartment, path in [('nuclear', args.nuclear_json), ('plastid', args.plastid_json)]:
            if sha(path) != manifest[compartment + '_json_sha256']:
                raise ValueError('Paired input digest mismatch')
            receipt = call([args.python, '-B', '-m', 'genealogy_workbench', 'sequence',
                            str(path.resolve())], project, output, compartment)
            result['receipts'].append(receipt)
            mappings.append(receipt.get('result', {}).get('result', {}).get('original_taxon_id_mapping'))
        result.update(title='Paired public nuclear/plastid sequence baseline',
                      explanation='The existing exploratory quartet and bootstrap adapter runs on each declared compartment separately. Supplied hashes bind inputs, but they do not authenticate the original alignment transformation, orthology or independence. Bootstrap support is descriptive; linked plastid markers are not counted as independent ancestry replicates. A capture certificate is withheld.',
                      status='EXPLORATORY_SEQUENCE_COMPARISON', public_manifest=manifest,
                      original_taxon_sets_match=bool(mappings[0]) and mappings[0] == mappings[1],
                      public_provenance_independently_verified=False,
                      empirical_source_admission='NOT_ESTABLISHED')
        if not result['original_taxon_sets_match']:
            result['status'] = 'PAIR_COMPARISON_REFUSED'
    failed = any(x.get('exit_code', 1) != 0 for x in result['receipts'])
    if failed:
        result['execution_failure'] = True
        result['status'] = 'EXECUTION_FAILURE'
    write_report(output, result)
    print(result['title'])
    print(result['explanation'])
    if failed:
        print('A requested computation failed; see the report. Saved evidence is labeled separately.')
    if result.get('real_sequence_baseline'):
        for row in result['real_sequence_baseline']['rows']:
            split = ' | '.join(' + '.join(part) for part in row['estimated_split'])
            print(row['marker'] + ': ' + split)
        print('Marker bootstrap is descriptive; chloroplast capture remains UNKNOWN.')
    print('Evidence: ' + str(output / 'RESULT.json'))
    print('Readable report: ' + str(output / 'REPORT.html'))
    return 3 if failed else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['cwu', 'workbench', 'molecular', 'sequence-pair'])
    parser.add_argument('--output', type=Path, help='fresh result directory; default creates a dated local report')
    parser.add_argument('--commons', type=Path, default=DEFAULT_COMMONS)
    parser.add_argument('--python', default=sys.executable)
    parser.add_argument('--solver-python', default=sys.executable)
    parser.add_argument('--replay', action='store_true')
    parser.add_argument('--replay-sequences', action='store_true',
                        help='recompute the public CWU marker baseline using Biopython 1.88')
    parser.add_argument('--core-binary', type=Path)
    parser.add_argument('--nuclear-json', type=Path)
    parser.add_argument('--plastid-json', type=Path)
    parser.add_argument('--public-manifest', type=Path)
    args = parser.parse_args()
    if args.replay_sequences and args.mode != 'cwu':
        parser.error('--replay-sequences applies to cwu')
    if args.output is None:
        import datetime
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
        args.output = Path.cwd() / 'integration-results' / (stamp + '-' + args.mode)
    if args.mode == 'sequence-pair' and not all((args.nuclear_json, args.plastid_json, args.public_manifest)):
        parser.error('sequence-pair needs both compartment JSON inputs and a public manifest')
    try:
        return execute(args)
    except (OSError, ValueError, KeyError):
        print('Input or application error; prior artifacts are preserved.', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
