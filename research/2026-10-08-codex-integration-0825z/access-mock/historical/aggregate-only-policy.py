"""Credential-free policy contract exercise; no SDK, client or network code.

This does not replace or replay the private molecular application. It exercises
the proposed operation/attempt policy using fixed, labelled synthetic outcomes.
"""
import json
import sqlite3
from fractions import Fraction
from pathlib import Path

SCENARIOS = ('REF', 'A', 'B', 'A+B')
SETTINGS = 'fixed-public-reference-mock-context-v1'
EXPRESSION = dict(zip(SCENARIOS, (100, 110, 95, 112)))
SPLICE_USAGE = dict(zip(SCENARIOS, map(Fraction, ('1/5', '3/10', '3/20', '29/100'))))


class MockPolicy:
    def __init__(self, ledger):
        self.db = sqlite3.connect(ledger, isolation_level=None)
        self.db.execute('PRAGMA synchronous=FULL')
        self.db.execute('CREATE TABLE IF NOT EXISTS budget (id INTEGER PRIMARY KEY, used INTEGER NOT NULL CHECK(used BETWEEN 0 AND 5))')
        self.db.execute('INSERT OR IGNORE INTO budget VALUES (1, 0)')

    def close(self):
        self.db.close()

    def used(self):
        return self.db.execute('SELECT used FROM budget WHERE id=1').fetchone()[0]

    def reserve(self):
        self.db.execute('BEGIN IMMEDIATE')
        try:
            used = self.used()
            if used >= 5:
                self.db.execute('ROLLBACK')
                return False
            self.db.execute('UPDATE budget SET used=? WHERE id=1', (used + 1,))
            self.db.execute('COMMIT')
            return True
        except BaseException:
            self.db.execute('ROLLBACK')
            raise

    def exercise(self, request, outcome='OK'):
        allowed = {'mode', 'operation', 'scenario', 'length', 'settings', 'phase'}
        if set(request) - allowed:
            return {'status': 'INVALID_FIELDS'}
        if request.get('mode') != 'OFFLINE_MOCK':
            return {'status': 'LIVE_DISABLED'}
        operation = request.get('operation')
        if operation not in ('metadata', 'predict_sequence'):
            return {'status': 'UNSUPPORTED_OPERATION'}
        if operation == 'predict_sequence':
            if request.get('scenario') not in SCENARIOS or request.get('length') != 131072:
                return {'status': 'INVALID_INPUT'}
            if request.get('settings') != SETTINGS:
                return {'status': 'SETTINGS_MISMATCH'}
            if request.get('phase') not in ('unknown', 'hypothetical'):
                return {'status': 'PHASE_EVIDENCE_REQUIRED'}
        if outcome not in ('OK', 'UNAVAILABLE', 'RESOURCE_EXHAUSTED', 'TIMEOUT', 'CRASH'):
            return {'status': 'INVALID_MOCK_OUTCOME'}
        if not self.reserve():
            return {'status': 'RESOURCE_LIMIT', 'attempts': 0}
        # Every enumerated result consumes exactly one durable reservation.
        # No retry wrapper/provider exists and no exception text is emitted.
        if outcome != 'OK':
            return {'status': outcome, 'attempts': 1}
        if operation == 'metadata':
            return {'status': 'MOCK_SYNTHETIC', 'attempts': 1, 'live_support_verified': False}
        scenario = request['scenario']
        return {'status': 'MOCK_SYNTHETIC', 'attempts': 1,
                'scenario': scenario, 'settings': SETTINGS,
                'phase': request['phase'], 'combined_is_observed': False,
                'expression_linear': str(EXPRESSION[scenario]),
                'splice_usage_fraction': str(SPLICE_USAGE[scenario]),
                'splice_junctions': {'status': 'UNAVAILABLE'},
                'PSI': {'status': 'UNAVAILABLE'},
                'PAS': {'status': 'UNAVAILABLE', 'reason': 'NO_ANNOTATED_SITE_WINDOWS'},
                'calibrated_model_interval': None,
                'biological_conclusion_established': False}


def request(scenario):
    return {'mode': 'OFFLINE_MOCK', 'operation': 'predict_sequence',
            'scenario': scenario, 'length': 131072,
            'settings': SETTINGS, 'phase': 'hypothetical'}


def comparison(rows):
    if set(rows) != set(SCENARIOS):
        raise ValueError('four matched scenarios required')
    for name, row in rows.items():
        if row['status'] != 'MOCK_SYNTHETIC' or row['scenario'] != name or row['settings'] != SETTINGS:
            raise ValueError('complete matched mock context required')
    result = {'evidence': 'MOCK_SYNTHETIC', 'biological_conclusion_established': False}
    for endpoint in ('expression_linear', 'splice_usage_fraction'):
        values = {name: Fraction(row[endpoint]) for name, row in rows.items()}
        additive = values['A'] + values['B'] - 2 * values['REF']
        combined = values['A+B'] - values['REF']
        result[endpoint] = {'additive_change': str(additive),
                            'combined_change': str(combined),
                            'interaction': str(combined - additive)}
    result.update(PAS='UNAVAILABLE', PSI='UNAVAILABLE', splice_junctions='UNAVAILABLE',
                  model_confidence='NOT_CALIBRATED')
    return result


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--ledger', type=Path, required=True)
    args = parser.parse_args()
    if args.ledger.exists():
        raise SystemExit('preserve prior ledger; choose a fresh exercise path')
    policy = MockPolicy(args.ledger)
    metadata = policy.exercise({'mode': 'OFFLINE_MOCK', 'operation': 'metadata'})
    rows = {name: policy.exercise(request(name)) for name in SCENARIOS}
    print(json.dumps({'metadata': metadata, 'rows': rows,
                      'comparison': comparison(rows), 'reserved_attempts': policy.used()}, sort_keys=True))
    policy.close()
