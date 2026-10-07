"""Authenticate original interval forward law and transfer joint exclusions.

Only original physical source boxes are supported. No inverse search, source
witness, journal acceptance, admission certificate or accuracy conclusion.
"""
from pathlib import Path
import hashlib
import importlib.util
import sys
import tempfile

import joint_betting as jb

PHYSICAL = ('h', 'u', 'v', 'rA', 'rB', 'rC', 'rAB', 'rR', 'g')
DOMAIN = {key: ['1/32', '1/8'] if key in ('h', 'u', 'v') else
          ['1/6', '2/3'] if key == 'g' else ['1/2', '6'] for key in PHYSICAL}
DEPENDENCIES = {
    'research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py':
        ('msci-330-feature-public-20261005-1039z/evaluator/certified_forward.py',
         'c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace'),
    'research/2026-10-05-dot-msci-original-domain-profile-localization-1621z/interval_math.py':
        ('msci-ab-profile-implementation-20261005-1612z/interval_math.py',
         '939b28c8d22652b6b5aa845dbb20dc85f8fe7c942d48495e16a86521a7910653')}


class OriginalSourceBridge:
    def __init__(self, repository_root):
        self.root = Path(repository_root)
        self._temporary = tempfile.TemporaryDirectory(prefix='cloud-practical-forward-')
        workspace = Path(self._temporary.name)
        for source, (destination, digest) in DEPENDENCIES.items():
            path = self.root / source
            if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise jb.Invalid('original interval source identity changed')
            target = workspace / destination
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(path.read_bytes())
        module_path = workspace / DEPENDENCIES[next(source for source in DEPENDENCIES if source.endswith('interval_math.py'))][0]
        spec = importlib.util.spec_from_file_location('_cloud_practical_original_interval', module_path)
        self.math = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = self.math
        spec.loader.exec_module(self.math)
        if tuple(self.math.FEATURES) != jb.FEATURES:
            raise jb.Invalid('original interval feature interface changed')

    def close(self):
        self._temporary.cleanup()

    def authenticate(self):
        for source, (_, digest) in DEPENDENCIES.items():
            path = self.root / source
            if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise jb.Invalid('original interval source identity changed')

    def enclose(self, record):
        self.authenticate()
        if not isinstance(record, dict) or set(record) != set(PHYSICAL):
            raise jb.Invalid('original nine physical keys required')
        physical = {}
        for name in PHYSICAL:
            pair = record[name]
            if not isinstance(pair, list) or len(pair) != 2:
                raise jb.Invalid('two physical endpoints required')
            lo, hi = map(jb.rational, pair)
            left, right = map(jb.rational, DOMAIN[name])
            if not left <= lo <= hi <= right:
                raise jb.Invalid('physical source box outside unchanged original domain')
            physical[name] = self.math.I(lo, hi)
        h, u, v = (physical[name] for name in ('h', 'u', 'v'))
        auxiliary = {'A': h + u, 'T': h + u + v, 'L': u + v}
        raw = self.math.selected(physical, auxiliary)
        shifted = {name: self.math.rounded((1 + raw[name]) / 2) for name in jb.FEATURES}
        result = {name: [str(shifted[name].lo), str(shifted[name].hi)] for name in jb.FEATURES}
        jb.mean_box(result)
        self.authenticate()
        return result

    def replay(self, rows, physical_box, plan, delta='1/20', max_bits=16384):
        shifted = self.enclose(physical_box)
        result = jb.replay(rows, shifted, plan, delta, max_bits)
        result.update(schema='original-source-box-joint-betting-receiver-v1',
                      physical_source_box_excluded=result['status'] == 'CONDITIONAL_MEAN_BOX_EXCLUDED',
                      physical_box_sha256=hashlib.sha256(jb.canonical(physical_box)).hexdigest(),
                      conditional_status='CONDITIONAL_ORIGINAL_SOURCE_BOX_EXCLUDED' if
                        result['status'] == 'CONDITIONAL_MEAN_BOX_EXCLUDED' else 'UNKNOWN',
                      dependency_sha256={source: entry[1] for source, entry in DEPENDENCIES.items()},
                      original_domain=DOMAIN,
                      normalized_width_targets={name: '1/20' for name in PHYSICAL},
                      forward_enclosed_shifted_means=shifted,
                      numerical_inverse_journal_validated=False)
        return result
