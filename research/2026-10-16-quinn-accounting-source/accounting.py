"""Independent, standard-library accounting for synthetic viewshed receipts.

No raster I/O, GDAL, command execution, retry, or published-run inference.
Artifact validation flags are assertions supplied by a separate storage owner.
"""
from dataclasses import dataclass, fields
from fractions import Fraction
import re

STAGES = ('viewshed', 'translate', 'weight', 'translate_weighted')

def _label(value):
    if not isinstance(value, str) or not value.strip():
        raise ValueError('Expected a nonempty identity')
    return value

def _natural(value):
    if type(value) is not int or value < 0:
        raise ValueError('Expected an exact nonnegative integer')
    return value

@dataclass(frozen=True)
class Grid:
    identity: str
    width: int
    height: int
    mask: tuple

    def __post_init__(self):
        _label(self.identity)
        if type(self.width) is not int or type(self.height) is not int or min(self.width, self.height) <= 0:
            raise ValueError('Positive integer grid dimensions required')
        if type(self.mask) is not tuple or len(self.mask) != self.width * self.height or any(type(x) is not bool for x in self.mask):
            raise ValueError('An explicit common Boolean mask is required')

@dataclass(frozen=True)
class BooleanRaster:
    grid: Grid
    cells: tuple

    def __post_init__(self):
        if not isinstance(self.grid, Grid) or type(self.cells) is not tuple or len(self.cells) != len(self.grid.mask):
            raise ValueError('Raster shape does not match grid')
        if any(type(x) not in (int, bool) or x not in (0, 1) for x in self.cells):
            raise ValueError('Boolean cells only, including masked positions')

@dataclass(frozen=True)
class Artifact:
    sha256: str
    raster: BooleanRaster
    checksum_checked: bool
    grid_checked: bool
    crs_checked: bool
    nodata_checked: bool
    binary_checked: bool

    def valid_for(self, grid):
        return (isinstance(self.sha256, str) and re.fullmatch(r'[0-9a-f]{64}', self.sha256) is not None
                and isinstance(self.raster, BooleanRaster) and self.raster.grid == grid
                and all(x is True for x in (self.checksum_checked, self.grid_checked,
                    self.crs_checked, self.nodata_checked, self.binary_checked)))

@dataclass(frozen=True)
class Event:
    event_id: str
    row_id: str
    run_id: str
    config_id: str
    kind: str
    stage: str | None = None
    exit_code: int | None = None
    artifact: Artifact | None = None

def _event_schema_error(event):
    """Check the complete typed receipt before ANY duplicate acceptance.

    False validation assertions are well-typed failed evidence. Integer 1 is
    not a Boolean assertion; float/bool exits are not exact integer exits.
    This is schema validation, not file checking or production authentication.
    """
    if type(event) is not Event:
        return 'a typed immutable Event is required'
    for name in ('event_id', 'row_id', 'run_id', 'config_id', 'kind'):
        value = getattr(event, name)
        if type(value) is not str or not value.strip():
            return 'nonempty exact string identities and kind are required'
    if event.kind == 'attempt':
        if any(value is not None for value in (event.stage, event.exit_code, event.artifact)):
            return 'attempt events cannot carry stage or artifact fields'
    elif event.kind == 'stage':
        if (type(event.stage) is not str or event.stage not in STAGES or event.artifact is not None
                or (event.exit_code is not None and type(event.exit_code) is not int)):
            return 'stage receipt requires a named stage and an exact integer or unconfirmed exit'
    elif event.kind == 'artifact':
        if event.stage is not None or event.exit_code is not None or type(event.artifact) is not Artifact:
            return 'artifact event requires only a typed Artifact receipt'
        value = event.artifact
        if type(value.sha256) is not str or re.fullmatch(r'[0-9a-f]{64}', value.sha256) is None:
            return 'artifact checksum requires a lowercase SHA256 string'
        if any(type(getattr(value, name)) is not bool for name in
                ('checksum_checked', 'grid_checked', 'crs_checked', 'nodata_checked', 'binary_checked')):
            return 'artifact assertions require exact Boolean fields'
        if type(value.raster) is not BooleanRaster or type(value.raster.grid) is not Grid:
            return 'artifact raster and grid require their exact declared types'
        raster, grid = value.raster, value.raster.grid
        if (type(grid.identity) is not str or not grid.identity.strip()
                or type(grid.width) is not int or type(grid.height) is not int
                or min(grid.width, grid.height) <= 0 or type(grid.mask) is not tuple
                or len(grid.mask) != grid.width * grid.height or any(type(x) is not bool for x in grid.mask)
                or type(raster.cells) is not tuple or len(raster.cells) != len(grid.mask)
                or any(type(x) not in (int, bool) or x not in (0, 1) for x in raster.cells)):
            return 'artifact raster/grid/mask fields violate the declared Boolean schema'
    else:
        return 'unknown event kind'
    return None

def _typed_equal(left, right):
    """Exact replay includes Python representation types, including nested data."""
    if type(left) is not type(right):
        return False
    if type(left) in (Event, Artifact, BooleanRaster, Grid):
        return all(_typed_equal(getattr(left, field.name), getattr(right, field.name)) for field in fields(left))
    if type(left) is tuple:
        return len(left) == len(right) and all(_typed_equal(a, b) for a, b in zip(left, right))
    return left == right

class Registry:
    """A fixed expected universe; a new attempt/configuration needs a new registry.

    The status partition is disjoint. Attempted is an independent observation,
    never a substitute for validated. Failures latch for this run.
    """
    def __init__(self, expected_ids, run_id, config_id, grid):
        if isinstance(expected_ids, (str, bytes)):
            raise ValueError('Supply a sequence of expected IDs')
        ids = tuple(expected_ids)
        if not ids:
            raise ValueError('An explicit nonempty expected-ID universe is required')
        for row in ids:
            _label(row)
        if len(set(ids)) != len(ids):
            raise ValueError('Duplicate expected IDs')
        if not isinstance(grid, Grid):
            raise ValueError('Declared common grid required')
        self.expected_ids = ids
        self.run_id, self.config_id, self.grid = _label(run_id), _label(config_id), grid
        self._seen = {}
        self._rows = {row: {'attempted': False, 'stages': {}, 'artifact': None, 'errors': []} for row in ids}
        self.issues = []

    def _fail(self, row, reason):
        self._rows[row]['errors'].append(reason)

    def record(self, event):
        error = _event_schema_error(event)
        if error is not None:
            # Retain a safe identity anchor and latch bound-row failure even
            # for a malformed first arrival. A later valid event cannot erase
            # it or turn the malformed observation into an idempotent replay.
            bound_rows = set()
            if type(event) is Event:
                if type(event.row_id) is str and event.row_id in self._rows:
                    bound_rows.add(event.row_id)
                if type(event.event_id) is str and event.event_id.strip() and type(event.row_id) is str:
                    if event.event_id in self._seen:
                        bound_rows.add(self._seen[event.event_id].row_id)
                        self.issues.append('conflicting malformed event identity: ' + event.event_id)
                    else:
                        self._seen[event.event_id] = event
            for row in bound_rows & self._rows.keys():
                self._fail(row, 'malformed event schema: ' + error)
            if not (bound_rows & self._rows.keys()):
                self.issues.append('unbound malformed event schema')
            raise ValueError('Malformed event schema: ' + error)
        if event.event_id in self._seen:
            old = self._seen[event.event_id]
            if _typed_equal(old, event):
                return False
            for row in {old.row_id, event.row_id} & self._rows.keys():
                self._fail(row, 'conflicting event identity')
            self.issues.append('conflicting event identity: ' + event.event_id)
            raise ValueError('Conflicting event replay')
        if event.row_id not in self._rows:
            self.issues.append('unexpected row: ' + str(event.row_id))
            raise ValueError('Event outside fixed expected-ID universe')
        self._seen[event.event_id] = event
        row = self._rows[event.row_id]
        if (event.run_id, event.config_id) != (self.run_id, self.config_id):
            self._fail(event.row_id, 'stale run or wrong configuration')
            return True
        if event.kind == 'attempt':
            if any(x is not None for x in (event.stage, event.exit_code, event.artifact)):
                self._fail(event.row_id, 'malformed attempt event')
            else:
                row['attempted'] = True
        elif event.kind == 'stage':
            row['attempted'] = True
            if event.stage not in STAGES or event.artifact is not None or (event.exit_code is not None and type(event.exit_code) is not int):
                self._fail(event.row_id, 'malformed stage receipt')
            elif event.stage in row['stages'] and row['stages'][event.stage] != event.exit_code:
                self._fail(event.row_id, 'conflicting stage outcome')
            else:
                row['stages'][event.stage] = event.exit_code
                if event.exit_code is not None and event.exit_code != 0:
                    self._fail(event.row_id, 'stage did not exit zero: ' + event.stage)
        elif event.kind == 'artifact':
            if event.stage is not None or event.exit_code is not None or not isinstance(event.artifact, Artifact) or not event.artifact.valid_for(self.grid):
                self._fail(event.row_id, 'artifact validation missing or invalid')
            elif row['artifact'] is not None and row['artifact'] != event.artifact:
                self._fail(event.row_id, 'conflicting artifact receipt')
            else:
                row['artifact'] = event.artifact
        else:
            self._fail(event.row_id, 'unknown event kind')
        return True

    def status(self, row_id):
        row = self._rows[row_id]
        if row['errors']:
            return 'failed'
        if (row['attempted'] and set(row['stages']) == set(STAGES)
                and all(value == 0 for value in row['stages'].values()) and row['artifact'] is not None):
            return 'validated'
        return 'pending'

    def snapshot(self):
        groups = {name: [row for row in self.expected_ids if self.status(row) == name]
                  for name in ('validated', 'failed', 'pending')}
        return {'run_id': self.run_id, 'config_id': self.config_id,
                'expected': list(self.expected_ids),
                'attempted': [row for row in self.expected_ids if self._rows[row]['attempted']],
                **groups, 'issues': list(self.issues),
                'rows': {row: {'attempted': value['attempted'], 'status': self.status(row),
                    'stage_exits': dict(value['stages']), 'errors': list(value['errors']),
                    'artifact_sha256': value['artifact'].sha256 if value['artifact'] else None}
                    for row, value in self._rows.items()},
                'all_expected_validated': not self.issues and len(groups['validated']) == len(self.expected_ids),
                'artifact_checks_are_owner_assertions': True}

    def validated_rasters(self):
        if self.issues:
            raise ValueError('Unresolved registry-level issues block aggregation')
        return {row: self._rows[row]['artifact'].raster for row in self.expected_ids if self.status(row) == 'validated'}

def weighted_sum(weights, rasters, grid, partitions=None):
    """Exact integers, no normalization, overflow or floating-point conversion."""
    if not isinstance(grid, Grid):
        raise ValueError('Declared common grid required')
    if set(weights) != set(rasters):
        raise ValueError('Weights must bind exactly the supplied raster IDs')
    for weight in weights.values():
        _natural(weight)
    for raster in rasters.values():
        if not isinstance(raster, BooleanRaster) or raster.grid != grid:
            raise ValueError('Common grid/mask mismatch')
    groups = [tuple(rasters)] if partitions is None else [tuple(part) for part in partitions]
    flat = [row for group in groups for row in group]
    if len(flat) != len(set(flat)) or set(flat) != set(rasters):
        raise ValueError('Partitions must cover supplied IDs exactly once')
    totals = [0] * len(grid.mask)
    for group in groups:
        subtotal = [sum(weights[row] * int(rasters[row].cells[i]) for row in group) for i in range(len(totals))]
        totals = [a + b for a, b in zip(totals, subtotal)]
    return tuple(value if active else None for value, active in zip(totals, grid.mask))

def missing_envelope(registry, weights, partitions=None):
    if set(weights) != set(registry.expected_ids):
        raise ValueError('Weights must bind every expected ID exactly once')
    for weight in weights.values():
        _natural(weight)
    rasters = registry.validated_rasters()
    lower = weighted_sum({row: weights[row] for row in rasters}, rasters, registry.grid, partitions)
    missing = [row for row in registry.expected_ids if row not in rasters]
    mass = sum(weights[row] for row in missing)
    upper = tuple(None if value is None else value + mass for value in lower)
    return {'lower': lower, 'upper': upper, 'unvalidated_ids': tuple(missing), 'unvalidated_weight': mass}

def threshold_decisions(envelope, threshold, strict=False):
    if type(threshold) is not int and not isinstance(threshold, Fraction):
        raise ValueError('Use an exact integer or Fraction threshold')
    if type(strict) is not bool:
        raise ValueError('Strict comparison flag must be Boolean')
    if len(envelope['lower']) != len(envelope['upper']):
        raise ValueError('Envelope endpoints must have the same shape')
    result = []
    for low, high in zip(envelope['lower'], envelope['upper']):
        if low is None and high is None:
            result.append('MASKED')
        else:
            _natural(low)
            _natural(high)
            if low > high:
                raise ValueError('Envelope lower endpoint exceeds upper endpoint')
            if (low > threshold) if strict else (low >= threshold):
                result.append('YES')
            elif (high <= threshold) if strict else (high < threshold):
                result.append('NO')
            else:
                result.append('UNKNOWN')
    return tuple(result)
