"""Additive reliability adaptation of Sterling D. Quinn (2022), CC BY 4.0.
Modifications: Codex, 2026-10-16. Cooperative local use; see README.md.
"""
import argparse
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import uuid

import numpy as np
from osgeo import gdal, osr

gdal.UseExceptions()
MAX_AADT = 4294967292  # below the GDAL UInt32 calculator NoData sentinel


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def write_json(path, value):
    temp = path.with_name(path.name + '.tmp')
    with open(temp, 'x') as f:
        json.dump(value, f, indent=2, allow_nan=False)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    os.replace(temp, path)


def srs(text):
    s = osr.SpatialReference()
    s.SetFromUserInput(text)
    s.SetAxisMappingStrategy(osr.OAMS_TRADITIONAL_GIS_ORDER)
    return s


def blocks(ds):
    for y in range(0, ds.RasterYSize, 256):
        for x in range(0, ds.RasterXSize, 256):
            yield x, y, min(256, ds.RasterXSize-x), min(256, ds.RasterYSize-y)


def admit_dem(path, point_crs):
    ds = gdal.Open(str(path), gdal.GA_ReadOnly)
    if ds is None or ds.GetDriver().ShortName != 'GTiff' or ds.RasterCount != 1:
        raise ValueError('Require a single-band standalone GeoTIFF DEM')
    if {Path(p).resolve() for p in ds.GetFileList()} != {path.resolve()}:
        raise ValueError('DEM sidecars/external dependencies unsupported; flatten explicitly first')
    crs = srs(ds.GetProjection())
    if not crs.IsProjected() or not math.isclose(crs.GetLinearUnits(), 1.0):
        raise ValueError('Require projected metre CRS')
    if not crs.IsSame(srs(point_crs)):
        raise ValueError('CSV CRS must equal DEM CRS; no implicit reprojection')
    gt = ds.GetGeoTransform()
    if gt[2] != 0 or gt[4] != 0 or gt[1] <= 0 or gt[5] >= 0:
        raise ValueError('Require north-up, unrotated DEM')
    band = ds.GetRasterBand(1)
    if gdal.DataTypeIsComplex(band.DataType) or band.GetScale() not in (None, 1) or band.GetOffset() not in (None, 0):
        raise ValueError('Complex/scaled/offset DEM unsupported')
    if band.GetUnitType() not in ('', 'm', 'metre', 'meter'):
        raise ValueError('DEM elevation must be metres')
    for window in blocks(ds):
        a = band.ReadAsArray(*window)
        mask = band.GetMaskBand().ReadAsArray(*window)
        if not np.isfinite(a).all() or not (mask == 255).all():
            raise ValueError('DEM contains invalid/NoData cells; no implicit filling')
    return ds


def admit_csv(path, dem):
    result = []
    seen = set()
    gt = dem.GetGeoTransform()
    with open(path, newline='', encoding='utf-8-sig') as f:
        reader = csv.DictReader(f)
        fields = reader.fieldnames or []
        if len(fields) != len(set(fields)) or not {'X','Y','TARGET_FID','AADT'} <= set(fields):
            raise ValueError('Missing/duplicate CSV columns')
        for row in reader:
            if None in row or any(v is None for v in row.values()):
                raise ValueError('Malformed CSV row')
            ident = row['TARGET_FID']
            if not re.fullmatch(r'[A-Za-z0-9_-]{1,80}', ident) or ident in seen:
                raise ValueError('Unsafe or duplicate TARGET_FID')
            seen.add(ident)
            if not re.fullmatch(r'0|[1-9][0-9]{0,9}', row['AADT']):
                raise ValueError('AADT must be an exact nonnegative decimal integer')
            aadt = int(row['AADT'])
            if aadt > MAX_AADT:
                raise ValueError('AADT exceeds supported UInt32 non-NoData range')
            x, y = float(row['X']), float(row['Y'])
            if not math.isfinite(x) or not math.isfinite(y):
                raise ValueError('Nonfinite coordinates')
            col, line = (x-gt[0])/gt[1], (y-gt[3])/gt[5]
            if not (0 <= col < dem.RasterXSize and 0 <= line < dem.RasterYSize):
                raise ValueError('Observer outside DEM')
            # Ordinals are injective within the byte-bound CSV, independent of raw IDs.
            result.append(dict(id=ident, x=x, y=y, aadt=aadt,
                               storage_id=f'job-{len(result):08d}', row=dict(row)))
    if not result:
        raise ValueError('Empty CSV')
    return result


def validate(path, dem, dtype, reference=None, factor=1, compressed=False):
    ds = gdal.Open(str(path), gdal.GA_ReadOnly)
    if ds is None or ds.RasterCount != 1 or ds.GetDriver().ShortName != 'GTiff':
        raise ValueError('Invalid output raster')
    if (ds.RasterXSize, ds.RasterYSize) != (dem.RasterXSize, dem.RasterYSize):
        raise ValueError('Output dimensions changed')
    if ds.GetGeoTransform() != dem.GetGeoTransform() or not srs(ds.GetProjection()).IsSame(srs(dem.GetProjection())):
        raise ValueError('Output grid/CRS changed')
    band = ds.GetRasterBand(1)
    if band.DataType != dtype:
        raise ValueError('Unexpected output type')
    # Installed gdal_calc assigns UInt32 max minus two as NoData; no valid AADT may collide.
    if band.GetNoDataValue() not in (None, 4294967293):
        raise ValueError('Unexpected output NoData (zero must remain a valid invisible cell)')
    if compressed and ds.GetMetadata('IMAGE_STRUCTURE').get('COMPRESSION') != 'DEFLATE':
        raise ValueError('Missing DEFLATE compression')
    ref = gdal.Open(str(reference)) if reference else None
    for window in blocks(ds):
        a = band.ReadAsArray(*window)
        if not (band.GetMaskBand().ReadAsArray(*window) == 255).all():
            raise ValueError('Invalid output cells')
        if ref:
            expected = ref.GetRasterBand(1).ReadAsArray(*window).astype(np.uint64)*factor
            if not np.array_equal(a, expected):
                raise ValueError('Output pixels differ from exact expected values')
        elif not np.isin(a, [0, 1]).all():
            raise ValueError('Viewshed must be binary')
    ds = ref = None
    return digest(path)


def execute(argv, directory, label):
    write_json(directory / (label+'.command.json'), argv)
    with open(directory/(label+'.stdout.txt'), 'xb') as out, open(directory/(label+'.stderr.txt'), 'xb') as err:
        result = subprocess.run(argv, stdout=out, stderr=err, check=False, shell=False)
        out.flush(); err.flush()
        os.fsync(out.fileno()); os.fsync(err.fileno())
    write_json(directory/(label+'.exit.json'), {'returncode': result.returncode})
    if result.returncode:
        raise RuntimeError(f'{label} returned {result.returncode}')


def pipeline(job, directory, dem_path, dem, tools, curvature, executor=execute):
    raw, plain, weighted, final = [directory/n for n in ('raw.tif','visibility.tif','weighted.tif','traffic.tif')]
    stages = [
        ('viewshed', [tools['gdal_viewshed'], '-ox', str(job['x']), '-oy', str(job['y']), '-oz', '1', '-vv', '1', '-cc', curvature, str(dem_path), str(raw)], raw, gdal.GDT_Byte, None, 1, False),
        ('compress', [tools['gdal_translate'], '-ot','UInt32','-co','COMPRESS=DEFLATE','-co','PREDICTOR=2','-co','ZLEVEL=9',str(raw),str(plain)], plain, gdal.GDT_UInt32, raw, 1, True),
        ('weight', [tools['gdal_calc.py'], '-A',str(plain),'--calc=A*'+str(job['aadt']),'--outfile='+str(weighted),'--type=UInt32','--NoDataValue=4294967293'], weighted, gdal.GDT_UInt32, plain, job['aadt'], False),
        ('compress_weighted', [tools['gdal_translate'],'-co','COMPRESS=DEFLATE','-co','PREDICTOR=2','-co','ZLEVEL=9',str(weighted),str(final)], final, gdal.GDT_UInt32, weighted, 1, True)]
    hashes = {}
    for label, argv, path, dtype, ref, factor, compressed in stages:
        if path.exists():
            raise ValueError('Stage destination already exists')
        executor(argv, directory, label)
        hashes[path.name] = validate(path, dem, dtype, ref, factor, compressed)
        write_json(directory/(label+'.validated.json'), {'sha256': hashes[path.name]})
    return hashes


def run(csv_path, dem_path, run_path, point_crs, curvature, resume=False, retry=False, executor=execute):
    csv_path, dem_path, run_path = map(lambda p: Path(p).resolve(), (csv_path, dem_path, run_path))
    if curvature not in ('0.85714', '0.85417'):
        raise ValueError('Select original-code or paper curvature explicitly')
    tools = {n: shutil.which(n) for n in ('gdal_viewshed','gdal_translate','gdal_calc.py')}
    if not all(tools.values()):
        raise ValueError('Missing GDAL command tools')
    dem = admit_dem(dem_path, point_crs)
    jobs = admit_csv(csv_path, dem)
    identity = {'csv_sha256': digest(csv_path), 'dem_sha256': digest(dem_path), 'point_crs':point_crs,
                'curvature':curvature, 'runner_sha256':digest(__file__), 'gdal':gdal.VersionInfo(),
                'tools':{n: {'path':v,'sha256':digest(v)} for n,v in tools.items()}}
    if resume:
        if json.loads((run_path/'identity.json').read_text()) != identity:
            raise ValueError('Resume identity mismatch')
    else:
        run_path.mkdir(parents=True, exist_ok=False)
        write_json(run_path/'identity.json', identity)
    lock = run_path/'LOCK'
    lock.mkdir()  # cooperative exclusion; never auto-remove an existing lock
    summary = dict(attempted=0, succeeded=0, failed=0, skipped=0)
    invocation = 'invocation-'+uuid.uuid4().hex

    def checkpoint(status, error=None):
        snapshot = dict(summary, invocation=invocation, status=status)
        if error is not None:
            snapshot['error'] = {'type':type(error).__name__, 'message':str(error)}
        # Each invocation retains its own final record; summary is a latest pointer/copy.
        write_json(run_path/(invocation+'.json'), snapshot)
        write_json(run_path/'summary.json', snapshot)

    try:
        previous = run_path/'summary.json'
        if previous.exists():
            # Preserve even legacy/unversioned summary bytes before replacing the latest copy.
            with open(run_path/(invocation+'.previous-summary.json'), 'xb') as archive:
                archive.write(previous.read_bytes())
                archive.flush()
                os.fsync(archive.fileno())
        checkpoint('running')
        for job in jobs:
            jobdir = run_path/job['storage_id']
            success = jobdir/'success.json'
            if success.exists():
                record = json.loads(success.read_text())
                if record.get('job') != job:
                    raise ValueError('Success receipt job identity mismatch')
                attempt = jobdir/record['attempt']
                if not re.fullmatch(r'attempt-[0-9a-f]{32}',record['attempt']):
                    raise ValueError('Invalid receipt path')
                if json.loads((attempt/'job.json').read_text()) != job:
                    raise ValueError('Saved attempt job identity mismatch')
                for name, sha in record['hashes'].items():
                    if name not in ('raw.tif','visibility.tif','weighted.tif','traffic.tif') or digest(attempt/name) != sha:
                        raise ValueError('Completed output changed; refusing overwrite')
                if set(record['hashes']) != {'raw.tif','visibility.tif','weighted.tif','traffic.tif'}:
                    raise ValueError('Incomplete receipt')
                validate(attempt/'visibility.tif', dem, gdal.GDT_UInt32, compressed=True)
                validate(attempt/'traffic.tif', dem, gdal.GDT_UInt32, attempt/'visibility.tif', job['aadt'], True)
                summary['skipped'] += 1
                continue
            if jobdir.exists() and not retry:
                raise ValueError('Prior incomplete/failed attempt; explicit --retry-failed required')
            jobdir.mkdir(exist_ok=True)
            attempt = jobdir/('attempt-'+uuid.uuid4().hex)
            attempt.mkdir()
            summary['attempted'] += 1
            write_json(attempt/'job.json', job)
            try:
                if digest(dem_path) != identity['dem_sha256'] or digest(csv_path) != identity['csv_sha256']:
                    raise ValueError('Input changed during run')
                hashes = pipeline(job, attempt, dem_path, dem, tools, curvature, executor)
                if digest(dem_path) != identity['dem_sha256'] or digest(csv_path) != identity['csv_sha256']:
                    raise ValueError('Input changed during run')
                write_json(success, {'attempt':attempt.name,'hashes':hashes,'job':job})
                summary['succeeded'] += 1
            except Exception as e:
                write_json(attempt/'failure.json', {'error':str(e),'type':type(e).__name__})
                summary['failed'] += 1
            checkpoint('running')
        checkpoint('completed_with_failures' if summary['failed'] else 'completed')
        return summary
    except BaseException as e:
        checkpoint('interrupted' if isinstance(e, (KeyboardInterrupt, SystemExit)) else 'refused', e)
        raise
    finally:
        lock.rmdir()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--csv', required=True); p.add_argument('--dem', required=True)
    p.add_argument('--run', required=True); p.add_argument('--point-crs', required=True)
    p.add_argument('--curvature', required=True, choices=['0.85714','0.85417'])
    p.add_argument('--elevation-metres', action='store_true', required=True, help='Explicitly attest DEM heights are metres')
    p.add_argument('--resume', action='store_true'); p.add_argument('--retry-failed', action='store_true')
    a=p.parse_args()
    try:
        result=run(a.csv,a.dem,a.run,a.point_crs,a.curvature,a.resume,a.retry_failed)
        print(json.dumps(result)); return 1 if result['failed'] else 0
    except Exception as e:
        print(str(e),file=sys.stderr); return 2

if __name__ == '__main__':
    sys.exit(main())
