"""Quinn CC BY 4.0 source, executed through an explicitly intercepted I/O adapter.
Harness by Codex, 2026-10-16. No Windows shell execution or historical-run claim.
"""
import argparse
import builtins
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch

import numpy as np
from osgeo import gdal, osr

PACKAGE=Path(__file__).resolve().parent.parent/'2026-10-16-quinn-reliable-runner'
sys.path.insert(0,str(PACKAGE))
import runner
ORIGINAL=PACKAGE/'original/quinn.py'
ORIGINAL_HASH='7aee3ae34ee0f4fd9e6c686dde0813f0a9e29291ff0b33d2c6022d893c42ecff'
STAGES=['viewshed','compress','weight','compress_weighted']


def snapshot(path):
    if not path.exists():return {'exists':False}
    ds=gdal.Open(str(path));b=ds.GetRasterBand(1);a=b.ReadAsArray()
    return {'exists':True,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'shape':list(a.shape),
            'type':gdal.GetDataTypeName(b.DataType),'nodata':b.GetNoDataValue(),
            'geotransform':list(ds.GetGeoTransform()),'crs':ds.GetProjection(),
            'compression':ds.GetMetadata('IMAGE_STRUCTURE').get('COMPRESSION'),
            'pixels':a.tolist(),'pixel_sha256':hashlib.sha256(a.tobytes()).hexdigest()}


def fixture(root, terrain):
    dem=root/'dem.tif';csv=root/'points.csv'
    ds=gdal.GetDriverByName('GTiff').Create(str(dem),9,9,1,gdal.GDT_Float32)
    sr=osr.SpatialReference();sr.ImportFromEPSG(26910)
    ds.SetProjection(sr.ExportToWkt());ds.SetGeoTransform((500000,30,0,5200000,0,-30))
    a=np.zeros((9,9),dtype=np.float32)
    if terrain=='ridge':a[:,5]=80
    ds.GetRasterBand(1).WriteArray(a);ds=None
    csv.write_text('X,Y,TARGET_FID,AADT\n500075,5199925,p1,123\n')
    return dem,csv


def original_adapted(root, dem, csv, failure=None, stale=None):
    """Compile/exec exact source bytes; replace only three I/O entrypoints.
    All original assignments/loop/try/finally/control flow and coefficient stay intact.
    """
    root.mkdir();source=ORIGINAL.read_bytes()
    assert len(source)==3705 and hashlib.sha256(source).hexdigest()==ORIGINAL_HASH
    namespace={};events=[];removed=[];commands=[]
    paths={key:root/name for key,name in [
        ('outViewshed','vizUncompressedp1.tif'),('outViewshedUInt','vizp1.tif'),
        ('outWeightedViewshed','vizaadtUncompressedp1.tif'),('outCompressedWeightedViewshed','vizaadtp1.tif')]}
    if stale:shutil.copyfile(stale,paths['outViewshedUInt'])
    real_open=builtins.open;real_remove=os.remove

    def open_csv(path,*args,**kwargs):
        if path!=namespace.get('csvPath'):raise RuntimeError('Unmapped original open refused')
        return real_open(csv,*args,**kwargs)

    def remove_intermediate(path):
        keys=[k for k in ('outViewshed','outWeightedViewshed') if namespace.get(k)==path]
        if len(keys)!=1:raise RuntimeError('Unmapped original deletion refused')
        local=paths[keys[0]]
        assert local.parent==root and local.resolve().is_relative_to(root.resolve())
        removed.append({'original_path':path,'mapped_name':local.name,'before_delete':snapshot(local)})
        real_remove(local)

    def system_adapter(command):
        g=namespace
        candidates=[('viewshed','viewshedCmd'),('compress','translateCmd'),
                    ('weight','calcCmd'),('compress_weighted','translateWeightedCmd')]
        matches=[stage for stage,key in candidates if g.get(key)==command]
        if len(matches)!=1:raise RuntimeError('Unrecognized original command')
        stage=matches[0]
        # Exact original numerical flags and types; only executable/path transport changes.
        raw,plain,weighted,final=[str(paths[k]) for k in paths]
        argv={
            'viewshed':[shutil.which('gdal_viewshed'),'-ox',g['xCoord'],'-oy',g['yCoord'],'-oz','1','-vv','1','-cc','0.85714',str(dem),raw],
            'compress':[shutil.which('gdal_translate'),'-ot','UInt32','-co','COMPRESS=DEFLATE','-co','PREDICTOR=2','-co','ZLEVEL=9',raw,plain],
            'weight':[shutil.which('gdal_calc.py'),'-A',plain,'--calc=(A)*'+g['aadt'],'--outfile',weighted],
            'compress_weighted':[shutil.which('gdal_translate'),'-co','COMPRESS=DEFLATE','-co','PREDICTOR=2','-co','ZLEVEL=9',weighted,final]}[stage]
        executed=['/usr/bin/false'] if failure==stage else argv
        proc=subprocess.run(executed,capture_output=True,text=True,shell=False)
        # POSIX os.system status encoding; only zero/nonzero is relevant (original ignores both).
        status=proc.returncode<<8
        commands.append({'stage':stage,'original_command':command,'translated_argv':argv,
                         'executed_argv':executed,'returncode':proc.returncode,'returned_os_system_status':status,
                         'stdout':proc.stdout,'stderr':proc.stderr})
        events.append({'stage':stage,'outputs_after_stage':{k:snapshot(v) for k,v in paths.items()}})
        return status

    output=io.StringIO()
    with patch('builtins.open',open_csv),patch('os.system',system_adapter),patch('os.remove',remove_intermediate),contextlib.redirect_stdout(output):
        exec(compile(source,str(ORIGINAL),'exec'),namespace)
    return {'execution':'exact original Python source bytes with intercepted I/O; no original shell execution',
            'itemsProcessed':namespace['itemsProcessed'],'printed':output.getvalue(),
            'commands':commands,'stages':events,'deletions':removed,
            'final_outputs':{k:snapshot(v) for k,v in paths.items()}}


def repaired(root,dem,csv,failure=None,stale=None,curvature='0.85714'):
    def execute(argv,directory,label):
        if failure==label:
            if stale:shutil.copyfile(stale,directory.parent/'unaccepted-stale-visibility.tif')
            return runner.execute(['/usr/bin/false'],directory,label)
        return runner.execute(argv,directory,label)
    counts=runner.run(csv,dem,root,'EPSG:26910',curvature,executor=execute)
    jobdir=root/'job-00000000';attempt=next(jobdir.glob('attempt-*'))
    return {'counts':counts,'summary':json.loads((root/'summary.json').read_text()),
            'accepted':(jobdir/'success.json').exists(),
            'failure':json.loads((attempt/'failure.json').read_text()) if (attempt/'failure.json').exists() else None,
            'outputs':{n:snapshot(attempt/n) for n in ['raw.tif','visibility.tif','weighted.tif','traffic.tif']},
            'stage_logs':{p.name:p.read_text() for p in attempt.iterdir() if p.suffix in ('.json','.txt')}}


def compare(output):
    output.mkdir(parents=True,exist_ok=False)
    cases=[]
    with tempfile.TemporaryDirectory(prefix='quinn-isolated-comparison-') as tmp:
        root=Path(tmp)
        for terrain in ['flat','ridge']:
            base=root/terrain;base.mkdir();dem,csv=fixture(base,terrain)
            seed=base/'seed.tif'
            ds=gdal.GetDriverByName('GTiff').CreateCopy(str(seed),gdal.Open(str(dem)))
            ds.GetRasterBand(1).Fill(0);ds=None
            # Deliberately obsolete but structurally plausible all-invisible UInt32 visibility.
            stale=base/'stale.tif'
            subprocess.run([shutil.which('gdal_translate'),'-ot','UInt32',str(seed),str(stale)],check=True,capture_output=True)
            baseline=None
            for label,failure,old in [('success',None,None)]+[(x,x,None) for x in STAGES]+[('stale_after_compress_failure','compress',stale)]:
                old_result=original_adapted(base/('old-'+label),dem,csv,failure,old)
                new_result=repaired(base/('new-'+label),dem,csv,failure,old)
                case={'terrain':terrain,'case':label,'curvature':'0.85714','dem':snapshot(dem),'csv_sha256':runner.digest(csv),
                      'original':old_result,'repaired':new_result}
                assert old_result['itemsProcessed']==1
                if failure is None:
                    a=old_result['final_outputs']['outCompressedWeightedViewshed'];b=new_result['outputs']['traffic.tif']
                    for key in ['pixels','type','shape','geotransform','crs','nodata','compression']:assert a[key]==b[key],key
                    a=old_result['final_outputs']['outViewshedUInt'];b=new_result['outputs']['visibility.tif']
                    for key in ['pixels','type','shape','geotransform','crs','nodata','compression']:assert a[key]==b[key],key
                    assert new_result['counts']==dict(attempted=1,succeeded=1,failed=0,skipped=0)
                    baseline=new_result['outputs']['traffic.tif']['pixels']
                    case['comparison']='successful raster values and checked metadata equal; TIFF bytes not required equal'
                else:
                    assert new_result['counts']==dict(attempted=1,succeeded=0,failed=1,skipped=0)
                    assert not new_result['accepted']
                    if failure!='viewshed':assert new_result['outputs']['raw.tif']['exists']
                    if failure=='compress_weighted':
                        assert not old_result['final_outputs']['outWeightedViewshed']['exists']
                        assert new_result['outputs']['weighted.tif']['exists']
                        assert 'Error processing' not in old_result['printed']
                    if old:
                        a=old_result['final_outputs']['outCompressedWeightedViewshed']
                        assert a['exists'] and a['pixels']!=baseline
                        case['comparison']='original emitted stale-derived weighted raster different from successful baseline; repair refused acceptance'
                    else:case['comparison']='original counted attempt as processed; repair recorded failure and retained available intermediates'
                cases.append(case)
            paper=repaired(base/'paper-coefficient',dem,csv,curvature='0.85417')
            assert paper['accepted']
            cases.append({'terrain':terrain,'case':'paper_curvature_repair_only','curvature':'0.85417',
                          'original_executed_for_this_case':False,'repaired':paper,
                          'pixels_equal_code_coefficient_fixture':paper['outputs']['traffic.tif']['pixels']==baseline})
    report={'original_sha256':runner.digest(ORIGINAL),'runner_sha256':runner.digest(PACKAGE/'runner.py'),
            'harness_sha256':runner.digest(__file__),'gdal':gdal.VersionInfo('--version'),'cases':cases,
            'assertions':'passed','historical_failure_claim':False,'original_windows_shell_executed':False}
    (output/'RESULTS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'cases':len(cases),'assertions':'passed','gdal':report['gdal']}))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True)
    compare(parser.parse_args().output)
