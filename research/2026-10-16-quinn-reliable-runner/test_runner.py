import json
from pathlib import Path
import tempfile
import unittest
import numpy as np
from osgeo import gdal, osr
import runner as r

class RepairTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.root=Path(self.tmp.name)
        self.dem=self.root/'terrain with spaces.tif'; self.csv=self.root/'points.csv'
        ds=gdal.GetDriverByName('GTiff').Create(str(self.dem),9,9,1,gdal.GDT_Float32)
        s=osr.SpatialReference();s.ImportFromEPSG(26910)
        ds.SetProjection(s.ExportToWkt());ds.SetGeoTransform((500000,30,0,5200000,0,-30))
        a=np.zeros((9,9),dtype=np.float32);a[:,5]=80
        ds.GetRasterBand(1).WriteArray(a);ds=None
        self.csv.write_text('X,Y,TARGET_FID,AADT\n500075,5199925,p1,123\n')
    def tearDown(self):self.tmp.cleanup()
    def run_job(self,name='run',**kwargs):
        return r.run(self.csv,self.dem,self.root/name,'EPSG:26910','0.85714',**kwargs)
    def test_real_smoke_and_resume(self):
        result=self.run_job();self.assertEqual(result,dict(attempted=1,succeeded=1,failed=0,skipped=0))
        receipt=json.loads((self.root/'run/p1/success.json').read_text())
        attempt=self.root/'run/p1'/receipt['attempt']
        a=gdal.Open(str(attempt/'visibility.tif')).ReadAsArray()
        b=gdal.Open(str(attempt/'traffic.tif')).ReadAsArray()
        self.assertEqual(set(np.unique(a)),{0,1});self.assertTrue(np.array_equal(b,a.astype(np.uint64)*123))
        self.assertEqual(len(list(attempt.glob('*.validated.json'))),4)
        self.assertEqual(self.run_job(resume=True)['skipped'],1)
        with self.assertRaises(FileExistsError):self.run_job()
    def test_each_external_failure_retains_evidence_and_stops(self):
        for index,label in enumerate(['viewshed','compress','weight','compress_weighted']):
            calls=[]
            def fail(argv,directory,stage):
                calls.append(stage)
                if stage==label:
                    # An actual failing process, still through the repaired logger.
                    return r.execute(['/bin/sh','-c','exit 7'],directory,stage)
                return r.execute(argv,directory,stage)
            name='fail'+str(index);result=self.run_job(name,executor=fail)
            self.assertEqual(result['failed'],1);self.assertEqual(result['succeeded'],0)
            self.assertEqual(len(calls),index+1)
            attempt=next((self.root/name/'p1').glob('attempt-*'))
            self.assertTrue((attempt/'failure.json').exists())
            if index:self.assertTrue((attempt/'raw.tif').exists())
            if index==3:self.assertTrue((attempt/'weighted.tif').exists())
            self.assertFalse((self.root/name/'p1/success.json').exists())
            with self.assertRaises(ValueError):self.run_job(name,resume=True)
            self.assertEqual(self.run_job(name,resume=True,retry=True)['succeeded'],1)
            self.assertEqual(len(list((self.root/name/'p1').glob('attempt-*'))),2)
    def test_success_exit_missing_or_corrupt_output_rejected(self):
        for mode in ['missing','corrupt']:
            def fake(argv,directory,label):
                if mode=='corrupt':(directory/'raw.tif').write_bytes(b'not a raster')
            result=self.run_job(mode,executor=fake)
            self.assertEqual(result['failed'],1)
    def test_stale_attempt_never_accepted(self):
        def fail(argv,directory,label):raise RuntimeError('interrupted')
        self.run_job(executor=fail)
        old=next((self.root/'run/p1').glob('attempt-*'));(old/'traffic.tif').write_bytes(b'stale')
        self.assertEqual(self.run_job(resume=True,retry=True)['succeeded'],1)
        self.assertEqual((old/'traffic.tif').read_bytes(),b'stale')
    def test_modified_completed_output_refuses_overwrite(self):
        self.run_job();receipt=json.loads((self.root/'run/p1/success.json').read_text())
        f=self.root/'run/p1'/receipt['attempt']/'traffic.tif';f.write_bytes(b'changed')
        with self.assertRaises(ValueError):self.run_job(resume=True)
        self.assertEqual(f.read_bytes(),b'changed')
    def test_csv_admission(self):
        bad=['X,Y,TARGET_FID,AADT\n500075,5199925,p,1.5\n',
             'X,Y,TARGET_FID,AADT\nNaN,5199925,p,1\n',
             'X,Y,TARGET_FID,AADT\n0,0,p,1\n',
             'X,Y,TARGET_FID,AADT\n500075,5199925,../bad,1\n',
             'X,Y,TARGET_FID,AADT\n500075,5199925,p,4294967295\n',
             'X,Y,TARGET_FID,AADT\n500075,5199925,p,-1\n',
             'X,Y,TARGET_FID,AADT\n500075,5199925,p,1\n500075,5199925,p,2\n',
             'X,Y,TARGET_FID,AADT,X\n1,2,p,1,1\n']
        for data in bad:
            self.csv.write_text(data)
            with self.assertRaises(ValueError):self.run_job()
    def test_identity_and_crs(self):
        self.run_job();self.csv.write_text(self.csv.read_text().replace('123','124'))
        with self.assertRaises(ValueError):self.run_job(resume=True)
        with self.assertRaises(ValueError):r.admit_dem(self.dem,'EPSG:4326')
    def test_nodata(self):
        ds=gdal.Open(str(self.dem),gdal.GA_Update);ds.GetRasterBand(1).SetNoDataValue(0);ds=None
        with self.assertRaises(ValueError):self.run_job()
    def test_lock_excludes_concurrent_resume(self):
        self.run_job();(self.root/'run/LOCK').mkdir()
        with self.assertRaises(FileExistsError):self.run_job(resume=True)
    def test_output_contract_rejects_type_grid_and_pixel_changes(self):
        dem=r.admit_dem(self.dem,'EPSG:26910')
        for kind in ['type','grid','pixels','dimensions']:
            f=self.root/(kind+'.tif');ds=gdal.GetDriverByName('GTiff').Create(str(f),8 if kind=='dimensions' else 9,9,1,gdal.GDT_UInt16 if kind=='type' else gdal.GDT_Byte)
            ds.SetProjection(dem.GetProjection());gt=list(dem.GetGeoTransform());gt[0]+=30 if kind=='grid' else 0;ds.SetGeoTransform(gt)
            ds.GetRasterBand(1).Fill(2 if kind=='pixels' else 1);ds=None
            with self.assertRaises(ValueError):r.validate(f,dem,gdal.GDT_Byte)
    def test_interrupted_attempt_requires_explicit_retry(self):
        def interrupt(argv,directory,label):raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt):self.run_job(executor=interrupt)
        self.assertFalse((self.root/'run/p1/success.json').exists())
        with self.assertRaises(ValueError):self.run_job(resume=True)
        self.assertEqual(self.run_job(resume=True,retry=True)['succeeded'],1)
    def test_wrong_weight_rejected_before_final_compression(self):
        calls=[]
        def corrupt(argv,directory,label):
            calls.append(label);r.execute(argv,directory,label)
            if label=='weight':
                ds=gdal.Open(str(directory/'weighted.tif'),gdal.GA_Update)
                ds.GetRasterBand(1).Fill(99);ds=None
        self.assertEqual(self.run_job(executor=corrupt)['failed'],1)
        self.assertNotIn('compress_weighted',calls)
    def test_reserved_id_and_nonfinite_dem(self):
        self.csv.write_text(self.csv.read_text().replace('p1','LOCK'))
        with self.assertRaises(ValueError):self.run_job()
        ds=gdal.Open(str(self.dem),gdal.GA_Update);ds.GetRasterBand(1).Fill(float('nan'));ds=None
        with self.assertRaises(ValueError):r.admit_dem(self.dem,'EPSG:26910')
    def test_zero_and_max_aadt(self):
        for aadt in [0,r.MAX_AADT]:
            self.csv.write_text(f'X,Y,TARGET_FID,AADT\n500075,5199925,p1,{aadt}\n')
            self.assertEqual(self.run_job('aadt'+str(aadt))['succeeded'],1)

if __name__=='__main__':unittest.main(verbosity=2)
