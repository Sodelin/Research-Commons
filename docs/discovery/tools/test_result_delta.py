"""Exercise real Git/body/query behavior without changing canonical cards."""
import gzip,hashlib,json,pathlib,runpy,subprocess,tempfile,unittest
HERE=pathlib.Path(__file__).resolve().parent
ENGINE=runpy.run_path(str(HERE/'index-research-results.py'))
class Delta(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.root=pathlib.Path(self.temp.name);self.repo=self.root/'repo';self.repo.mkdir();self.git('init','-q');self.git('remote','add','origin','https://github.com/Sodelin/Research-Commons.git');(self.repo/'research').mkdir();(self.repo/'docs').mkdir();(self.repo/'docs/claims.json').write_text('{"claims":[]}\n');self.card=(self.repo/'docs/claims.json').read_bytes()
 def git(self,*args):return subprocess.check_output(['git','-C',str(self.repo),*args],stderr=subprocess.STDOUT)
 def commit(self):
  self.git('add','.');self.git('-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-qm','fixture');return self.git('rev-parse','HEAD').decode().strip()
 def query(self,index,word,path):
  p=subprocess.check_output(['node',str(HERE/'query.mjs'),'--research-results',str(index/'manifest.json'),'--query',word,'--research-path',path,'--limit','10']);return json.loads(p)
 def test_changed_removed_and_shared_body_aliases(self):
  for name in ['a.md','b.md']:(self.repo/'research'/name).write_text('olduniqueneedle\n')
  (self.repo/'research/c.md').write_text('keptuniqueneedle\n');old=self.commit();base=self.root/'base';ENGINE['build'](self.repo,old,base);before={p.name:p.read_bytes() for p in base.glob('*.gz')};manifest=(base/'manifest.json').read_bytes()
  (self.repo/'research/a.md').write_text('newuniqueneedle\n');(self.repo/'research/b.md').unlink();new=self.commit();out=self.root/'current';ENGINE['build'](self.repo,new,out,base);ENGINE['check'](self.repo,out,new)
  q=self.query(out,'newuniqueneedle','research/a.md');hit=q['results'][0];self.assertEqual(hit['sha256'],hashlib.sha256(b'newuniqueneedle\n').hexdigest());self.assertEqual(self.query(out,'olduniqueneedle','research/')['total'],0);self.assertEqual((self.repo/'docs/claims.json').read_bytes(),self.card);self.assertEqual((base/'manifest.json').read_bytes(),manifest)
  for name,data in before.items():self.assertEqual((base/name).read_bytes(),data)
  self.assertEqual(ENGINE['read_manifest'](out)['incremental_delta'],{'added_paths':0,'changed_paths':1,'removed_paths':1})
 def test_source_only_addition_with_archived_base_manifest(self):
  (self.repo/'research/old.md').write_text('existing proof body\n');old=self.commit();base=self.root/'base';ENGINE['build'](self.repo,old,base);original=(base/'manifest.json').read_bytes();(base/'manifest.json.gz').write_bytes(gzip.compress(original,mtime=0));(base/'manifest.json').unlink()
  (self.repo/'research/new.lean').write_text('-- newsourceidentifier\nexample : True := True.intro\n');new=self.commit();out=self.root/'current';ENGINE['build'](self.repo,new,out,base);ENGINE['check'](self.repo,out,new);q=self.query(out,'newsourceidentifier','research/new.lean');self.assertEqual(q['results'][0]['git_blob'],self.git('rev-parse',new+':research/new.lean').decode().strip());self.assertEqual((self.repo/'docs/claims.json').read_bytes(),self.card);self.assertEqual(gzip.decompress((base/'manifest.json.gz').read_bytes()),original)
if __name__=='__main__':unittest.main()
