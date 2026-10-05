import copy,json,unittest,tempfile,hashlib
from pathlib import Path
from unittest.mock import patch
import project_fixture as p
class ProjectionTests(unittest.TestCase):
    def fixture(self):
        labels=[pop+'^'+pop.lower()+str(i) for pop,n in p.COUNTS.items() for i in range(1,n+1)]
        full=('32 489\n'+'\n'.join(label+'  '+'A'*489 for label in labels)+'\n\n')*5
        mapping='\n'.join(label.split('^')[1]+' '+label.split('^')[0] for label in labels)+'\n'
        layout=json.loads(p.LAYOUT.read_text());return full.encode(),mapping.encode(),layout
    def test_exact_crop_and_mask_only(self):
        data,mapping,layout=self.fixture();out,outmap,report=p.project_data(data,mapping,layout)
        self.assertEqual(outmap,mapping);self.assertEqual(sum(x['question_marks'] for x in report),7)
        for (_,rows),mask in zip(p.parse_alignments(out),layout['loci']):
            self.assertEqual([a for a,_ in rows],[r['synthetic_label'] for r in mask['rows']])
            for (label,seq),rule in zip(rows,mask['rows']):
                self.assertEqual([i for i,c in enumerate(seq,1) if c=='?'],rule['question_mark_sites_1based'])
                self.assertTrue(set(seq)<=set('A?'))
    def test_bad_mask_index(self):
        a,b,l=self.fixture();l['loci'][4]['rows'][0]['question_mark_sites_1based']=[0]
        with self.assertRaises(ValueError):p.project_data(a,b,l)
    def test_wrong_simulated_alphabet(self):
        a,b,l=self.fixture();a=a.replace(b'AAAA',b'AANA',1)
        with self.assertRaises(ValueError):p.project_data(a,b,l)
    def test_duplicate_row(self):
        a,b,l=self.fixture();l['loci'][0]['rows'][1]=copy.deepcopy(l['loci'][0]['rows'][0])
        with self.assertRaises(ValueError):p.project_data(a,b,l)
    def test_wrong_map(self):
        a,b,l=self.fixture();b=b.replace(b'k1 K',b'k1 C')
        with self.assertRaises(ValueError):p.project_data(a,b,l)
    def setup_stage(self,base):
        data,mapping,layout=self.fixture();sim=base/'simulation';sim.mkdir()
        (sim/'full-synthetic.txt').write_bytes(data);(sim/'full-synthetic.Imap.txt').write_bytes(mapping)
        receipt={'status':'EXECUTION_EXIT_ZERO','inputs_stable':True,'settings':{'seed':21001},'output_inventory':[{'path':name,'sha256':hashlib.sha256(value).hexdigest()} for name,value in [('full-synthetic.txt',data),('full-synthetic.Imap.txt',mapping)]]}
        (sim/'TERMINAL.json').write_text(json.dumps(receipt));return sim
    def test_immutable_projection_stage(self):
        with tempfile.TemporaryDirectory() as d:
            base=Path(d);sim=self.setup_stage(base);out=base/'projection';r=p.project(sim,out);before=(out/'matched-synthetic.txt').read_bytes()
            self.assertEqual(r['status'],'PROJECTED_AND_VALIDATED')
            with self.assertRaises(FileExistsError):p.project(sim,out)
            self.assertEqual((out/'matched-synthetic.txt').read_bytes(),before)
    def test_input_hash_mismatch(self):
        with tempfile.TemporaryDirectory() as d:
            base=Path(d);sim=self.setup_stage(base);(sim/'full-synthetic.txt').write_text('tampered')
            with self.assertRaisesRegex(ValueError,'output changed'):p.project(sim,base/'projection')
    def test_partial_failure_kept(self):
        with tempfile.TemporaryDirectory() as d:
            base=Path(d);sim=self.setup_stage(base);out=base/'projection';original=Path.write_bytes
            def writing(path,data):
                if path.name=='matched-synthetic.Imap.txt':raise OSError('injected small write failure')
                return original(path,data)
            with patch.object(Path,'write_bytes',writing):
                with self.assertRaises(OSError):p.project(sim,out)
            self.assertTrue((out/'matched-synthetic.txt').exists());self.assertTrue((out/'PROJECTION-FAILURE.json').exists());self.assertFalse((out/'PROJECTION.json').exists())
if __name__=='__main__':unittest.main()
