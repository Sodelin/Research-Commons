import hashlib,json,pathlib,tempfile,unittest
from unittest.mock import patch
import summarize_fixed as s
class ScalarTests(unittest.TestCase):
    def fixture(self,p):
        folder=p/'fake';folder.mkdir()
        data='Gen theta:1:K theta:2:C theta:3:L theta:4:H tau:5:K,C,L,H lnL\n'
        for i in range(1,5):data+=f'{2*i} .001 .002 .003 .004 {0.001+i*.0001} {-100-i}\n'
        (folder/'result.mcmc.txt').write_text(data)
        result='param mean median S.D min max 2.5% 97.5% 2.5%HPD 97.5%HPD ESS* Eff* rho1\n'
        for label,mean in [('theta:1',.001),('theta:2',.002),('theta:3',.003),('theta:4',.004),('tau:5',.00125),('lnL',-102.5)]:
            result+=label+' '+str(mean)+' 0 0 0 0 0 0 0 0 4 1 0\n'
        result+='List of nodes, taus and thetas:\n'
        (folder/'result.txt').write_text(result)
        (folder/'TERMINAL.json').write_text(json.dumps({'status':'EXECUTION_EXIT_ZERO','inputs_stable':True,'settings':{'nsample':4,'sampfreq':2},'conditional_topology':'(((H,L),C),K);','output_inventory':[{'path':'result.mcmc.txt','sha256':hashlib.sha256(data.encode()).hexdigest()},{'path':'result.txt','sha256':hashlib.sha256(result.encode()).hexdigest()}]}))
        return folder
    def test_identity_and_header(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d);self.fixture(p)
            with patch.object(s,'RUNS',p):r=s.summarize('fake')
            self.assertEqual(set(r['columns']),{'root_tau','theta_K','theta_C','theta_L','theta_H','lnL'});self.assertAlmostEqual(r['columns']['root_tau']['mean'],.00125)
            self.assertIsNone(r['columns']['theta_K']['ess'])
    def test_changed_trace_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d);f=self.fixture(p);(f/'result.mcmc.txt').write_text('changed')
            with patch.object(s,'RUNS',p):
                with self.assertRaises(ValueError):s.summarize('fake')
    def test_changed_vendor_mean_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d);f=self.fixture(p);text=(f/'result.txt').read_text().replace('tau:5 0.00125','tau:5 0.00999');(f/'result.txt').write_text(text)
            t=json.loads((f/'TERMINAL.json').read_text());t['output_inventory'][1]['sha256']=hashlib.sha256(text.encode()).hexdigest();(f/'TERMINAL.json').write_text(json.dumps(t))
            with patch.object(s,'RUNS',p):
                with self.assertRaisesRegex(ValueError,'mean discrepancy'):s.summarize('fake')
    def test_duplicate_root_label_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d);f=self.fixture(p);text=(f/'result.mcmc.txt').read_text().replace('tau:5:K,C,L,H','tau:5:K,C,L,H,H');(f/'result.mcmc.txt').write_text(text)
            t=json.loads((f/'TERMINAL.json').read_text());t['output_inventory'][0]['sha256']=hashlib.sha256(text.encode()).hexdigest();(f/'TERMINAL.json').write_text(json.dumps(t))
            with patch.object(s,'RUNS',p):
                with self.assertRaisesRegex(ValueError,'duplicate root'):s.summarize('fake')
if __name__=='__main__':unittest.main()
