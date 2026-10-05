import copy,unittest
from unittest.mock import patch
import check_recovery_identity as c
class IdentityTests(unittest.TestCase):
    def fixtures(self):
        inputs={k:k for k in ['binary','watchdog','projector','admission','control','alignment','map']}
        a={'status':'RESOURCE_TIME_LIMIT','inputs_stable':True,'settings':{'seed':21101},'command':['bpp'],'address_space_limit_bytes':2147483648,'aggregate_attempt_limit_bytes':268435456,'threads':1,'conditional_topology':'tree','input_hashes_before':inputs,'wall_limit_seconds':600}
        b=copy.deepcopy(a);b.update(status='EXECUTION_EXIT_ZERO',wall_limit_seconds=1800)
        data={'result.mcmc.txt':b'header\nrow\npartial',**{f'result.gtree.L{i}':b'tree\npartial' for i in range(1,6)}}
        out={k:v[:v.rfind(b'\n')+1]+b'another complete row\n' for k,v in data.items()}
        return a,b,data,out
    def test_complete_prefix(self):
        a,b,data,out=self.fixtures()
        with patch.object(c,'authenticated',side_effect=[(a,c.ORIGINAL_TERMINAL_SHA,data),(b,'new',out)]):r=c.main()
        self.assertTrue(all(x['matches_recovery_byte_prefix'] for x in r['prefix_comparisons'].values()))
        self.assertFalse(r['different_independent_chain_claimed'])
    def test_target_change_rejected(self):
        a,b,data,out=self.fixtures();b['input_hashes_before']['alignment']='changed'
        with patch.object(c,'authenticated',side_effect=[(a,c.ORIGINAL_TERMINAL_SHA,data),(b,'new',out)]):
            with self.assertRaisesRegex(ValueError,'input difference'):c.main()
    def test_incomplete_recovery_rejected(self):
        a,b,data,out=self.fixtures();b['status']='RESOURCE_TIME_LIMIT'
        with patch.object(c,'authenticated',side_effect=[(a,c.ORIGINAL_TERMINAL_SHA,data),(b,'new',out)]):
            with self.assertRaisesRegex(ValueError,'complete stable'):c.main()
if __name__=='__main__':unittest.main()
