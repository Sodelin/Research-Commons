import collections,pathlib,tempfile,unittest
from unittest.mock import patch
import compare_genealogies as c
A='A^a';B='B^b';EXPECTED={A+'.1',A+'.2',B+'.1',B+'.2'};MAP={'a':'K','b':'C'}
T='((A^a.1:0.1,B^b.1:0.1):0.1,(A^a.2:0.1,B^b.2:0.1):0.1):0.0; [TH=0.2, TL=0.6]'
SWAP='((A^a.2:0.1,B^b.1:0.1):0.1,(A^a.1:0.1,B^b.2:0.1):0.1):0.0; [TH=0.2, TL=0.6]'
PAIR='((A^a.1:0.1,A^a.2:0.1):0.1,(B^b.1:0.1,B^b.2:0.1):0.1):0.0; [TH=0.2, TL=0.6]'
def colors():return {x:(x.rsplit('.',1)[0],MAP[x.rsplit('.',1)[0].split('^')[1]]) for x in EXPECTED}
class GenealogyTests(unittest.TestCase):
    def test_within_individual_swap_invariant(self):
        a=c.Parser(T).parse();b=c.Parser(SWAP).parse();self.assertEqual(c.canonical(a,colors()),c.canonical(b,colors()));self.assertNotEqual(c.canonical(a,{x:x for x in EXPECTED}),c.canonical(b,{x:x for x in EXPECTED}))
    def test_biological_topology_difference_preserved(self):
        self.assertNotEqual(c.canonical(c.Parser(T).parse(),colors()),c.canonical(c.Parser(PAIR).parse(),colors()))
    def test_population_and_individual_identity_preserved(self):
        x=c.Parser(T).parse();a=colors();b=dict(a);b[A+'.1']=b[A+'.2']=('different','K');self.assertNotEqual(c.canonical(x,a),c.canonical(x,b));b=dict(a);b[A+'.1']=b[A+'.2']=(A,'differentpopulation');self.assertNotEqual(c.canonical(x,a),c.canonical(x,b))
    def test_child_order_and_branch_time_marginal(self):
        a=c.Parser(T).parse();self.assertEqual(c.canonical(a,colors()),c.canonical((a[1],a[0]),colors()));self.assertEqual(c.canonical(a,colors()),c.canonical(c.Parser(T.replace(':0.1',':0.11')).parse(),colors()))
    def test_duplicate_clade_vectors_are_multiset(self):
        vectors=c.clade_vectors(c.Parser(T).parse(),{x:0 if x.startswith(A) else 1 for x in EXPECTED});self.assertEqual(vectors,[((0,1),(1,1)),((0,1),(1,1))])
    def test_complete_rows_and_labels(self):
        with patch.object(c,'N',2):
            r=c.inspect_trace(((T+'\n')*2).encode(),EXPECTED,MAP);self.assertEqual(sum(r['clades'].values()),4);self.assertEqual(len(r['clades']),1)
            for raw in [(T+'\n').encode(),(T+'\n'+T).encode(),((T.replace('B^b.2','B^b.1')+'\n')*2).encode()]:
                with self.assertRaises(ValueError):c.inspect_trace(raw,EXPECTED,MAP)
    def test_parser_rejects_malformed(self):
        bad=['(a:1,b:1,c:1):0; [TH=1, TL=3]',T+'garbage',T.replace(':0.1',':nan'),T.replace(':0.1',':-1'),T.replace(';',''),T.replace('):0.0',')node:0.0')]
        for x in bad:
            with self.assertRaises(ValueError):c.Parser(x).parse()
    def test_tv_normalized_occurrences(self):
        self.assertEqual(c.total_variation(collections.Counter(a=2),collections.Counter(a=9)),0);self.assertEqual(c.total_variation(collections.Counter(a=2),collections.Counter(b=2)),1)
    def test_input_hashes_without_output_inventory(self):
        with tempfile.TemporaryDirectory() as d:
            folder=pathlib.Path(d);p=folder/'alignment.txt';p.write_bytes(b'fixture');h=c.sha(b'fixture')
            t={'input_hashes_before':{'alignment':h},'input_hashes_after':{'alignment':h},'output_inventory':[]}
            self.assertEqual(c.authenticated_input(folder,p.name,'alignment',t),b'fixture')
            p.write_bytes(b'changed')
            with self.assertRaises(ValueError):c.authenticated_input(folder,p.name,'alignment',t)
    def test_blank_map_lines_are_not_records(self):
        self.assertEqual(c.parse_map(b'a K\nb C\n\n'),{'a':'K','b':'C'})
        for raw in [b'\n',b'a K\na C\n',b'a K extra\n']:
            with self.assertRaises(ValueError):c.parse_map(raw)
if __name__=='__main__':unittest.main()
