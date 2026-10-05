"""Static compiler/parser and mocked lifecycle tests; never executes BPP."""
import copy,tempfile,unittest
from fractions import Fraction as F
from pathlib import Path
from unittest.mock import patch
import compile_control as d
import admit_generated as a
import run_simulation as r

def settings_fixture():
    _,c=d.compile_control();order=['A','B','C','R','AB','H_main','CS','H_mirror'];ids={role:i for i,role in enumerate(order)}
    text='bpp v4.8.7_linux_x86_64\nSubstitution model: JC69\n3 species: A (2) B (2) C (2)\nHybridization events: 1\nBidirectional introgressions: 0\nLabel Node Child1 Child2 Parent\n'
    for role in order:
        children=[str(ids[x]) for x in c['graph_children'][role]];children+=['N/A']*(2-len(children));parent=c['graph_parents'][role];label='H' if role.startswith('H_') else role;tail=''
        if role=='H_main':tail=' [tau = 1, phi = 0.750000, prop_tau = 1, has_phi = 1]'
        if role=='H_mirror':tail=' Mirrored hybridization node [Hybrid = H (5)] [tau = 0, phi = 0.250000, prop_tau = 0, has_phi = 0]'
        text+=f"{label} {ids[role]} {children[0]} {children[1]} {'N/A' if parent is None else ids[parent]}{tail}\n"
    text+='\nMap of populations and ancestors (1 in map indicates ancestor):\nSpecies 1 2 3 4 5 6 7 8\n'
    for role in order:
        label='H' if role.startswith('H_') else role;n=c['expected_node_roles'][role]
        text+=f"{ids[role]+1} {label} "+' '.join('1' if j==ids[role] else '0' for j in range(8))+f" tau = {float(F(n['tau'])):.6f} theta = {float(F(n['theta'])):.6f}\n"
    return text+'\n',c

def panels(m=2):return ('\n\n'+'\n\n'.join('6 2\n'+'\n'.join(name+' AC' for name in d.ALIASES) for _ in range(m))+'\n').encode()
class StaticTests(unittest.TestCase):
    def test_control_exact_values_and_rate_ties(self):
        control,c=d.compile_control();self.assertEqual(d.sha(control),'7f5d4df135213f3ac6c391a361c24d97ce16e657e85e5dd5eae3113e3db40918');self.assertIn(b'phase = 0 0 0',control);self.assertIn(b'loci&length = 1024 2',control);self.assertIn(b'alpha_siterate = 1 0',control)
        for lhs,rhs in [('B','H_main'),('C','CS')]:self.assertEqual(c['expected_node_roles'][lhs]['theta'],c['expected_node_roles'][rhs]['theta'])
        for role in ('A','B','C','AB','R'):self.assertEqual(2/F(c['expected_node_roles'][role]['theta']),F(d.TRUTH['r'+role]))
    def test_dyadic_decimal_has_no_rounding(self):
        for x in ['0','1/16','1/8','3/16','1/2','2','-1']:self.assertEqual(F(d.exact_decimal(x)),F(x))
        with self.assertRaises(ValueError):d.exact_decimal('1/3')
    def test_graph_and_numeric_table_roles(self):
        text,c=settings_fixture();r=a.validate_settings(text,c);self.assertEqual(r['node_roles']['H_main'],5);self.assertEqual(r['node_roles']['H_mirror'],7);self.assertEqual(r['population_rows'][5]['tau'],'1/16');self.assertEqual(r['network_nodes'][5]['htau'],1);self.assertEqual(r['population_rows'][7]['theta'],'-1')
    def test_phi_or_numeric_time_tampering_rejected(self):
        text,c=settings_fixture()
        for altered in [text.replace('phi = 0.750000','phi = 0.250000'),text.replace('tau = 0.062500 theta = 1.000000','tau = 0.125000 theta = 1.000000'),text.replace('theta = -1.000000','theta = 1.000000')]:
            with self.assertRaises(ValueError):a.validate_settings(altered,c)
    def test_missing_or_duplicate_population_identity(self):
        text,c=settings_fixture()
        for altered in [text.replace('8 H ','7 H '),text.replace('R 3 4 6 N/A','R 3 4 5 N/A'),text.replace('3 species: A (2) B (2) C (2)','3 species: A (2) B (2) C (2) X (1)')]:
            with self.assertRaises(ValueError):a.validate_settings(altered,c)
    def test_complete_phased_literal_parser(self):
        parsed=a.extract_panels(panels(),2);self.assertEqual(len(parsed['loci']),2);self.assertEqual(set(parsed['loci'][0]['calls']),set(d.ALIASES.values()));self.assertEqual(parsed['loci'][0]['columns'],[1,2])
    def test_incomplete_or_ambiguous_alignment_refused(self):
        for raw in [panels()[:-1],panels().replace(b'A^a1 AC',b'A^a1 AN',1),panels().replace(b'6 2',b'-6 2',1),panels().replace(b'B^b1',b'A^a1',1)]:
            with self.assertRaises(ValueError):a.extract_panels(raw,2)
    def test_existing_genealogy_parser_reused(self):
        module=a.load_parser();line='((A^a1:0.1,A^a2:0.1):0.1,((B^b1:0.1,B^b2:0.1):0.05,(C^c1:0.1,C^c2:0.1):0.05):0.05):0; [TH=0.200000, TL=0.850000]';p=module.Parser(line);p.parse();self.assertEqual(set(p.leaves),set(d.ALIASES));self.assertEqual(len(p.leaves),6)

class RunnerTests(unittest.TestCase):
    def test_startup_receipt_failure_never_spawns(self):
        control,_=d.compile_control();pins={'control_sha256':d.sha(control)};real=r.dump
        def fail(path,value):
            if Path(path).name=='BEFORE.json':raise OSError('mock before receipt')
            return real(path,value)
        with tempfile.TemporaryDirectory() as td,patch.object(r,'authenticate',return_value=(pins,d)),patch.object(r,'dump',side_effect=fail),patch.object(r.subprocess,'Popen') as spawn:
            out=r.run(Path(td)/'attempt','unused','0'*64);spawn.assert_not_called();self.assertEqual(out['status'],'RUNNER_FAILURE');self.assertIsNotNone(out['runner_failure'])
    def test_post_spawn_receipt_failure_cleans_owned_group(self):
        control,_=d.compile_control();pins={'control_sha256':d.sha(control)};real=r.dump
        class Child:pid=12345
        class Watch:
            terminated=False
            def terminate_group(self,proc):self.terminated=True
            def tree_bytes(self,path):return sum(x.stat().st_size for x in path.rglob('*') if x.is_file())
        watchdog=Watch()
        def fail(path,value):
            if Path(path).name=='PID.json':raise OSError('mock pid receipt')
            return real(path,value)
        with tempfile.TemporaryDirectory() as td,patch.object(r,'authenticate',return_value=(pins,d)),patch.object(r,'dump',side_effect=fail),patch.object(r,'load_watchdog',return_value=watchdog),patch.object(r.subprocess,'Popen',return_value=Child()):
            out=r.run(Path(td)/'attempt','unused','0'*64);self.assertTrue(watchdog.terminated);self.assertEqual(out['status'],'RUNNER_FAILURE')
if __name__=='__main__':unittest.main()
