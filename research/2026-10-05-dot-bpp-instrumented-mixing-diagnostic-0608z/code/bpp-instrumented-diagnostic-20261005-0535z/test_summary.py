import unittest
from summarize_instrumented import tuning,genealogy_stats,expected_locus_labels
class SummaryTests(unittest.TestCase):
    def fixture(self):
        names=['Gage','Gspr']+['th'+str(i) for i in range(1,8)]+['tau','mix']
        return ' '.join(names)+'\nCurrent Pjump: '+' '.join(['0.3']*11)+'\nCurrent finetune: '+' '.join(['0.01']*11)+'\nNew finetune: '+' '.join(['0.02']*11)+'\n100% .6 .2 '+' '.join(['.3:.9']*7)+' .3 .3 0.1 0.2\n'
    def test_pernode_labels(self):
        r=tuning(self.fixture(),{i:'node'+str(i) for i in range(1,8)});self.assertEqual(r['autotune_rounds'],1);self.assertEqual(len(r['final_step_sizes']),11);self.assertEqual(r['final_progress_node_acceptance_rounded_2dp']['node7']['metropolized_gibbs'],.9)
    def test_grouped_format_rejected(self):
        with self.assertRaises(ValueError):tuning(self.fixture().replace('th7','th2'),{i:str(i) for i in range(1,8)})
    def test_genealogy_labels_and_metadata(self):
        raw=b'(a.1:0.001,a.2:0.001):0.000000; [TH=0.001000, TL=0.002000]\n'
        r=genealogy_stats(raw,{'a.1','a.2'},1);self.assertEqual(r['gene_copy_count'],2);self.assertEqual(r['TH']['mean'],.001)
        with self.assertRaises(ValueError):genealogy_stats(raw,{'a.1','wrong'},1)
    def test_genealogy_bad_metadata(self):
        with self.assertRaises(ValueError):genealogy_stats(b'(a.1:0.001,a.2:0.001); [TH=0.001, TL=0.0001]\n',{'a.1','a.2'},1)
    def test_phase_label_expansion(self):
        raw=('2 1\n^a A\n^b G\n'*5).encode();labels=expected_locus_labels(raw);self.assertEqual(len(labels),5);self.assertEqual(labels[0],{'^a.1','^a.2','^b.1','^b.2'})
if __name__=='__main__':unittest.main()
