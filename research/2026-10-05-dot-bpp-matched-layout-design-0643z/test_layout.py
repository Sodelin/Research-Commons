import json,unittest
from unittest.mock import patch
import prepare_layout as p
class LayoutTests(unittest.TestCase):
    def test_declared_layout(self):
        local,summary=p.prepare()
        self.assertEqual(summary['simulation_individuals_per_population'],{'K':6,'C':10,'L':14,'H':2})
        self.assertEqual([x['length'] for x in summary['loci']],[489,455,440,285,457])
        self.assertEqual([x['individuals'] for x in summary['loci']],[21,28,28,24,30])
        self.assertEqual([x['question_mark_count'] for x in summary['loci']],[0,0,0,0,7])
        for locus in local['loci']:
            labels=[x['synthetic_label'] for x in locus['rows']]
            self.assertEqual(len(labels),len(set(labels)))
            for row in locus['rows']:
                self.assertEqual(set(row),{'synthetic_label','population','question_mark_sites_1based'})
                self.assertTrue(all(1<=s<=locus['length'] for s in row['question_mark_sites_1based']))
        self.assertFalse(local['copy_observed_alleles']);self.assertFalse(local['execute_simulation'])
    def test_pin_guard(self):
        with patch.object(p,'sha',return_value='wrong'):
            with self.assertRaisesRegex(ValueError,'unreviewed'):p.prepare()
if __name__=='__main__':unittest.main()
