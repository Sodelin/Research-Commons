import copy,importlib.util,json,math,subprocess,sys,tempfile,unittest
from fractions import Fraction as Q
from pathlib import Path
from unittest.mock import patch
from genealogy_workbench.core import *
from genealogy_workbench.statistics import statistical_sort,radius,sqrt_upper
from genealogy_workbench.demo import source,experiment,fixtures
from genealogy_workbench.provenance import receipt,verify_receipt,verify_vendor
from genealogy_workbench.cli import run
from genealogy_workbench.vendor import count_controls as C
from tests import independent_forest_oracle as O


class ExactSourceTests(unittest.TestCase):
    def test_normalization_full_coordinates(self):
        for p in [(Q(1,3),Q(2,3),Q(1,3),Q(1,2),Q(1,2)),(Q(7,8),Q(3,8),Q(2,5),Q(1,7),Q(2,3))]:
            for n in range(1,6):
                d=complete_law(p,n)
                self.assertEqual(sum(d.values()),1);self.assertTrue(all(v>=0 for v in d.values()))
                self.assertEqual(set(d),set(F.forests(tuple(range(n)))))

    def test_direct_historical_forest_oracle(self):
        for params in [(Q(1,3),Q(2,3),Q(1,3),Q(1,2),Q(1,2)),(Q(7,8),Q(3,8),Q(2,5),Q(1,7),Q(2,3))]:
            for n in range(1,6):
                def cv(t):return int(t[4:]) if isinstance(t,str) else F.tree(cv(t[0]),cv(t[1]))
                oracle={F.forest(cv(t) for t in f):p for f,p in O.complete(params,n).items()}
                self.assertEqual(complete_law(params,n),oracle)

    def test_projectivity_preserves_historical_subtrees(self):
        params=Source.read(source('s')).parameters
        for n in range(2,6):
            def prune(t):
                if isinstance(t,int):return None if t==n-1 else t
                a,b=prune(t[0]),prune(t[1])
                return b if a is None else a if b is None else F.tree(a,b)
            pushed=defaultdict(Q)
            for f,p in complete_law(params,n).items():
                pushed[F.forest(x for t in f if (x:=prune(t)) is not None)]+=p
            self.assertEqual(dict(pushed),complete_law(params,n-1))

    def test_arm_exchange_full_forest(self):
        a,x,y,g,b=map(Q,['2/3','3/4','1/3','2/5','5/6'])
        for n in range(1,6):self.assertEqual(complete_law((a,x,y,g,b),n),complete_law((a,y,x,1-g,b),n))

    def test_exchangeability_label_permutation(self):
        from itertools import permutations
        d=complete_law(Source.read(source('s')).parameters,4)
        for perm in permutations(range(4)):
            pushed={F.forest(F.relabel(t,dict(enumerate(perm))) for t in f):p for f,p in d.items()}
            self.assertEqual(pushed,d)

    def test_independent_count_projection(self):
        s=Source.read(source('s'));a,x,y,g,b=s.parameters
        for n in range(1,6):
            count=law(s,Experiment.read(experiment(n,'root_count')))
            for r in range(1,n+1):
                direct=sum((C.p(n,i,a)*C.b(i,j,x,y,g)*C.p(j,r,b) for i in range(1,n+1) for j in range(1,i+1)),Q(0))
                self.assertEqual(count[r],direct)

    def test_known_complete_forest_pad_collision_and_separator(self):
        s=Source.read(source('left'));t=Source.read(source('right',a='1/2',b='1/3'))
        for n in range(1,5):self.assertEqual(complete_law(s.parameters,n),complete_law(t.parameters,n))
        d,e=complete_law(s.parameters,5),complete_law(t.parameters,5)
        self.assertEqual(sum(d[k]!=e[k] for k in d),255)
        self.assertFalse(equivalence(s,t)['equivalent'])

    def test_theorem_scope_and_arm_ids(self):
        r=equivalence(Source.read(source('s')),Source.read(source('t',x='1/3',y='2/3')))
        self.assertTrue(r['equivalent']);self.assertIn('arm_exchange',r['branches'])
        self.assertFalse(r['finite_determining_cutoff_executed']);self.assertFalse(r['lean_kernel_checked'])


class InputAndSorterTests(unittest.TestCase):
    def job(self,name='cap5-refined'):return copy.deepcopy(fixtures()[name][1])
    def test_expected_answers_and_abstention(self):
        f=fixtures()
        for name,status in [('cap4-ambiguous','ABSTAIN_AMBIGUOUS'),('cap5-refined','CERTIFIED_WITHIN_CATALOGUE'),('original-arm-abstention','ABSTAIN_AMBIGUOUS')]:
            r=run(*f[name]);self.assertEqual(r['status'],status);self.assertIn('catalogue only',r['coverage'])

    def test_exact_four_root_trailing_inference(self):
        op,j=fixtures()['recover-trailing-survival'];r=run(op,j)
        self.assertEqual(r['status'],'CONDITIONAL_EXACT_LAW_INFERENCE');self.assertEqual(r['answer'],{'trailing_survival':'1/2'})
        self.assertFalse(r['source_membership_verified'])

    def test_degenerate_inference_abstains(self):
        op,j=fixtures()['recover-trailing-survival'];e=Experiment.read(j['experiment'])
        j['probabilities']=law_entries(Source.read(source('degenerate')),e)
        self.assertEqual(run(op,j)['status'],'ABSTAIN_DEGENERATE_BRANCH')

    def test_inference_detects_impossible_zero_denominator(self):
        op,j=fixtures()['recover-trailing-survival']
        j['probabilities']=[{'outcome':[[['A-copy-1','A-copy-2'],['A-copy-3','A-copy-4']]],'probability':'1/3'},
            {'outcome':['A-copy-1',['A-copy-2',['A-copy-3','A-copy-4']]],'probability':'2/3'}]
        self.assertEqual(run(op,j)['status'],'ABSTAIN_SOURCE_PROMISE_CONFLICT')

    def test_weaker_inference_readout_rejected(self):
        op,j=fixtures()['recover-trailing-survival'];j['experiment']['readout']='root_count'
        with self.assertRaises(InputError):run(op,j)

    def test_cannot_mix_exact_and_empirical_intakes(self):
        j=self.job();j['records']=[]
        with self.assertRaises(InputError):exact_sort(j)
        j=copy.deepcopy(fixtures()['fresh-loci-conditional'][1]);j['exact_observations']=[]
        with self.assertRaises(InputError):statistical_sort(j)

    def test_nonpositive_and_float_parameters_rejected(self):
        for value in ['0','1','-1/3',0.5,True,'1/0']:
            s=source('s');s['parameters']['left']=value
            with self.assertRaises(InputError):Source.read(s)

    def test_unknown_parameters_and_family_rejected(self):
        s=source('s');s['parameters']['other']='1/2'
        with self.assertRaises(InputError):Source.read(s)
        s=source('s');s['family']='arbitrary-network'
        with self.assertRaises(InputError):Source.read(s)

    def test_duplicate_copy_source_and_row_ids_rejected(self):
        e=experiment(2);e['entering_roots'][1]['copy_id']=e['entering_roots'][0]['copy_id']
        with self.assertRaises(InputError):Experiment.read(e)
        for field in ['sources','experiments']:
            j=self.job()
            if field=='sources':j['catalogue']['sources'].append(copy.deepcopy(j['catalogue']['sources'][0]))
            else:j['experiments'].append(copy.deepcopy(j['experiments'][0]))
            with self.assertRaises(InputError):exact_sort(j)

    def test_original_ids_round_trip_and_malformed_outcomes(self):
        e=Experiment.read(experiment(3));f=((0,(1,2)),)
        self.assertEqual(e.decode(e.encode(f)),f)
        for value in [['A-copy-1','A-copy-1','A-copy-3'],[['A-copy-1','missing'],'A-copy-3'],[]]:
            with self.assertRaises(InputError):e.decode(value)

    def test_readout_alphabet_encode_decode_round_trips(self):
        for readout in ['full_forest','root_count']:
            for n in range(1,6):
                e=Experiment.read(experiment(n,readout))
                for outcome in e.alphabet():
                    self.assertEqual(e.decode(e.encode(outcome)),outcome)
        e=Experiment.read(experiment(2,'root_count'))
        for bad in [True,0,3,[],[0,1]]:
            with self.assertRaises(InputError):e.encode(bad)

    def test_rational_probability_and_normalization_validation(self):
        for value in [0.5,'-1/4','3/2']:
            j=self.job();j['exact_observations'][0]['probabilities'][0]['probability']=value
            with self.assertRaises(InputError):exact_sort(j)
        j=self.job();j['exact_observations'][0]['probabilities']=[]
        with self.assertRaises(InputError):exact_sort(j)

    def test_requires_bounded_catalogue(self):
        j=self.job();j['catalogue']['coverage']='all_sources'
        with self.assertRaises(InputError):exact_sort(j)

    def test_one_shared_source_across_rows(self):
        low=source('low');high=source('high',a='9/10',b='9/10',x='9/10',y='9/10')
        e2,e3=experiment(2),experiment(3)
        j=self.job();j['catalogue']['sources']=[low,high];j['experiments']=[e2,e3]
        j['exact_observations']=[{'experiment_id':e2['experiment_id'],'probabilities':law_entries(Source.read(low),Experiment.read(e2))},
            {'experiment_id':e3['experiment_id'],'probabilities':law_entries(Source.read(high),Experiment.read(e3))}]
        self.assertEqual(exact_sort(j)['status'],'INCOMPATIBLE')

    def test_resource_cap_is_not_scientific_cutoff(self):
        with self.assertRaises(InputError):Experiment.read(experiment(6))

    def test_unknown_keys_rejected(self):
        j=self.job();j['some_ignored_model_parameter']='1/2'
        with self.assertRaises(InputError):exact_sort(j)


class StatisticalTests(unittest.TestCase):
    def job(self):return copy.deepcopy(fixtures()['fresh-loci-conditional'][1])
    def test_conditional_certificate_and_duplicate_unit(self):
        r=statistical_sort(self.job());self.assertEqual(r['status'],'CONDITIONAL_CERTIFICATE_WITHIN_CATALOGUE')
        self.assertEqual(r['independent_observation_units'],256);self.assertEqual(r['identical_same_locus_duplicates_ignored'],1)
        self.assertFalse(r['assumptions_verified_by_program']);self.assertTrue(r['intersects_all_observed_prefix_constraints'])

    def test_small_sample_abstains(self):
        j=self.job();j['records']=j['records'][:1]
        self.assertEqual(statistical_sort(j)['status'],'ABSTAIN_AMBIGUOUS')

    def test_different_same_locus_rejected(self):
        j=self.job();j['records'][-1]['outcome']=3-j['records'][0]['outcome']
        with self.assertRaises(InputError):statistical_sort(j)

    def test_cross_row_same_locus_requires_joint_outcome(self):
        j=self.job();e=experiment(3,'root_count');j['experiments'].append(e)
        j['records'].append({'locus_id':j['records'][0]['locus_id'],'experiment_id':e['experiment_id'],'outcome':1})
        with self.assertRaises(InputError):statistical_sort(j)

    def test_uncalibrated_sequence_channel_rejected(self):
        j=self.job();j['sampling']['channel']='estimated_quartet'
        with self.assertRaises(InputError):statistical_sort(j)

    def test_missing_independence_rejected(self):
        j=self.job();j['sampling']['independent_fresh_loci']=False
        with self.assertRaises(InputError):statistical_sort(j)

    def test_no_survivor_is_not_certificate(self):
        j=self.job();j['catalogue']['sources']=j['catalogue']['sources'][-1:]
        self.assertEqual(statistical_sort(j)['status'],'ABSTAIN_MODEL_OR_CONFIDENCE_CONFLICT')

    def test_eta_is_charged(self):
        j=self.job();j['sampling']['eta']='1'
        self.assertEqual(statistical_sort(j)['status'],'ABSTAIN_AMBIGUOUS')

    def test_rational_radius_upper_bounds_log_formula(self):
        for n in [1,2,10,100,1000,1000000]:
            for d in [2,37,266]:
                a=Q(1,60);b=radius(n,d,a)
                expected=min(1,math.sqrt(math.log(2*d*n*(n+1)/float(a))/(2*n)))
                self.assertGreaterEqual(float(b),expected)
                self.assertGreaterEqual(sqrt_upper(Q(2))**2,2)

    def test_nested_compatible_sets_across_prefixes(self):
        j=self.job();last=None
        for n in [1,5,10,25,50,100,256]:
            jj=copy.deepcopy(j);jj['records']=jj['records'][:n];now=set(statistical_sort(jj)['compatible_source_ids'])
            if last is not None:self.assertLessEqual(now,last)
            last=now


class ReceiptTests(unittest.TestCase):
    def test_vendor_pins_match(self):verify_vendor()
    def test_reexecution_and_changed_input(self):
        op,j=fixtures()['cap5-refined'];r=receipt(op,j,run(op,j))
        self.assertEqual(verify_receipt(j,r,run)['status'],'PASS')
        j=copy.deepcopy(j);j['catalogue']['catalogue_id']='modified'
        with self.assertRaisesRegex(InputError,'input binding'):verify_receipt(j,r,run)
    def test_modified_receipt_rejected(self):
        op,j=fixtures()['cap5-refined'];r=receipt(op,j,run(op,j));r['result']['status']='FAKE'
        with self.assertRaisesRegex(InputError,'hash changed'):verify_receipt(j,r,run)
    def test_changed_engine_binding_rejected(self):
        op,j=fixtures()['cap5-refined'];r=receipt(op,j,run(op,j))
        with patch('genealogy_workbench.provenance.engine_files',return_value={'changed':'hash'}):
            with self.assertRaisesRegex(InputError,'engine/provenance'):verify_receipt(j,r,run)
    def test_duplicate_json_keys_rejected(self):
        from genealogy_workbench.cli import load_json
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'duplicate.json';p.write_text('{"source":1,"source":2}')
            with self.assertRaises(InputError):load_json(p)
    def test_cli_invalid_returns_exit2(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'bad.json';p.write_text('{}')
            result=subprocess.run([sys.executable,'-m','genealogy_workbench','sort-exact',str(p)],capture_output=True,text=True)
            self.assertEqual(result.returncode,2);self.assertIn('INVALID_INPUT_OR_BLOCKED',result.stderr)


@unittest.skipUnless(importlib.util.find_spec('Bio'),'Optional Biopython absent')
class SequenceTests(unittest.TestCase):
    def records(self):
        from genealogy_workbench.vendor.sequence_adapter import fixture
        return [{'locus_id':'one','fasta':fixture('AB|CD')},{'locus_id':'star','fasta':'\n'.join('>'+x+'\n'+'A'*256 for x in 'ABCD')+'\n'}]
    def test_operational_comparison(self):
        from genealogy_workbench.benchmark import life_science_comparison
        r=life_science_comparison();self.assertEqual(r['status'],'PASS');self.assertEqual(r['metric']['matching_cases'],4)
        self.assertFalse(r['biological_validity_established'])
    def test_sequence_receipt_replays_json_round_trip(self):
        records=self.records();r=receipt('sequence',records,run('sequence',records))
        saved=json.loads(json.dumps(r))
        self.assertEqual(verify_receipt(records,saved,run)['status'],'PASS')
    def test_original_taxon_id_mapping_and_abstention(self):
        from genealogy_workbench.sequence import adapt_sequence
        records=self.records()
        for r in records:
            for before,after in [('A','taxon-A'),('B','taxon-B'),('C','taxon-C'),('D','taxon-D')]:r['fasta']=r['fasta'].replace('>'+before+'\n','>'+after+'\n')
        r=adapt_sequence(records);self.assertEqual(r['loci'][0]['original_taxon_split'],[['taxon-A','taxon-B'],['taxon-C','taxon-D']])
        self.assertTrue(r['g6_target_certificate'].startswith('ABSTAIN'));self.assertEqual(r['loci'][1]['label'],'UNRESOLVED')
    def test_sequence_duplicate_and_differing_same_locus(self):
        from genealogy_workbench.sequence import adapt_sequence
        records=self.records();records.append(copy.deepcopy(records[0]))
        r=adapt_sequence(records);self.assertEqual(r['independent_observation_units'],2);self.assertEqual(r['identical_same_locus_duplicates_ignored'],1)
        records[-1]['fasta']=records[-1]['fasta'].replace('ACGT','NCGT',1)
        with self.assertRaises(InputError):adapt_sequence(records)
    def test_invalid_sequences_rejected(self):
        from genealogy_workbench.sequence import adapt_sequence
        for change in [lambda s:s.replace('>B','>A'),lambda s:s.replace('ACGT','NCGT',1),lambda s:s.split('>D')[0],lambda s:s.replace('ACGT','AC-T',1)]:
            records=self.records();records[0]['fasta']=change(records[0]['fasta'])
            with self.assertRaises(InputError):adapt_sequence(records)

if __name__=='__main__':unittest.main()
