#!/usr/bin/env python3
"""Bounded exact controls. Existing native execution only; no compiler."""
import argparse
import copy
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import random
import sys
import unittest

import selected_readout as subject

C, ENCODING, BRIDGE = subject.providers()
BINARY = RESTORED = OUTPUT = None


def fixture(name='dot2200-selected.json'):
    return C.loads((subject.HERE/'examples'/name).read_bytes())


class SelectedTests(unittest.TestCase):
    def directory(self, name):
        return OUTPUT/self._testMethodName/name

    def table(self, request, i='A', j='B', k=2):
        source, menu = request['source'], request['menu']
        values, maps = subject.source_binding(source, menu, C)
        query = next(q for q in ENCODING.fixed_queries(menu)['queries']
                     if q['directed_pair'] == [i,j] and q['level'] == k)
        transport = subject.copy_transport(query, source, C)
        wire = subject.native_request(source, [x['native_leaf_index'] for x in transport['selected_bijection']], request['budgets'])
        out = self.directory(f'{i}-{j}-{k}')
        native = BRIDGE.consume(dict(schema='native_rc1_operation_v1', operation='solve', request=wire),
                               out, BINARY, RESTORED)
        self.assertEqual(native['status'], 'CHECKED_SYMBOLIC_FORWARD_TABLE')
        raw = (out/'RESPONSE.rc1').read_bytes()
        variables = [f'X:{n}' for n in range(len(source['edges']))] + [f'G:{n}' for n in range(len(source['hybrids']))]
        table = subject.table_terms(raw, wire, variables, C)
        return query, transport, values, maps, table, raw, wire, variables

    def test_dot_source_identity_copy_transport_and_exact_normalization(self):
        request = fixture()
        self.assertEqual(hashlib.sha256((subject.HERE/'examples/DOT-PHYSICAL-FIXTURE.json').read_bytes()).hexdigest(),
                         '7552a9e8ae32ee759ed3665bd9a9176deeb6dcbf4be6605b55f8afbb0c7633ba')
        for k, expected in [(1,Q(1)),(2,Q(1,6)),(3,Q(1,144))]:
            query, transport, values, maps, table, *_ = self.table(request,k=k)
            rows, value = subject.configuration_readouts(table,transport['native_rooted_comb'],
                request['source'],request['menu'],values,maps,C,subject.Arithmetic())
            self.assertEqual(value,expected)
            self.assertEqual(len(transport['full_padded_row']['allocation']),4+k+1)
            self.assertEqual(len(transport['retained_baselines']),4)
            self.assertEqual(len(transport['selected_bijection']),k+1)
            self.assertEqual(transport['selected_bijection'][0]['padded_tag'],['inl','inr','unit'])
            self.assertEqual(rows[0]['rooted_total_mass'],'1')
            self.assertFalse(transport['full_padded_forward_table_generated'])
            self.assertEqual(query['required_event_probability'],str(expected))

    def test_unequal_arm_natural_force0_force1_and_gamma_direction(self):
        request=fixture('unequal-arm-selected.json')
        query,transport,values,maps,table,*_=self.table(request)
        expected=[(None,Q(11,72)),(0,Q(1,6)),(1,Q(1,8))]
        for bit, probability in expected:
            menu=copy.deepcopy(request['menu']);menu['configurations'][0]['mask']['H:pendant-A']=bit
            rows,value=subject.configuration_readouts(table,transport['native_rooted_comb'],request['source'],
                menu,values,maps,C,subject.Arithmetic())
            self.assertEqual(value,probability)
            self.assertEqual(rows[0]['complete_original_mask'],[bit])
        reversed_values=list(values);reversed_values[-1]=1-values[-1]
        _,reversed_value=subject.configuration_readouts(table,transport['native_rooted_comb'],request['source'],
            request['menu'],reversed_values,maps,C,subject.Arithmetic())
        self.assertEqual(reversed_value,Q(5,36));self.assertNotEqual(reversed_value,Q(11,72))

    def test_correlated_whole_masks_differ_from_equal_marginals(self):
        request=fixture('correlated-two-site-selected.json')
        query,transport,values,maps,table,*_=self.table(request)
        rows,correlated=subject.configuration_readouts(table,transport['native_rooted_comb'],request['source'],
            request['menu'],values,maps,C,subject.Arithmetic())
        self.assertEqual(correlated,Q(7,80))
        self.assertEqual(rows[-1]['configuration']['weight'],'0');self.assertEqual(rows[-1]['weighted_probability'],'0')
        anti=copy.deepcopy(request['menu'])
        anti['configurations'][0]['mask']['H:second']=1
        anti['configurations'][1]['mask']['H:second']=0
        _,anticorrelated=subject.configuration_readouts(table,transport['native_rooted_comb'],request['source'],
            anti,values,maps,C,subject.Arithmetic())
        self.assertEqual(anticorrelated,Q(27,320));self.assertNotEqual(correlated,anticorrelated)

    def test_independent_sympy_exact_evaluation(self):
        import sympy as sp
        self.assertEqual(sp.__version__,'1.14.0')
        request=fixture('unequal-arm-selected.json')
        _,_,values,_,table,*_=self.table(request,k=3)
        variables=sp.symbols('z:'+str(len(values)))
        cases=0
        for terms in table.values():
            expression=sum(sp.Rational(q.numerator,q.denominator)*sp.prod(x**p for x,p in zip(variables,powers))
                           for q,powers in terms)
            for g in [Q(0),Q(1,3),Q(2,3),Q(1)]:
                assignment=values[:-1]+[g]
                expected=expression.subs(dict(zip(variables,[sp.Rational(q.numerator,q.denominator) for q in assignment])))
                actual=subject.evaluate(terms,assignment,subject.Arithmetic())
                self.assertEqual(actual,Q(int(expected.p),int(expected.q)));cases+=1
        self.assertEqual(cases,60)
        print(json.dumps(dict(differential='existing native four-copy polynomials vs SymPy exact substitution',cases=cases)))

    def test_checked_table_identity_and_malformed_transport_controls(self):
        request=fixture()
        _,_,_,_,_,raw,wire,variables=self.table(request)
        bad=[raw+b'EXTRA\n',raw.replace(b'VARIABLES 10 ',b'VARIABLES 9 '),
             raw.replace(b'STATUS TABLE',b'STATUS UNKNOWN'),raw.replace(b'TERM 1/1 ',b'TERM 1.0 ',1),
             raw.replace(b'GATE SOURCE_ADMISSION_NOT_ESTABLISHED',b'GATE ADMITTED')]
        for value in bad:
            with self.subTest(value=value[:80]),self.assertRaises(C.Refused):
                subject.table_terms(value,wire,variables,C)
        with self.assertRaises(C.Refused):subject.table_terms(raw,wire.replace('SAMPLE 0 1','SAMPLE 0 0'),variables,C)
        altered=raw.replace(b'TERM ',b'TERM -',1)
        checked=BRIDGE.consume(dict(schema='native_rc1_operation_v1',operation='check',request=wire,
            certificate=altered.decode()),self.directory('corrupt-check'),BINARY,RESTORED)
        self.assertEqual(checked['status'],'REFUSED_REQUEST')

    def test_native_budget_unknown_and_invalid_source(self):
        request=fixture();request['budgets']['states']=0
        result=subject.run(json.dumps(request).encode(),self.directory('budget'),BINARY,RESTORED)
        self.assertEqual(result['status'],'UNKNOWN');self.assertFalse(result['readout_complete'])
        self.assertFalse(result['source_feasibility_certified'])
        request=fixture();request['source']['edges'][8]['target']=7
        result=subject.run(json.dumps(request).encode(),self.directory('invalid-source'),BINARY,RESTORED)
        self.assertEqual(result['status'],'REFUSED_REQUEST');self.assertFalse(result['readout_complete'])

    def test_typed_ids_explicit_order_and_full_taxon_bijection(self):
        request=fixture();source=request['source'];menu=request['menu']
        source['protected_edges']['A']=source['protected_edges'].pop('e0')
        menu['protected_edges'][0]='A'
        source['protected_hybrids']['A']=source['protected_hybrids'].pop('H:pendant-A')
        menu['protected_hybrids']=['A'];menu['configurations'][0]['mask']={'A':None}
        C.common_packet(menu);subject.source_binding(source,menu,C)
        changes=[lambda s:s['hybrids'][0].update(incoming=[4,3]),
                 lambda s:s['hybrids'][0].update(native_parent_0_probability='1/3'),
                 lambda s:s['taxa'][0].update(id='missing'),
                 lambda s:s['edges'][4].update(index=3),
                 lambda s:s['protected_edges'].update(A='unknown')]
        for change in changes:
            altered=copy.deepcopy(source);change(altered)
            with self.assertRaises(C.Refused):subject.source_binding(altered,menu,C)
        # Taxon enumeration may differ from menu order only with explicit indices.
        reordered=copy.deepcopy(source);reordered['taxa'].reverse()
        for i,taxon in enumerate(reordered['taxa']):taxon['index']=i
        subject.source_binding(reordered,menu,C)
        query=ENCODING.fixed_queries(menu)['queries'][3]
        tr=subject.copy_transport(query,reordered,C)
        by_id={x['id']:x['index'] for x in reordered['taxa']}
        self.assertTrue(all(x['native_leaf_index']==by_id[x['original_taxon_id']] for x in tr['selected_bijection']))

    def test_malformed_request_and_unencoded_ties_refused(self):
        bad=[b'{"schema":1,"schema":2}',b'{"x":0.2}',b'NaN',b'\xff']
        request=fixture();request['menu']['parameter_constraints']=[{'tie':['e3','e4']}]
        bad.append(json.dumps(request).encode())
        for i,raw in enumerate(bad):
            result=subject.run(raw,self.directory(str(i)))
            self.assertEqual(result['status'],'REFUSED_REQUEST')
            self.assertFalse(result['physical_source_admission_verified'])

    def test_missing_runtime_and_arithmetic_caps_are_unknown(self):
        result=subject.run(json.dumps(fixture()).encode(),self.directory('missing'))
        self.assertEqual(result['status'],'UNKNOWN');self.assertFalse(result['readout_complete'])
        with self.assertRaises(subject.Unknown):subject.Arithmetic(operations=0).mul(Q(1),Q(1))
        with self.assertRaises(subject.Unknown):subject.Arithmetic(bits=8).power(Q(17,19),8)
        with self.assertRaises(subject.Unknown):subject.Arithmetic().power(Q(1,2),subject.MAX_POWER+1)

    def test_direct_api_oversize_refused_before_input_file_write(self):
        for i,raw in enumerate([b' '*(C.MAX_BYTES+1),'é'*(C.MAX_BYTES//2+1)]):
            out=self.directory(str(i));result=subject.run(raw,out)
            self.assertEqual(result['status'],'REFUSED_REQUEST')
            self.assertFalse((out/'REQUEST.json').exists())


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--binary',type=Path,required=True)
    parser.add_argument('--restored',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();BINARY=args.binary;RESTORED=args.restored;OUTPUT=args.output
    OUTPUT.mkdir(parents=True,exist_ok=False)
    print(json.dumps(dict(executed_source_pins={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [Path(__file__),subject.HERE/'selected_readout.py']})),flush=True)
    unittest.main(argv=[sys.argv[0]],verbosity=2)
