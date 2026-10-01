from fractions import Fraction as F
from pathlib import Path
import random,json
from rank_ledger import ExactLedger

rng=random.Random(1072026)
cases=calls=simulated=0
for d in range(1,9):
    for trial in range(20):
        z=[F(rng.randrange(1,20),23) for _ in range(d)]
        ledger=ExactLedger(d)
        def oracle(rows,offset):
            return [sum(a*b for a,b in zip(row,z))+c for row,c in zip(rows,offset)]
        previous=F(0)
        for step in range(40):
            raw=[rng.randrange(1,9)+(int(previous>F(1,2)) if j==0 else 0) for j in range(d)]
            row=[F(a,sum(raw)) for a in raw]
            # Blocks include deliberately dependent rows and known offsets.
            rows=[row,[2*x for x in row]] if step%3==0 else [row]
            offset=[F(step%5,11)]*len(rows)
            expected=tuple(oracle(rows,offset))
            actual=ledger.query(rows,offset,oracle)
            assert actual==expected
            previous=actual[0]
        assert ledger.oracle_calls<=d and ledger.rank<=d
        calls+=ledger.oracle_calls; simulated+=ledger.simulated_calls; cases+=1
zero=ExactLedger(0)
assert zero.query([[]],[F(2,3)],lambda *_: (_ for _ in ()).throw(AssertionError('Redundant oracle call')))==(F(2,3),)
report={'status':'PASS','adaptive_exact_rational_runs':cases,'programs_per_run':40,
        'informative_oracle_calls':calls,'simulated_redundant_programs':simulated,
        'zero_dimensional_constant_control':True,
        'limits':'Exact rational measurement certificates. Finite tests do not prove the universal real-action theorem or verify a noisy-sampling procedure.'}
Path(__file__).with_name('rank-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
