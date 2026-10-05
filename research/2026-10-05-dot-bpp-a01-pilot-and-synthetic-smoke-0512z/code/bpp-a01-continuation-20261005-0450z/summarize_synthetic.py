"""Apply the reviewed four-tip parser to the separately admitted synthetic smoke."""
import json
from pathlib import Path
from summarize_a01 import main
BASE=Path(__file__).resolve().parent
names=['A01-synthetic-seed8001','A01-synthetic-seed8002']
report=main(names,run_root=BASE/'synthetic-runs')
report.update(schema='bpp-known-truth-smoke-summary-v1',truth='((C,K),(H,L));',simulation_seed=7001,calibration_replicates=1)
for run in report['runs']:
    run['truth_posterior_frequency']=next((r['frequency'] for r in run['topologies'] if r['tree']==report['truth']),0)
    run['truth_in_95_percent_set']=report['truth'] in run['credible_set_95']
    run['root_truth_in_equal_tail_95_interval']=run['root_height']['quantiles_025_50_975'][0] <= .002 <= run['root_height']['quantiles_025_50_975'][2]
print(json.dumps(report,indent=2))
