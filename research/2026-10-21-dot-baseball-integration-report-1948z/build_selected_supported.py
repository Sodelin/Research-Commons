"""Compose selected September baseline with subtotal-only uncertainty diagnostics."""
import sys,csv,json
from pathlib import Path
from compose import compose
p=Path(__file__).parent;inp=Path(sys.argv[1]) if len(sys.argv)>1 else p.parent/'real-test'/'next-round'/'selected-baseline-report-local.csv';out=[]
for r in csv.DictReader(inp.open()):
 rec=dict(player_id=r['player_id'],window_start=r['window_start'],window_end=r['window_end_exclusive'],window_convention='[start,end)',mode='forecast',reference_id='frozen-2020-supported-score',accounting_version='supported-v1',components={})
 for name,col in [('batting','forecast_batting_proxy'),('baserunning','forecast_steal_only'),('pitching','forecast_pitching_proxy')]:
  v={k:rec[k] for k in ['player_id','window_start','window_end','window_convention','mode','reference_id','accounting_version']};v.update(status='partial',value=float(r[col]),units='runs',source='Retrosheet2020–25; frozen September baseline',definition={'batting':'Fixed-reference event score; lacks park/league normalization','baserunning':'Steal-only centered score; other advancement absent','pitching':'Simplified FIP-difference proxy; not full WAR allocation'}[name]);rec['components'][name]=v
 for name in ['fielding','position','league','replacement']:rec['components'][name]=dict(status='missing')
 c=compose(rec);assert abs(c['supported_subtotal_runs']-float(r['supported_subtotal']))<1e-10
 out.append(dict(name=r['name'],ledger=rec,composition=c,subtotal_only_diagnostic_band=[float(r['diagnostic_lower']),float(r['diagnostic_upper'])],full_value_uncertainty=None))
assert len(out)==738 and all(r['composition']['total_runs'] is None for r in out)
(p/'selected-baseline-ledgers-local.json').write_text(json.dumps(out))
(p/'selected-coverage-summary.json').write_text(json.dumps(dict(rows=len(out),complete_value_available=0,mode='historical September2025 forecast evaluation',current2026_projections=False,band_scope='supported subtotal only; empirical diagnostic, no guarantee'),indent=2))
print('738 selected-baseline ledgers validated; full totals and full-value uncertainty unavailable')
