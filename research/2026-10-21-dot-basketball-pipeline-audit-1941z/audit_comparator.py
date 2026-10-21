"""Structural audit of licensed publisher output, NOT outcome validation."""
import csv,hashlib,json,math
from collections import Counter
from pathlib import Path
p=Path(__file__).resolve().parent.parent/'licensed-comparator'
rows=list(csv.DictReader((p/'board.csv').open()))
fields=['loki','lo90','hi90','lo80','hi80','sd','skill','lineups','poss_2026','poss_2025']
missing={f:sum(not r[f].strip() for r in rows) for f in fields}
nonfinite=[];badinterval=[];baddecomp=[]
for i,r in enumerate(rows):
 v={f:float(r[f]) for f in fields if r[f].strip()}
 if any(not math.isfinite(x) for x in v.values()):nonfinite.append(i)
 if all(k in v for k in ['lo90','lo80','loki','hi80','hi90']) and not v['lo90']<=v['lo80']<=v['loki']<=v['hi80']<=v['hi90']:badinterval.append(i)
 if all(k in v for k in ['skill','lineups','loki']) and abs(v['skill']+v['lineups']-v['loki'])>.002:baddecomp.append(i)
out={'source':'LUMA Basketball Research / CourtShare; https://court-share.com/luma',
'license':'CC BY 4.0 for these publisher outputs; see preserved LICENSE and acquisition.json',
'rows':len(rows),'unique_nonblank_player_ids':len({r['pid'] for r in rows if r['pid']}),'blank_player_id_rows':sum(not r['pid'] for r in rows),
'duplicate_player_ids':[p for p,n in Counter(r['pid'] for r in rows).items() if n>1 and p],
'coverage_denominator_all_rows':len(rows),'joinable_nonblank_rows':sum(bool(r['pid']) for r in rows),
'unresolved_rows':[{'csv_line':i+2,'source_rank':r['rank_all'],'reason':'blank pid; mapping unresolved'} for i,r in enumerate(rows) if not r['pid']],
'publisher_intervals_not_our_calibrated_intervals':True,
'missing_numeric_fields':missing,'nonfinite_rows':nonfinite,'unordered_interval_rows':badinterval,
'skill_plus_lineups_discrepancies_above_rounding':baddecomp,'status_counts':dict(Counter(r['status'] for r in rows)),
'evidence_counts':dict(Counter(r['evidence'] for r in rows)),
'board_sha256':hashlib.sha256((p/'board.csv').read_bytes()).hexdigest(),
'interpretation':'Actual publisher comparator-data audit only. No NBA outcomes, prediction accuracy, interval coverage or all-in-one model validation established.',
'join_key':'nonblank pid only; exclude60 blank rookie IDs until a verified crosswalk exists',
'missing_for_pipeline':['observed possessions and outcomes','ten-player lineups','per-game dates','separate offensive/defensive comparator ratings','verified as-of snapshot availability date']}
(Path(__file__).resolve().parent/'comparator-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
