"""Real MLB schema/aggregation audit only. Not a fitted forecast or skill ranking."""
import csv,json,collections,hashlib,sys
from pathlib import Path
p=Path(__file__).parent; data=Path(sys.argv[1]) if len(sys.argv)>1 else p/'statcast-2025-04-01.csv'; r=list(csv.DictReader(data.open(encoding='utf-8-sig')))
assert {x['game_date'] for x in r}=={'2025-04-01'}
assert {x['game_type'] for x in r}=={'R'}
keys=[(x['game_pk'],x['at_bat_number'],x['pitch_number']) for x in r]
assert len(keys)==len(set(keys))
terminal=[x for x in r if x['events'] and x['events']!='truncated_pa']
assert len(terminal)==len({(x['game_pk'],x['at_bat_number']) for x in terminal})
contact=[x for x in terminal if x['type']=='X']
tracked=[x for x in contact if x['launch_speed']]
weighted=[x for x in terminal if x['woba_denom'] and x['woba_value']]
report={'status':'real-data ingestion audit; no predictive validation','pitch_rows':len(r),'unique_games':len({x['game_pk'] for x in r}),'unique_batters':len({x['batter'] for x in terminal}),'nonempty_event_rows':sum(bool(x['events']) for x in r),'excluded_truncated_pa':sum(x['events']=='truncated_pa' for x in r),'completed_pa_rows':len(terminal),'contact_rows':len(contact),'contact_missing_launch_speed':len(contact)-len(tracked),'contact_missing_expected_woba':sum(not x['estimated_woba_using_speedangle'] for x in contact),'rows_with_woba_fields':len(weighted),'woba_denominator_sum':sum(float(x['woba_denom']) for x in weighted),'woba_value_sum':sum(float(x['woba_value']) for x in weighted),'handedness_pa_counts':dict(collections.Counter(x['p_throws'] for x in terminal)),'forbidden_future_fields_present':[k for k in r[0] if 'until_next' in k],'source_sha256':hashlib.sha256(data.read_bytes()).hexdigest()}
report['missingness_not_zero_imputed']=True
(p/'one-day-audit.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
