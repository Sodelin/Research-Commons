"""Publisher-attributed LUMA deployment calculator, NOT our fitted estimator.
Every row retained, including blank IDs. Inputs are scenarios, not forecasts.
"""
import argparse,csv,hashlib,json,math
from pathlib import Path

def calculate(board,config,out):
    if not config.get('reference_label') or not config.get('scenario_label'):raise ValueError('explicit scenario/reference labels required')
    ref=float(config['reference_net_per100']);minutes=float(config['minutes_per_game']);games=float(config['games_available']);pace=float(config['pace_per48'])
    if not all(math.isfinite(x) for x in [ref,minutes,games,pace]) or min(minutes,games,pace)<0:raise ValueError('invalid scenario')
    possession_exposure=minutes/48*games*pace
    digest=hashlib.sha256(board.read_bytes()).hexdigest()
    with board.open() as handle:rows=list(csv.DictReader(handle))
    result=[]
    for i,r in enumerate(rows):
        rating=float(r['loki']);lo=float(r['lo90']);hi=float(r['hi90'])
        result.append({'source_row_key':f'luma:{digest}:csvline:{i+2}','source_rank':r['rank_all'],'player_id':r['pid'],
          'player_name':r['name'],'join_status':'verified_source_nonblank_id' if r['pid'] else 'unresolved_blank_id_do_not_join',
          'publisher_net_per100':rating,'publisher_lo90':lo,'publisher_hi90':hi,'reference_label':config['reference_label'],
          'scenario_label':config['scenario_label'],'scenario_minutes_per_game':minutes,'scenario_games':games,'scenario_pace_per48':pace,
          'scenario_possessions':possession_exposure,'point_value_vs_reference':(rating-ref)*possession_exposure/100,
          'transformed_publisher_low':(lo-ref)*possession_exposure/100,'transformed_publisher_high':(hi-ref)*possession_exposure/100,
          'interval_status':'publisher estimate interval scaled at fixed scenario; NOT our validated future-production interval',
          'model_attribution':'LUMA Basketball Research / CourtShare; CC BY4.0; https://court-share.com/luma'})
    out.mkdir(parents=True,exist_ok=True)
    with (out/'publisher-reference-values.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=list(result[0]));w.writeheader();w.writerows(result)
    metadata={'kind':'existing-publisher-metric exposure calculator; not our trained model','board_sha256':digest,'total_rows':len(result),
      'joinable_nonblank_id_rows':sum(bool(r['player_id']) for r in result),'unresolved_blank_id_rows':sum(not r['player_id'] for r in result),
      'scenario':config,'source_release':'LOKI2026–27 R1 v3.3; October2026 release; prospective comparator, not historical as-of archive',
      'license':'preserve adjacent LICENSE and acquisition manifest; CC BY4.0 for publisher output',
      'limits':['No projected availability or minutes inferred','No empirical replacement benchmark inferred',
      'No proof publisher intervals are calibrated','No own-model superiority or causal effect claim',
      'No direct fantasy scoring interpretation','No offensive/defensive split recovered from net-only rating']}
    (out/'publisher-reference-metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    return result,metadata

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('board',type=Path);p.add_argument('scenario',type=Path);p.add_argument('out',type=Path);a=p.parse_args()
    _,meta=calculate(a.board,json.loads(a.scenario.read_text()),a.out);print(json.dumps(meta,indent=2))
