"""Separate net-points-per48 adapter. Does NOT reconstruct possessions or O/D.
Requires verified chronological segment order, exact durations and home/away.
"""
from collections import defaultdict
import math

def integrate_game(rows, expected_home_margin=None):
    """Rows: game_id, quarter, side(home/away), order, seconds, lineup[5], pm.
    Source durations must be exact seconds, not rounded display minutes.
    Zero-duration scoring is rejected for explicit upstream reconciliation.
    """
    if not rows:raise ValueError('empty game')
    if len({r['game_id'] for r in rows})!=1:raise ValueError('multiple games')
    quarters=defaultdict(lambda:defaultdict(list))
    for r in rows:
        if r['side'] not in ('home','away'):raise ValueError('unknown side')
        if len(r['lineup'])!=5 or len(set(r['lineup']))!=5:raise ValueError('invalid lineup')
        if not math.isfinite(r['seconds']) or r['seconds']<=0:raise ValueError('nonpositive or nonfinite duration')
        if not math.isfinite(r['pm']):raise ValueError('invalid net points')
        quarters[r['quarter']][r['side']].append(r)
    qs=sorted(quarters)
    if len(qs)<4 or qs!=list(range(1,max(qs)+1)):raise ValueError('incomplete or nonconsecutive quarters')
    result=[];total_home=0;total_away=0
    for quarter,sides in sorted(quarters.items()):
        timed={}
        for side in ('home','away'):
            rs=sorted(sides[side],key=lambda r:r['order'])
            if not rs or len({r['order'] for r in rs})!=len(rs):raise ValueError('missing or duplicate segment ordering')
            t=0;timed[side]=[]
            for r in rs:timed[side].append((t,t+r['seconds'],r));t+=r['seconds']
        duration=720 if quarter<=4 else 300
        for side in ('home','away'):
            if abs(timed[side][-1][1]-duration)>1e-6:raise ValueError('quarter duration does not reconcile')
        hp=sum(r['pm'] for _,_,r in timed['home']);ap=sum(r['pm'] for _,_,r in timed['away'])
        if abs(hp+ap)>1e-6:raise ValueError('quarter pm totals not complementary')
        total_home+=hp;total_away+=ap
        for start,end,r in timed['home']:
            opposing_seconds=defaultdict(float)
            for a,b,other in timed['away']:
                overlap=max(0,min(end,b)-max(start,a))
                if overlap:
                    if set(r['lineup'])&set(other['lineup']):raise ValueError('same player on both teams')
                    for p in other['lineup']:opposing_seconds[p]+=overlap
            if abs(sum(opposing_seconds.values())-5*r['seconds'])>1e-6:raise ValueError('opponent exposure does not reconcile')
            result.append({'game_id':r['game_id'],'quarter':quarter,'source_order':r['order'],
                'seconds':r['seconds'],'observed_home_pm':r['pm'],'home_lineup':r['lineup'],
                'opponent_player_seconds':dict(opposing_seconds),
                'home_net_points_per48':r['pm']*2880/r['seconds'],
                'target_is_original_home_segment':True})
    if expected_home_margin is not None and abs(total_home-expected_home_margin)>1e-6:raise ValueError('final margin mismatch')
    return result
