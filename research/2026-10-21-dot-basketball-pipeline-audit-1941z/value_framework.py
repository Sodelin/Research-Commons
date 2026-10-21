"""Explicit net-impact and exposure accounting; no empirical calibration supplied."""
import math

def deployment_value(player, reference, teammates, center, common_context_coef=0.):
    """p/r have a,b,u,rate; four teammate profiles have u,rate.
    a: offensive PPP coefficient; b: defensive PPP ALLOWED coefficient.
    Recompute every affected teammate interaction. Defense currently additive.
    Reference may be average, replacement or another player; caller must label.
    """
    if len(teammates)!=4:raise ValueError('four fixed teammate profiles required')
    for profile in [player,reference,*teammates]:
        if not all(math.isfinite(float(v)) for v in profile.values()):raise ValueError('nonfinite profile')
    mix=sum(t['rate'] for t in teammates)/4
    spillover=sum(t['u'] for t in teammates)*(player['rate']-reference['rate'])/4
    common_shift=common_context_coef*(player['rate']-reference['rate'])/5
    off=100*(player['a']-reference['a']+(player['u']-reference['u'])*(mix-center)+spillover+common_shift)
    defense=100*(reference['b']-player['b'])
    return {'offense_points_per100':off,'defense_points_saved_per100':defense,
            'net_points_per100':off+defense,'teammate_spillover_per100':100*spillover,'common_context_shift_per100':100*common_shift,
            'interpretation':'model-dependent fixed-deployment contrast, not identified causal talent'}

def exposure_value(net_points_per100, minutes_per_game, games_available, pace_per48, points_per_win=None):
    values=[net_points_per100,minutes_per_game,games_available,pace_per48]
    if not all(math.isfinite(float(x)) for x in values):raise ValueError('nonfinite exposure input')
    if minutes_per_game<0 or games_available<0 or pace_per48<0:raise ValueError('negative exposure input')
    possessions=minutes_per_game/48*games_available*pace_per48
    points=net_points_per100*possessions/100
    result={'on_court_possessions':possessions,'net_points_above_stated_reference':points,
            'wins_above_stated_reference':None,'availability_is_supplied_scenario_not_prediction':True}
    if points_per_win is not None:
        if not math.isfinite(points_per_win) or points_per_win<=0:raise ValueError('invalid points-per-win calibration')
        result['wins_above_stated_reference']=points/points_per_win
    return result

def scenario_envelope(profiles, references, deployments, centers, exposure_scenarios, common_context_coefs):
    """All scenarios must be supplied, not inferred probabilities. No CI claim."""
    if not profiles or not references or not deployments or not centers or not exposure_scenarios or not common_context_coefs:
        raise ValueError('empty scenario set')
    outputs=[]
    for p in profiles:
      for r in references:
       for teammates in deployments:
        for c in centers:
         for common in common_context_coefs:
          v=deployment_value(p,r,teammates,c,common)
          for exposure in exposure_scenarios:
           outputs.append({**v,**exposure_value(v['net_points_per100'],**exposure)})
    return {'kind':'supplied-model-and-exposure sensitivity envelope; NOT a confidence interval',
            'net_points_per100_range':[min(o['net_points_per100'] for o in outputs),max(o['net_points_per100'] for o in outputs)],
            'total_points_range':[min(o['net_points_above_stated_reference'] for o in outputs),max(o['net_points_above_stated_reference'] for o in outputs)],
            'scenarios':outputs}
