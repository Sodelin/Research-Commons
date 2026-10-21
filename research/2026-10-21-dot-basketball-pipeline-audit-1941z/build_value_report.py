"""Consume pipeline coefficients and an explicitly supplied deployment/exposure file."""
import argparse,json
from pathlib import Path
from value_framework import deployment_value,exposure_value

def build(report,config):
    if not config.get('reference_label'):raise ValueError('explicit reference label required; no automatic replacement level')
    output={'status':report['status'],'reference_label':config['reference_label'],
            'kind':'conditional model/scenario values, not causal effects or confidence bounds','players':{}}
    for player in config['players']:
        values=[]
        for model,m in report['models'].items():
            if player not in m['player_coefficients']:raise ValueError(f'unknown player {player}')
            p=m['player_coefficients'][player]
            # Teammates may be explicit abstract profiles, not hidden average-player assumptions.
            teammates=config['teammate_profiles']
            ref=config['reference_profile']
            v=deployment_value(p,ref,teammates,m['context_center'],m['common_context_coef'])
            for e in config['exposure_scenarios']:
                values.append({'model':model,'exposure_inputs':e,**v,**exposure_value(v['net_points_per100'],**e)})
        output['players'][player]={'net_points_per100_sensitivity_range':[min(v['net_points_per100'] for v in values),max(v['net_points_per100'] for v in values)],
             'total_points_sensitivity_range':[min(v['net_points_above_stated_reference'] for v in values),max(v['net_points_above_stated_reference'] for v in values)],'scenarios':values}
    output['limitations']=['Reference is explicitly supplied, not empirically estimated replacement level',
        'Exposure scenarios are supplied, not availability predictions','Sensitivity range is not a confidence interval',
        'Defensive component is additive and has not received a role-interaction extension',
        'No adjustment for endogenous coaching, injury or latent role selection',
        'No empirical NBA validation when input status says implementation test',
        'A positive value is not guaranteed future production or fantasy points']
    return output

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('fit_report',type=Path);p.add_argument('config',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    a.output.write_text(json.dumps(build(json.loads(a.fit_report.read_text()),json.loads(a.config.read_text())),indent=2)+'\n')
