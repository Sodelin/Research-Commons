"""Independent exact verification of the universal pad-recognition identities.
No unknown-source solver or sampled parameter screen is run.
"""
import json,re,hashlib,platform
from pathlib import Path
from argparse import ArgumentParser
import sympy as S

def main():
    ap=ArgumentParser();ap.add_argument('--source-dir',required=True);a=ap.parse_args();d=Path(a.source_dir)
    g,r=S.symbols('g r')
    def parse(x):
        assert re.fullmatch(r'[0-9gr\s+*/().-]+',x)
        return S.sympify(x,locals={'g':g,'r':r})
    genpath=d/'commutator-generators.json';cpath=d/'exceptional-cubic-certificates.json';resultpath=d/'uniform-placement-six-results.json'
    p={k:parse(v) for k,v in json.loads(genpath.read_text()).items()};cs=json.loads(cpath.read_text());saved=json.loads(resultpath.read_text())
    f=[r**3-9*r**2+27*r-9,9*r**3-27*r**2+9*r-1]
    for cert,fi,target in zip(cs,f,[g,g-1]):
        assert S.expand(parse(cert['cubic'])-fi)==0
        assert S.expand(parse(cert['U'])*p['m53']+parse(cert['V'])*p['m62']+parse(cert['W'])*fi-target)==0
    R1=S.resultant(p['m53'],p['m62'],g);R2=S.resultant(p['m53'],p['m64'],g)
    assert S.expand(R1-parse(saved['resultant_53_62']))==0
    assert S.expand(R2-parse(saved['resultant_53_64']))==0
    z=saved['resultant_bezout'];G=parse(z['G'])
    assert S.expand(parse(z['U'])*R1+parse(z['V'])*R2-G)==0
    expected=81*r**24*(r-1)**11*f[0]*f[1]
    assert S.expand(G-expected/729)==0
    # Each removed source denominator is a nonzero constant times a power
    # of -(g+(1-g)*r^3), strictly nonzero for r>0,0<g<1.
    modes=saved['source_mode_identities'];expectedpowers={(5,3):6,(6,2):7,(6,4):10}
    for row in modes:
        mode=tuple(row['mode']);den=parse(row['denominator']);power=expectedpowers[mode]
        ratio=S.cancel(den/(g*r**3-g-r**3)**power)
        assert not ratio.free_symbols and ratio!=0
        const=parse(row['removed_nonzero_constant']);assert not const.free_symbols and const!=0
    output={'status':'PASS','generator_sha256':hashlib.sha256(genpath.read_bytes()).hexdigest(),
            'exceptional_certificate_sha256':hashlib.sha256(cpath.read_bytes()).hexdigest(),
            'source_result_sha256':hashlib.sha256(resultpath.read_bytes()).hexdigest(),
            'reviewer_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'exact_exceptional_cubic_identities':2,'independent_resultants':2,
            'explicit_resultant_bezout_verified':True,'strict_domain_denominators_verified':3,
            'python':platform.python_version(),'sympy':S.__version__,
            'scope':'Independent finite algebraic identity check; source mode extraction, positive tomography, graft and sharpness bridges have separate reviewed evidence.'}
    Path(__file__).with_name('uniform-pad-head-review-results.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__':main()
