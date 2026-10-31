import sympy as S,json
R,M,E,ra,rb,ka,kb,ba,bb=S.symbols('R M E ra rb ka kb ba bb')
def step(state,r,k,b):
 R,M,E=state
 return R+r,M-b*R,E+S.Rational(9,2)*R*k-b*R**2
ab=step(step((R,M,E),ra,ka,ba),rb,kb,bb)
ba_=step(step((R,M,E),rb,kb,bb),ra,ka,ba)
dm=ba*rb-bb*ra
de=S.Rational(9,2)*(ra*kb-rb*ka)+2*R*dm+ba*rb**2-bb*ra**2
assert S.expand(ab[1]-ba_[1]-dm)==0
assert S.expand(ab[2]-ba_[2]-de)==0
sub={ra:S.Rational(131,2048),rb:S.Rational(-349,131072),ka:S.Rational(3649,2949120),kb:S.Rational(-85567,1509949440),ba:S.Rational(1,32),bb:S.Rational(49,256),R:0}
values=[S.factor(v.subs(sub)) for v in [ra*kb-rb*ka,dm,de]]
assert values==[-S.Rational(340423,1030792151040),-S.Rational(51701,4194304),-S.Rational(2156151911,2748779069440)]
print(json.dumps({'status':'PASS','method':'exact symbolic recurrence and rational actual-cell swap only','swap_values':list(map(str,values))},indent=2))
