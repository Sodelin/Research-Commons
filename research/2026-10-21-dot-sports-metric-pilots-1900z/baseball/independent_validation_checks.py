"""Synthetic accounting diagnostics, not an empirical baseball backtest."""
from fractions import Fraction as F
# All three players were eligible at forecast time. Future qualification removes two.
players = [('A',200,F(80)),('B',20,F(4)),('C',0,F(0))]
qualified = [x for x in players if x[1]>=200]
assert len(qualified)==1 and len(players)==3
qualified_rate=sum(x[2] for x in qualified)/sum(x[1] for x in qualified)
all_exposure_rate=sum(x[2] for x in players)/sum(x[1] for x in players)
assert qualified_rate==F(2,5) and all_exposure_rate==F(21,55)
# Zero-exposure player's rate is undefined, not zero.
rates=[w/n if n else None for _,n,w in players]
assert rates==[F(2,5),F(1,5),None]
# Fixed hypothetical strata: no skill change, different opponent mix.
stratum_rates={'easy':F(2,5),'hard':F(1,5)}
old_mix={'easy':F(1,4),'hard':F(3,4)}
new_mix={'easy':F(3,4),'hard':F(1,4)}
def avg(m):return sum(m[k]*stratum_rates[k] for k in m)
assert avg(new_mix)-avg(old_mix)==F(1,10)
assert avg({'easy':F(1,2),'hard':F(1,2)})==F(3,10)
# Target totals need a joint model; multiplying marginal means loses covariance.
states=[(F(200),F(2,5)),(F(20),F(1,5))]
actual=sum(n*r for n,r in states)/2
product=(sum(n for n,r in states)/2)*(sum(r for n,r in states)/2)
assert actual==42 and product==33
# Overlapping forward windows share outcomes despite distinct cutoffs.
w1=set(range(1,61));w2=set(range(31,91));assert len(w1&w2)==30
print('PASS: 7 exact assertions in synthetic accounting fixtures.')
print('Qualification changes evaluated cohort 3 -> 1; rates 2/5 versus21/55.')
print('Opponent-mix-only apparent improvement=1/10; standardized rate=3/10.')
print('E[N*r]=42 versus E[N]*E[r]=33; overlap=30 outcome days.')
print('No MLB records or predictive accuracy evaluated.')
