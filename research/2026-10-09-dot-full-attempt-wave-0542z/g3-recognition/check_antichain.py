from fractions import Fraction as F
from itertools import product

z=a=F(3,4); c=z*a

def direct(mode,d):
    x,y=F(1,2)-d,F(1,2)+d
    if mode=='COMMON':
        p=c*(x+y)/2
        q=c**3*(x**3+y**3)/2
    else:
        def survival(k):
            total=F(0)
            for coins in product((0,1),repeat=k):
                left=coins.count(0); right=k-left
                total += F(1,2)**k*x**(left*(left-1)//2)*y**(right*(right-1)//2)
            return total
        p=c*survival(2); q=c**3*survival(3)
    r=F(3,2)*(p-q); s=1-q-r
    probs=[q]+[r/3]*3+[s/3]*3
    assert all(v>=0 for v in probs) and sum(probs)==1
    return p,q,(r+s)/3,s/3

for mode in ['COMMON','INDEPENDENT']:
    rows=[]
    for n in range(1,33):
        d=F(1,n+5)
        p,q,u,v=direct(mode,d)
        expected_p=c*(F(1,2) if mode=='COMMON' else F(3,4))
        expected_q=c**3*((F(1,8)+F(3,2)*d*d) if mode=='COMMON' else (F(13,32)+F(3,8)*d*d))
        assert p==expected_p and q==expected_q
        assert u==(1-q)/3 and v==F(1,3)-p/2+q/6
        rows.append((d,p,q,u,v))
    for i in range(len(rows)):
        for j in range(i+1,len(rows)):
            assert rows[i][1]==rows[j][1]
            assert (rows[i][3]-rows[j][3])*(rows[i][4]-rows[j][4])<0
    print(mode, '32 direct rational controls and 496 incomparable pairs PASS')
    print('first',*(str(x) for x in rows[0]))
    print('second',*(str(x) for x in rows[1]))
print('No simulation, source inverse, compiler, QE, or proof-assistant run.')
