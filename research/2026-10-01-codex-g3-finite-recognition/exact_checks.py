from fractions import Fraction as F
import json

def h(u,t):
    a=u*(1-t)
    b=u+(1-u)*t
    return (1-u)*a**3+u*b**3

def verify(u,t):
    a=u*(1-t)
    b=u+(1-u)*t
    v=h(u,t)
    assert 0<a<u<b<1
    assert (1-u)*a+u*b == u
    assert u**3<v<u
    c=1-(1-b)/5
    q=a/b
    entry=b/c**2
    assert all(0<x<1 for x in [c,q,entry,c*q,u,1-u])
    assert entry*c*c == b
    assert entry*c*q*c == a
    pair=(u-v)/2
    full=(1-F(3,2)*u+v/2)/3
    assert pair>0 and full>0
    assert v+3*pair+3*full == 1
    assert v+2*pair == u
    assert pair+3*full == 1-u
    derivative=3*u*(1-u)*(b*b-a*a)
    cubic_derivative=6*u*u*(1-u)*t+3*u*(1-u)*(1-2*u)*t*t
    assert derivative == cubic_derivative and derivative>0
    assert h(u,0)==u**3 and h(u,1)==u
    assert v == u**3+3*u*u*(1-u)*t*t+u*(1-u)*(1-2*u)*t**3

def recognized_common_pair(u,v):
    return 0<u<1 and u**3<=v<u

def main():
    cases=0
    for i in range(1,20):
        u=F(i,20)
        for j in range(1,20):
            verify(u,F(j,20))
            cases+=1
        assert recognized_common_pair(u,u**3)
        for v in [u, u+F(1,100), u**3-F(1,100)]:
            assert not recognized_common_pair(u,v)
    for u in [F(0),F(1),F(-1),F(2)]:
        assert not recognized_common_pair(u,u**3)
    # Independent routing, one genuine positive equal-arm bigon.
    x=F(1,10)
    u=(1+x)/2
    v=(x**3+3*x)/4
    assert v<u**3
    # Genuine positive ordinary connectors preserve this negative control.
    z=F(9,10)
    assert v*z**3<(u*z)**3
    result={
      "status":"passed",
      "rational_positive_constructions":cases,
      "ordinary_equality_cases":19,
      "common_boundary_rejections":61,
      "independent_negative_controls":2,
      "scope":"exact rational cap-three formulas; no general G3 recognizer"
    }
    print(json.dumps(result,indent=2))

if __name__=="__main__":
    main()
