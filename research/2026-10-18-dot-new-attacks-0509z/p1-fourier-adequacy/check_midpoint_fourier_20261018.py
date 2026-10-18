"""Finite checks for the midpoint Fourier adequacy note.
Exact rational algebra controls plus explicitly noncertifying floating diagnostics.
No all-dimension proof, optimization-cost theorem, or state-preparation claim.
"""
import sympy as sp
import numpy as np
from scipy.linalg import expm, solve_sylvester, eigvalsh
from scipy.integrate import quad_vec

r=sp.Matrix([[sp.Rational(3,5),0],[0,sp.Rational(2,5)]])
s=sp.Matrix([[sp.Rational(1,2),sp.Rational(1,8)],[sp.Rational(1,8),sp.Rational(1,2)]])
zvar=sp.Matrix(2,2,sp.symbols('z0:4'))
sol=sp.solve(list(s*zvar+zvar*r+2*r),list(zvar),dict=True)[0]
z=zvar.subs(sol)
w=sp.Matrix([[sp.Rational(1,7),sp.Rational(2,9)],[-sp.Rational(1,5),sp.Rational(3,11)]])
def Q(x):return sp.trace(r*x.H*x+s*x*x.H)/2
def F(x):return 1+sp.trace(r*(x+x.H))+Q(x)
assert s*z+z*r==-2*r
assert z != z.H
assert sp.simplify(F(z+w)-F(z)-Q(w))==0
assert sp.simplify(F(-sp.eye(2)+w)-sp.trace((r-s)*(w+w.H))/2-Q(w))==0
print('EXACT PASS: noncommuting rational Sylvester orientation and both square expansions')
print('Exact optimizer:',str(z))

I=np.eye(2,dtype=complex);X=np.array([[0,1],[1,0]],complex)
Y=np.array([[0,-1j],[1j,0]],complex);Z=np.diag([1,-1]).astype(complex)
H=.3*np.kron(X,I)+.2*np.kron(Z,Z)
K=-.4*np.kron(I,Y)+.1*np.kron(X,X)
beta=.7;M=15;eps=.2
er=expm(-beta*H);es=expm(-beta*K);rho=er/np.trace(er);sig=es/np.trace(es)
b=float(np.real(np.log(np.trace(er))-np.log(np.trace(es))))
star=solve_sylvester(sig/2,rho/2,-rho)
eta=min(1,np.pi*eps/(128*beta*M));upper=np.log(128/eps)/np.pi

def U(t):return np.exp(1j*t*b)*expm(-1j*t*beta*K)@expm(1j*t*beta*H)
def integ(t):return (U(t)-U(-t))/(1j*np.sinh(np.pi*t))
zc=-np.eye(4)+quad_vec(integ,eta,upper,epsabs=1e-12,epsrel=1e-12)[0]
def q(x):return float(np.real(np.trace(rho@x.conj().T@x+sig@x@x.conj().T))/2)
def f(x):return float(1+2*np.real(np.trace(rho@x))+q(x))
B=1+2/np.pi*np.log(1/np.tanh(np.pi*eta/2))
assert np.linalg.norm(sig@star+star@rho+2*rho)<1e-12
assert np.sqrt(q(zc-star))<=eps/8
assert np.linalg.norm(zc,2)<=B
assert abs(f(zc)-f(star)-q(zc-star))<1e-12
tracegap=float(sum(abs(eigvalsh(rho-sig))))
assert f(star)<=-tracegap**2/4+1e-12
R=(B+2)**2
C=np.kron(zc+zc.conj().T+zc.conj().T@zc/2,np.eye(4))+np.kron(np.eye(4),zc@zc.conj().T/2)
effect=(R*np.eye(16)-(np.eye(16)+C))/(2*R)
assert min(eigvalsh(effect))>=-1e-12 and max(eigvalsh(effect))<=1+1e-12
assert abs(np.real(np.trace(np.kron(rho,sig)@effect))-(.5-f(zc)/(2*R)))<1e-12

# Check the displayed null moment estimate for a fixed complex W.
W=zc+np.eye(4);HW=(W+W.conj().T)/2
D=np.kron(HW,np.eye(4))-np.kron(np.eye(4),HW)+np.kron(W.conj().T@W,np.eye(4))/2+np.kron(np.eye(4),W@W.conj().T)/2
qn=float(np.real(np.trace(rho@(W.conj().T@W+W@W.conj().T)))/2)
nul=np.kron(rho,rho)
mean=float(np.real(np.trace(nul@D)));second=float(np.real(np.trace(nul@D@D)))
assert abs(mean-qn)<1e-12
assert second<=(4+2*np.linalg.norm(W,2)**2)*qn+1e-12
print('DIAGNOSTIC PASS: two-qubit Fourier truncation, weighted error, effect normalization and null moment')
print({'full_trace_gap':tracegap,'eta':eta,'S':upper,'weighted_truncation_error':float(np.sqrt(q(zc-star))),
       'loss_exact':f(star),'loss_truncated':f(zc),'truncated_operator_norm':float(np.linalg.norm(zc,2)),
       'proven_norm_envelope_B':float(B),'null_mean':mean,'null_second_moment':second})
print('No numerical diagnostic is a substitute for the parameterized hand proof.')
