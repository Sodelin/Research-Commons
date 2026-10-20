exec(open(__import__('pathlib').Path(__file__).with_name('probe.py')).read().split('best=(0,None)')[0])
def logm(a):
 v,u=eigh(a);return (u*np.log(np.maximum(v,1e-15)))@u.conj().T
worst=0
for z in range(10000):
 d=3;e=3;k=3;a=rng.normal(size=(e*k,d))+1j*rng.normal(size=(e*k,d));v=np.linalg.qr(a)[0];ks=[v[i*e:(i+1)*e]for i in range(k)]
 def phi(x):return sum(k@x@k.conj().T for k in ks)
 a=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));rho=a@a.conj().T;rho/=np.trace(rho)
 s=phi(np.eye(d));out=phi(rho);delta=-ent(rho)+ent(out)+np.trace(out@logm(s)).real
 t=power(s,-.25)@phi(power(rho,.5))@power(s,-.25);x=np.trace(t@t).real
 gap=delta+np.log(x)
 if gap<worst:worst=gap;print('worst',z,gap,delta,x,flush=True)
 if gap < -1e-7:break
print('done',worst)
