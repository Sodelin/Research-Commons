exec(open(__import__('pathlib').Path(__file__).with_name('probe.py')).read().split('best=(0,None)')[0])
best=(0,None)
for d,n,m,count in [(2,1,3,1000),(2,3,3,1000),(2,6,3,150),(3,2,3,300),(4,2,3,200)]:
 for trial in range(count):
  rs=[]
  for i in range(m):
   z=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));u=np.linalg.qr(z)[0];v=np.exp(rng.uniform(-20,0,d));v/=v.sum();rs.append((u*v)@u.conj().T)
  p=np.exp(rng.uniform(-10,0,m));p/=p.sum();r,de=calc(rs,p,n)
  if de<1e-10:continue
  ratio=r/de
  if ratio>best[0]:best=(ratio,(d,n,m,trial,r,de));np.savez(str(__import__('pathlib').Path(__file__).with_name('adversarial_best.npz')),rs=rs,p=p,n=n)
 print(d,n,m,'best',best,flush=True)
