#!/usr/bin/env python3
"""Independent finite transcription controls; never a nonregularity test."""
import json
w='0'
while len(w)<513:w=''.join({'0':'01','1':'00'}[x] for x in w)
N=256
P=[0];C=[False]
for end in range(1,N+2):
 candidates=[]
 for start in range(end):
  f=w[start:end]
  if f==f[::-1]:candidates.append((P[start]+1,C[start] or f=='1'))
 best=min(x for x,_ in candidates)
 P.append(best);C.append(any(mark for cost,mark in candidates if cost==best))
edgechecks=0
for a in range(129):
 for b in range(a,129):
  f=w[a:b];pal=f==f[::-1];L=b-a
  if L<2:pred=True
  elif L%2==0:pred=L==2 and w[a//2]=='1'
  else:
   g=w[a//2:b//2];pred=g==g[::-1]
  assert pal==pred;edgechecks+=1
for n in range(129):
 k=P[n]
 expected=(k,k) if C[n] else (k+k%2,k+1-k%2)
 assert (P[2*n],P[2*n+1])==expected
 assert C[n]==(P[2*n+1]-P[2*n]==0)
 for bit in (0,1):
  assert P[2*n+bit]==P[n]+(not C[n])*(P[n]%2!=bit)
  assert P[2*n+bit]%2==(P[n]%2 if C[n] else bit)
 if n:
  values=[P[2*i+1] for i in range(n) if w[i:n]==w[i:n][::-1]]
  if w[n-1]=='1':values.append(P[2*n-2])
  assert P[2*n]==1+min(values)
 values=[P[2*i] for i in range(n+1) if w[i:n]==w[i:n][::-1]]
 if n and w[n-1]=='1':values.append(P[2*n-1])
 assert P[2*n+1]==1+min(values)
print(json.dumps({'status':'PASS_FINITE_INDEPENDENT_LIFT_CONTROLS','palindrome_edge_cases':edgechecks,'direct_optimal_marked_factorization_prefixes':N+2,'lift_and_marked_identity_n_range':[0,128],'coupled_recurrences_checked':True,'weighted_transition_identities_checked':True,'finite_controls_prove_nonregularity':False},indent=2))
