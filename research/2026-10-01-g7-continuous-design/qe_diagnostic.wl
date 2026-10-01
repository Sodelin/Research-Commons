(* Reproduces the successful direct continuous-weight QE diagnostic.
   Two abstract Bernoulli model images, not a biological all-source optimum. *)
Module[{w,a,b,t,u,dom,one,two,sep},
 dom=0<t<1/2 && 0<u<1/2;
 one=Resolve[Exists[w,0<=w<=1 && ForAll[{t,u},Implies[dom,t!=u+(1-w)/4]]],Reals];
 sep=Reduce[0<=a<=1 && 0<=b<=1 && ForAll[{t,u},Implies[dom,Not[t==u+(1-a)/4 && t==u+(1-b)/4]]],{a,b},Reals];
 two=Resolve[Exists[{a,b},0<=a<=1 && 0<=b<=1 && ForAll[{t,u},Implies[dom,Not[t==u+(1-a)/4 && t==u+(1-b)/4]]]],Reals];
 <|"one_continuous_program_identifies"->one,"two_continuous_programs_identify"->two,
   "two_weight_identification_region"->sep,
   "expected_region_equivalence"->Resolve[ForAll[{a,b},Equivalent[sep,0<=a<=1 && 0<=b<=1 && a!=b]],Reals]|>
]
