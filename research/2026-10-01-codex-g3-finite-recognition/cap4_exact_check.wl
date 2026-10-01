(* Exact cap-four compression witness; Wolfram Language. *)
Clear[a,b,p];
ks={1,3,6};
xs={4/5,2/5,3/5,3/10};
ws={2/5,1/5,4/15,2/15};
ms=Table[ws.(xs^k),{k,ks}];
eqs=Table[p*a^ks[[j]]+(1-p)*b^ks[[j]]==ms[[j]],{j,3}];
sol=First[FindInstance[0<a<b<1&&0<p<1&&(And@@eqs),{a,b,p},Reals]];
Print[ms];
Print[FullSimplify[RootReduce[eqs/.sol]]];
Print[FullSimplify[(0<a<b<1&&0<p<1)/.sol]];
Print[N[{a,b,p}/.sol,12]];
(* Executed exact results: moments {3/5,697/2500,295539/2500000};
   equalities {True,True,True}; strict inequalities True.
   Approximate parameters are orientation only.
   General source catalogue and proof-assistant verification not executed. *)
