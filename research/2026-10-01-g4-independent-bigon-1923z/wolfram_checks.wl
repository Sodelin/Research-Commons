(* Exact finite checks for ASTRA-G4-INDEPENDENT-BIGON-20261001-1923Z.
   Run in Wolfram Language. The universal cutoff search is NOT run by default.
   Timeouts are unknown, never equivalence or impossibility certificates.
   This packaged wrapper restates successful individual connector calls;
   it was not itself run as one local batch during the session. *)
ClearAll[pp, aa, fiber, equivalent, cutoffSearch, x, y, g, u, v, w, z];
pp[k_Integer, z_] := Expand[
  Product[Binomial[l, 2], {l, 2, k}] *
  Sum[z^Binomial[j, 2]/Product[
    If[l == j, 1, Binomial[l, 2] - Binomial[j, 2]], {l, 1, k}], {j, 1, k}]];
aa[k_Integer] := Expand[g^k pp[k, x] + (1-g)^k pp[k, y]];
fiber[ref_List] := Reduce[
  And @@ Table[aa[k] == (aa[k] /. Thread[{x,y,g} -> ref]), {k,2,4}]
   && 0<x<1 && 0<y<1 && 0<g<1, {x,y,g}, Reals];
refs = {{1/2,3/4,1/3}, {1/2,1/2,1/2}, {1/4,3/4,1/2}, {1/2,1/2,1/3}};
Print[<|"ExactReferenceFibers" -> Table[
  <|"reference" -> ref, "fiber" -> TimeConstrained[fiber[ref],30,"TIME_LIMIT"]|>,
  {ref, refs}]|>];
refRules = {x->9/10,y->1/3,g->13/25};
eq = And @@ Table[aa[k] == (aa[k] /. refRules), {k,2,4}];
box = 65/100<x<66/100 && 98/100<y<99/100 && 72/100<g<73/100;
Print[<|"SummaryCollisionAndHigherSeparation" -> TimeConstrained[
  Resolve[Exists[{x,y,g},eq && box && aa[5] != (aa[5] /. refRules)],Reals],
  30,"TIME_LIMIT"]|>];

(* Proven finite search principle; not executed here for a universal cutoff.
   A bounded call may return Missing without contradicting eventual termination.
   Each UNSAT result has to be literal False. No plateau is accepted. *)
equivalent = (x==u && y==v && g==w) || (x==v && y==u && g==1-w);
cutoffSearch[max_Integer?Positive] := Module[{m, decision, domain},
  domain = And @@ (Function[t, 0<t<1] /@ {x,y,g,u,v,w});
  Do[
    decision = Resolve[Exists[{x,y,g,u,v,w}, domain && !equivalent &&
      And @@ Table[aa[k] == (aa[k] /. {x->u,y->v,g->w}),{k,2,m}]],Reals];
    If[decision === False, Return[<|"summary_cutoff"->m,"certificate"->False|>]],
    {m,2,max}];
  Missing["NoCertificateThroughRequestedCap",max]
];
(* Optional stronger full-cap-four diagnostic, not run by default.
   The analogous six-variable connector call returned upstream 502.
   The following scalar is the particular forest with two specified cherries. *)
b22 = Expand[g^4(x/5-x^3/3+2x^6/15) +
  (1-g)^4(y/5-y^3/3+2y^6/15) + 2g^2(1-g)^2(1-x)(1-y)];
