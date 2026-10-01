(* Exact pooled-program strategy formula for a supplied finite polynomial-law
   census. It does not enumerate biological source topologies. Each model:
   <|"Vars"->{parameters}, "Domain"->positiveSourceFormula,
     "Laws"->(baseRows x observedCoordinates matrix), "Target"->label|>.
   Supports explicitly list the permitted positive-weight row sets.
   Node weights may depend on all previous exact response vectors.
   Complete Resolve over Reals is used; no floating or finite-grid weights. *)
ClearAll[qExists,qForAll,qFresh,qCons,G7WinFormula,G7Decide];
qExists[v_List,f_] := If[v==={},f,With[{vv=v,ff=f},Exists[vv,ff]]];
qForAll[v_List,f_] := If[v==={},f,With[{vv=v,ff=f},ForAll[vv,ff]]];
qFresh[m_Association] := m /. Thread[m["Vars"] -> Table[Unique["p"],{Length[m["Vars"]]}]];
qCons[m_Association,hist_List] := And@@Table[And@@Thread[h[[1]].m["Laws"]==h[[2]]],{h,hist}];
G7WinFormula[models_List,supports_List,maxPrograms_Integer,
             rowSites_List,rowCap_Integer,siteCap_Integer] := Module[
 {k,q,win,hom},
 If[models==={} || maxPrograms<0 || rowCap<0 || siteCap<0,Return[$Failed]];
 {k,q}=Dimensions[models[[1]]["Laws"]];
 If[Length[rowSites]!=k || !And@@(Dimensions[#["Laws"]]=={k,q}& /@ models),Return[$Failed]];
 If[!And@@(Length[#]>0 && DuplicateFreeQ[#] && And@@(IntegerQ[#] && 1<=#<=k& /@ #)& /@ supports),Return[$Failed]];
 hom[hist_] := And@@Flatten[Table[
   If[models[[i]]["Target"]===models[[j]]["Target"],True,
     Module[{a=qFresh[models[[i]]],b=qFresh[models[[j]]]},
       Not[qExists[Join[a["Vars"],b["Vars"]],a["Domain"] && b["Domain"] && qCons[a,hist] && qCons[b,hist]]]]],
   {i,Length[models]},{j,i+1,Length[models]}]];
 win[hist_,0,ur_,us_] := hom[hist];
 win[hist_,depth_,ur_,us_] := hom[hist] || Or@@Table[
   Module[{nr=Union[ur,supp],ns=Union[us,Flatten[rowSites[[supp]]]],w,wfull,y},
     If[Length[nr]>rowCap || Length[ns]>siteCap,False,
       w=If[Length[supp]==1,{1},Table[Unique["w"],{Length[supp]}]];
       wfull=ReplacePart[ConstantArray[0,k],Thread[supp->w]];
       y=Table[Unique["y"],{q}];
       qExists[Select[w,!NumberQ[#]&],And@@Thread[w>0] && Total[w]==1 &&
         qForAll[y,win[Append[hist,{wfull,y}],depth-1,nr,ns]]]]],
   {supp,supports}];
 win[{},Min[maxPrograms,k],{},{}]
];
G7Decide[models_List,supports_List,maxPrograms_Integer,
         rowSites_List,rowCap_Integer,siteCap_Integer] :=
 Resolve[G7WinFormula[models,supports,maxPrograms,rowSites,rowCap,siteCap],Reals];

(* Safe preprocessing only: a singleton positive support has weight 1.
   Original code otherwise retained. Diagnostics distinguish passes/failures. *)
Clear[x,z,u,v]; f[t_,a_]:=Table[If[j==t,1-2 a/3,a/3],{j,3}]; laws={f[1,x],f[2,x],f[3,x],(f[1,x]+f[2,z])/2,(f[1,x]+f[3,z])/2,(f[2,x]+f[3,z])/2}; If[Dimensions[laws]!={6,3},Abort[]]; pairs=Subsets[Range[6],{2}]; result=Table[Resolve[Exists[{x,z,u,v},0<x<1&&0<z<1&&0<u<1&&0<v<1&&And@@Thread[laws[[pair[[1]]]]==(laws[[pair[[2]]]]/.{x->u,z->v})]],Reals],{pair,pairs}]; <|"dimensions"->Dimensions[laws],"pairs"->pairs,"distinct_target_collisions"->result,"pass"->(Length[result]==15&&AllTrue[result,SameQ[#,False]&])|>
(* Exact evaluator returned dimension {6,3}, fifteen False collisions, pass True.
   Original recursive positive-tree call: 15-second TIMEOUT.
   Normalized singleton recursive positive-tree budgets {0,1}: {False,True}.
   Larger six-target recursive call: $Aborted, no certificate. *)
