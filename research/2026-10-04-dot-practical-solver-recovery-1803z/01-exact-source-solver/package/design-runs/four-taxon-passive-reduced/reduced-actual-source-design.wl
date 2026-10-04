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
       w=Table[Unique["w"],{Length[supp]}];
       wfull=ReplacePart[ConstantArray[0,k],Thread[supp->w]];
       y=Table[Unique["y"],{q}];
       qExists[w,And@@Thread[w>0] && Total[w]==1 &&
         qForAll[y,win[Append[hist,{wfull,y}],depth-1,nr,ns]]]]],
   {supp,supports}];
 win[{},Min[maxPrograms,k],{},{}]
];
G7Decide[models_List,supports_List,maxPrograms_Integer,
         rowSites_List,rowCap_Integer,siteCap_Integer] :=
 Resolve[G7WinFormula[models,supports,maxPrograms,rowSites,rowCap,siteCap],Reals];

models={<|"Vars"->{survival},"Domain"->0<survival<1,"Laws"->{{1 - 2/3*survival,(1/3)*survival,(1/3)*survival}},"Target"->0|>,<|"Vars"->{survival},"Domain"->0<survival<1,"Laws"->{{(1/3)*survival,1 - 2/3*survival,(1/3)*survival}},"Target"->1|>,<|"Vars"->{survival},"Domain"->0<survival<1,"Laws"->{{(1/3)*survival,(1/3)*survival,1 - 2/3*survival}},"Target"->2|>};
answer0=TimeConstrained[G7Decide[models,{{1}},0,{{}},0,0],15,"UNKNOWN_TIMEOUT"];
answer1=TimeConstrained[G7Decide[models,{{1}},1,{{}},1,0],15,"UNKNOWN_TIMEOUT"];
policyCorrect=Resolve[And@@Table[ForAll[s,0<s<1,1-2s/3>s/3],{3}],Reals];
<|"ActualSourceCount"->15,"ExactSourceImageCount"->3,"ZeroCallBudget"->answer0,"OnePassiveCallBudget"->answer1,"LargestCFPolicyCorrect"->policyCorrect,"Scope"->"complete four-taxon positive original-tree class; exact unrooted law; free edge clocks"|>
