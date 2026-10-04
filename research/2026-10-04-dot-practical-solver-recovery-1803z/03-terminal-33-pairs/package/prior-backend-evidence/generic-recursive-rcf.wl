(* Derived from the pinned Commons constructor; singleton simplex normalization only. *)
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
G7WinFromHistory[models_List,supports_List,maxPrograms_Integer,
             rowSites_List,rowCap_Integer,siteCap_Integer,initialHistory_List,initialUsedRows_List,initialUsedSites_List] := Module[
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
       y=Table[Unique["y"],{q}];
       If[Length[supp]==1,
         (* Positive singleton-simplex weight is EXACTLY1. Eliminate it before QE. *)
         wfull=ReplacePart[ConstantArray[0,k],First[supp]->1];
         qForAll[y,win[Append[hist,{wfull,y}],depth-1,nr,ns]],
         w=Table[Unique["w"],{Length[supp]}];
         wfull=ReplacePart[ConstantArray[0,k],Thread[supp->w]];
         qExists[w,And@@Thread[w>0] && Total[w]==1 &&
           qForAll[y,win[Append[hist,{wfull,y}],depth-1,nr,ns]]]]]],
   {supp,supports}];
 win[initialHistory,Min[maxPrograms,k],initialUsedRows,initialUsedSites]
];
G7Decide[models_List,supports_List,maxPrograms_Integer,
         rowSites_List,rowCap_Integer,siteCap_Integer] :=
 Resolve[G7WinFormula[models,supports,maxPrograms,rowSites,rowCap,siteCap],Reals];

G7WinFormula[models_List,supports_List,maxPrograms_Integer,rowSites_List,rowCap_Integer,siteCap_Integer] :=
 G7WinFromHistory[models,supports,maxPrograms,rowSites,rowCap,siteCap,{},{},{}];

(* An online exact-RCF selector for REAL ALGEBRAIC encoded response histories.
   This does not claim a generic symbolic CAD selector for all real histories. *)
ClearAll[G7EncodedHistoryNextAction];
G7EncodedHistoryNextAction[models_List,supports_List,rowSites_List,
 budget:{_Integer,_Integer,_Integer},history_List] := Module[
 {k,q,usedRows,usedSites,remaining,hom,targets,validHistory,supp,nr,ns,
  w,wfull,y,relation,reduced,instance,weights,verified,answer},
 If[models==={} || Min[budget]<0,Return[<|"Status"->"INVALID_POLICY_INPUT"|>]];
 {k,q}=Dimensions[models[[1]]["Laws"]];
 If[Length[rowSites]!=k || !And@@(Dimensions[#["Laws"]]=={k,q}& /@ models),
   Return[<|"Status"->"INVALID_SOURCE_MODEL_DIMENSIONS"|>]];
 validHistory=And@@Table[
   ListQ[h] && Length[h]==2 && Length[h[[1]]]==k && Length[h[[2]]]==q &&
   FreeQ[h,_Real] && And@@(TrueQ[Element[#,Reals] && Element[#,Algebraics]]& /@ Flatten[h]) &&
   Total[h[[1]]]==1 && And@@Thread[h[[1]]>=0] && Total[h[[2]]]==1 && And@@Thread[h[[2]]>=0] &&
   MemberQ[Sort /@ supports,Flatten[Position[h[[1]],x_/;TrueQ[x>0],{1}]]],{h,history}];
 If[!TrueQ[validHistory],Return[<|"Status"->"UNSUPPORTED_OR_INVALID_ENCODED_HISTORY"|>]];
 usedRows=Union@@(Flatten[Position[#[[1]],x_/;TrueQ[x>0],{1}]]& /@ history);
 usedSites=Union@@(Flatten[rowSites[[Flatten[Position[#[[1]],x_/;TrueQ[x>0],{1}]]]]]& /@ history);
 remaining=budget[[1]]-Length[history];
 If[remaining<0 || Length[usedRows]>budget[[2]] || Length[usedSites]>budget[[3]],
   Return[<|"Status"->"EXECUTED_PATH_ALREADY_EXCEEDS_BUDGET"|>]];
 hom=Resolve[G7WinFromHistory[models,supports,0,rowSites,budget[[2]],budget[[3]],history,usedRows,usedSites],Reals];
 If[hom===True,
   targets=DeleteDuplicates[Cases[Table[
     If[Resolve[qExists[m["Vars"],m["Domain"] && qCons[m,history]],Reals]===True,m["Target"],Nothing],{m,models}],_]];
   Return[If[Length[targets]==1,<|"Status"->"IDENTIFIED_TARGET","Target"->First[targets]|>,
     If[targets==={},<|"Status"->"NO_ADMITTED_SOURCE_MATCHES_ENCODED_HISTORY"|>,
       <|"Status"->"UNKNOWN_TERMINAL_CONSISTENCY"|>]]]];
 If[hom=!=False,Return[<|"Status"->"UNKNOWN_HOMOGENEITY_BACKEND"|>]];
 If[remaining==0,Return[<|"Status"->"BUDGET_EXHAUSTED_TARGET_AMBIGUOUS"|>]];
 answer=Missing["NoAction"];
 Do[
   nr=Union[usedRows,supp];ns=Union[usedSites,Flatten[rowSites[[supp]]]];
   If[Length[nr]<=budget[[2]] && Length[ns]<=budget[[3]],
     y=Table[Unique["response"],{q}];
     If[Length[supp]==1,
       weights={1};wfull=ReplacePart[ConstantArray[0,k],First[supp]->1];
       verified=Resolve[qForAll[y,G7WinFromHistory[models,supports,remaining-1,
         rowSites,budget[[2]],budget[[3]],Append[history,{wfull,y}],nr,ns]],Reals],
       w=Table[Unique["weight"],{Length[supp]}];
       wfull=ReplacePart[ConstantArray[0,k],Thread[supp->w]];
       relation=And@@Thread[w>0] && Total[w]==1 && qForAll[y,G7WinFromHistory[
         models,supports,remaining-1,rowSites,budget[[2]],budget[[3]],Append[history,{wfull,y}],nr,ns]];
       reduced=Reduce[relation,w,Reals];
       If[reduced===False,Continue[]];
       If[!FreeQ[reduced,_Reduce|_Resolve|$Failed|$Aborted],answer=<|"Status"->"UNKNOWN_ACTION_RELATION_BACKEND"|>;Break[]];
       instance=FindInstance[reduced,w,Reals,1];
       If[!ListQ[instance] || instance==={},answer=<|"Status"->"UNKNOWN_ALGEBRAIC_ACTION_SELECTION"|>;Break[]];
       weights=w/.First[instance];verified=Resolve[relation/.First[instance],Reals]
     ];
     If[verified===True,answer=<|"Status"->"NEXT_EXACT_PROGRAMME","Support"->supp,
       "Weights"->weights,"RemainingCallsAfterExecution"->remaining-1,
       "UsedConfigurationsAfterExecution"->nr,"UsedOriginalSitesAfterExecution"->ns|>;Break[]];
     If[verified=!=False,answer=<|"Status"->"UNKNOWN_SELECTED_ACTION_VERIFICATION"|>;Break[]]
   ],{supp,supports}];
 If[AssociationQ[answer],answer,<|"Status"->"NO_IDENTIFYING_ACTION_WITHIN_REMAINING_BUDGET"|>]
];

models={<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->{{1 - 2/3*survivalA,(1/3)*survivalA,(1/3)*survivalA},{1 - 2/3*survivalB,(1/3)*survivalB,(1/3)*survivalB}},"Target"->0|>,
<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->{{1 - 2/3*survivalA,(1/3)*survivalA,(1/3)*survivalA},{(1/3)*survivalB,1 - 2/3*survivalB,(1/3)*survivalB}},"Target"->1|>,
<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->{{1 - 2/3*survivalA,(1/3)*survivalA,(1/3)*survivalA},{(1/3)*survivalB,(1/3)*survivalB,1 - 2/3*survivalB}},"Target"->2|>,
<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->{{(1/3)*survivalA,1 - 2/3*survivalA,(1/3)*survivalA},{1 - 2/3*survivalB,(1/3)*survivalB,(1/3)*survivalB}},"Target"->1|>,
<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->{{(1/3)*survivalA,1 - 2/3*survivalA,(1/3)*survivalA},{(1/3)*survivalB,1 - 2/3*survivalB,(1/3)*survivalB}},"Target"->3|>,
<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->{{(1/3)*survivalA,1 - 2/3*survivalA,(1/3)*survivalA},{(1/3)*survivalB,(1/3)*survivalB,1 - 2/3*survivalB}},"Target"->4|>,
<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->{{(1/3)*survivalA,(1/3)*survivalA,1 - 2/3*survivalA},{1 - 2/3*survivalB,(1/3)*survivalB,(1/3)*survivalB}},"Target"->2|>,
<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->{{(1/3)*survivalA,(1/3)*survivalA,1 - 2/3*survivalA},{(1/3)*survivalB,1 - 2/3*survivalB,(1/3)*survivalB}},"Target"->4|>,
<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->{{(1/3)*survivalA,(1/3)*survivalA,1 - 2/3*survivalA},{(1/3)*survivalB,(1/3)*survivalB,1 - 2/3*survivalB}},"Target"->5|>};
supports={{1},{2},{1,2}};
rowSites={{1},{1}};

<|"OneConfigurationBudget"->TimeConstrained[G7Decide[models,supports,1,rowSites,1,1],12,"UNKNOWN_TIMEOUT"],"TwoConfigurationBudget"->TimeConstrained[G7Decide[models,supports,1,rowSites,2,1],20,"UNKNOWN_TIMEOUT"],"NextAction"->TimeConstrained[G7EncodedHistoryNextAction[models,supports,rowSites,{1,2,1},{}],20,"UNKNOWN_TIMEOUT"]|>