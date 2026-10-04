(* G7 semialgebraic fibre selector, derived from the accepted master algorithm.
   History variables precede action variables in every complete CAD.
   Unsupported cylinder shapes/timeouts return UNKNOWN, never a policy. *)
ClearAll[G7AtomPairs,G7CellList,G7CellPoint,G7CADSelector];
G7CellList[e_] := Module[{f=LogicalExpand[e]},
  Which[f===False,{},Head[f]===Or,List@@f,True,{f}]];
G7AtomPairs[e_] := Module[{h=Head[e],a=List@@e},
  Which[e===True,{},e===False,{False},
    h===And,Flatten[G7AtomPairs /@ a,1],
    h===Inequality,Table[a[[2i]][a[[2i-1]],a[[2i+1]]],{i,(Length[a]-1)/2}],
    MemberQ[{Less,LessEqual,Greater,GreaterEqual,Equal},h],
      Table[h[a[[i]],a[[i+1]]],{i,Length[a]-1}],
    True,{e}]];
G7CellPoint[cell_,history_List,actions_List] := Module[
  {relations=G7AtomPairs[cell],rules={},x,own,lower,upper,sections,
   present,primary,lhs,rhs,head,point,guard,bad=False},
  Do[
    x=actions[[i]]; lower={};upper={};sections={};
    Do[
      present=Select[actions,!FreeQ[atom,#]&];
      If[present=!={},
        primary=Last[present];
        If[primary===x,
          own=atom/.rules;head=Head[own];
          If[!MemberQ[{Less,LessEqual,Greater,GreaterEqual,Equal},head] || Length[own]!=2,
             bad=True;Break[]];
          lhs=own[[1]];rhs=own[[2]];
          If[lhs===x && FreeQ[rhs,Alternatives@@Drop[actions,i-1]],
            Which[head===Equal,AppendTo[sections,rhs],
              MemberQ[{Less,LessEqual},head],AppendTo[upper,rhs],
              MemberQ[{Greater,GreaterEqual},head],AppendTo[lower,rhs]],
            If[rhs===x && FreeQ[lhs,Alternatives@@Drop[actions,i-1]],
              Which[head===Equal,AppendTo[sections,lhs],
                MemberQ[{Less,LessEqual},head],AppendTo[lower,lhs],
                MemberQ[{Greater,GreaterEqual},head],AppendTo[upper,lhs]],
              bad=True;Break[]]]]],
      {atom,relations}];
    If[bad,Break[]];
    point=Which[sections=!={},First[sections],
      lower=!={} && upper=!={},((Max@@lower)+(Min@@upper))/2,
      lower=!={},(Max@@lower)+1,upper=!={},(Min@@upper)-1,True,0];
    AppendTo[rules,x->point],
    {i,Length[actions]}];
  If[bad,Return[<|"Status"->"UNKNOWN_UNSUPPORTED_CYLINDER_SHAPE"|>]];
  guard=FullSimplify[cell/.rules,Element[history,Reals]];
  If[!FreeQ[guard,Alternatives@@actions],
    Return[<|"Status"->"UNKNOWN_RESIDUAL_ACTION_IN_CELL_GUARD"|>]];
  <|"Status"->"CELL_POINT_CONSTRUCTED","Guard"->guard,"Rules"->rules,"Cell"->cell|>
];
G7CADSelector[relation_,history_List,actions_List,seconds_:20] := Module[
 {cad,cells,points,good,coverage,soundness,domain,prior=False,ordered={},g,check},
 If[actions==={} || !DuplicateFreeQ[Join[history,actions]],
   Return[<|"Status"->"UNKNOWN_INVALID_SELECTOR_CARRIER"|>]];
 cad=TimeConstrained[CylindricalDecomposition[relation,Join[history,actions]],seconds,$Aborted];
 If[cad===$Aborted || !FreeQ[cad,_CylindricalDecomposition],
   Return[<|"Status"->"UNKNOWN_CAD_RESOURCE_OR_INCOMPLETE","Raw"->cad|>]];
 cells=G7CellList[cad];points=G7CellPoint[#,history,actions]& /@ cells;
 If[!(And@@(#["Status"]==="CELL_POINT_CONSTRUCTED"& /@ points)),
   Return[<|"Status"->"UNKNOWN_CELL_SELECTOR_EXTRACTION","Cells"->points|>]];
 good=Select[points,#["Guard"]=!=False&];
 domain=With[{aa=actions,rr=relation},Exists[aa,rr]];
 coverage=TimeConstrained[Resolve[With[{hh=history,ff=Implies[domain,Or@@(#["Guard"]& /@ good)]},
                       If[hh==={},ff,ForAll[hh,ff]]],Reals],seconds,$Aborted];
 soundness=Table[
   check=Implies[p["Guard"],relation/.p["Rules"]];
   TimeConstrained[Resolve[With[{hh=history,ff=check},If[hh==={},ff,ForAll[hh,ff]]],Reals],seconds,$Aborted],
   {p,good}];
 If[coverage=!=True || !And@@(#===True& /@ soundness),
   Return[<|"Status"->"UNKNOWN_OR_FAILED_SELECTOR_CERTIFICATION","Coverage"->coverage,
           "Soundness"->soundness,"RawCAD"->cad,"Cells"->good|>]];
 Do[g=FullSimplify[p["Guard"] && !prior,Element[history,Reals]];
    AppendTo[ordered,<|"Guard"->g,"Rules"->p["Rules"]|>];prior=prior||p["Guard"],{p,good}];
 <|"Status"->"SEMIALGEBRAIC_FIBRE_SELECTOR_CERTIFIED_SAME_BACKEND",
   "HistoryVariables"->history,"ActionVariables"->actions,"OrderedCells"->ordered,
   "Coverage"->coverage,"Soundness"->soundness,"RawCAD"->cad,
   "Trust"->"Complete Wolfram CAD and exact Resolve checks; not an independent Lean proof"|>
];

(* Full reachable-state G7 policy assembly. Requires cad_selector.wl first.
   Every consistency formula uses one original source parameter vector through
   the entire history. General resource/QE/cell failures remain UNKNOWN. *)
ClearAll[G7Exists,G7ForAll,G7FreshModel,G7Consistent,G7Homogeneous,
 G7Win,G7ActionFibre,G7PolicyNode,G7CompilePolicy];
G7Exists[v_List,e_] := With[{vv=v,ff=e},If[vv==={},ff,Exists[vv,ff]]];
G7ForAll[v_List,e_] := With[{vv=v,ff=e},If[vv==={},ff,ForAll[vv,ff]]];
G7FreshModel[m_Association] := m/.Thread[m["Vars"]->Table[Unique["source"],{Length[m["Vars"]]}]];
G7Consistent[m_Association,h_List] := Module[{p},And@@Table[And@@Thread[p[[1]].m["Laws"]==p[[2]]],{p,h}]];
G7Homogeneous[models_List,h_List] := Module[{i,j},And@@Flatten[Table[
 If[models[[i]]["Target"]===models[[j]]["Target"],True,
   Module[{a=G7FreshModel[models[[i]]],b=G7FreshModel[models[[j]]]},
    Not[G7Exists[Join[a["Vars"],b["Vars"]],a["Domain"]&&b["Domain"]&&G7Consistent[a,h]&&G7Consistent[b,h]]]]],
 {i,Length[models]},{j,i+1,Length[models]}]]];
G7ActionFibre[models_,supports_,sites_,h_,d_,usedRows_,usedSites_,caps_,support_,a_List] := Module[
 {rows=Union[usedRows,support],ss=Union[usedSites,Flatten[sites[[support]]]],k,q,w,y,legal,pairs,i,j},
 {k,q}=Dimensions[models[[1]]["Laws"]];
 If[d<1||Length[rows]>caps[[1]]||Length[ss]>caps[[2]],Return[False]];
 If[Length[support]==1,
  w=ReplacePart[ConstantArray[0,k],First[support]->1];legal=True,
  w=ReplacePart[ConstantArray[0,k],Thread[support->a]];legal=And@@Thread[a>0]&&Total[a]==1];
 If[d==1,
  pairs=And@@Flatten[Table[If[models[[i]]["Target"]===models[[j]]["Target"],True,
    Module[{x=G7FreshModel[models[[i]]],z=G7FreshModel[models[[j]]]},
     Not[G7Exists[Join[x["Vars"],z["Vars"]],legal&&x["Domain"]&&z["Domain"]&&
       G7Consistent[x,h]&&G7Consistent[z,h]&&And@@Thread[w.x["Laws"]==w.z["Laws"]]]]]],
   {i,Length[models]},{j,i+1,Length[models]}]];
  legal&&pairs,
  y=Table[Unique["response"],{q}];
  legal&&G7ForAll[y,G7Win[models,supports,sites,Append[h,{w,y}],d-1,rows,ss,caps]]]
];
G7Win[models_,supports_,sites_,h_,d_,usedRows_,usedSites_,caps_] := Module[{s},
 G7Homogeneous[models,h]||If[d==0,False,Or@@Table[
  Module[{a=If[Length[s]==1,{},Table[Unique["weight"],{Length[s]}]]},
   G7Exists[a,G7ActionFibre[models,supports,sites,h,d,usedRows,usedSites,caps,s,a]]],{s,supports}]]];
G7PolicyNode[models_,supports_,sites_,h_,hv_List,d_,ur_,us_,caps_,domain_,seconds_,nodeCap_] := Catch[Module[
 {hom,targets,leaves={},branches={},remaining=domain,leafguard,base,fibre,a,selector,gg,rules,
  w,y,child,rows,ss,cover,own,region,target,mm,s,cell,homraw,uniform},
 $G7PolicyNodes++;If[$G7PolicyNodes>nodeCap,Throw[<|"Status"->"UNKNOWN_POLICY_NODE_LIMIT"|>,"G7PolicyFailure"]];
 homraw=G7Homogeneous[models,h];
 uniform=TimeConstrained[Resolve[G7ForAll[hv,Implies[domain,homraw]],Reals],seconds,$Aborted];
 hom=If[uniform===True,True,
   uniform=TimeConstrained[Resolve[G7ForAll[hv,Implies[domain,!homraw]],Reals],seconds,$Aborted];
   If[uniform===True,False,TimeConstrained[Resolve[homraw,Reals],seconds,$Aborted]]];
 If[hom===$Aborted,Throw[<|"Status"->"UNKNOWN_HOMOGENEITY_QE"|>,"G7PolicyFailure"]];
 targets=DeleteDuplicates[#["Target"]& /@ models];
 Do[own=Select[models,#["Target"]===target&];
  region=Or@@Table[Module[{m=G7FreshModel[mm]},G7Exists[m["Vars"],m["Domain"]&&G7Consistent[m,h]]],{mm,own}];
  leafguard=TimeConstrained[Resolve[domain&&hom&&region,Reals],seconds,$Aborted];
  If[leafguard===$Aborted,Throw[<|"Status"->"UNKNOWN_TARGET_FIBRE_QE"|>,"G7PolicyFailure"]];
  If[leafguard=!=False,AppendTo[leaves,<|"Guard"->leafguard,"Target"->target|>]],{target,targets}];
 remaining=domain&&!hom;
 If[d>0,Do[
  a=If[Length[s]==1,{},Table[Unique["action"],{Length[s]}]];
  fibre=remaining&&G7ActionFibre[models,supports,sites,h,d,ur,us,caps,s,a];
  selector=If[a==={},
   gg=TimeConstrained[Resolve[fibre,Reals],seconds,$Aborted];
   If[gg===$Aborted,<|"Status"->"UNKNOWN_DISCRETE_ACTION_QE"|>,
      <|"Status"->"SEMIALGEBRAIC_FIBRE_SELECTOR_CERTIFIED_SAME_BACKEND","OrderedCells"->{<|"Guard"->gg,"Rules"->{}|>}|>],
   G7CADSelector[fibre,hv,a,seconds]];
  If[selector["Status"]=!="SEMIALGEBRAIC_FIBRE_SELECTOR_CERTIFIED_SAME_BACKEND",
    Throw[<|"Status"->"UNKNOWN_ACTION_FIBRE_SELECTOR","Raw"->selector|>,"G7PolicyFailure"]];
  Do[gg=cell["Guard"];rules=cell["Rules"];
   If[gg=!=False,
    w=If[Length[s]==1,ReplacePart[ConstantArray[0,Length[sites]],First[s]->1],
       ReplacePart[ConstantArray[0,Length[sites]],Thread[s->(a/.rules)]]];
    y=Table[Unique["nextObserved"],{Dimensions[models[[1]]["Laws"]][[2]]}];
    rows=Union[ur,s];ss=Union[us,Flatten[sites[[s]]]];
    base=Or@@Table[Module[{m=G7FreshModel[mm]},G7Exists[m["Vars"],m["Domain"]&&G7Consistent[m,Append[h,{w,y}]]]],{mm,models}];
    child=G7PolicyNode[models,supports,sites,Append[h,{w,y}],Join[hv,y],d-1,rows,ss,caps,gg&&base,seconds,nodeCap];
    If[child["Status"]=!="POLICY_NODE_CERTIFIED_SAME_BACKEND",Throw[child,"G7PolicyFailure"]];
    AppendTo[branches,<|"Guard"->gg,"Support"->s,"Weights"->w,"ResponseVariables"->y,"Child"->child|>]],
   {cell,selector["OrderedCells"]}];
  remaining=remaining&&!(Or@@(#["Guard"]& /@ selector["OrderedCells"])),{s,supports}]];
 cover=TimeConstrained[Resolve[G7ForAll[hv,Implies[domain,Or@@Join[#["Guard"]& /@ leaves,#["Guard"]& /@ branches]]],Reals],seconds,$Aborted];
 If[cover=!=True,Throw[<|"Status"->"UNKNOWN_OR_FAILED_GLOBAL_POLICY_COVERAGE","Coverage"->cover|>,"G7PolicyFailure"]];
 <|"Status"->"POLICY_NODE_CERTIFIED_SAME_BACKEND","ReachableDomain"->domain,
   "TargetLeaves"->leaves,"ActionBranches"->branches,"Coverage"->cover|>
],"G7PolicyFailure"];
G7CompilePolicy[models_List,supports_List,sites_List,programs_Integer,rowCap_Integer,siteCap_Integer,seconds_:10,nodeCap_:1000] := Module[
 {budget,domain,policy},$G7PolicyNodes=0;
 budget=Check[TimeConstrained[Resolve[G7Win[models,supports,sites,{},Min[programs,Length[sites]],{},{},{rowCap,siteCap}],Reals],seconds,$Aborted],$Failed];
 If[budget=!=True,Return[<|"Status"->If[budget===False,"BUDGET_FALSE_SAME_BACKEND","UNKNOWN_RECURSIVE_BUDGET_QE"],"Budget"->budget|>]];
 policy=G7PolicyNode[models,supports,sites,{},{},Min[programs,Length[sites]],{},{},{rowCap,siteCap},True,seconds,nodeCap];
 <|"Status"->If[policy["Status"]==="POLICY_NODE_CERTIFIED_SAME_BACKEND","WHOLE_ADAPTIVE_POLICY_CERTIFIED_SAME_BACKEND","BUDGET_TRUE_POLICY_COMPILATION_PENDING"],
   "Budget"->budget,"Policy"->policy,"PolicyNodes"->$G7PolicyNodes,
   "Trust"->"Complete Wolfram real QE/CAD and original reachable-domain checks; not a Lean certificate"|>
];

models={<|"Vars"->{s},"Domain"->0<s<1,"Laws"->{{1-2s/3,s/3,s/3}},"Target"->0|>,<|"Vars"->{s},"Domain"->0<s<1,"Laws"->{{s/3,1-2s/3,s/3}},"Target"->1|>,<|"Vars"->{s},"Domain"->0<s<1,"Laws"->{{s/3,s/3,1-2s/3}},"Target"->2|>}; G7CompilePolicy[models,{{1}},{{}},1,1,0,5,20]
