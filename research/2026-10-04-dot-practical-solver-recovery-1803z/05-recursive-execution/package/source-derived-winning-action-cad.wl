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

G7CADSelector[And[Not[LessEqual[g7var1,0]],Not[GreaterEqual[g7var1,1]]],{originalObservedPrefix0,originalObservedPrefix1,originalObservedPrefix2},{g7var1},10]
