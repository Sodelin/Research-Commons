g7DeclaredMenuPriority=<|0->1,1->2,2->0|>;
(* G7 semialgebraic fibre selector, derived from the accepted master algorithm.
   History variables precede action variables in every complete CAD.
   Unsupported cylinder shapes/timeouts return UNKNOWN, never a policy. *)
ClearAll[G7AtomPairs,G7CellList,G7PreferredCellPoint,G7PreferredCADSelector];
G7CellList[e_] := Module[{f=LogicalExpand[e]},
  Which[f===False,{},Head[f]===Or,List@@f,True,{f}]];
G7AtomPairs[e_] := Module[{h=Head[e],a=List@@e},
  Which[e===True,{},e===False,{False},
    h===And,Flatten[G7AtomPairs /@ a,1],
    h===Inequality,Table[a[[2i]][a[[2i-1]],a[[2i+1]]],{i,(Length[a]-1)/2}],
    MemberQ[{Less,LessEqual,Greater,GreaterEqual,Equal},h],
      Table[h[a[[i]],a[[i+1]]],{i,Length[a]-1}],
    True,{e}]];
G7PreferredCellPoint[cell_,history_List,actions_List] := Module[
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
      lower=!={} && upper=!={},(Max@@lower)+((Min@@upper)-(Max@@lower))*If[history==={},1/2,Sqrt[(First[history]^2+1)/(First[history]^2+2)]],
      lower=!={},(Max@@lower)+1,upper=!={},(Min@@upper)-1,True,0];
    AppendTo[rules,x->point],
    {i,Length[actions]}];
  If[bad,Return[<|"Status"->"UNKNOWN_UNSUPPORTED_CYLINDER_SHAPE"|>]];
  guard=FullSimplify[cell/.rules,Element[history,Reals]];
  If[!FreeQ[guard,Alternatives@@actions],
    Return[<|"Status"->"UNKNOWN_RESIDUAL_ACTION_IN_CELL_GUARD"|>]];
  <|"Status"->"CELL_POINT_CONSTRUCTED","Guard"->guard,"Rules"->rules,"Cell"->cell|>
];
G7PreferredCADSelector[relation_,history_List,actions_List,seconds_:20] := Module[
 {cad,cells,points,good,coverage,soundness,domain,prior=False,ordered={},g,check},
 If[actions==={} || !DuplicateFreeQ[Join[history,actions]],
   Return[<|"Status"->"UNKNOWN_INVALID_SELECTOR_CARRIER"|>]];
 cad=TimeConstrained[CylindricalDecomposition[relation,Join[history,actions]],seconds,$Aborted];
 If[cad===$Aborted || !FreeQ[cad,_CylindricalDecomposition],
   Return[<|"Status"->"UNKNOWN_CAD_RESOURCE_OR_INCOMPLETE","Raw"->cad|>]];
 cells=G7CellList[cad];points=G7PreferredCellPoint[#,history,actions]& /@ cells;
 If[!(And@@(#["Status"]==="CELL_POINT_CONSTRUCTED"& /@ points)),
   Return[<|"Status"->"UNKNOWN_CELL_SELECTOR_EXTRACTION","Cells"->points|>]];
 good=Select[points,#["Guard"]=!=False&];
 If[!And@@(IntegerQ[Last[actions]/.#["Rules"]] && KeyExistsQ[g7DeclaredMenuPriority,Last[actions]/.#["Rules"]]& /@ good),Return[<|"Status"->"UNKNOWN_NONCONSTANT_CONFIGURED_SUPPORT"|>]];
 good=SortBy[good,g7DeclaredMenuPriority[Last[actions]/.#["Rules"]]&];
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

(* Exact AST export at the CAD-to-runtime boundary. No supplied text is parsed.
   The mapping is constructed by the caller from declared history coordinates
   and earlier own actions. A source/unknown symbol cannot be exported. *)
ClearAll[G7ExactCellValueAST];
G7ExactCellValueAST[expression_,mapping_List] := Module[
 {known,go,z=Unique["rootPolynomialVariable"],polynomial,coefficients},
 If[!And@@(MatchQ[#,Rule[_Symbol,_String]]& /@ mapping),
   Return[<|"Status"->"UNKNOWN_INVALID_TYPED_OBSERVATION_MAPPING"|>]];
 If[!DuplicateFreeQ[First/@mapping] || !DuplicateFreeQ[Last/@mapping] ||
    !And@@(StringQ[#] && StringMatchQ[#,RegularExpression["h[0-9]+_[0-9]+|action_root_[A-Za-z0-9_]+"]]& /@ (Last/@mapping)),
   Return[<|"Status"->"UNKNOWN_INVALID_TYPED_OBSERVATION_MAPPING"|>]];
 known=Association[mapping];
 go[e_] := Which[
   IntegerQ[e],<|"kind"->"rational","value"->ToString[e,InputForm]|>,
   Head[e]===Rational,<|"kind"->"rational","value"->ToString[Numerator[e],InputForm]<>"/"<>ToString[Denominator[e],InputForm]|>,
   Head[e]===Symbol && KeyExistsQ[known,e],<|"kind"->"observation","name"->known[e]|>,
   Head[e]===Plus,<|"kind"->"add","args"->(go/@(List@@e))|>,
   Head[e]===Times,<|"kind"->"multiply","args"->(go/@(List@@e))|>,
   Head[e]===Power && IntegerQ[e[[2]]],<|"kind"->"power","base"->go[e[[1]]],"exponent"->e[[2]]|>,
   Head[e]===Power && Head[e[[2]]]===Rational,
     <|"kind"->"principal_power","base"->go[e[[1]]],"numerator"->Numerator[e[[2]]],"denominator"->Denominator[e[[2]]]|>,
   MemberQ[{Min,Max},Head[e]],<|"kind"->If[Head[e]===Min,"minimum","maximum"],"args"->(go/@(List@@e))|>,
   Head[e]===Root && (Length[e]===2 || (Length[e]===3 && MemberQ[{0,1},e[[3]]])) &&
     Head[e[[1]]]===Function && IntegerQ[e[[2]]] && e[[2]]>0,
     polynomial=e[[1]][z];
     If[!PolynomialQ[polynomial,z],Throw["UNKNOWN_NONPOLYNOMIAL_ROOT","cellAST"]];
     coefficients=CoefficientList[polynomial,z];
     If[Length[coefficients]<2,Throw["UNKNOWN_CONSTANT_ROOT_POLYNOMIAL","cellAST"]];
     <|"kind"->"root","coefficients"->(go/@coefficients),"real_root_index"->e[[2]]|>,
   True,Throw["UNKNOWN_UNSUPPORTED_OR_UNDECLARED_CELL_VALUE","cellAST"]
 ];
 Catch[<|"Status"->"STRUCTURED_CAD_VALUE_EXPORTED","AST"->go[expression],
         "DeclaredCoordinates"->(<|"namespace"->If[StringStartsQ[#,"h"],"recorded_history","earlier_own_action"],"name"->#|>& /@ (Last/@mapping)),
         "RootIndexSemantics"->"Wolfram real roots increasingly ordered with input polynomial multiplicity", 
         "Scope"->"Value export only; source-winning relation, cell coverage and policy verification are separate"|>,
       "cellAST",(<|"Status"->#1|>&)]
];

(* Convert a COMPLETE already certified history-first selector to typed data.
   The source winning-relation/registry binding remains a separate producer. *)
ClearAll[G7ExactGuardAST,G7ExportCertifiedSelector];
G7ExactGuardAST[guard_,mapping_List] := Module[{go,value,op},
 value[e_] := Module[{v=G7ExactCellValueAST[e,mapping]},
   If[v["Status"]=!="STRUCTURED_CAD_VALUE_EXPORTED",Throw[v["Status"],"guardAST"]];v["AST"]];
 go[e_] := Which[
   e===True || e===False,<|"kind"->"boolean","value"->e|>,
   Head[e]===And || Head[e]===Or,<|"kind"->If[Head[e]===And,"and","or"],"args"->(go/@(List@@e))|>,
   Head[e]===Not && Length[e]===1,<|"kind"->"not","arg"->go[e[[1]]]|>,
   Head[e]===Inequality,
      If[Length[e]<3 || !OddQ[Length[e]] ||
         !And@@(MemberQ[{Less,LessEqual,Greater,GreaterEqual,Equal,Unequal},e[[#]]]& /@ Range[2,Length[e]-1,2]),
        Throw["UNKNOWN_MALFORMED_INEQUALITY_CHAIN","guardAST"]];
      <|"kind"->"and","args"->Table[go[e[[2i]][e[[2i-1]],e[[2i+1]]]],{i,(Length[e]-1)/2}]|>,
   Head[e]===Unequal && Length[e]>=2,
      <|"kind"->"and","args"->(<|"kind"->"comparison","op"->"ne","left"->value[#[[1]]],"right"->value[#[[2]]]|>& /@ Subsets[List@@e,{2}])|>,
   MemberQ[{Less,LessEqual,Greater,GreaterEqual,Equal},Head[e]] && Length[e]>=2,
      op=Switch[Head[e],Less,"lt",LessEqual,"le",Greater,"gt",GreaterEqual,"ge",Equal,"eq",Unequal,"ne"];
      <|"kind"->"and","args"->Table[<|"kind"->"comparison","op"->op,"left"->value[e[[i]]],"right"->value[e[[i+1]]]|>,{i,Length[e]-1}]|>,
   True,Throw["UNKNOWN_UNSUPPORTED_GUARD_HEAD","guardAST"]];
 Catch[<|"Status"->"STRUCTURED_EXACT_GUARD_EXPORTED","AST"->go[guard]|>,"guardAST",(<|"Status"->#1|>&)]
];
G7ExportCertifiedSelector[selector_Association,mapping_List,weightTemplates_List] := Module[
 {cells={},g,weights,entry},
 If[selector["Status"]=!="SEMIALGEBRAIC_FIBRE_SELECTOR_CERTIFIED_SAME_BACKEND" ||
    selector["Coverage"]=!=True || !And@@(#===True& /@ selector["Soundness"]),
   Return[<|"Status"->"UNKNOWN_OR_UNCERTIFIED_INPUT_SELECTOR"|>]];
 Do[
   g=G7ExactGuardAST[cell["Guard"],mapping];
   weights=G7ExactCellValueAST[#,mapping]& /@ (weightTemplates/.cell["Rules"]);
   If[g["Status"]=!="STRUCTURED_EXACT_GUARD_EXPORTED" ||
      !And@@(#["Status"]==="STRUCTURED_CAD_VALUE_EXPORTED"& /@ weights),
     Return[<|"Status"->"UNKNOWN_SELECTOR_AST_EXPORT"|>]];
   AppendTo[cells,<|"guard"->g["AST"],"weights"->(#["AST"]& /@ weights)|>],
   {cell,selector["OrderedCells"]}];
 <|"Status"->"CERTIFIED_HISTORY_FIRST_SELECTOR_AST_EXPORTED_SAME_BACKEND",
   "cells"->cells,"coverage"->selector["Coverage"],"soundness"->selector["Soundness"],
   "Scope"->"One complete supplied winning-action relation; full source/recursive policy binding remains separate"|>
];


Module[{relation,result,export},relation=Or[And[Equal[g7TypedMenuIndex,0],Greater[g7TypedWeight0,0],Equal[(1-g7TypedWeight0),0],False],And[Equal[g7TypedMenuIndex,1],Equal[g7TypedWeight0,0],Greater[(1-g7TypedWeight0),0],And[Or[Or[And[Greater[(1-g7TypedHistory0),0],Greater[((3*g7TypedHistory0)-1),0],GreaterEqual[((-(g7TypedHistory0)-(2*g7TypedHistory1))+1),0],GreaterEqual[((-(g7TypedHistory0)-(2*g7TypedHistory2))+1),0],GreaterEqual[((g7TypedHistory0+(2*g7TypedHistory1))-1),0],GreaterEqual[((g7TypedHistory0+(2*g7TypedHistory2))-1),0]]],Or[And[Greater[g7TypedHistory0,0],Greater[(1-(3*g7TypedHistory0)),0],GreaterEqual[(-(g7TypedHistory0)+g7TypedHistory1),0],GreaterEqual[(g7TypedHistory0-g7TypedHistory1),0],GreaterEqual[(((-(2)*g7TypedHistory0)-g7TypedHistory2)+1),0],GreaterEqual[(((2*g7TypedHistory0)+g7TypedHistory2)-1),0]]],Or[And[Greater[g7TypedHistory0,0],Greater[(1-(3*g7TypedHistory0)),0],GreaterEqual[(-(g7TypedHistory0)+g7TypedHistory2),0],GreaterEqual[(g7TypedHistory0-g7TypedHistory2),0],GreaterEqual[(((-(2)*g7TypedHistory0)-g7TypedHistory1)+1),0],GreaterEqual[(((2*g7TypedHistory0)+g7TypedHistory1)-1),0]]]],And[Greater[1,0]]]],And[Equal[g7TypedMenuIndex,2],Greater[g7TypedWeight0,0],Greater[(1-g7TypedWeight0),0],And[Or[Or[And[Greater[(1-g7TypedHistory0),0],Greater[((3*g7TypedHistory0)-1),0],GreaterEqual[((-(g7TypedHistory0)-(2*g7TypedHistory1))+1),0],GreaterEqual[((-(g7TypedHistory0)-(2*g7TypedHistory2))+1),0],GreaterEqual[((g7TypedHistory0+(2*g7TypedHistory1))-1),0],GreaterEqual[((g7TypedHistory0+(2*g7TypedHistory2))-1),0]]],Or[And[Greater[g7TypedHistory0,0],Greater[(1-(3*g7TypedHistory0)),0],GreaterEqual[(-(g7TypedHistory0)+g7TypedHistory1),0],GreaterEqual[(g7TypedHistory0-g7TypedHistory1),0],GreaterEqual[(((-(2)*g7TypedHistory0)-g7TypedHistory2)+1),0],GreaterEqual[(((2*g7TypedHistory0)+g7TypedHistory2)-1),0]]],Or[And[Greater[g7TypedHistory0,0],Greater[(1-(3*g7TypedHistory0)),0],GreaterEqual[(-(g7TypedHistory0)+g7TypedHistory2),0],GreaterEqual[(g7TypedHistory0-g7TypedHistory2),0],GreaterEqual[(((-(2)*g7TypedHistory0)-g7TypedHistory1)+1),0],GreaterEqual[(((2*g7TypedHistory0)+g7TypedHistory1)-1),0]]]],And[Greater[g7TypedWeight0,0],Greater[(1-g7TypedWeight0),0]]]]];result=G7PreferredCADSelector[relation,{g7TypedHistory0,g7TypedHistory1,g7TypedHistory2},{g7TypedWeight0,g7TypedMenuIndex},12];export=If[result["Status"]==="SEMIALGEBRAIC_FIBRE_SELECTOR_CERTIFIED_SAME_BACKEND",G7ExportCertifiedSelector[result,{g7TypedHistory0->"h0_0",g7TypedHistory1->"h0_1",g7TypedHistory2->"h0_2"},{g7TypedWeight0,(1-g7TypedWeight0),g7TypedMenuIndex}],<|"Status"->"UNKNOWN_SELECTOR_EXTRACTION"|>];StringReplace[ExportString[<|"Version"->$Version,"SelectorStatus"->result["Status"],"Export"->export,"Coverage"->Lookup[result,"Coverage",False],"Soundness"->Lookup[result,"Soundness",{}],"RawCAD"->ToString[Lookup[result,"RawCAD",Lookup[result,"Raw",Missing["Unavailable"]]],InputForm]|>,"RawJSON"],{"\n"->"","\t"->""}]]