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
