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
