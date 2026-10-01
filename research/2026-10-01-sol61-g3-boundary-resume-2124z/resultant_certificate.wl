(* Exact construction recipe for the executed cap-six calibration. *)
Clear[p,q];
la={1,3,6,10,15}; cc=Array[c,5]; ff=1-p+p q^la;
pc=Cancel[Expand[Sum[cc[[j]] (1-q^la[[j]])
  Times@@Delete[ff,j],{j,5}]]/(q-1)^2];
qc=Cancel[Expand[Sum[cc[[j]] la[[j]] q^(la[[j]]-1)
  Times@@Delete[ff,j],{j,5}]]/(q-1)];
rr=Cancel[Resultant[pc,qc,p]/Times@@cc];
tr=CoefficientRules[rr,cc];
integerMatrix=Transpose[PadRight[CoefficientList[#[[2]],q],
  1+Exponent[rr,q]]&/@tr];
rf=RowReduce[Transpose[integerMatrix],Modulus->1009];
piv=Table[First[FirstPosition[rf[[i]],z_Integer/;z!=0]],
  {i,Length[rf]}];
minor=integerMatrix[[piv]];
{Dimensions[integerMatrix],Length[tr],MatrixRank[integerMatrix,Modulus->1009],
 piv-1,Mod[Det[minor],1009]}
(* Observed: 35 covector monomials, rank35; minor determinant527 mod1009.
   The complete numeric integer matrix was NOT successfully serialized:
   its evaluator text export was middle-elided. This recipe defines each
   integer entry exactly. cap6-modular-minor.json holds the complete selected
   modular minor, checked independently by local modular elimination.
   This concerns FULL SUPPORT c1*c2*c3*c4*c5 != 0 only.
   Zero-coordinate branches require their actual support denominators. *)
