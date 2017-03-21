freeze;

////////////////////////////////////////////////////////////////////////////
//                    Decomposition Types
////////////////////////////////////////////////////////////////////////////

intrinsic DecompositionType(F::FldFun, P::PlcFunElt) -> SeqEnum
{
  Sequence of tuples of residue degrees and ramification indices of the
  places of F lying over the place P
};

    require Degree(F) cmpne Infinity() :
				"Function field must be a finite extension";

    if Degree(FunctionField(P)) cmpeq Infinity() then
       require IsRationalFunctionField(CoefficientField(F)) : 
       						"Arguments are incompatible";
       return [ <f, e> where e is RamificationIndex(Q)
                       where f is ResidueClassDegree(Q) :
                       Q in Decomposition(F, P) ];
    else
	require CoefficientField(F) cmpeq FunctionField(P) :
				    "Arguments are incompatible";

	if IsFinite(P) then
	    return DecompositionType(MaximalOrderFinite(F), Ideal(P));
	else
	    return DecompositionType(MaximalOrderInfinite(F), Ideal(P));
	end if;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////////

intrinsic InfinitePlaces(K::FldFun) -> SeqEnum
{The infinite places of K}
    Kfin := RationalExtensionRepresentation(K);
    return Zeros(K!Kfin!(1/BaseField(Kfin).1));
end intrinsic;

