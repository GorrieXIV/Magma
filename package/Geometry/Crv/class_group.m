freeze;

///////////////////////////////////////////////////////////////////////
// Class group
///////////////////////////////////////////////////////////////////////

intrinsic ClassGroup(C::Crv[FldFin]) -> GrpAb, Map, Map
    {The divisor class group of the curve C defined over a finite
    field together with a map of representatives from the class group to the divisor group and the homomorphism from the divisor group onto the class group.}
    k := BaseRing(C);
    F := FunctionField(C);
    FF := AlgorithmicFunctionField(F);
    Cl, _, phi := ClassGroup(FF);
    psi := map< DivisorGroup(C) -> Cl |
		x :-> phi(FunctionFieldDivisor(x)),
		y :-> CurveDivisor(C, (y @@ phi)) >;
    return Cl, Inverse(psi), psi;
end intrinsic;

intrinsic ClassNumber(C::Crv[FldFin]) -> RngIntElt
{The order of the class group of the curve C}
    return ClassNumber(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;

intrinsic GlobalUnitGroup(C::Crv[FldFin]) -> GrpAb,Map
{The group of global units of the function field F of the curve C, that is
the multiplicative group of the exact constant field of F as an Abelian group
together with the map into F}
    return GlobalUnitGroup(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;


