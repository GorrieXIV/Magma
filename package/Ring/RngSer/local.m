freeze;

intrinsic ResidueClassField(R::RngSerPow) -> Rng, Map
{The residue class field of the series ring R};

    m := map<R -> CoefficientRing(R) | x :-> Coefficient(x, 0), y:-> y >;
    return CoefficientRing(R), m;

end intrinsic;

intrinsic IsIrreducible(f::RngUPolElt[RngSer]) -> BoolElt
{True iff f is irreducible}
    require Type(CoefficientRing(CoefficientRing(f))) eq FldFin : 
    		"Coefficient ring of argument must be over a finite field";
    F := Factorization(f);
    return #F eq 1 and F[1][2] eq 1;
end intrinsic;

intrinsic IsIrreducible(f::RngUPolElt[RngSerExt]) -> BoolElt
{True iff f is irreducible}
    F := Factorization(f);
    return #F eq 1 and F[1][2] eq 1;
end intrinsic;

