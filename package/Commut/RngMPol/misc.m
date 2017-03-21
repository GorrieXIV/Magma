freeze;

intrinsic ConstantTerm(f::RngMPolElt) -> RngMPolElt
   {The constant term of f}
   P := Parent(f);
   return &+[ P | m : m in Terms(f) | WeightedDegree(m) eq 0 ];
end intrinsic;

////////////////////////////////////////////////////////////////////////////////
//
// IsAlgebraicallyDependent: Determine if a sequence of polynomials is 
//   algebraically dependent.  Slightly naive implementation based on the
//   elimination-theory approach.  BS 9.12.02
//
////////////////////////////////////////////////////////////////////////////////

intrinsic IsAlgebraicallyDependent(S::{RngMPolElt}) -> BoolElt
{
    True iff the polynomials in the set S are algebraically dependent.
}

    if #S eq 0 then
        return false;
    end if;

    A := Universe(S);
    B := PolynomialRing(BaseRing(A), #S);

    phi := hom< B -> A | Setseq(S) >;

    return not IsZero(AffineAlgebraMapKernel(phi));

end intrinsic;

