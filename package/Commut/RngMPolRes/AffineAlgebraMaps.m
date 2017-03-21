freeze;
////////////////////////////////////////////////////////////////////////////////
//
// AffineAlgebraMapKernel: the kernel of a map between affine algebras or
//   polynomial rings.  Basically just extends the standard elimination method
//   for polynomial rings, used in PolyMapKernel.
//
////////////////////////////////////////////////////////////////////////////////


intrinsic AffineAlgebraMapKernel(phi::Map) -> MPol
{
    Determines the kernel of a map phi of affine R-algebras (or polynomial rings).
}
    A1 := Domain(phi);
    A2 := Codomain(phi);
    require Type(A1) in [RngMPol, RngMPolRes] :
      "Domain of map must be an affine algebra or polynomial ring";
    require Type(A2) in [RngMPol, RngMPolRes] :
      "Codomain of map must be an affine algebra or polynomial ring";
    require CoefficientRing(A1) cmpeq CoefficientRing(A2) :
      "Domain and Codomain of map must have the same coefficient ring";

    P1 := (Type(A1) eq RngMPolRes) select PreimageIdeal(A1) else A1;
    require P1 eq Generic(P1):
      "Domain of map must be either a full polynomial ring or a quotient of" cat      " a full polynomial ring";

    P2 := (Type(A2) eq RngMPolRes) select PreimageIdeal(A2) else A2;
    require P2 eq Generic(P2):
      "Codomain of map must be either a full polynomial ring of a quotient " cat
      "of a full polynomial ring";

    r1 := Rank(P1);
    r2 := Rank(P2);

    R := CoefficientRing(P1); // eq CoefficientRing(P2).

    T := PolynomialRing(R, r1 + r2, "elim", r2);
    i1 := hom< P1 -> T | [T.(r2+i) : i in [1..r1]] >;
    i2 := hom< P2 -> T | [T.i : i in [1..r2]] >;

    I := ideal<T | [i1(P1.i) - i2(phi(P1.i)) : i in [1..r1]]>;

    if(Type(A2) eq RngMPolRes) then
        B := Basis(DivisorIdeal(A2));
        if #B ne 0 then // that is, if the divisor ideal of A2 is nontrivial,
            I +:= ideal<T | [i2(b): b in B]>;
        end if;
    end if;

    J := EliminationIdeal(I, r2 : Al := "Direct");

    pi := hom< T -> A1 | [A1| 0 : i in [1..r2]] cat [A1.i : i in [1..r1]] >;
    L := ideal< A1 | Basis(J)@pi >;

    return L;
end intrinsic;

