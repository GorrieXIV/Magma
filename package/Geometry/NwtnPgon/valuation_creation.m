freeze;

intrinsic NewtonPolygon(f::RngUPolElt, P::RngFunOrdIdl : Faces := "Inner") -> NwtnPgon
{The Newton polygon of f with respect to the prime ideal P}

    require FieldOfFractions(CoefficientRing(Parent(f))) eq
                FieldOfFractions(Order(P)) :
                "Arguments must be associated with the same field";

    require IsPrime(P) : "Argument 2 must be prime";
    s := Sprint(Faces);
    require Faces in {"Inner", "Lower", "All"} : "Invalid parameter rhs string \"" cat s cat "\"";

    return NewtonPolygon(f, Place(P) : Faces := Faces);

end intrinsic;

