freeze;

intrinsic Slopes(N::NwtnPgon) -> SeqEnum
{The slopes of the newton polygon N}

    F := Faces(N);
    L := [ ];
    for faces in F do
        g := GradientVector(faces);
        Append(~L, -g[1]/g[2]);
    end for;

    return L;
end intrinsic;

function ValuationsOfRoots_function(N)
// the valuations of the roots of the polynomial the polygon is of

    v := Valuation(Polynomial(N));
    if v gt 0 then
        S := [<Infinity(), v>];
    else
        S := [];
    end if;
    F := Faces(N);
    G := [GradientVector(f) : f in F];
    G := [g[1]/g[2] : g in G];
    E := [EndVertices(f) : f in F];
    E := [e[2][1] - e[1][1] : e in E];
    return S cat [<G[i], Integers()!E[i]> : i in [1 .. #G]];

end function;

intrinsic ValuationsOfRoots(f::RngUPolElt) -> SeqEnum
{The valuations of the roots of f over some local or series ring}

    require Type(CoefficientRing(Parent(f))) in {RngPad, RngPadRes, RngPadResExt, FldPad, RngSerPow, RngSerLaur, RngSerPuis, RngVal}:
                        "Argument 1 must be over some valuation ring";

    return ValuationsOfRoots_function(NewtonPolygon(f : Faces := "Lower"));
end intrinsic;


intrinsic ValuationsOfRoots(f::RngUPolElt, P::RngIntElt) -> SeqEnum
{The valuations (with respect to P) of the roots of f over the integers or rationals}

    require FieldOfFractions(CoefficientRing(Parent(f))) eq Rationals() :
                        "Argument 1 must be over the integers or rationals";

    require IsPrime(P) : "Argument 2 must be prime";

    return ValuationsOfRoots_function(NewtonPolygon(f, P : Faces := "Lower"));

end intrinsic;

intrinsic ValuationsOfRoots(f::RngUPolElt, P::RngOrdIdl) -> SeqEnum
{The valuations (with respect to P) of the roots of f over a number field}

    require FieldOfFractions(CoefficientRing(Parent(f)))
                eq FieldOfFractions(Order(P)) or
                CoefficientRing(Parent(f)) eq NumberField(Order(P)) :
                "Arguments must be associated with the same number field";

    require IsPrime(P) : "Argument 2 must be prime";

    return ValuationsOfRoots_function(NewtonPolygon(f, P : Faces := "Lower"));

end intrinsic;

intrinsic ValuationsOfRoots(f::RngUPolElt, P::PlcFunElt) -> SeqEnum
{The valuations (with respect to P) of the roots of f over a function field}

    require FieldOfFractions(CoefficientRing(Parent(f))) cmpeq
                FunctionField(P) :
                "Arguments must be associated with the same field";

    return ValuationsOfRoots_function(NewtonPolygon(f, P : Faces := "Lower"));

end intrinsic;

intrinsic InnerSlopes(N::NwtnPgon) -> SeqEnum
{The slopes of the newton polygon N}

    F := InnerFaces(N);
    L := [ ];
    for faces in F do
        g := GradientVector(faces);
        Append(~L, -g[1]/g[2]);
    end for;

    return L;
end intrinsic;

intrinsic LowerSlopes(N::NwtnPgon) -> SeqEnum
{The slopes of the newton polygon N}

    F := LowerFaces(N);
    L := [ ];
    for faces in F do
        g := GradientVector(faces);
        Append(~L, -g[1]/g[2]);
    end for;

    return L;
end intrinsic;

intrinsic AllSlopes(N::NwtnPgon) -> SeqEnum
{The slopes of the newton polygon N}

    F := AllFaces(N);
    L := [ ];
    for faces in F do
        g := GradientVector(faces);
        Append(~L, -g[1]/g[2]);
    end for;

    return L;
end intrinsic;

