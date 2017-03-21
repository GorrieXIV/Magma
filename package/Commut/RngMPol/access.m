freeze;

/*******************************************************************************
                                Base Function
*******************************************************************************/

intrinsic CoefficientsAndMonomials(f::RngMPolElt, S::{RngIntElt}) -> RngMPolElt
{The coefficients and monomials of F over S as parallel sequences, where
S is a set of variable numbers}

    P := Generic(Parent(f));
    if f eq 0 then
        return P!0;
    end if;

    n := Rank(P);
    require forall{v: v in S | v ge 1 and v le n}: "Integers in S out of range";

    //SC := [i: i in [1 .. n] | i notin S];

    A := AssociativeArray();
    C, M := CoefficientsAndMonomials(f);
    for i := 1 to #C do
        m := Exponents(M[i]);
        mm := P!1;
        cc := C[i];
        for j := 1 to n do
            t := P.j^m[j];
            if j in S then
                mm *:= t;
            else
                cc *:= t;
            end if;
        end for;
//"Here:", m, mm, cc;
        l, o := IsDefined(A, mm);
        if l then
            cc +:= o;
        end if;
        A[mm] := cc;
    end for;

//Keys(A);
    C := [];
    M := [];
    for mm in Keys(A) do
        Append(~M, mm);
        Append(~C, A[mm]);
    end for;
//"NOW:", M, C;
    Sort(~M, ~p);
    //C := C^p^-1;
    C := [C[i^p]: i in [1 .. #C]];
    //return C, M;
    return Reverse(C), Reverse(M);

end intrinsic;

intrinsic CoefficientsAndMonomials(f::RngMPolElt, S::{RngMPolElt}) -> RngMPolElt
{The coefficients and monomials of F over S as parallel sequences, where
S is a set of variables}

    P := Generic(Parent(f));
    require Generic(Universe(S)) cmpeq P: "Variables are not compatible";
    require forall{v: v in S | Length(v) eq 1 and Degree(v) eq 1}:
        "Set S does not consist of variables";

    n := Rank(P);
    V := {@ P.i : i in [1 .. n] @};
    return CoefficientsAndMonomials(f, {Index(V, v): v in S});

end intrinsic;

/*******************************************************************************
                                Derivative versions
*******************************************************************************/

intrinsic LeadingCoefficient(f::RngMPolElt, S::{RngIntElt}) -> RngMPolElt
{The leading coefficient of F over S}

    P := Generic(Parent(f));
    if f eq 0 then
        return P!0;
    end if;
    C, M := CoefficientsAndMonomials(f, S);
    return C[1];

end intrinsic;

intrinsic LeadingMonomial(f::RngMPolElt, S::{RngIntElt}) -> RngMPolElt
{The leading coefficient of F over S}

    require f ne 0: "Argument 1 is not non-zero";
    C, M := CoefficientsAndMonomials(f, S);
    return M[1];

end intrinsic;
