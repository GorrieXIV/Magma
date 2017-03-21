freeze;

//////////////////////////////////////////////////////////////////////
// skewtableau.m
//////////////////////////////////////////////////////////////////////
// $Revision: 29986 $
// $Date: 2010-11-01 04:40:21 +1100 (Mon, 01 Nov 2010) $
// $LastChangedBy: kasprzyk $
//////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
//////////////////////////////////////////////////////////////////////
// Extends the skew tableau support.
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
// Intrinsics
//////////////////////////////////////////////////////////////////////

intrinsic DefinesTableau( S::SeqEnum ) -> BoolElt, Tbl
{True iff the given sequence defines a tableau. If so, also gives the tableau defined.}
    try
        T:=Tableau(S);
    catch e;
        return false,_;
    end try;
    return true,T;
end intrinsic;

intrinsic BaseRing( T::Tbl ) -> Rng
{The coefficient ring of the monoids defining the tableau T}
    // If T doesn't have any rows, this is fiddly
    return NumberOfRows(T) gt 0 select
                Universe(Eltseq(Row(T,1))) else
                Universe(Eltseq(Identity(Universe(Rows(T)))));
end intrinsic;

intrinsic NumberOfColumns( T::Tbl ) -> RngIntElt
{The number of columns of the tableau T}
    shape:=Shape(T);
    return IsEmpty(shape) select 0 else Maximum(shape);
end intrinsic;

intrinsic Eltseq( T::Tbl ) -> SeqEnum
{The row sequence of the tableau T}
    return [PowerSequence(BaseRing(T)) |
                                  Eltseq(Row(T,i)) : i in [1..NumberOfRows(T)]];
end intrinsic;

intrinsic Matrix( T::Tbl ) -> Mtrx
{A matrix representation of the tableau T}
    // Collect the data we need
    R:=BaseRing(T);
    n:=NumberOfColumns(T);
    // Handle the empty tableau as a special case
    if n eq 0 then return Matrix(R,0,0,[R|]); end if;
    // We need to pad the row sequences with the correct number of zeros
    S:=Eltseq(T);
    SS:=[Universe(S)|];
    for s in S do
        Append(~SS,s cat ZeroSequence(R,n - #s));
    end for;
    // Return the matrix
    return Matrix(R,SS);
end intrinsic;

intrinsic 'subset'( T1::Tbl, T2::Tbl ) -> BoolElt
{True iff the tableau T2 covers the tableau T1}
    // Check that the coefficient rings are compatible...
    if not BaseRing(T1) cmpeq BaseRing(T2) then return false; end if;
    // ...and that the sizes are OK
    if NumberOfRows(T1) gt NumberOfRows(T2) or
       NumberOfColumns(T1) gt NumberOfColumns(T2) then return false; end if;
    // Check the shapes
    nr:=Minimum(NumberOfRows(T1),NumberOfRows(T2));
    shape1:=Shape(T1);
    shape2:=Shape(T2);
    if &or[shape1[i] gt shape2[i] : i in [1..nr]] then return false; end if;
    // Now we have to slog through the entries
    S1:=Eltseq(T1);
    S2:=Eltseq(T2);
    return &and[&and[S1[i][j] eq S2[i][j] : j in [1..Minimum(#S1[i],#S2[i])]] :
                                                                  i in [1..nr]];
end intrinsic;

intrinsic Complement( T1::Tbl, T2::Tbl ) -> Tbl
{The complement of the tableau T1 in the tableau T2}
    // Sanity check
    require T1 subset T2: "Argument 2 must cover argument 1";
    // Create the defining sequence
    shape1:=Shape(T1);
    S2:=Eltseq(T2);
    if #shape1 lt #S2 then
        shape1 cat:= ZeroSequence(Integers(),#S2 - #shape1);
    end if;
    S:=[Universe(S2) | S2[i][shape1[i] + 1..#S2[i]] : i in [1..#S2]];
    // Verify that the shape is correct
    shape:=[Integers() | #s : s in S];
    require shape eq Reverse(Sort(shape)):
        "The complement does not define a tableau";
    // Try to create the tableau
    bool,T:=DefinesTableau(S);
    require bool: "The complement does not define a tableau";
    return T;
end intrinsic;
