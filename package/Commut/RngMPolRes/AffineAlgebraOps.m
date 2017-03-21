freeze;

//////////////////////////
// SOME BASIC FUNCTIONS //
//////////////////////////

/*
iintrinsic Generic (I::RngMPolRes) -> RngMPolRes
{Return the whole quotient ring containing I}
// This is now implemented in C

    return quo<OriginalRing(I) | DivisorIdeal(I)>;

end intrinsic;
*/

//////////////////////////
// COMPARISON OF IDEALS //
//////////////////////////

intrinsic 'eq' (I::RngMPolRes, J::RngMPolRes) -> BoolElt
{Return true iff I equals J}

    require (DivisorIdeal(I) cmpeq DivisorIdeal(J)) :
            "Ideals are not in the same quotient ring";

    return (PreimageIdeal(I) eq PreimageIdeal(J));

end intrinsic;

// ----------------------------------------------------------------

/*
intrinsic 'ne' (I::RngMPolRes, J::RngMPolRes) -> BoolElt
{Return true iff I does not equal J}

    require (DivisorIdeal(I) eq DivisorIdeal(J)) :
            "Ideals are not in the same quotient ring";

    return (PreimageIdeal(I) ne PreimageIdeal(J));

end intrinsic;
*/

// ----------------------------------------------------------------

intrinsic 'subset' (I::RngMPolRes, J::RngMPolRes) -> BoolElt
{Return true iff I is a subset of J}

    require (DivisorIdeal(I) cmpeq DivisorIdeal(J)) :
            "Ideals are not in the same quotient ring";

    return (PreimageIdeal(I) subset PreimageIdeal(J));

end intrinsic;

// ----------------------------------------------------------------

/*
intrinsic 'notsubset' (I::RngMPolRes, J::RngMPolRes) -> BoolElt
{Return false iff I is contained in J}

    require (DivisorIdeal(I) cmpeq DivisorIdeal(J)) :
            "Ideals are not in the same quotient ring";

    return (PreimageIdeal(I) notsubset PreimageIdeal(J));

end intrinsic;
*/

//////////////////////////
// ARITHMETIC OF IDEALS //
//////////////////////////


intrinsic '+' (I::RngMPolRes, J::RngMPolRes) -> RngMPolRes
{Return the ideal I + J}

//    require (DivisorIdeal(I) cmpeq DivisorIdeal(J)) :
//            "Ideals are not in the same quotient ring";

    basis_of_I := SequenceToSet(Basis(PreimageIdeal(I)));
    basis_of_J := SequenceToSet(Basis(PreimageIdeal(J)));

    K := ideal<Generic(I) | basis_of_I join basis_of_J>;
    return K;

end intrinsic;

// ----------------------------------------------------------------

intrinsic '*' (I::RngMPolRes, J::RngMPolRes) -> RngMPolRes
{Return the ideal I * J}

//    require (DivisorIdeal(I) cmpeq DivisorIdeal(J)) :
//            "Ideals are not in the same quotient ring";

    K := ideal<Generic(I) | PreimageIdeal(I) * PreimageIdeal(J) >;
    return K;

end intrinsic;

// ----------------------------------------------------------------

/*
intrinsic '^' (I::RngMPolRes, n::RngIntElt) -> RngMPolRes
{Return the ideal I ^ n}

    require n gt 0 :
        "Non-positive exponent";

    Tmp := I;
    for i in [2..n] do
        Tmp := Tmp*I;
    end for;   
    return Tmp;

end intrinsic;
*/

// ----------------------------------------------------------------

intrinsic ColonIdeal (I::RngMPolRes, J::RngMPolRes) -> RngMPolRes
{Return the colon ideal I:J (or ideal quotient of I by J), 
consisting of the polynomials f of P such that f * g
is in I for all g in J }

//    require (DivisorIdeal(I) cmpeq DivisorIdeal(J)) :
//            "Ideals are not in the same quotient ring";

    K := ideal<Generic(I) | ColonIdeal(PreimageIdeal(I), PreimageIdeal(J)) >;
    return K;

end intrinsic;

// ----------------------------------------------------------------
/*
 * Preimage( ) below is an undefined reference. BAS 9.1.02

intrinsic ColonIdeal (I::RngMPolRes, f::RngMPolResElt) -> RngMPolRes
{Return the saturation colon ideal}

//    require (DivisorIdeal(I) cmpeq DivisorIdeal(J)) :
//            "Ideals are not in the same quotient ring";

    K := ideal<Generic(I) | ColonIdeal(PreimageIdeal(I), Preimage(f)) >;
    return K;

end intrinsic;
*/


//////////////////////
// Ideal Predicates //
//////////////////////


intrinsic IsProper (I::RngMPolRes) -> BoolElt
{Return true iff I is not equal to the whole quotient ring}

    return IsProper(PreimageIdeal(I));

end intrinsic;

// ----------------------------------------------------------------


intrinsic IsMaximal (I::RngMPolRes) -> BoolElt
{Return true iff I is a maximal ideal}
/*(the
restrictions on I are the same as for the function
PrimaryDecomposition---see the description of that function)}
*/

    return IsMaximal(PreimageIdeal(I));

end intrinsic;

// ----------------------------------------------------------------

intrinsic IsPrimary (I::RngMPolRes) -> BoolElt
{Return true iff I is a primary ideal}
/*
.  An ideal I is primary 
if and only if for all ab in I, either a in I or b^n in I for some n >= 1.
The restrictions on I are the same as for the function
PrimaryDecomposition---see the description of that function. }
*/

    return IsPrimary(PreimageIdeal(I));

end intrinsic;

// ----------------------------------------------------------------

// The function IsPrime is implemented in C, for no particular reason.

// ----------------------------------------------------------------

intrinsic IsRadical (I::RngMPolRes) -> BoolElt
{True iff the ideal I is radical}
/*
that is, whether the radical of I is I itself. The restrictions on I 
are the same as for the function Radical---see the description of that 
function.  }
*/

    return IsRadical(PreimageIdeal(I));

end intrinsic;

// ----------------------------------------------------------------

intrinsic IsZero (I::RngMPolRes) -> BoolElt
{Return whether I is the zero ideal}
/*
.  This is true iff the preimage of I is contained
in or equal to the divisor ideal}
*/

    return (PreimageIdeal(I) subset DivisorIdeal(I));

end intrinsic;


//////////////////////////////////
// Ring Predicates and Booleans //
//////////////////////////////////

// intrinsic IsField (Q::RngMPolRes) -> BoolElt
// {Return true iff Q=P J is a field, which is true iff J is maximal}
// 
//    return IsMaximal(DivisorIdeal(Q));
// 
// end intrinsic;

// ----------------------------------------------------------------

// intrinsic IsDomain (I::RngMPolRes) -> BoolElt
// {Return true iff I is an integral domain, which is true iff J is prime}
// 
//    return IsPrime(DivisorIdeal(I));
// 
// end intrinsic;


//////////////////////////////////////
// Operations on Elements of Ideals //
//////////////////////////////////////

// Not yet implemented

///////////////////////////////
// Changing Coefficient Ring //
///////////////////////////////

intrinsic ChangeRing (I::RngMPolRes, S::Rng) -> RngMPolRes
{Given an ideal I of a quotient  ring 
P=R[x_1, ..., x_n] / J, where J is an ideal of R[x_1, ..., x_n], with
coefficient ring R, together with a ring S, construct the ideal J of the
polynomial ring Q=S[x_1, ..., x_n]/J obtained by coercing the coefficients 
of the elements of the basis of I into S. It is necessary that all elements 
of the old coefficient ring R can be automatically coerced into 
the new coefficient ring S}

    Pnew   := ChangeRing(OriginalRing (I), S);
    Jbasis := [Pnew!e : e in Basis(DivisorIdeal(I))];
    Ibasis := [Pnew!e : e in Basis(PreimageIdeal(I))];
    R      := ideal< quo< Pnew | Jbasis> | Ibasis>;
    return R;

end intrinsic;

/////////////////////////////////////////////////
// Radical and Primary Decomposition of Ideals //
/////////////////////////////////////////////////

intrinsic Radical (I::RngMPolRes) -> RngMPolRes
{The radical of I}

    R := ideal< Generic(I) | Radical(PreimageIdeal(I))>;
    return R;

end intrinsic;

// ----------------------------------------------------------------

intrinsic PrimaryDecomposition(I::RngMPolRes) -> [ ], [ ]
{The primary decomposition of ideal I}

    Q, P := PrimaryDecomposition(PreimageIdeal(I));
    G := Generic(I);
    Qprime := [ ideal< G | q> : q in Q  ];
    Pprime := [ ideal< G | p> : p in P  ];
    return Qprime, Pprime;

end intrinsic;

// ----------------------------------------------------------------

intrinsic RadicalDecomposition(I::RngMPolRes) -> []
{The (prime) decomposition of the radical of I; note that this may be 
different to the associated primes of I}

    R := RadicalDecomposition(PreimageIdeal(I));
    G := Generic(I);
    Rprime := [ ideal< G | r> : r in R  ];
    return Rprime;

end intrinsic;

// ----------------------------------------------------------------

/*
intrinsic ProbableRadicalDecomposition(I::RngMPolRes) -> [ ], [ ]
{  A probable (prime) decomposition of the radical of I }

    R := ProbableRadicalDecomposition(PreimageIdeal(I));
    G := Generic(I);
    Rprime := [ ideal< G | r> : r in R  ];
    return Rprime;

end intrinsic;
*/
