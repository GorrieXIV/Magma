freeze;

/////////////////////////////////////////////////////////////////////////
// utilities.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 48644 $
// $Date: 2014-10-16 22:02:43 +1100 (Thu, 16 Oct 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Utilities for working with Cox data.
/////////////////////////////////////////////////////////////////////////

intrinsic AreGradingsEquivalent( W1::SeqEnum[SeqEnum[RngIntElt]],
    W2::SeqEnum[SeqEnum[RngIntElt]] ) -> BoolElt,AlgMatElt,GrpPermElt
{True iff there exists an element M in GL(n,Z) and permutation sigma in Sym(m) such that (M * W1)^sigma equals W2, where W1 and W2 are sequences of length n > 0, whose entries are integer sequences of length m > 0.}
    // Sanity check
    require #W1 eq #W2: "Arguments must be of the same length";
    require #W1 ne 0: "Arguments must not be empty";
    m1:=#W1[1];
    require &and[#W eq m1 : W in W1]:
        "The sequences contained in argument 1 must all be of the same length";
    m2:=#W2[1];
    require &and[#W eq m2 : W in W2]:
        "The sequences contained in argument 2 must all be of the same length";
    require m1 eq m2:
        "The sequences contained in the arguments must all be of the same length";
    require m1 gt 0:
        "The sequences contained in the arguments must not be empty";
    // Extract the divisors
    D1:=RowSequence(Transpose(Matrix(W1)));
    D2:=RowSequence(Transpose(Matrix(W2)));
    // We use the polytope machinery to build a change of basis
    P1:=Polytope(D1);
    P2:=Polytope(D2);
    bool,phi:=IsIsomorphic(P1,P2);
    if not bool then
        return false,_,_;
    end if;
    // Map the divisors across
    ChangeUniverse(~D1,Ambient(P1));
    D1:=Matrix(phi(D1));
    D2:=[Eltseq(v) : v in D2];
    Sort(~D2,~perm2);
    // We might require an automorphism action
    for M in AutomorphismGroup(P2) do
        DD1:=[Eltseq(v) : v in RowSequence(D1 * M)];
        Sort(~DD1,~perm1);
        if DD1 eq D2 then
            return true,Transpose(DefiningMatrix(phi) * M),perm2^-1 * perm1;
        end if;
    end for;
    // If we get here, the gradings were different
    return false,_,_;
end intrinsic;