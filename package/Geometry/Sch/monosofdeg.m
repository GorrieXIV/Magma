freeze;

/////////////////////////////////////////////////////////////////////////
// monosofdeg.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 45096 $
// $Date: 2013-11-22 03:16:51 +1100 (Fri, 22 Nov 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Alexander Kasprzyk and Gavin Brown
/////////////////////////////////////////////////////////////////////////
// Calculates the monomials of given multi-degree on the ambient scheme.
/////////////////////////////////////////////////////////////////////////

intrinsic MonomialsOfWeightedDegree( A::Sch, S::SeqEnum[RngIntElt] )
    -> SetIndx,SetIndx
{All monomials of weighted degree S[i] with respect to the i-th grading of the ambient space of A. If there exists an infinite number of such monomials, the second return value will describe the generators of the kernel.}
    // Extract the data we'll need
    A:=Ambient(A);
    W:=Gradings(A);
    // Sanity check on the number of degrees
    require #S eq #W:
        Sprintf("The length of the degree sequence must match the number of gradings (%o) of the ambient space",#W);
    // Recover the vectors
    CP,IP:=MonomialsOfWeightedDegree(W,S);
    R:=CoordinateRing(A);
    n:=Rank(R);
    return {@ R | &*[R.i^v[i] : i in [1..n]] : v in CP @},
           {@ R | &*[R.i^v[i] : i in [1..n]] : v in IP @};
end intrinsic;

intrinsic MonomialsOfWeightedDegree( W::SeqEnum[SeqEnum[RngIntElt]],
    S::SeqEnum[RngIntElt] ) -> SetIndx,SetIndx
{All vectors of weighted degree S[i] with respect to the i-th grading of the ambient space of A. If there exists an infinite number of such monomials, the second return value will describe the generators of the kernel.}
    // Sanity check
    require #W ne 0: "There must be at least one grading";
    n:=#W[1];
    require n ne 0: "The gradings must be on non-zero length";
    require &and[#w eq n : w in W]:
        "The gradings must all be of the same length";
    require #S eq #W:
        Sprintf("The length of the degree sequence must match the number of gradings (%o)",#W);
    // Build the inequalities describing the polyhedron of solutions
	M:=Matrix(W);
	I:=IdentityMatrix(Integers(),Ncols(M));
	inequs:=RowSequence(M) cat RowSequence(-M) cat RowSequence(I);
	cs:=S cat [-d : d in S] cat ZeroSequence(Integers(),Ncols(M));
    // Create the polyhedron
	P:=PolyhedronWithInequalities(inequs,cs);
    // Extract and return the results
    CP:={@ PowerSequence(Integers()) | Eltseq(v) :
                                        v in Points(CompactPart(P)) @};
    IP:={@ PowerSequence(Integers()) | Eltseq(v) :
                                        v in ZGenerators(InfinitePart(P)) @};
	return CP,IP;
end intrinsic;
