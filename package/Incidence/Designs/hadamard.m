freeze;

intrinsic IsHadamardEquivalent(H1::AlgMatElt, H2::AlgMatElt : Al := "nauty")
	-> BoolElt, AlgMatElt, AlgMatElt
{True iff the two Hadamard matrices are equivalent.  If so (and the nauty
algorithm is used) then transformation matrices X and Y are returned such
that H2 = X*H1*Y};

    require IsHadamard(H1) and IsHadamard(H2):
    "The input matrices must be Hadamard";

    if Al eq "nauty" then
	m1,X1,Y1 := HadamardCanonicalForm(H1);
	m2,X2,Y2 := HadamardCanonicalForm(H2);
	if m1 ne m2 then
	    return false,_,_;
	end if;
	return true, X2^-1*X1, Y1*Y2^-1;
    end if;

    return IsHadamardEquivalentLeon(H1, H2),_,_;
end intrinsic;

intrinsic HadamardMatrixToInteger(H::AlgMatElt) -> RngIntElt
{Returns an integer encoding the entries of the Hadamard matrix};
    Z := Integers();
    return Seqint([Sign(1-x) : x in ChangeUniverse(Eltseq(H), Z)], 2);
end intrinsic;

intrinsic HadamardMatrixFromInteger(x::RngIntElt, n::RngIntElt) -> AlgMatElt
{Returns a Hadamard matrix of dimension n as encoded by the integer x};
    Z := Integers();
    return MatrixRing(Z, n)![(-1)^k : k in Intseq(x, 2, n^2)];
end intrinsic;

