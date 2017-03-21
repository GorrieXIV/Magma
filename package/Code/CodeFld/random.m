freeze;

// Random Linear Code,          Lancelot Pecquet, 1996

good_R := func<R | Type(R) in {FldFin, RngIntRes, RngGal}>;

intrinsic RandomLinearCode(R::Rng,n::RngIntElt,k::RngIntElt) -> Code
{Return a random linear code of length n over R with k generators}
    require good_R(R): "Bad base ring";
    requirege n, 1;
    requirerange k, 0, n;
    RS := RMatrixSpace(R, k, n );
    repeat
	C := LinearCode( Random(RS) );
    until Ngens(C) eq k;
    return C;
end intrinsic;

// Random Linear Code,		Lancelot Pecquet, 2000

intrinsic RandomLinearCode(n::RngIntElt,k::RngIntElt,R::Rng) -> Code
{Return a random linear code of length n over R with k generators}
    return RandomLinearCode(R, n, k);
end intrinsic;

intrinsic RandomAdditiveCode(F::FldFin, K::FldFin, n::RngIntElt, k::RngIntElt)
                                                             -> CodeAdd
{Return a random additive code of length n from F, with dimension k
over the coefficient ring K (a subfield of F)};

    require Characteristic(K) eq Characteristic(F) and
		K subset F: "K is not a subfield of F";

    m := Degree(F, K);

    requirege n, 1;
    requirerange k, 0, m*n;

    FS := KMatrixSpace(F, k, n);
    repeat
	C := AdditiveCode(K, Random(FS) );
    until Ngens(C) eq k;
    return C;

end intrinsic;

intrinsic SyndromeDecoding(C::CodeLinFld, v::ModTupRngElt) -> BoolElt, ModTupRngElt
{Given vector v from the ambient space of code C, return true and the decoded vector from v if possible, false otherwise.}
    return Decode(C, v : Al := "Syndrome");
end intrinsic;

intrinsic SyndromeDecoding(C::CodeLinFld, Q::SeqEnum[ModTupRngElt]) -> SeqEnum, SeqEnum
{Given vector v from the ambient space of code C, attempt to decode the vectors from Q; return sequences B and D so that for each Q[i], B[i] tells whether the vector was decodable and D[i] gives the decoded vector if B[i] is true.}
    return Decode(C, Q : Al := "Syndrome");
end intrinsic;

