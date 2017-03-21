freeze;

good_R := func<R | Type(R) in {FldFin, RngIntRes, RngGal}>;

// Several basic codes,		Lancelot Pecquet, 1996

intrinsic ZeroCode(R::Rng, n::RngIntElt) -> Code
{Return the [n,0,n] zero code over R}
	require good_R(R): "Bad base ring";
	requirege n,1;
	return LinearCode<R,n | [0: i in [1 .. n]]>;
end intrinsic;

intrinsic UniverseCode(R::Rng, n::RngIntElt) -> Code
{Return the [n,n,1] universe code over R}
	require good_R(R): "Bad base ring";
	requirege n,1;
	C := LinearCode(RSpace(R,n));
	C`MinimumWeight := 1;
        C`MinimumWeightLowerBound := 1;
        C`MinimumWeightUpperBound := 1;
        return C;
end intrinsic;

intrinsic RepetitionCode(R::Rng, n::RngIntElt) -> Code
{Return the [n,1,n] code over R with repeating codewords}
	requirege n,1;
	require good_R(R): "Bad base ring";
	C :=  LinearCode<R,n | [1: i in [1 .. n]]>;
	C`MinimumWeight := n;
        C`MinimumWeightLowerBound := n;
        C`MinimumWeightUpperBound := n;
	return C;
end intrinsic;

intrinsic ZeroSumCode(R::Rng, n::RngIntElt) -> Code
{Return the [n,n-1,2] code over R
of codewords whose elements sum to zero}
	require good_R(R): "Bad base ring";
	requirege n,1;
	C := Dual(RepetitionCode(R,n));
	C`MinimumWeight := 2;
	C`MinimumWeightLowerBound := 2;
	C`MinimumWeightUpperBound := 2;
	return C;
end intrinsic;

intrinsic EvenWeightCode(n::RngIntElt) -> Code
{Return the [n,n-1,2] even-weight code over GF(2)}
	requirege n,1;
	return ZeroSumCode(GF(2),n);
end intrinsic;

intrinsic EvenWeightSubcode(C::CodeLinFld) -> CodeLinFld
{Returns the subcode of C of words of even weight}
    if #Alphabet(C) ne 2 then
	error "Code must be a linear binary code";
    end if;
    return sub<C | C meet EvenWeightCode(Length(C))>;
end intrinsic;

/********************** additive versions *****************************/

intrinsic AdditiveZeroCode(F::FldFin, K::FldFin, n::RngIntElt) -> CodeAdd
{Return the [n,0,n] zero K-additive code over F}
        require K subset F: "F must contain K";
        requirege n,1;

	return AdditiveCode(K, Matrix(F, 0, n, []) );
end intrinsic;

intrinsic AdditiveRepetitionCode(F::FldFin, K::FldFin, n::RngIntElt) -> CodeAdd
{Return the [n, 1(Degree(F, K)), n] K-additive code over F 
consisting of all repeating codewords}
        require K subset F: "F must contain K";
        requirege n,1;

	elts := [F| 1 : i in [1..n]];

	m := Degree(F, K);
	prim := PrimitiveElement(F);
	al := F!1;
	for i in [2..m] do
	    al *:= prim;
	    elts cat:= [ al : i in [1..n]];
	end for;

	G := Matrix(F, m, n, elts);
	
        C := AdditiveCode(K, G);
	C`MinimumWeight := n;
        C`MinimumWeightLowerBound := n;
        C`MinimumWeightUpperBound := n;

	return C;
end intrinsic;

intrinsic AdditiveZeroSumCode(F::FldFin, K::FldFin, n::RngIntElt) -> CodeAdd
{Return the [n,n-1,2]  K-additive code over F
of codewords whose elements sum to zero}
	require K subset F: "F must contain K";
        requirege n,1;
        C := AdditiveCode(K, ZeroSumCode(F,n));
        return C;
end intrinsic;


intrinsic AdditiveUniverseCode(F::FldFin, K::FldFin, n::RngIntElt) -> CodeAdd
{Return the length n K-additive code over F consisting of all codewords}
    return AdditiveCode(K, UniverseCode(F, n));
end intrinsic;


//////////////////////////////////////

intrinsic TraceInnerProduct(K::FldFin, v::ModTupFldElt, w::ModTupFldElt)
                                                                -> FldFinElt
{The trace of the inner product of v and w};

    F := CoefficientRing(v);
    require CoefficientRing(w) eq F: "Vectors must be over that same field";
    require K subset F: "K must be a subfield of the coefficient field";

    return Trace( InnerProduct(v,w), K);

end intrinsic;


intrinsic MinimumWord(C::Code) -> ModTupRngElt
{A word of Minimum Weight};

    require Dimension(C) gt 0 : "C must be non-zero";

    S := MinimumWords(C : NumWords := 1 );
    return Representative(S);
end intrinsic;
