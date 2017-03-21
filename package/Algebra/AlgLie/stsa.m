freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "stsa-char2.m":findSTSAChar2;
import "stsa-char3.m":findSTSACharNot2;

function DR_IsSTSA(L, H) //->BoolElt
/* Is H a split toral subalgebra of L? */
	local pols, polsok, minpols, minpolsok, ar, ok, ok0, BH;

	BH := [ L!b : b in Basis(H) ];

	ar := AdjointRepresentation(L : ComputePreImage := false);
	ok := true;

	//Commuting
	ok0 := forall{<b,c> : b,c in BH | IsZero(L!b*L!c)};
	vprintf ChevBas, 4: "[IsSTSA]: Basis elts commute:             %o\n", ok0; 
	ok := ok and ok0;
		
	//Linear factors only in adjoint action
	pols := [ Factorization(CharacteristicPolynomial(Matrix(ar(L!b)))) : b in BH ];
	polsok := [ forall{f : f in p | Degree(f[1]) eq 1} : p in pols ];
	ok0 := &and(polsok);

	vprintf ChevBas, 4: "[IsSTSA]: Linear factors only:            %o (%o)\n",
		ok0, &cat([ p select "+" else "-" : p in polsok]);
	vprintf ChevBas, 4: "[IsSTSA]: Total degrees of factorization: %o\n",
			[ &+[ f[2] : f in p ] : p in pols ];
	ok := ok and ok0;

	//Minimal polynomials squarefree
	minpols := [ Factorization(MinimalPolynomial(Matrix(ar(L!b)))) : b in BH ];
	minpolsok := [ forall{f : f in p | f[2] eq 1} : p in minpols ];
	ok0 := &and(minpolsok);
	vprintf ChevBas, 4: "[IsSTSA]: Minimalpolynomial squarefree:   %o (%o)\n",
		ok0, &cat([ p select "+" else "-" : p in minpolsok]);
	ok := ok and ok0;

	//Conclusion
	vprintf ChevBas, 4: "[IsSTSA]: %o\n", ok select "OK" else "FAIL"; 
	return ok;
end function;

intrinsic SplitToralSubalgebra(L::AlgLie : H0 := false, TryMaximal := true) -> AlgLie
{Find a split toral subalgebra of L, containing H0 if given.}

	/* Check cached */
	if assigned L`SplitMaximalToralSubalgebra then
		H := L`SplitMaximalToralSubalgebra;
		if (H0 cmpeq false) or forall{b : b in Basis(H0) | L!b in H} then
			return H;
		end if;
	end if;
	
	/* Do stuff */
	c := Characteristic(BaseRing(L));
	if c eq 2 then
		H := findSTSAChar2(L : StartH := H0, TryMaximal := TryMaximal);
	elif IsOdd(c) and IsFinite(BaseRing(L)) then
	//elif c eq 3 then
		H := findSTSACharNot2(L : StartH := H0, TryMaximal := TryMaximal);
	else
		if H0 cmpne false then error "Passing H0 is not supported in this case of the algorithm"; end if;
		H := SplittingCartanSubalgebra(L);
	end if;

	return H;
end intrinsic;

intrinsic InternalfindSTSAChar2(L::AlgLie : H0 := false) -> AlgLie
{Internal}
	return findSTSAChar2(L : StartH := H0);
end intrinsic;

intrinsic InternalfindSTSACharNot2(L::AlgLie : H0 := false) -> AlgLie
{Internal}
	return findSTSACharNot2(L : StartH := H0);
end intrinsic;


