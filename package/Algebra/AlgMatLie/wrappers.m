freeze;

intrinsic MatrixLieAlgebra(A::AlgMat) -> AlgMatLie
{The matrix Lie algebra given by the Lie product on A}
  bas := Basis(A);
  mla := MatrixLieAlgebra( BaseRing(A), Degree(A) );
  if #bas eq 0 then 
	L := sub<mla | >;
  else
	L := sub<mla | [ Matrix(b) : b in bas ]>;
  end if;
  return L;  // we dont want to return the 2nd argument
end intrinsic;


intrinsic LieAlgebra(A::AlgMat) -> AlgLie
{A structure constant Lie algebra given by the Lie product on A}
  L := LieAlgebra( MatrixLieAlgebra(A) );
  return L;  // we dont want to return the 2nd argument
end intrinsic;

intrinsic Center(L::AlgMatLie) -> AlgMatLie
{The center of the matrix lie algebra L};

    A, m := Algebra(L);
    C := Center(A);
    return C @@ m;
end intrinsic;

intrinsic Centralizer(L::AlgMatLie, K::AlgMatLie) -> AlgMatLie
{The centralizer of the subalgebra K in L};

    require K subset L : "Argument 2 is not contained in Argument 1";
    A, m := Algebra(L);
    B := m(K);
    C := Centralizer(A, B);
    return C @@ m;
end intrinsic;

intrinsic Centralizer(L::AlgMatLie, x::AlgMatLieElt) -> AlgMatLie
{The centralizer of the element x in the Lie algebra L};

    require x in L : "Argument 2 must lie in argument 1";
    A, m := Algebra(L);
    C, Cm := Centralizer(A, m(x));
    C := C @@ m;
    return C;
end intrinsic;

intrinsic HasLeviSubalgebra(L::AlgMatLie) -> BoolElt, AlgMatLie
{A Levi subalgebra of the Lie algebra L}

    A, m := Algebra(L);
    b, levi := HasLeviSubalgebra(A);
    if b then
	return true, levi @@ m;
    else
	return false, _;
    end if;
end intrinsic;

intrinsic IsAbelian(L::AlgMatLie) -> BoolElt
{Test whether the Lie algebra L is abelian};

    return IsAbelian(Algebra(L));
end intrinsic;

intrinsic IsCartanSubalgebra(L::AlgMatLie, H::AlgMatLie) -> BoolElt
{True iff H is a Cartan subalgebra of L};

    return IsCartanSubalgebra(Algebra(L), Algebra(H));
end intrinsic;

intrinsic IsSemisimple(L::AlgMatLie) -> BoolElt
{Return whether L is semisimple};
    
    A := Algebra(L);
    return IsSemisimple(A);
end intrinsic;

intrinsic IsReductive(L::AlgMatLie) -> BoolElt
{True iff L is a semisimple Lie algebra};

    return IsReductive(Algebra(L));
end intrinsic;

intrinsic IsAssociative(L::AlgMatLie) -> BoolElt
{Return whether L is associative};

    return IsAssociative(Algebra(L));
end intrinsic;

intrinsic IsSimple(L::AlgMatLie) -> BoolElt
{Return whether L is simple (has no non-trivial ideals)};

    if Dimension(L) eq 1 then
	return false;
    end if;
    return IsSimple(Algebra(L));
end intrinsic;

intrinsic CartanSubalgebra(L::AlgMatLie) -> AlgMatLie
{The Cartan subalgebra of the Lie algebra L};

    A, m := Algebra(L);
    C := CartanSubalgebra(A);
    return C @@ m;
end intrinsic;

intrinsic IsNilpotent(L::AlgMatLie) -> BoolElt
{Test whether the Lie algebra L is nilpotent};

    return IsNilpotent(Algebra(L));
end intrinsic;

intrinsic IsSolvable(L::AlgMatLie) -> BoolElt
{Test whether the Lie algebra L is solvable};

    return IsSolvable(Algebra(L));
end intrinsic;

intrinsic IsSplittingCartanSubalgebra(L::AlgMatLie, H::AlgMatLie) -> BoolElt
{True iff H is a splitting Cartan subalgebra of L};
	require H subset L : "H must be a subalgebra of L";
	
	AL, phi := Algebra(L);
	AH := sub<AL | [ phi(L!b) : b in Basis(H) ]>;

    return IsSplittingCartanSubalgebra(AL, AH);
end intrinsic;

intrinsic SplittingCartanSubalgebra( L::AlgMatLie ) -> AlgMatLie
{A splitting Cartan subalgebra for L}

	A, m := Algebra(L);
	return SplittingCartanSubalgebra(A) @@ m;
end intrinsic;

intrinsic IsSplitToralSubalgebra(L::AlgMatLie, H::AlgMatLie) -> BoolElt
{True iff H is a toral subalgebra of L.};
	require H subset L : "H must be a subalgebra of L";

	AL, phi := Algebra(L);
	AH := sub<AL | [ phi(L!b) : b in Basis(H) ]>;

	return IsSplitToralSubalgebra(AL, AH);
end intrinsic;

intrinsic SplitToralSubalgebra( L::AlgMatLie : H0 := false, TryMaximal := true) -> AlgMatLie
{Find a split toral subalgebra of L, containing H0 if given.}

	if (H0 cmpne false) then
		require H0 subset L : "H0 must be a subalgebra of L";
	end if;

	AL, phi := Algebra(L);
	if (H0 cmpne false) then
		AH0 := sub<AL | [ phi(L!b) : b in Basis(H0) ]>;
		AH := SplitToralSubalgebra(AL : H0 := AH0, TryMaximal := TryMaximal);
	else
		AH := SplitToralSubalgebra(AL : TryMaximal := TryMaximal);
	end if;
	
	return AH @@ phi;
end intrinsic;



intrinsic Nilradical(L::AlgMatLie) -> AlgMatLie
{The nilradical of the Lie algebra L};

    A, m := Algebra(L);
    return Nilradical(A) @@ m;
end intrinsic;

intrinsic SolvableRadical(L::AlgMatLie) -> AlgMatLie
{The soluble radical of the Lie algebra L};

    A, m := Algebra(L);
    return SolvableRadical(A) @@ m;
end intrinsic;

intrinsic Normalizer(L::AlgMatLie, K::AlgMatLie) -> AlgMatLie, Map
{The normalizer of ideal K in the Lie algebra L};

    A, m := Algebra(L);
    N, nm := Normalizer(A, Algebra(K));
    return N @@ m, nm*Inverse(m);
end intrinsic;

intrinsic CanonicalGenerators(L::AlgMatLie) -> SeqEnum, SeqEnum, SeqEnum
{A set of canonical generators of the semisimple Lie algebra L}
    A, m := Algebra(L);
    a, b, c := CanonicalGenerators(A);
    return a @@ m, b @@ m, c @@ m;
end intrinsic;

intrinsic ChevalleyBasis(L::AlgMatLie) -> SeqEnum, SeqEnum, SeqEnum
{A Chevalley basis of L}
    require IsReductive(L) : "Algebra must be reductive";
    A, m := Algebra(L);
    a, b, c := ChevalleyBasis(A);
    return a @@ m, b @@ m, c @@ m;
end intrinsic;

intrinsic DerivedSeries(L::AlgMatLie) -> SeqEnum
{The derived series of the Lie algebra L}

    A, m := Algebra(L);
    return DerivedSeries(A) @@ m;
end intrinsic;

intrinsic DirectSumDecomposition(L::AlgMatLie) -> SeqEnum
{The decomposition of L as a direct sum of indecomposable ideals}
    A, m := Algebra(L);
    return DirectSumDecomposition(A) @@ m;
end intrinsic;

intrinsic IndecomposableSummands(L::AlgMatLie) -> SeqEnum
{The decomposition of L as a direct sum of indecomposable ideals}
    A, m := Algebra(L);
    return DirectSumDecomposition(A) @@ m;
end intrinsic;

intrinsic KillingForm(L::AlgMatLie) -> AlgMatElt
{The killing form of A}
    return KillingForm(Algebra(L));
end intrinsic;

intrinsic KillingMatrix(L::AlgMatLie) -> ModMatFldElt
{The matrix of the Killing form of L}
    return KillingMatrix(Algebra(L));
end intrinsic;

intrinsic LowerCentralSeries(L::AlgMatLie) -> SeqEnum
{The lower central series of the Lie algebra L}
    A, m := Algebra(L);
    return LowerCentralSeries(A) @@ m;
end intrinsic;

intrinsic NilRadical(L::AlgMatLie) -> AlgMatLie
{The nilradical of the Lie algebra L}
    return Nilradical(L);
end intrinsic;

intrinsic RootDatum(L::AlgMatLie) -> RootDtm
{The root datum of the Lie algebra L}
    return RootDatum(Algebra(L));
end intrinsic;

intrinsic RootSystem(L::AlgMatLie) -> SeqEnum, SeqEnum, SeqEnum, SeqEnum
{The root system of a semisimple Lie algebra}
    A, m := Algebra(L);
    a, b, c, d := RootSystem(A);
    return a, b @@ m, c, d;
end intrinsic;

intrinsic UpperCentralSeries(L::AlgMatLie) -> SeqEnum
{The upper central series of the Lie algebra L}
    A, m := Algebra(L);
    return UpperCentralSeries(A) @@ m;
end intrinsic;

intrinsic SemisimpleType(L::AlgMatLie) -> MonStgElt
{The Cartan type of a semisimple Lie algebra}

    F:= CoefficientRing( L );
    require not Characteristic( F ) in [ 2, 3 ] :
           "The field of definition must not be of characteristic 2 or 3.";

    require Dimension( L ) gt 0 : "The dimension of L must be > 0.";

    // We test whether the Killing form of L is nondegenerate.
    d:= Determinant(KillingMatrix(L));
    require not IsZero(d) : "The Killing form of L is degenerate.";

    return SemisimpleType(Algebra(L));
end intrinsic;

intrinsic CartanName(L::AlgMatLie) -> MonStgElt
{The Cartan name of the reductive Lie algebra L}
    F:= CoefficientRing( L );
    require not Characteristic( F ) in [ 2, 3 ] :
           "The field of definition must not be of characteristic 2 or 3.";

    require Dimension( L ) gt 0 : "The dimension of L must be > 0.";

    // We test whether the Killing form of L is nondegenerate.
    d:= Determinant(KillingMatrix(L));
    require not IsZero(d) : "The Killing form of L is degenerate.";

    return CartanName(Algebra(L));
end intrinsic;

intrinsic LieAlgebra(L::AlgMatLie) -> AlgLie
{Construct a structure-constant Lie algebra isomorphic to L}
  return Algebra(L);
end intrinsic;

intrinsic '+'(x::AlgMatLie,y::AlgMatLie) -> AlgMatLie
{Sum of x and y}
  ok, L := ExistsCoveringStructure(x,y);
  require ok : "No covering structure";
  sum := sub< L | [ x.i : i in [1..Ngens(x)]] cat 
    [ y.i : i in [1..Ngens(y)]] >;
  return sum;
end intrinsic;


