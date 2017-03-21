freeze;

/*******************************************************************************
			    Product by ideal
*******************************************************************************/

is_compatible := func<M, I | Generic(BaseRing(M)) cmpeq Generic(I)>;

intrinsic '*'(M::ModMPol, I::RngMPol) -> ModMPol
{M*I}
    require is_compatible(M, I): "Arguments are not compatible";
    MB := SmallBasis(M);
    IB := SmallBasis(I);
    return sub<Ambient(M) | [g*x: g in MB, x in IB]>;
end intrinsic;

intrinsic '*'(I::RngMPol, M::ModMPol) -> ModMPol
{I*M}
    require is_compatible(M, I): "Arguments are not compatible";
    MB := SmallBasis(M);
    IB := SmallBasis(I);
    return sub<Ambient(M) | [x*g: g in MB, x in IB]>;
end intrinsic;

intrinsic '*'(M::ModMPol, f::RngMPolElt) -> ModMPol
{M*f}
    require is_compatible(M, Parent(f)): "Arguments are not compatible";
    MB := SmallBasis(M);
    return sub<Ambient(M) | [g*f: g in MB]>;
end intrinsic;

intrinsic '*'(f::RngMPolElt, M::ModMPol) -> ModMPol
{f*M}
    require is_compatible(M, Parent(f)): "Arguments are not compatible";
    MB := SmallBasis(M);
    return sub<Ambient(M) | [f*g: g in MB]>;
end intrinsic;

/*******************************************************************************
			    Annihilator
*******************************************************************************/

intrinsic Annihilator(M::ModMPol) -> RngMPol
{The annihilator of the R-module M, which is the ideal I
of R ring of M such that f*M = 0 for all f in I};

    return ColonIdeal(sub<M|>, M);
end intrinsic;

/*******************************************************************************
				Direct Sum
*******************************************************************************/

intrinsic DirectSum(L::List) -> ModMPol, [], []
{The direct sum of the modules in the sequence L and the corresponding
embedding and projection maps}

    require #L gt 0: "Sum must be non-trivial";
    require forall{M: M in L | ISA(Type(M), ModMPol)}:
	"Summands are not modules";

    P := BaseRing(L[1]);
    require forall{M: M in L | BaseRing(M) cmpeq P}: "Modules not compatible";

    B := DirectSum(<BasisMatrix(M): M in L>);
    R := DirectSum(<RelationMatrix(M): M in L>);
    P := BaseRing(B);
    n := Ncols(R);
    assert Ncols(B) eq n;

    is_reduced := exists{M: M in L | IsReduced(M)};
    if IsLocal(L[1]) then
	if is_reduced then
	    G := RModule(P, n);
	else
	    G := EModule(P, n);
	end if;
    else
	W := &cat[ColumnWeights(M): M in L];
	assert #W eq n;
	if forall{M: M in L | Type(M) eq ModMPolGrd} then
	    G := GradedModule(P, W);
	elif is_reduced then
	    G := RModule(P, W);
	else
	    G := EModule(P, W);
	end if;
    end if;

    D := sub<G | Rows(B)>;
    D := quo<D | Rows(R)>;

    emb := [];
    proj := [];
    c := 0;
    n := Degree(D);
    for M in L do
	d := Degree(M);
	X := ZeroMatrix(P, d, n);
	for i := 1 to d do
	    X[i, c + i] := 1;
	end for;

	h := Homomorphism(M, D, X);
	Append(~emb, h);

	h := Homomorphism(D, M, Transpose(X));
	Append(~proj, h);

	c +:= d;
    end for;

    return D, emb, proj;
end intrinsic;

intrinsic DirectSum(L::[ModMPol]) -> ModMPol, [], []
{The direct sum of the modules in the sequence L and the corresponding
embedding and projection maps}

    return DirectSum([* M: M in L *]);
end intrinsic;

intrinsic DirectSum(M::ModMPol, N::ModMPol) -> ModMPol, [], []
{The direct sum of modules M and N and the corresponding embedding and
projection maps}

    return DirectSum([* M, N *]);
end intrinsic;

/*******************************************************************************
				Fitting Ideals
*******************************************************************************/

intrinsic FittingIdeal(M::ModMPol, i::RngIntElt) -> RngMPol
{The i-th Fitting ideal of M}

    requirege i, 0;

    M := Presentation(M);
    X := PresentationMatrix(M);
    m := Ncols(X);
    if i ge m then
	L := [BaseRing(M) | 1];
    else
	L := Minors(X, m - i);
    end if;
    return Ideal([Universe(L) | f: f in L | not IsZero(f)]);
end intrinsic;

intrinsic FittingIdeals(M::ModMPol) -> []
{The Fitting ideals of M}

    M := Presentation(M);
    return [FittingIdeal(M, i): i in [0 .. Degree(M)]];
end intrinsic;
