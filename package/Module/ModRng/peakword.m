freeze;

/*
Peakwords for internal Hom algorithm.
AKS, Jan 2010.
*/

intrinsic Peakwords(L: M1 := 0, M2 := M1, WantInd := [1 .. #L]) -> [], []
{Peakwords for list L}

    ZEIT := Cputime();
    hom_case := M1 cmpne M2;

    want_ind := Set(WantInd);

    M := L[1];
    K := BaseRing(M);
    x := PolynomialRing(K).1;
    nag := Nagens(M);
    l := #L;

    cdim := [];
    for i := 1 to #L do
	f, _, e := IsAbsolutelyIrreducible(L[i]);
	Append(~cdim, f select 1 else e);
    end for;

    if M1 cmpne 0 then
	Append(~L, M1);
	if hom_case then
	    Append(~L, M2);
	end if;
    end if;

    rand_coeffs := func<| [Random(K): i in [1 .. nag]]>;
    //eval_coeffs := func<A, rc | &+[rc[i]*A.i: i in [1 .. nag]]>;
    nullspace_dim := func<X | Nrows(X) - Rank(X)>;

    Multi := true;
    Multi := false;
    nr := nag + 2;

    vprintf Hom: "Multi: %o, nag: %o, nr: %o\n", Multi, nag, nr;

    function eval_coeffs(A, rc)
	X := Generic(A)!0;
	for i := 1 to nag do
	    c := rc[i];
	    if not IsZero(c) then
		AddScaledMatrix(~X, c, A.i);
	    end if;
	end for;
	return X;
    end function;

    LA := [Action(T): T in L];
    MW := [];
    MW2 := MW;
    res := [* 0: i in [1 .. l] *];

    rc := rand_coeffs();
    if Multi then
	LWA := <[eval_coeffs(A, rc): i in [1 .. nr]]: A in LA>;
    else
	LW := <eval_coeffs(A, rc): A in LA>;
    end if;

    count := 0;
    while true do
	count +:= 1;

	if Multi then
	    j := Random(1, nr);
	    repeat k := Random(1, nr); until k ne j;

	    rc1 := rand_coeffs();

	    LW := <>;
	    for i in [1 .. #LA] do
		LWA[i, j] := LWA[i, j]*LWA[i, k] + eval_coeffs(LA[i], rc1);
		Append(~LW, LWA[i, j]);
	    end for;
	else
	    for c := 1 to 1 do
		rc1 := rand_coeffs();
		rc2 := rand_coeffs();
		LW := <
		    LW[i]*eval_coeffs(LA[i], rc1) + eval_coeffs(LA[i], rc2):
		    i in [1 .. #LW] >;
	    end for;
	end if;

	for i in want_ind do
	    SW := LW[i];

	    if #K eq 2 and cdim[i] eq 1 then
		fact := [<x, 1>, <x + 1, 1>];
	    elif 1 eq 1 then
		cp := CharacteristicPolynomial(SW);
		sqf := SquarefreeFactorization(cp);
		qd := #K^cdim[i];
//i, cdim[i];
		fact := &cat[
		    Factorization(GCD(Modexp(x, qd, t[1]) - x, t[1])): t in sqf
		];
//fact; FactoredCharacteristicPolynomial(SW);
	    else
		fact := FactoredCharacteristicPolynomial(SW);
	    end if;

	    for t in fact do
		f := t[1];
		if Degree(f) ne cdim[i] then
		    continue;
		end if;
		fSW := Evaluate(f, SW);
		d := nullspace_dim(fSW);
		if d gt 0 and nullspace_dim(fSW^2) eq d then
		    good := true;
		    fLW := <>;
		    for j := 1 to l do
			if j eq i then
			    fT := fSW;
			else
			    fT := Evaluate(f, LW[j]);
			    if nullspace_dim(fT) gt 0 then
				good := false;
				break;
			    end if;
			end if;
			Append(~fLW, fT);
		    end for;

		    if good then
			vprintf Hom: "Found %o after %o tries (%o)\n",
			    i, count, Cputime(ZEIT);

			res[i] := fLW;

			if M1 cmpne 0 then
			    MW[i] := Evaluate(f, LW[l + 1]);
			    if hom_case then
				MW2[i] := Evaluate(f, LW[l + 2]);
			    end if;
			end if;
			Exclude(~want_ind, i);
			if #want_ind eq 0 then
			    if M1 cmpeq 0 then
				return res, _, _;
			    end if;
			    if not hom_case then
				MW2 := MW;
			    end if;
			    return res, MW, MW2;
			end if;
			break;
		    end if;

		    delete fLW;

		end if;
	    end for;
	end for;

    end while;

end intrinsic;

intrinsic InternalHomPeakwords(M::ModRng, M2::ModRng) -> [], []
{Internal}

    hom_case := M cmpne M2;

    J := JacobsonRadical(M);
    C := Constituents(M / J);

    vprint Hom: "Get peakwords for:", C;
    vtime Hom: _, MW, MW2 := Peakwords(C: M1 := M, M2 := M2);

    Jspace := Rowspace(Morphism(JacobsonRadical(M), M));
    GN := Generic(Jspace);

    gens := <>;
    NQ := <>;

    //vtime Hom: for i := 1 to #MW do
    vtime Hom: for i := #MW to 1 by -1 do
	vprint Hom: i;
	X := MW[i];
	Y := X;
	if hom_case then
	    X2 := MW2[i];
	    Y2 := X2;
	end if;
	Yrank := Rank(Y);
	vtime Hom: while true do
	    new := Y*X;
	    newrank := Rank(new);
	    if newrank eq Yrank then
		break;
	    end if;
	    Y := new;
	    Yrank := newrank;
	    if hom_case then
		Y2 := Y2*X2;
	    end if;
	end while;

	vtime Hom: N := Nullspace(Y);
	vprint Hom: "LHS nullity:", Dimension(N);

	NJ, NJf := N/(N meet Jspace);
	k := Dimension(NJ);
	vprint Hom: "N/J dim:", k;
	repeat
	    g := [GN | Random(N): i in [1 .. k]];
	until Rank(Matrix(NJf(g))) eq k;

	if hom_case then
	    vtime Hom: N := Nullspace(Y2);
	    vprint Hom: "RHS nullity:", Dimension(N);
	end if;

	Append(~gens, Matrix(g));
	Append(~NQ, BasisMatrix(N));

    end for;

    vprint Hom: "Peakword structure:",
	[<Nrows(gens[i]), Nrows(NQ[i])>: i in [1 .. #NQ]];

    return gens, NQ;

end intrinsic;
