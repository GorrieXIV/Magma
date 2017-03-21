freeze;

declare verbose ModRep, 2;

/*******************************************************************************
			Mod rep (prime dividing)
*******************************************************************************/

Z := IntegerRing();
Q := RationalField();

function integral(
    M: p := 0, Prec := 0, StopED := 0, ERM := 0, D := 0, DoED := false
)

    NEW := true;
    NEW_INT := true;

    USE_MOD := true;
    USE_DEN := true and not USE_MOD;

    n := Dimension(M);

    L := ActionGenerators(M);

    if D eq 0 then
	D := LCM({Denominator(x): x in L});
    end if;

    vprint ModRep: "Denom LCM:", D;
    OD := D;

    modular := p gt 0;
    if modular then
	Dval := Valuation(D, p);
	vprint ModRep: "Dval:", Dval;

	D := p^Dval;
	vprint ModRep: "New D:", D;

	if Prec gt 0 then
	    prec := Prec;
	else
	    prec := 2*Dval + 2;
	    prec := 50;
	    prec := 14;

	    prec := Floor(Log(p, 2^23.5)); // to fit in double
	    //prec := 23;
	    ////prec := 20;
	end if;

	R := IntegerRing(p^prec);
	vprint ModRep: "prec:", prec;
	vprint ModRep: "R:", R;
	ER := R;

	NEW_INT := false;
    else
	R := Z;
	ER := R;

	if ERM ne 0 then
	    ER := IntegerRing(ERM);
	elif 1 eq 0 then
	    ER := IntegerRing(2*D);
	end if;
    end if;

    if StopED eq 0 then
	StopED := D;
    end if;

    function divmat(X, d)
	X := Matrix(Z, X);
	Y := X div d;
	if not d*Y eq X then
	    vprint ModRep: "FAIL div by", d;
	    vprint ModRep: "Bad x:", rep{x: x in Eltseq(X) | x mod d ne 0};
	    error "err";
	end if;
	return Matrix(R, Y);
    end function;

    function redmatd(X, d)
	X := Matrix(Z, X);
	Xg := GCD({X[i, j]: j in [1 .. Ncols(X)], i in [1 .. Nrows(X)]});
	assert Xg ne 0;
	
	vprint ModRep: "redmatd [Xg: %o, d: %o] -> ", Xg, d;

	g := GCD(Xg, d);
	Xg := Xg div g;
	d := d div g;
	vprint ModRep: "[Xg: %o, d: %o] (g %o)\n", Xg, d, g;

	if g ne 1 then
	    Y := X div g;
	    assert Y*g eq X;
	    X := Y;
	end if;
	X := Matrix(R, X);
	return X, d;
    end function;

    Ld := [1: i in [1 .. #L]];
    if USE_MOD then

	OL := [];
	OLd := [];
	OLdd := [];
	maxn := [];
	vprint ModRep: "Get max num"; vtime ModRep:
	for i := 1 to #L do
	    OL[i], d := IntegralMatrix(L[i]);
	    OLd[i] := GCD(d, D);
	    OLdd[i] := d div OLd[i];
	    vprint ModRep: "Max num", i; vtime ModRep:
	    Append(~maxn, Max(Eltseq(OL[i])) * ExactQuotient(OD, d));
	end for;

	vprint ModRep: "Max scaled numerators:", maxn;
	vprint ModRep: "OLd:", OLd;
	vprint ModRep: "OLdd:", OLdd;

	NB := Max(maxn);
	//NB := Max(Abs(X[i, j]): i, j in [1 .. n]});
B := NB*OD*1000;
	B := NB*1000;

	qlist := [];
	q := 2^Floor(23.5);
	P := 1;
	repeat
	    q := PreviousPrime(q);
	    Append(~qlist, q);
	    P *:= q;
	until P gt B;

	vprint ModRep: "Numerator bound:", NB;
	vprint ModRep: "Bound B:", B;
	vprint ModRep: "Num primes:", #qlist;

	Flist := [GF(q): q in qlist];

	vprint ModRep: "Get mod mats"; vtime ModRep:
	L := [<Matrix(F, x): F in Flist>: x in L];

	function mult(X, Xd, Y, Yd)
	    assert #X eq #Y;
	    return <X[i]*Y[i]: i in [1 .. #X]>, 1;
	end function;

    elif USE_DEN then
	OL := L;
	L := [];
	Ld := [];
	for i := 1 to #OL do
	    L[i], Ld[i] := redmatd(Matrix(R, D*OL[i]), D);
	end for;
	OL := L;
	OLd := Ld;

	function mult(X, Xd, Y, Yd)
	    X := X * Y;
	    vprint ModRep: "do redmatd"; vtime ModRep:
	    X, Xd := redmatd(X, Xd*Yd);
	    return X, Xd;
	end function;
    else
	//L := [Matrix(R, D*x): x in L];
	OL := L;

	function mult(X, Xd, Y, Yd)
	    X := X * Y;
	    "do div 1"; vtime ModRep:
	    X := divmat(X, D);
	    return X, Xd;
	end function;
    end if;

//"L:", L;
    vprint ModRep: "Input matrix denoms:", Ld;

    if 0 eq 1 then
	L := L cat L cat L;
	Ld := Ld cat Ld cat Ld;
    end if;

    U := L[1];
    Ud := Ld[1];

    if NEW then
	A := MatrixRing(R, n)!D;
    else
	A := ZeroMatrix(R, 0, n);
    end if;
    Ad := 1;

    if USE_MOD and NEW_INT then
	AF := <MatrixRing(F, n)!D: F in Flist>;
    end if;

    ZEIT := Cputime();

    function symmat(X, M)
	M2 := M div 2;
	m := Nrows(X);
	n := Ncols(X);
	return Matrix(Z, m, n, [x ge M2 select x - M else x: x in Eltseq(X)]);
    end function;

    AED := 0;

    failc := 0;
    count := 0;
    while true do
	count +:= 1;

vprint ModRep: "***";
	vprint ModRep: "Step", count, Cputime(ZEIT);
	vprint ModRep: "GB:", GetMemoryUsage()/2^30.0;

	i := Random(1, #L);
	repeat j := Random(1, #L); until j ne i;
	vprintf ModRep: "i: %o, j: %o\n", i, j;

	oldA := A;
	oldAd := Ad;

        if p le 2 then
            NR := 3;
        else
            NR := 1;
        end if;

vprint ModRep: "Do", NR, "random elts";
IndentPush();
vtime ModRep: for nr := 1 to NR do
	Xi := L[i];
	Xj := L[j];
	vprint ModRep: "Rand prod 1"; vtime ModRep:

	Xi, Ld[i] := mult(Xi, Ld[i], Xj, Ld[j]);
	L[i] := Xi;

// "new Xi:", Xi; "new Ld[i]:", Ld[i];
// "first U:", U; "first Ud:", Ud;

	vprint ModRep: "Rand prod 2"; vtime ModRep:
	U := mult(U, Ud, Xi, Ld[i]);

// "prod U:", U;
//end for; IndentPop();

	if USE_MOD and NEW_INT then

	    vprint ModRep: "Get AU"; vtime ModRep:
	    AU := mult(AF, 1, U, 1);
	    AU := [Matrix(Z, x): x in AU];

	    vprint ModRep: "Get CRT"; vtime ModRep:
	    AU := CRT(AU, qlist);
	    AU := symmat(AU, &*qlist);
//"CRT AU:", AU;
	    A := VerticalJoin(A, AU);
	    delete AU;

	elif USE_MOD then
//"U order:", [Order(x): x in U];
	    //Rq := IntegerRing(&*qlist);
	    vprint ModRep: "Get UU"; vtime ModRep:
	    UU := CRT([Matrix(Z, OD*x): x in U], qlist);
	    UU := symmat(UU, &*qlist);
	    //l, UU := RationalReconstruction(UU);
//"UU:", UU;
	    UU := Matrix(R, UU);

	    if NEW then
//		UU := 1/(R!(OD div D))*UU;
// "New UU:", UU;
		vprint ModRep: "Get A*UU"; vtime ModRep:
		AUU := A*UU;
//"AUU:", AUU;
		try
		    vprint ModRep: "divmat AUU by", D; vtime ModRep:
		    AUU := divmat(AUU, D);
		catch e
		    AUU := 0;
		end try;

		if AUU cmpeq 0 then
		    vprint ModRep: "FAIL AUU DIV!";
		    continue;
		end if;
//"div AUU:", AUU;
		A := VerticalJoin(A, AUU);
	    else
		A := VerticalJoin(A, UU);
	    end if;
	    delete UU;
	elif USE_DEN then
	    l := LCM(Ad, Ud);
	    vprint ModRep: "Ad:", Ad;
	    vprint ModRep: "Ud:", Ud;
	    vprint ModRep: "LCM:", l;
	    A := VerticalJoin((l div Ad)*A, (l div Ud)*U);
	    Ad := l;
	else
	    A := VerticalJoin(A, U);
	end if;
end for; IndentPop();

A := Matrix(ER, A);
	vprint ModRep: "Echelon over", ER; vtime ModRep:
	A := EchelonForm(A);
	RemoveZeroRows(~A);
A := Matrix(R, A);
	A := Matrix(A);
	//A := BasisMatrix(Rowspace(A));

	if USE_DEN then
	    vprint ModRep: "Fix A denom";
	    A, Ad := redmatd(A, Ad);
	end if;

	//"Diag:", Sort(Diagonal(A));
	vprint ModRep: "Diag:", SequenceToMultiset(Diagonal(A));

	if DoED then
	    vprint ModRep: "Get ED";
	    //vtime ModRep: ED := ElementaryDivisors(A);
	    vtime ModRep: ED := ElementaryDivisors(SparseMatrix(A));
	    vprint ModRep: "ED:", SequenceToMultiset(ED);
	else
	    vprint ModRep: "Skip ED";
	    ED := 0;
	end if;

	//"New A:", A;
	vprint ModRep: "Ad:", Ad;

	// Parent(A); "Hash A:", Hash(A);

	if Nrows(A) eq Ncols(A) and A cmpne oldA and (not DoED or ED[#ED] le StopED) then

//"A:", A;
vprint ModRep: "A density:", Density(A);

if 1 eq 1 then
    A := Matrix(Z, A);
end if;
	    vprint ModRep: "%%% Do PseudoInverse"; vtime ModRep:
	    AI, Ad := PseudoInverse(A);
	    vprint ModRep: "Ad:", Ad;
	    if Ad eq 0 then
		"ZERO; continue";
		continue;
	    end if;
//"AI:", AI;
vprint ModRep: "AI density:", Density(AI);

if modular then
    A := Matrix(R, A);
    AI := Matrix(R, AI);
    Ad := R!Ad;
end if;

	    vprint ModRep: "Conjugate"; vtime ModRep:
	    C := [A*x*AI: x in OL];
	    // "First C:", C;
	    if USE_MOD then
		C := [(R!OLdd[i])^-1*C[i]: i in [1 .. #C]];
		// "Scaled C:", C;
	    end if;

	    try
		vprint ModRep: "Div C"; vtime ModRep:
		CC := [divmat(x, Ad): x in C];
		//"Next CC:", CC;

		vprint ModRep: "Div CC"; vtime ModRep:
		C := [divmat(CC[i], OLd[i]): i in [1 .. #CC]];
	    catch e
		C := 0;
	    end try;
	    //"Final C:", C;

	    //if forall{i: i in [1 .. #C] | C[i]*D eq CC[i]} then
	    if C cmpne 0 then
		vprint ModRep: "GOOD";
		//"orig ord:", [Order(x): x in ActionGenerators(M)];
		//"L ord:", [Order(Matrix(Q, x)/D): x in OL];
		//"new ord:", [Order(x): x in C];
		if modular then
		    F := GF(p);
		    LF := [Matrix(F, x): x in C];
		else
		    LF := C;
		end if;
		if Type(M) eq ModGrp then
		    return GModule(Group(M), LF: Check:=false);
		end if;
		return RModule(LF);
	    end if;

	    vprint ModRep: "BAD";
	    if 0 eq 1 and modular then
		CC;
		vprint ModRep: "D:", D;
	    elif 0 eq 1 then
		//[Matrix(Q, Matrix(Z, x))/D: x in CC];

		vprint ModRep: "Bad denoms:",
		    {Denominator((Q!Z!x)/D): x in Eltseq(A), A in CC};
	    end if;
	    failc := 0;
	else
	    vprint ModRep: "Skip";
	    failc +:= 1;
	end if;

	if USE_MOD and NEW_INT then
	    AF := <Matrix(F, A): F in Flist>;
	end if;

//if count eq 10 then break; end if;
	//if failc eq 20 then break; end if;
    end while;

    return A;

end function;

/*******************************************************************************
				Mod rep
*******************************************************************************/

intrinsic GModule(M::ModGrp, p::RngIntElt: Prec := 0) -> ModGrp
{Reduce M mod p}

    G := Group(M);
    K := BaseRing(M);

    if Type(K) in {RngInt, FldRat} then
	try
	    return ChangeRing(M, GF(p));
	catch e
	    B := Isqrt(2^53 div Dimension(M));
	    vprint ModRep: "B:", B;

	    if Prec cmpeq 0 then
		Prec := Ilog(p, B);
	    end if;
	    vprint ModRep: "Use p-adic algorithm"; //, prec", Prec;
	    return integral(M: p := p, Prec := 0);
	end try;
    end if;

    f := DefiningPolynomial(K);
    F := GF(p);
    E<w> := SplittingField(PolynomialRing(F)!f);
    r := Roots(PolynomialRing(E)!f)[1, 1];
    h := hom<K -> E | r>;

    try
	return ChangeRing(M, E, h);
    catch e
	return GModule(Expand(M), p: Prec := Prec);
    end try;

end intrinsic;
