freeze;

/*
Discrete logarithm for invertible matrices.
AKS, Jul 2012.
*/

intrinsic Log(B::AlgMatElt, X::AlgMatElt) -> AlgMatElt
{The logarithm to base B of X; i.e., an integer l such that B^l = X
(both matrices must be over a finite field and invertible and such an l
must exist)}

    K := BaseRing(X);
    require ISA(Type(K), FldFin): "Matrix must be over a finite field";

    PK := PolynomialRing(K); x := PK.1;
    q := #K;
    p := Characteristic(K);

    J, T, F := JordanForm(B);
    require Coefficient(F[1,1], 0) ne 0: "Matrix is not invertible";

    X := T*X*T^-1;

// "J:", J; "Conj X:", X;

    res := 0;
    M := 0;
    last_g := PK!0;
    last_l := 0;
    b := 1;
    XB := <>;
    pc := 0;
    for fi := 1 to #F do
	t := F[fi];
	"fi:", fi, "t:", t;
	IndentPush();

	g, e := Explode(t);
	//assert e eq 1;
	d := Degree(g);

	JS := Submatrix(J, b,b, d*e,d*e);
	XS := Submatrix(X, b,b, d*e,d*e);

	//f := PK!Eltseq(XS[1]); assert Degree(f) lt d;

	if e gt 1 then
	    "Multiplicity:", e;
	    mJ := Ilog(p, e - 1) + 1; // Ceil(Log_p(e))
	    // p^mJ is in order of J
	    "mJ:", mJ;

	    gX := MinimalPolynomial(XS);
	    "gX:", gX;
	    eX := Valuation(gX, g);
	    require eX le e: "Not a power (multiplicity wrong)";
	    mX := eX eq 1 select 0 else Ilog(p, eX - 1) + 1;
	    
	    "eX:", eX;
	    "mX:", mX;

	    md := mJ - mX;
	    assert md ge 0;
	    pc := Max(pc, md);

	    // "md:", md; "new pc:", pc;

	    XS := XS^p^mX;
	    "New XS:", XS;
	    XS := Submatrix(X, b,b, d,d);
JS := Submatrix(JS, b,b, d,d);
	    // Check diag block sum
	end if;

	// "g:", g;

	if d eq Degree(last_g) then
	    "Re-use same degree";
	    l := last_l;
	else

	    L := ext<K | g>;
	    y := Eltseq(XS[1]);
	    y := SequenceToElement(y, L);
    assert MinimalPolynomial(y) eq MinimalPolynomial(XS);

	    // "y:", y;
	    "Get log";
	    L;
	    time l := Log(L.1, y); // Force L.1, in case it not primitive
	    last_l := l;

	    "Got l:", l;
	end if;

	// "JS^l:", JS^l; "XS:", XS;
	assert JS^l eq XS;

	Md := q^d - 1;
	if M eq 0 then
	    res := l;
	    M := Md;
	else
	    while true do
		gcd := GCD(M, Md);
		if gcd eq 1 then
		    break;
		end if;
		"GCD", gcd;
		assert res mod gcd eq l mod gcd;
		Md := Md div gcd;
		l := l mod Md;
	    end while;
	    res := CRT([res, l], [M, Md]);
	    M *:= Md;
	end if;
	"New M:", M;
	"New res:", res;

	IndentPop();

	//Append(~XB, Y);
	b +:= d*e;
	last_g := g;
    end for;

    return LCM(res, p^pc);
    // return res * p^pc;
end intrinsic;

/*

repeat X:=Random(MatrixAlgebra(GF(2), 10)); until IsUnit(X) and Order(X) mod 2^3
eq 0; FactoredMinimalPolynomial(X); Order(X);
time Log(X, X^2);

*/
