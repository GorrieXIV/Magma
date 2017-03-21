freeze;

/*
Code for emedding one finite field in another.
By Eric Rains.
Fiddled with and installed by Allan Steel, July 2007.
*/

// this computes a single Gauss period

UniqueNormalElement1:=function(F,m1,n1)
    nF:=Degree(F);
    char := Characteristic(F);
    P:=PolynomialAlgebra(F);
    Fm:=Integers(m1);
    o2:=Order(Fm!char);
    k:=o2 div Gcd(o2,nF); // order of required extension

    if (k gt 1) then
	if char eq 2 then
	    p:=P!IrreducibleLowTermGF2Polynomial(k);
	else
	    p:=P!IrreduciblePolynomial(GF(char),k);
	end if;
	Fk:=ext<F|p: Check := false>;
// "p:", p;
    else
	Fk:=F;
    end if;

    rm1:=(char^(nF*k)-1) div m1;

    vprintf FFEmbed: "UniqueNormalElement1: F degree: %o, m1: %o, n1: %o\n",
		Degree(F), m1, n1;
    vprintf FFEmbed: "Extension degree: %o\n", k;
    vprintf FFEmbed: "k degree: %o, exponent bits: %o\n",
	Degree(Fk), Ilog2(rm1);

// "#Fk bits:", Ilog2(#Fk);
//x:=rm1; mm:=#Fk - 1;
//printf "x := %o;\n", x; printf "m := %o;\n", mm;

    vtime FFEmbed:
	repeat
//"pow"; time
	    psi:=Random(Fk)^rm1;
	until not (psi eq 1 or psi eq 0);

    // now psi is a primitive m1th root.

    // There are now two cases: Gcd(n1,(m1-1) div o2)=1 or 2.
    if (Gcd(n1,(m1-1) div o2) eq 1) then
	I:={Fm| i^n1: i in Fm | i ne 0};
	// We now need to compute the Gauss period corresponding to I.
	GP1:=Fk!0;
	for i in I do
	    GP1:=GP1+psi^(Integers()!i);
	end for;
	GP1:=F!GP1;
    else
	assert char eq 2;
	g:=Sqrt(Fm!2);
	np:=n1;
	while ((np mod 2) eq 0) do
	    np:=np div 2;
	end while;
	g:=g^(np);

	I:={Fm| i^(2*n1): i in Fm | i ne 0};
	GP1:=Fk!0;
	for i in I do
	    GP1:=GP1+psi^(Integers()!i);
	end for;

	// Now we need to compute a trace from the field of degree n1.
	T:=Fk!0;
	for i:=0 to n1-1 do
	    T:=T+GP1;
	    GP1:=GP1^2;
	end for;
	if (T eq 0) then
	    g:=1/g;
	end if;
	for i in I do
	    GP1:=GP1+psi^(Integers()!(g*i));
	end for;
	GP1:=F!GP1;
    end if;
    return(-GP1);// so it has trace 1 from its subfield...
end function;

// It doesn't look like it's worth using the subfield approach internally
// to this case.
function UniqueNormalElement2(F,n2)
    char := Characteristic(F);
PF := PrimeField(F);
    // We need an element of trace 1
    t1:=Random(F);
    while (Trace(t1, PF) ne 1) do
	t1:=Random(F);
    end while;
    if n2 eq 0 then return(F!1); end if;
    GP1:=0;
    t1:=t1^char;
    t2:=1;
    for j:=2 to Degree(F) do
	GP1:=GP1+t1*t2;
	t1:=t1^char;
	t2:=t2+1;
    end for;
    if (char eq 2) then
	GP:=GP1;
    else
	GP:=1/GP1;
    end if;
    if n2 eq 1 then return(GP); end if;
    for i:=2 to n2 do
	GP1:=0;
	t1:=t1^char;
	t2:=GP;
	GP:=GP^char;
	for j:=2 to Degree(F) do
	    GP1:=GP1+t1*t2;
	    t1:=t1^char;
	    t2:=t2+GP;
	    GP:=GP^char;
	end for;
	if (char eq 2) then
	    GP:=GP*GP1;
	else
	    GP:=GP^2/GP1;
	end if;
    end for;
    return GP;
end function;

// note that this won't quite work with the new EmbedNumbers...
UniqueNormalElement_old:=function(F,ms,ns,n2)
    nF:=Degree(F);
    char := Characteristic(F);
    P:=PolynomialAlgebra(F);
    GP:=F!1;
    for f:=1 to #ms do
	GP*:=UniqueNormalElement1(F,ms[f],ns[f]);
    end for;
    if (n2 ge 1) then
	GP*:=UniqueNormalElement2(F,n2);
    end if;
    return GP;
end function;

UniqueNormalElement:=function(F,ms,ns,n2)
    nF:=Degree(F);
    char := Characteristic(F);
    P:=PolynomialAlgebra(F);

PF := PrimeField(F);

    // determine the degrees of the subfields we need to compute
    if true then
	degs:=ns;
    else
	// might be better; pushes more of the degree into the coefficient field
	// in the relative extensions we need.
	ords:=[Integers()|Order(GF(m)!char):m in ms];
	degs:=[Integers()|GCD(o,nF):o in ords];
	// make sure we can use an irreducible poly. over the prime field
	repeat
	    gcds:=[GCD(ords[i] div degs[i],degs[i]):i in [1..#degs]];
	    degs:=[degs[i]/gcds[i]:i in [1..#degs]];
	until Maximum(gcds) eq 1;
    end if;

    if (n2 gt 0) then Append(~degs,char^n2); end if;

    // compute generators of subfields [sub<F|d>:d in degs];
    // probably do something different in large characteristic!
    gens:=[F|0:i in [1..#degs]];
    Pc:=PolynomialAlgebra(GF(char));
    plys:=[Pc|0:i in [1..#degs]];
    repeat
	bad:=false;
	u:=Random(F);
	u0:=F!u;
	for i in [0..nF-Minimum(degs)] do
	    for f in [1..#degs] do
		if i mod degs[f] eq 0 then gens[f]+:=u0; end if;
	    end for;
	    u0:=u0^char;
	end for;
	for f in [1..#degs] do
	    if degs[f] ne nF then
		plys[f]:=MinimalPolynomial(gens[f], PF);
		if Degree(plys[f]) ne degs[f] then
		    bad:=true;
		end if;
	    end if;
	end for;
    until not bad;


// "ms:", ms;
// "plys:", plys;
    // now compute the main Gauss period
    GP:=F!1;
    for f:=1 to #ms do
	if degs[f] eq nF then
	    GP*:=UniqueNormalElement1(F,ms[f],ns[f]);
	else
	    Ff:=ext<GF(char)|plys[f]: Check := false>;
	    if 0 eq 1 then
		deg := Degree(plys[f]);
		vprint FFEmbed: "Create Ff2 of degree", deg;
		vtime FFEmbed: Ff2 := ext<GF(char) | deg>;
		vprint FFEmbed: "Now embed in Ff";
		IndentPush();
		vtime FFEmbed: Embed(Ff2, Ff);
		IndentPop();

		GP*:=Evaluate(
		    Pc!Eltseq(Ff!UniqueNormalElement1(Ff2,ms[f],ns[f])),gens[f]
		);
	    else
		GP*:=Evaluate(
		    Pc!Eltseq(UniqueNormalElement1(Ff,ms[f],ns[f])),gens[f]
		);
	    end if;
	end if;
    end for;

    // and throw in the Artin-Schreier term
    if (n2 ge 1) then
	if degs[#ms+1] eq nF then
	    GP*:=UniqueNormalElement2(F,n2);
	else
	    Ff:=ext<GF(char)|plys[#ms+1]: Check := false>;

	    if 0 eq 1 then
		deg := Degree(plys[#ms+1]);
		vprint FFEmbed: "Create Ff2 of degree", deg;
		vtime FFEmbed: Ff2 := ext<GF(char) | deg>;
		vprint FFEmbed: "Now embed in Ff";
		IndentPush();
		vtime FFEmbed: Embed(Ff2, Ff);
		IndentPop();
		GP*:=Evaluate(Pc!Eltseq(Ff!UniqueNormalElement2(Ff2,n2)),gens[#ms+1]);
	    else

		GP*:=Evaluate(Pc!Eltseq(UniqueNormalElement2(Ff,n2)),gens[#ms+1]);
	    end if;
	end if;
    end if;
    return GP;
end function;

function EmbedNumbers(p, n)
    ms := [];
    ns := [];
    n2 := 0;
    fact := Factorization(n);
    for f in fact do
	if f[1] eq p then
	    n2 := f[2];
	else
	    np := f[1]^f[2];
	    Append(~ns, np);
	    // find m
	    flag := false;
	    k := 0;
	    repeat
		// m is such that order o_m(p) of p mod m is a multiple of np
		repeat
		    k +:= 1;
		    while (IsPrime(k*np + 1) eq false) or
			(((k*np+1) mod p) eq 0) do
			k +:= 1;
		    end while;
		    F := Integers(k*np + 1);
		    ord := Order(F!p);
		until (ord mod np) eq 0;
		flag := true;
		// degree of extension
		ord_div := ord div np;
		// avoid the case of an extension not prime to np
		if Gcd(np, ord_div) ne 1 then
		    flag := false;
		end if;
		// (n, phi(m)/o_m(p)) == 1 ?
		if Gcd(np, k*np div ord) ne 1 then
		    flag := false;
		end if;
	    until flag eq true;
	    Append(~ms, k*np + 1);
	end if;
    end for;

    return ms, ns, n2;
end function;

intrinsic InternalEmbedRains(F1::FldFin, F2::FldFin, S::FldFin)
{Internal}

    /*
    AKS:
    Turned off Jan 16 (since only called when subfield relation not yet set).

    if IsSubfield(F1, F2) then
        return;
    end if;
    */

// "EMBED"; TES(F1); TES(F2);

HACK := false;
HACK := true;
    if HACK then
	OF1 := F1;
	g1 := Generator(F1, S);
	mp := MinimalPolynomial(g1, S);
	F1 := ext<S | mp>;
    end if;

    p := Characteristic(F1);
    assert Characteristic(F2) eq p;

    degreeF1 := Degree(F1);
    degreeF2 := Degree(F2);

    if (degreeF2 mod degreeF1) ne 0 then
	error "Error - not subfield\n";
    end if;

    // (maybe) Don't do this!
    // magma does extra stuff we might not want
    //  F2 := sub<F2|degreeF1>;

    vprintf FFEmbed: "Rains Embed: degree %o into degree %o\n",
	degreeF1, degreeF2;

    ms, ns, n2 := EmbedNumbers(p, degreeF1);
    vprintf FFEmbed: "ms = %o, ns = %o, n2 = %o\n", ms, ns, n2;

    vprint FFEmbed: "Get UniqueNormalElement 1";
    vtime FFEmbed: GP1:=UniqueNormalElement(F1,ms,ns,n2);

    //printf "GP1= %o\n", GP1;
    //  if not IsNormal(GP1) then
    //    printf "Error - not normal\n";
    //    exit;
    //  end if;
    //printf "%o\n", MinimalPolynomial(GP1);

    vprint FFEmbed: "Get UniqueNormalElement 2";
    vtime FFEmbed: GP2:=UniqueNormalElement(F2,ms,ns,n2);

    //printf "GP2= %o\n", GP2;
    //  if not IsNormal(GP2) then
    //    printf "Error - not normal\n";
    //    exit;
    //  end if;
    //printf "%o\n", MinimalPolynomial(GP2);

    PF := PrimeField(F1);

    if S ne PF then
	dS := Degree(S);
	vprintf FFEmbed: "Proper subfield of degree %o (quotients %o, %o)\n",
	    dS, degreeF1 div dS, degreeF2 div dS;

//"MP(GP1, S):", MinimalPolynomial(GP1, S);
//"MP(GP2, S):", MinimalPolynomial(GP2, S);
//"MP 2:", [MinimalPolynomial(Frobenius(GP2, PF, i), S): i in [0..Degree(F2,S)-1]];

	fc := 0;
	m1 := MinimalPolynomial(GP1, S);
	vtime FFEmbed:
	    while Evaluate(m1, GP2) ne 0 do
		fc +:= 1;
		GP2 := Frobenius(GP2, PF, 1);
	    end while;

	vprintf FFEmbed: "%o application(s) of Frobenius\n", fc;
    end if;

    // The remainder of this procedure should ideally read
    //
    // Embed(F1,F2,GP1,GP2)
    //
    // for a suitable internal function Embed that does the linear algebra
    // and whatever else magma wants to do once it's got its hands on a
    // subfield.

    if HACK then
	GP1 := Seqelt(Eltseq(GP1, S), OF1);
	F1 := OF1;
    end if;

if 1 eq 1 then
    // AVOIDS creating extra fields!
    vprint FFEmbed: "Get GP1 powers matrix";

    t := F1!1;
    mat := [Eltseq(t, PF)];
    for i := 2 to degreeF1 do
	t *:= GP1;
	Append(~mat, Eltseq(t, PF));
    end for;
    mat := Matrix(mat);
    v := Parent(mat[1]).2; // (0, 1, 0, ...) corresponds to F1.1 over PF
    v := Solution(mat, v); // Coordinates of F1.1 w.r.t. powers of GP1
    x := Evaluate(Polynomial(Eltseq(v)), GP2); // image of F1.1 in F2

else
    // the next line is a possibly expensive magma internal
    vprint FFEmbed: "Get FI sub";
    vtime FFEmbed: FI:=sub<F1|GP1>;
    //printf "FI= %o\n", FI;
    //printf "%o\n", Generator(FI);

    // the image of F1.1 in F2

    vprint FFEmbed: "Evaluate at GP2";
    //F1gen := F1.1;
    F1gen := Generator(F1, PF);
    vtime FFEmbed: x:=Evaluate(Polynomial(Eltseq(FI!F1gen)),GP2);
    delete FI;
end if;

    // the next line is a possibly expensive magma internal
    vprint FFEmbed: "Internal Embed";

    /*
    AKS:
    Check false added Jan 16 (to avoid recursive relshp derive calls)
    */

    vtime FFEmbed: Embed(F1,F2,x: Check := false);

    // the old version Embed(FI,F2,GP2) makes the first cast from F1 to F2 slow
    // in 2.12

end intrinsic;

intrinsic CheckEmbed(F1::FldFin, F2::FldFin: Count := 10)
{Internal}

    for i := 1 to Count do
	a := Random(F1);
	b := Random(F1);
	aa := F2!a;
	bb := F2!b;
	assert F2!(a + b) eq aa + bb;
	assert F2!(a * b) eq aa * bb;
    end for;

end intrinsic;
