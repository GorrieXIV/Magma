freeze;

/*
Functions to convert a chain of polynomial rings & field extensions
into canonical form and associated operations.

Allan Steel, Feb 2003.
*/

/*******************************************************************************
			    Convert to standard field
*******************************************************************************/

DEBUG := true;
DEBUG := false;

apply_sprint := func<Q | [Sprint(x): x in Q]>;

function conv(R: force_dpoly := true, force_dpolyq := false)
/*
Given generic polynomial ring R over chain, create canonical polynomial
ring C over polynomial quotient ring over rational function field, and
return maps R -> C, C -> R and C.
*/

    Rt := Type(R);

    AddAttribute(Rt, "InternalConvForward");
    AddAttribute(Rt, "InternalConvBackward");

    if assigned R`InternalConvForward then
	f := R`InternalConvForward;
	fi := R`InternalConvBackward;
	P := Codomain(f);
	return f, fi, P;
    end if;

    S := BaseRing(R);
    if Type(S) eq RngUPolRes and Type(BaseRing(S)) eq FldFin then

	/*
	This handles the case of a polynomial quotient over a finite
	field; move to extension finite field...
	*/

	SS := BaseRing(S);
	mf := Modulus(S);
	F := ext<SS | mf>;
	cf := hom<S -> F | F.1>;

	/*
	Make sure simple coercion used in linear ext case.
	*/

	if Degree(F) eq 1 or Degree(mf) eq 1 then
	    cfi := map<F -> S | x :-> S!x>;
	else
	    cfi := hom<F -> S | S.1>;
	end if;
	r := Rank(R);
	P := PolynomialRing(F, r);
	f := hom<R -> P | cf, [P.i: i in [1 .. r]]>;
	fi := hom<P -> R | cfi, [R.i: i in [1 .. r]]>;
	return f, fi, P;
    end if;

    is_dpoly_alff := func<S |
	Degree(S) cmpeq Infinity() and not IsRationalFunctionField(S)>;
    is_rff_alff := func<S |
	Degree(S) cmpeq Infinity() and IsRationalFunctionField(S)>;

    polyi := 0;
    L := <>;
    LI := <>;

    // <polyv, algv, transv>

    now_in_field := false;
    S := R;
    last := S;
    while true do
	is_poly := false;
	Append(~L, S);
	case Type(S):
	when RngUPol:
	    if now_in_field then
		u := <[], [], [R!last!S.i: i in [1 .. Rank(S)]]>;
	    else
		is_poly := true;
		u := <[S.1], [], []>;
	    end if;
	when RngMPol:
	    if now_in_field then
		u := <[], [], [R!last!S.i: i in [1 .. Rank(S)]]>;
	    else
		is_poly := true;
		u := <[S.i: i in [1 .. Rank(S)]], [], []>;
	    end if;
	when RngUPolRes:
	    u := <[], [S.1], []>;
	when RngMPolRes, FldFunFracSch:
	    u := <[], [S.i: i in [1 .. Rank(S)]], []>;
	when FldFun:
/*
"S:", S;
"Degree(S):", Degree(S);
"is_dpoly_alff:", is_dpoly_alff(S);
*/
	    if is_dpoly_alff(S) then
		u := <[], [S.1], [R!S.2]>;
	    elif is_rff_alff(S) then
		u := <[], [], [S.1]>;
            else    
		u := <[], GeneratorsSequence(S), []>;
	    end if;
	when FldFunOrd:
	    S := FieldOfFractions(Order(S));
	    u := <[], ChangeUniverse(GeneratorsSequence(FunctionField(Order(S))), S), []>;
	when FldFunRat:
	    u := <[], [], [R!S.i: i in [1 .. Rank(S)]]>;
	else:
	    base := S;
	    Prune(~L);
	    break;
	end case;
	if not is_poly then
	    now_in_field := true;
	end if;
	if not is_poly and polyi eq 0 then
	    polyi := #L - 1;
	end if;
	Append(~LI, u);
	last := S;
	S := BaseRing(S);
    end while;

    npolyv := &+[#t[1]: t in LI];
    nalgv := &+[#t[2]: t in LI];
    ntransv := &+[#t[3]: t in LI];

    if DEBUG then
	"L:";
	for i := 1 to #L do
	    printf "%o: %o, %o\n", i, L[i], LI[i];
	end for;
	"base:", base;
	"polyi:", polyi;

	"npolyv:", npolyv;
	"nalgv:", nalgv;
	"ntransv:", ntransv;
    end if;

    if ntransv eq 0 then
	F := base;
    else
	F := FunctionField(base, ntransv);
	AssignNames(~F, &cat[apply_sprint(t[3]): t in LI]);
    end if;
    if nalgv eq 0 then
	AP := F;
    else
	if not force_dpolyq and nalgv eq 1 then
	    AP := PolynomialRing(F);
	else
	    AP := PolynomialRing(F, nalgv);
	end if;
	AssignNames(~AP, &cat[apply_sprint(t[2]): t in LI]);
    end if;

    if DEBUG then
	"F:", F;
	"AP:", AP;
    end if;

    FV := [AP!F.i : i in [1 .. ntransv]];
    APV := [AP.i : i in [1 .. nalgv]];

    function make_field_maps(S, RHS, make_rels)
	rels := [];
	//LF := <>;

	f := Coercion(base, RHS);
	algv := nalgv;
	transv := ntransv;

	for i := #L to polyi + 1 by -1 do
	    if DEBUG then
		"******", i;
	    end if;
	    S := L[i];
	    case Type(S):
	    when RngUPolRes:
		nf := hom<S -> RHS | f, APV[algv]>;
		if make_rels then
		    modulus := Modulus(S);
		    mf := hom<Parent(modulus) -> RHS | f, APV[algv]>;
		    Append(~rels, mf(modulus));
		end if;
		algv -:= 1;
	    when RngMPolRes, FldFunFracSch:
		/*
		This returns m_dpoly_idealq_user_ngens(S) so counts
		the subfield transcendental var in FldFunFracSch case, so use
		this to define the map on S's gens:
		*/
		av := Rank(S);
		ims := [APV[j]: j in [algv - av + 1 .. algv]];

/*
"S:", S;
"Type(S):", Type(S);
"BaseRing(S):", BaseRing(S);
"PreimageIdeal(S):", PreimageIdeal(S);
"S.1:", S.1;
"P S.1:", Parent(S.1);
"S.2:", S.2;
"P S.2:", Parent(S.2);
"algv:", algv;
"av:", av;
"APV:", APV;
"ims:", ims;
*/
		nf := hom<S -> RHS | f, ims>;
		if make_rels then
		    /*
		    Reset av to use the actual dpoly rank (which will
		    be 1 in FldFunFracSch case) to map J gens:
		    */
		    J := DivisorIdeal(S);
		    av := Rank(J);
		    ims := [APV[j]: j in [algv - av + 1 .. algv]];
/*
"HOM dom:", Generic(J);
"HOM codom:", RHS;
"f:", f;
"ims2:", ims;
*/
		    mf := hom<Generic(J) -> RHS | f, ims>;
		    rels cat:= [mf(g): g in Basis(J)];
		end if;
		algv -:= av;
	    when FldFun:
		if is_dpoly_alff(S) then
		    //ims := [APV[algv - 1], APV[algv]];
		    ims := [APV[algv], FV[transv]];
		    nf := hom<S -> RHS | f, ims>;
		    if make_rels then
			/*
			modulus := DefiningPolynomial(S);
			mf := hom<Parent(modulus) -> RHS | f, ims>;
			*/
			RER := RationalExtensionRepresentation(S);
			modulus := MinimalPolynomial(RER ! S.2);
			mp := Parent(modulus);
			mf := hom<mp -> RHS |
			    hom<BaseRing(mp) -> RHS | f, ims[1]>, ims[2]>;
			Append(~rels, mf(modulus));
		    end if;
		    //algv -:= 2;
		    algv -:= 1;
		    transv -:= 1;
		elif is_rff_alff(S) then
		    nf := hom<S -> RHS | f, [FV[transv]]>;
		    transv -:= 1;
		else
                    if IsSimple(S) then
                      nf := hom<S -> RHS | f, APV[algv]>;
                    else
                      nf := hom<S -> RHS| f, APV[algv-Ngens(S)+1..algv]>;
                    end if;
		    if make_rels then
                        if IsSimple(S) then
                          modulus := DefiningPolynomial(S);
                          modulus := PolynomialRing(BaseRing(S)) ! modulus;
                          mf := hom<Parent(modulus) -> RHS | f, APV[algv]>;
                          Append(~rels, mf(modulus));
                        else
                          modulus := DefiningPolynomials(S);
                          modulus := [PolynomialRing(BaseRing(S), f)];
                          mf := hom<Parent(modulus[1]) -> RHS | f, APV[algv-Ngens(S)+1..algv]>;
                          rels cat:= [mf(f) : f in modulus];
                        end if;
		    end if;
		    algv -:= Ngens(S);
		end if;
	    when FldFunOrd:
		SS := FunctionField(Order(S));
                ff := hom<CoefficientRing(SS) -> RHS | x :-> f(x)>;
                if IsSimple(SS) then
                  SShom := hom<SS -> RHS | ff, APV[algv]>;
                  nf := hom<S -> RHS | x :-> SShom(SS!x)>;
                  if make_rels then
                      modulus := DefiningPolynomial(Order(S));
                      modulus := PolynomialRing(BaseRing(SS)) ! modulus;
                      mf := hom<Parent(modulus) -> RHS | ff, APV[algv]>;
                      Append(~rels, mf(modulus));
                  end if;
                else
                  SShom := hom<SS -> RHS| ff, APV[algv-Ngens(SS)+1..algv]>;
                  nf := hom<S -> RHS | x :-> SShom(SS!x)>;
                  if make_rels then
                      modulus := DefiningPolynomials(SS);
                      modulus := [Polynomial(BaseRing(SS), f)  : f in modulus];
                      rels cat:= [ hom<Parent(modulus[i]) -> RHS | ff, APV[algv-Ngens(SS)+i]>(modulus[i]) : i in [1..#modulus]];
                  end if;
                end if;
		algv -:= Ngens(SS);
	    //when FldFunRat:
	    when FldFunRat, RngMPol, RngUPol:
		tv := Rank(S);
/*
"RHS:", RHS;
"FV:", FV;
"transv:", transv;
"tv:", tv;
*/
// "Universe(FV):", Universe(FV);
		nf := hom<
		    S -> RHS | f, [FV[j]: j in [transv - tv + 1 .. transv]]
		>;
		transv -:= tv;
	    //when RngMPol, RngUPol:
		//nf := hom<S -> RHS | f, [S.i: i in [1 .. Rank(S)]] >;
	    else:
		error "DIE in field loop!!!", Type(S);
	    end case;

	    if DEBUG then
		"i:", i;
		"nf:", nf;
		"new rels:", rels;
	    end if;

	    //LF[i] := nf;
	    f := nf;
	end for;
	return f, rels;
    end function;

    APf, A_rels := make_field_maps(R, AP, true);

    if DEBUG then
	"First f:", APf;
	"A_rels:", A_rels;
	"univ A_rels:", Universe(A_rels);
    end if;

    if nalgv eq 0 then
	A := AP;
    else
	A := quo<AP | Reverse(A_rels)>;
	AssignNames(~A, &cat[apply_sprint(t[2]): t in LI]);
    end if;

    Af := make_field_maps(R, A, false);

    if not force_dpoly and npolyv eq 1 then
	P := PolynomialRing(A);
    else
	P := PolynomialRing(A, npolyv);
    end if;
    AssignNames(~P, &cat[apply_sprint(t[1]): t in LI]);
    PV := [P.i: i in [1 .. npolyv]];

    //f := Af;
    f := hom<Domain(Af) -> P | x :-> P!Af(x)>;

    polyv := npolyv;
    for i := polyi to 1 by -1 do
	if DEBUG then
	    "%%%%", i, f;
	end if;
	S := L[i];
	case Type(S):
	when RngUPol:
	    nf := hom<S -> P | f, PV[polyv]>;
	    polyv -:= 1;
	when RngMPol:
	    pv := Rank(S);
	    nf := hom<S -> P | f, PV[polyv - pv + 1 .. polyv]>;
	    polyv -:= pv;
	else:
	    error "DIE in poly ring loop!!!";
	end case;
	f := nf;
    end for;

    seq1A :=  &cat[[R!x: x in t[1]]: t in LI];

    if DEBUG then
	"seq3:", &cat[t[3]: t in LI];
	"seq2:", &cat[t[2]: t in LI];
	"seq1:", &cat[t[1]: t in LI];
	"seq1 A:", seq1A;
    end if;

    // "F:", F; Type(F); Rank(F); "R:", R; "LI:", LI;

    fi := hom<F -> R | &cat[t[3]: t in LI]>;
    if nalgv gt 0 then
	fi := hom<A -> R | fi, &cat[t[2]: t in LI]>;
    end if;
    //fi := hom<P -> R | fi, &cat[t[1]: t in LI]>;
    fi := hom<P -> R | fi, seq1A>;

    if DEBUG then
	"P.1:", P.1;
	"fi(P.1):", fi(P.1);
	"fi(F.1):", fi(F.1);
    end if;

    R`InternalConvForward := f;
    R`InternalConvBackward := fi;

    return f, fi, P;
end function;

/*******************************************************************************
			    GCD & Factorization
*******************************************************************************/

function conv_gcd(f, g)
    R := Parent(f);
    error if Parent(g) cmpne R, "conv_gcd(): incompatible arguments!";

    h, hi := conv(R);

    c := GCD(h(f), h(g));
    return Normalize(hi(c));
end function;

function conv_fact(f, sqf_only)
    R := Parent(f);

    h, hi := conv(R);
    f := h(f);
/*
"conv f:", f;
Parent(f);
B := BaseRing(Parent(f));
B;
IsField(B);
*/
    try
	L := sqf_only select SquarefreeFactorization(f) else Factorization(f);
    catch e
	return false, e;
    end try;
//"conv L:", L;

    return true, [<Normalize(hi(t[1])), t[2]>: t in L];
end function;

/*******************************************************************************
		    Decomposition/Radical of Canonical ideal
*******************************************************************************/

function expand_ideal(I: Radicalize := false)
    P := Generic(I);
    A := BaseRing(P);
    F := BaseRing(A);

    if ISA(Type(A), RngMPolRes) then
	AJ := DivisorIdeal(A);
	A_rels := GroebnerBasis(AJ);
	AP := Generic(AJ);
	nalgv := Rank(AP);
    elif Type(A) eq RngUPolRes then
	M := Modulus(A);
	AP := Parent(M);
	A_rels := [M];
	nalgv := 1;
    else
	F := A;
	AP := A;
	A_rels := [];
	nalgv := 0;
    end if;

    npolyv := Rank(P);
    ntransv := Rank(F);

    E := PolynomialRing(F, npolyv + nalgv);
    AssignNames(
	~E,
	[Sprint(P.i): i in [1 .. npolyv]] cat
	[Sprint(A.i): i in [1 .. nalgv]]
    );

    if nalgv gt 0 then
	Ah := hom<A -> E | [E.(npolyv + i): i in [1 .. nalgv]]>;
	Ph := hom<P -> E | Ah, [E.i: i in [1 .. npolyv]]>;
    else
	Ph := hom<P -> E | [E.i: i in [1 .. npolyv]]>;
    end if;

    B := GroebnerBasis(I);
    if Radicalize then
	for i := 1 to #B do
	    B[i] := SquarefreePart(B[i]);
	end for;
    end if;
    E_rels := [Ph(f): f in B];

    if nalgv gt 0 then
	APh := hom<AP -> E | [E.(npolyv + i): i in [1 .. nalgv]]>;
	Ah := hom<A -> E | [E.(npolyv + i): i in [1 .. nalgv]]>;
	E_rels cat:= [APh(f): f in A_rels];
    end if;

    EI := ideal<E | E_rels>;
    Eh := hom<E -> P | [P.i: i in [1 .. npolyv]] cat [A.i: i in [1 .. nalgv]]>;

    return EI, Eh;
end function;

function contract_ideal(E, Eh)
    B := GroebnerBasis(E);
    P := Codomain(Eh);
    J := ideal<P | [Eh(f): f in B]>;
    Groebner(J);
    return J;
end function;

function canonical_pdecomp(I)
    E, Eh := expand_ideal(I);
    EQ, EP := PrimaryDecomposition(E);
    Q := [contract_ideal(J, Eh): J in EQ];
    P := [contract_ideal(J, Eh): J in EP];
    return Q, P;
end function;

function canonical_rdecomp(I)
    E, Eh := expand_ideal(I); //: Radicalize);
    EP := RadicalDecomposition(E);
    return [contract_ideal(J, Eh): J in EP];
end function;

function canonical_radical(I)
    E, Eh := expand_ideal(I: Radicalize);
    ER := Radical(E);
    return contract_ideal(ER, Eh);
end function;

/*******************************************************************************
				Generic ideals
*******************************************************************************/

function is_canonical(I)
    K := BaseRing(Generic(I));
    if not exists{t: t in [ RngUPolRes, RngMPolRes ] | ISA(Type(K), t)} then
	return false;
    end if;
    B := BaseRing(K);
    return Type(B) eq FldFunRat and Type(BaseRing(B)) eq FldFin;
end function;

function conv_ideal(I)
    P := Generic(I);
    h, hi, PP := conv(P: force_dpolyq);
    return ideal<PP | [h(f): f in Basis(I)]>, hi;
end function;

function restore_ideal(J, hi)
    P := Codomain(hi);
    return ideal<P | [hi(g): g in Basis(J)]>;
end function;

function pdecomp(I)
    if is_canonical(I) then
	return canonical_pdecomp(I);
    end if;

    II, hi := conv_ideal(I);
    QQ, PP := canonical_pdecomp(II);
    Q := [restore_ideal(J, hi): J in QQ];
    P := [restore_ideal(J, hi): J in PP];
    return Q, P;
end function;

function rdecomp(I)
    if is_canonical(I) then
	return canonical_rdecomp(I);
    end if;

    II, hi := conv_ideal(I);
    PP := canonical_rdecomp(II);
    return [restore_ideal(J, hi): J in PP];
end function;

function radical(I)
    if is_canonical(I) then
	return canonical_radical(I);
    end if;

    II, hi := conv_ideal(I);
    RR := canonical_radical(II);
    return restore_ideal(RR, hi);
end function;

/*******************************************************************************
				INTRINSICS
*******************************************************************************/

intrinsic InternalGAFFPGCD(f::RngMPolElt, g::RngMPolElt) -> RngMPolElt
{Internal}
    return conv_gcd(f, g);
end intrinsic;

intrinsic InternalGAFFFactorization(f::RngMPolElt, s::BoolElt) -> []
{Internal}
    // s is whether sqf only
    l, L := conv_fact(f, s);
    require l: "Factorization algorithm not available (probably intermediate ring in chain is not a domain)"; //, L;
    if l then return L; end if;
end intrinsic;

intrinsic InternalGAFFPDecomp(I::RngMPol) -> [], []
{Internal}
    return pdecomp(I);
end intrinsic;

intrinsic InternalGAFFRDecomp(I::RngMPol) -> [], []
{Internal}
// "I:", I;
    return rdecomp(I);
end intrinsic;

intrinsic InternalGAFFRadical(I::RngMPol) -> RngMPol
{Internal}
    return radical(I);
end intrinsic;
