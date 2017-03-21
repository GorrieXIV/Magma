freeze;

///////////////////////////////////////////////////////////////////////////
//
// Weil pairing for hyperelliptic curves.
// Designed for genus 2 curves, but should work also for higher genus.
//
// P. Gaudry (March 2001)
//
///////////////////////////////////////////////////////////////////////////
//
// Two implementations:
//   * with Cantor's group law algorithm 
//   * with Function Fields machinery  -> slower, but works also for type 3/13
// NOTE: None of these are optimized!
// 
///////////////////////////////////////////////////////////////////////////
//
// Things TO DO :
//   * do more tests (especially: is there some infinite loop somewhere?)
//   * implement also Tate Pairing
//   * fix WeilPairingTry
//
///////////////////////////////////////////////////////////////////////////
/*
CHANGES:
 
 
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 fix Curve
                 
   2003-06: Nils
   Disabled use of (faster) WeilPairingTry in favour of WeilPairingTry2,
   where FF=FunctionField(Curve(J)) was replaced by
   FF=RationalExtensionRepresentation(FunctionField(Curve(J))), because
   MaximalOrderFinite is required.
   
   Problem with WeilPairingTry is that, sometimes, it does not return
   an n-th root of unity, as the example
   
   SetSeed(449443898,0);
   P := PolynomialRing(GF(49)); x := P.1;
   f := x^7 + x;
   C := HyperellipticCurve(f);
   J := Jacobian(C);
   Dimension(J);  // says 3
   a := Random(J);
   Order(a);      // says 8
   b := Random(J);
   Order(b);      // says 8
   repeat
     WeilPairing(a, b, 8); 
   until false;
   
   eventually shows.
   
   WeilPairingTry should be fixed some time.
  ------------------------------------------------------------------*/
 
 
 
 
 

///////////////////////////////////////////////////////////////////////////
//
// An example: (MOV reduction of DLog on HC -> DLog on finite field)
/*

Fq := GF(2);
PP := PolynomialRing(Fq); x := PP.1;
h := PP!1;
f := x^5 + x^4 + x^3 + 1;
J := Jacobian(HyperellipticCurve([f,h]));  // a supersingular curve
Jext := BaseExtend(J, 41);
Factorization(JacobianOrder(Jext));
m := 177722253954175633;                 // some big subgroup order
cofact := 3887047*7;

P := cofact*Random(Jext);
Q := 876213876263897634*P;               // Q in <P>

Jext2 := BaseExtend(Jext, 6);            // go to an ext of deg 6
NJ := JacobianOrder(Jext2);

R := Random(Jext2);
R *:= NJ div m^Valuation(NJ, m);

WeilPairing(Jext2!P, R, m);
WeilPairing(Jext2!Q, R, m);

assert $2^876213876263897634 eq $1;      // check consistency of the results

*/
//
///////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////////
//
// Cantor group law algorithm, adapted to return also the function
//
///////////////////////////////////////////////////////////////////////////

// intrinsic DivAddCantorFunc(D1::JacHypPt, D2::JacHypPt)
//    -> JacHypPt, FldFunRatMElt
//    { Compute D3 reduced and F a function such that D3 + div(F) = D1 + D2. } 

function DivAddCantorFunc(D1, D2)
    assert Parent(D1)`Type in {1, 11, 2, 12};
  
    J := Parent(D1);
    f, h := HyperellipticPolynomials(Curve(J));
    Fq := BaseRing(J);
    KC<X, Y> := RationalFunctionField(Fq, 2);
    F := KC!1;
    
    // trivial cases:
    if IsZero(D1) then
	return D2, F;
    elif IsZero(D2) then
	return D1, F;
    end if;

    // convert to Cantor's notations:
    A1 := D1[1]; B1 := D1[2];
    A2 := D2[1]; B2 := D2[2];

    //////////////////////////////////////////////////////////////////////
    // composition step:
    //////////////////////////////////////////////////////////////////////
    R, S1, S2 := XGCD(A1, A2);
    if Degree(R) le 0 then
	P2 := S1*A1*B2 + S2*A2*B1;
	P1 := A1*A2;
	P2 mod:= P1;
    else
	S := B1 + B2 + h;
	T, L, S3 := XGCD(R, S);
	S1 *:= L;
	S2 *:= L;
	F *:= Evaluate(T, X);
	P1 := (A1*A2) div (T^2);
	P2 := S1*A1*B2 + S2*A2*B1 + S3*(B1*B2+f);
	P2 := (P2 div T) mod P1;
    end if;

    //////////////////////////////////////////////////////////////////////
    // reduction step:
    //////////////////////////////////////////////////////////////////////
    g := Genus(Curve(J));
    while Degree(P1) gt g do
	P1 := (f - P2*(P2+h)) div P1;
	P2 := -P2;
	F *:= (Evaluate(P2, X)+Y)/Evaluate(P1, X);
	P2 := (P2 - h) mod P1;
    end while;
    P1 := Normalize(P1);
    return J![P1, P2], F;
end function;


//intrinsic DivNegateFunc(D1::JacHypPt) -> JacHypPt, FldFunRatMElt
//    { Compute D2 reduced and F a function such that D2 + div(F) = - D1 . } 

function DivNegateFunc(D1)
    assert Parent(D1)`Type in {1, 11, 2, 12};

    J := Parent(D1);
    f, h := HyperellipticPolynomials(Curve(J));
    Fq := BaseRing(J);
    KC<X, Y> := RationalFunctionField(Fq, 2);
    F := KC!1;

    return -D1, 1/Evaluate(D1[1], X);
end function;


///////////////////////////////////////////////////////////////////////////
//
// Evaluate a function at a divisor.
// WARNING : return 0 if this is not defined.
//
///////////////////////////////////////////////////////////////////////////

function EvalFunc(F, D)
    NF := Numerator(F);
    DF := Denominator(F);
    assert DF*F eq NF;

    x := Parent(D[1]).1;

    den := Resultant( D[1], Evaluate(DF, [ x, D[2] ]) );
    if den eq 0 then return false, _; end if;
    num := Resultant( D[1], Evaluate(NF, [ x, D[2] ]) );
    if num eq 0 then return false, _; end if;

    return true, num/den;
end function;


///////////////////////////////////////////////////////////////////////////
//
// Compute the function corresponding to the principality of [m].P,
// and evaluate it on the fly at some divisors instead of storing the
// function.
// WARNING : return a table of 0 if one of the evaluation gave 0 or infinity.
//
///////////////////////////////////////////////////////////////////////////

// intrinsic DivMultAndEvalFunc(m::RngIntElt, P::JacHypPt, Divs::SeqEnum)
//     -> SeqEnum
//     { Compute a function F such that [m] P = div(F) and evaluate this
//     function at the divisors listed in Divs.  Assume P is a m-torsion
//     divisor. }

function DivMultAndEvalFunc(m, P, Divs)
    assert m ge 0;
    assert Parent(P)`Type in {1, 11, 2, 12};

    Fq := BaseRing(Parent(P));

    CurrentEval1 := [ Fq!1 : d in Divs ];
    CurrentEval2 := [ Fq!1 : d in Divs ];
    
    D1 := P; D2 := Parent(P)!0;
    while m gt 0 do
	if IsOdd(m) then
	    D2, F := DivAddCantorFunc(D1, D2);
	    for i := 1 to #Divs do
		t, c := EvalFunc(F, Divs[i]);
		if not t then return [ Fq!0 : d in Divs ]; end if;
		CurrentEval2[i] *:= CurrentEval1[i]*c;
	    end for;
	end if;
	m := m div 2;
	D1, F := DivAddCantorFunc(D1, D1);
	for i := 1 to #Divs do
	    t, c := EvalFunc(F, Divs[i]);
	    if not t then return [ Fq!0 : d in Divs ]; end if;
	    CurrentEval1[i] := c*CurrentEval1[i]^2;
	end for;
    end while;

    assert IsZero(D2);
    return CurrentEval2;
end function;


///////////////////////////////////////////////////////////////////////////
//
// One try of WeilPairing: this may fail, due to bad choice in the random
// initialisation: some evaluation can fail in the addition chain.
// In case of failure, return 0;
//
///////////////////////////////////////////////////////////////////////////

// intrinsic WeilPairingTry(P::JacHypPt, Q::JacHypPt, m::RngIntElt) -> RngElt
//     { The Weil Pairing e_m(P, Q) where P and Q are in J[m] }

function WeilPairingTry(P, Q, m)
    J := Parent(P);
    Fq := BaseRing(J);
    repeat
	T := Random(J);
	U := Random(J);
	A := P+T;
	B := Q+U;
    until not (Degree(GCD(A[1], B[1])) gt 0 or
          Degree(GCD(A[1], U[1])) gt 0 or
          Degree(GCD(T[1], B[1])) gt 0 or
	  Degree(GCD(T[1], U[1])) gt 0);
    //print "A,B,U,T:",A,B,U,T;
    print [IsSquarefree(a[1]):a in [A,B,U,T]];
    cc := [];
    mT, F := DivNegateFunc(T);
    AmT, G := DivAddCantorFunc(A, mT);
    t, ccc := EvalFunc(F*G, B);
    if not t then 
	return Fq!0;
    end if;
    cc[1] := ccc^m;
    t, ccc := EvalFunc(F*G, U);
    if not t then 
	return Fq!0;
    end if;
    cc[2] := ccc^m;
    ccc := DivMultAndEvalFunc(m, AmT, [ B, U ]);
    if ccc[1] eq 0 or ccc[2] eq 0 then
	return Fq!0;
    end if;
    cc[1] *:= ccc[1]; cc[2] *:=ccc[2];
    Result := cc[1]/cc[2];
    
    mU, F := DivNegateFunc(U);
    BmU, G := DivAddCantorFunc(B, mU);

    t, ccc := EvalFunc(F*G, A);
    if not t then 
	return Fq!0;
    end if;
    cc[1] := ccc^m;
    t, ccc := EvalFunc(F*G, T);
    if not t then 
	return Fq!0;
    end if;
    cc[2] := ccc^m;
    ccc := DivMultAndEvalFunc(m, BmU, [ A, T ]);
    if ccc[1] eq 0 or ccc[2] eq 0 then
	return Fq!0;
    end if;
    cc[1] *:= ccc[1]; cc[2] *:=ccc[2];
    Result *:= cc[2]/cc[1];
    return Result;
end function;


///////////////////////////////////////////////////////////////////////////
//
// Implementation using function fields.
//    new version: trying to include all the types of jacobian.
//
///////////////////////////////////////////////////////////////////////////

function CoerceInFFDivGroup(D)
    J := Parent(D);
    Fq := BaseRing(J);
    
    R := RationalFunctionField(Fq);
    x := R.1;
    FF := RationalExtensionRepresentation(AlgorithmicFunctionField(FunctionField(Curve(J))));
    rho := FF.1;
    O := MaximalOrderFinite(FF);
    divinfty := &+[Divisor(p) : p in Poles(FF!x)];

    if D eq J!0 then return DivisorGroup(FF)!0; end if;
   
    I := ideal<O | Evaluate(D[1], x), rho-Evaluate(D[2] mod D[1], x), 0>;
    if D[3] eq Degree(D[1]) then
	assert IsDivisibleBy(D[3], Degree(divinfty));
	Div := Divisor(I)-(D[3] div Degree(divinfty))*divinfty;
    else
	// find the place at infinity which is involved in D
	c := Coefficient(D[2], 3); // here we know that we have genus 2!
	pl := Poles(FF!x);
	ple := [ Evaluate(rho/x^3, p) : p in pl ];
	pos := Position(ple, c);
	assert pos ne 0;
	pl := pl[pos];
	// put everything together
	Div := Divisor(I) + (D[3]-Degree(D[1]))*pl;
	assert IsDivisibleBy(Degree(Div), Degree(divinfty));
	Div := Div - (Degree(Div) div Degree(divinfty))*divinfty;
    end if;
    return Div;
end function;


function MyEvaluate(F, D) 
    Fq := BaseRing(BaseRing(Parent(F)));
    result := 1;
    supp := Support(D);
    for pl in supp do
	res := Evaluate(F, pl);
	if res cmpeq Infinity() then return res; end if;
	if Degree(Parent(res), Fq) gt 1 then
	    res := Norm(res);
	end if;
	val := Valuation(D, pl);
	if val ne 0 and res eq 0 then return Infinity(); end if;
	result *:= res^val;
    end for;
    return result;
end function;


// intrinsic WeilPairingTry2(P::JacHypPt, Q::JacHypPt, m::RngIntElt) -> RngElt
//     { The Weil Pairing e_m(P, Q) where P and Q are in J[m]. Returns 0
//     if it failed. }

function WeilPairingTry2(P, Q, m)
    J := Parent(P);
    Fq := BaseRing(J);
    repeat
	T := Random(J);
	U := Random(J);
	A := P+T;
	B := Q+U;
    until not(Degree(GCD(A[1], B[1])) gt 0 or
          Degree(GCD(A[1], U[1])) gt 0 or
          Degree(GCD(T[1], B[1])) gt 0 or
	  Degree(GCD(T[1], U[1])) gt 0);

    divA := CoerceInFFDivGroup(A);
    divB := CoerceInFFDivGroup(B);
    divT := CoerceInFFDivGroup(T);
    divU := CoerceInFFDivGroup(U);

    refDiv := DivisorOfDegreeOne(FunctionField(Parent(divA)));
	    
    Z, _, _, Fa := Reduction(m*(divA-divT), refDiv);
    assert Z eq 0;
    resa := MyEvaluate(1/Fa, divB-divU);

    if resa cmpeq Infinity() then return Fq!0; end if;

    Z, _, _, Fb := Reduction(m*(divB-divU), refDiv);
    assert Z eq 0;
    resb := MyEvaluate(1/Fb, divA-divT);
    
    if resb cmpeq Infinity() or resb eq 0 then return Fq!0; end if;

    return resa/resb;
end function;


///////////////////////////////////////////////////////////////////////////
//
// Main function : compute the weilpairing of two elements in Jac
//
///////////////////////////////////////////////////////////////////////////
//
// WeilPairingTry and WeilPairingTry2 are probablistic functions that may
// fail.  WeilPairingTry2 uses function field machinery, it is slower but
// is the only one available when there are 2 rational points at infinity.
//
///////////////////////////////////////////////////////////////////////////

intrinsic WeilPairing(P::JacHypPt, Q::JacHypPt, m::RngIntElt) -> RngElt
    { The Weil Pairing e_m(P, Q) where P and Q are in J[m]  }

    require Parent(P) eq Parent(Q) : "divisors must be in the same Jacobian";
    require IsZero(m*P) and IsZero(m*Q) : "divisors must be m-torsion elements";
    J := Parent(P);
    require J`Type ne 0 : "no known group law on this type of Jacobian";

    repeat
	if true or J`Type in {3, 13} then
	    e := WeilPairingTry2(P, Q, m);
	else
	    e := WeilPairingTry(P, Q, m);
	end if;
    until e ne 0;
    assert (e^m) eq Parent(e)!1;
    return e;
end intrinsic;
