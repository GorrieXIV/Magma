freeze;

///////////////////////////////////////////////////////////////////////////
//
//   Try to lift the 2-torsion points on a Jac of genus 2, in order to
//   perform a Schoof step to find P(\pi) mod 2^k
//     (see Ants iv)
//
//   P. Gaudry (March 2001)
//
///////////////////////////////////////////////////////////////////////////
//
//   non-exported functions used by JacobianOrderGenus2:
//     InitTwoTateModule
//     TTMNextSmallestDegree
//     ClimbTwoTateModuleNext
//     ExtractInfoFromTTM
//
///////////////////////////////////////////////////////////////////////////
/*
CHANGES:
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 fix Curve

   2008-11, Steve: 
   In TwoTorsionPoints: save time (avoid computing iso between two finite fields)
*/
 
 
function PropagateSolution(gb, x, FqBase)
    // assume gb is a Grobner basis in lex order and x is a starting root.
    assert Evaluate(UnivariatePolynomial(gb[#gb]), x) eq 0;

    Fq := BaseRing(Parent(gb[1]));
    rk := Rank(Parent(gb[1]));
    // stupid, but only way I found to get the polynomial ring...
    MP := Parent(Parent(gb[1]).1); 
    MP := ChangeRing(MP, Parent(x));
    ChangeUniverse(~gb, MP);
    
    Sol := [ x ];

    for i := rk-1 to 1 by -1 do
	SetPol := [];
	for p in gb do
	    np := p;
	    for k := 1 to #Sol do
		np := Evaluate(np, (rk+1-k), Sol[k]);
	    end for;
	    if IsUnivariate(np, i) then
		Append(~SetPol, UnivariatePolynomial(np));
	    end if;
	end for;
	pol := GCD(SetPol);
	if Degree(pol) lt 1 then
	    return [];
	end if;
	test, soli := HasRoot(pol);
	if not test then
	    fact := Factorization(pol);
	    currDeg := Degree(Parent(Sol[1]), FqBase);
	    Fext := ext<FqBase | Degree(fact[1][1])*currDeg>;
	    test, soli := HasRoot(PolynomialRing(Fext)!pol);
	    assert test;
	    ChangeUniverse(~Sol, Fext);
	    MP := ChangeRing(MP, Fext);
	    ChangeUniverse(~gb, MP);
	end if;
	Append(~Sol, soli);
    end for;
    return Sol;
end function;


// intrinsic HalveWeightOneDivisor(P::JacHypPt, J::JacHyp) -> JacHypPt
//     { Returns one of the halves of P.  The others can be obtained by
//     adding the 15 non-zero 2-torsion elements.  It must be given the
//     Jacobian J defined over the small definition field. }

function HalveWeightOneDivisor(P, J)
    // note: we assume that the extension fields are always the
    // canonical ones (given by ext<Fq|n>), so that it is easy
    // possible to compare elements.

    f, h := HyperellipticPolynomials(Curve(J));
    assert h eq 0 and Degree(f) eq 5 and Coefficient(f, 5) eq 1;

    FqBase := BaseRing(J);
        
    Fq := BaseRing(Parent(P));
    DegFq := Degree(Fq, FqBase);
    PP := PolynomialRing(Fq); x := PP.1;
    PP4<v0, v1,u1, u2> := PolynomialRing(Fq, 4);
    f1 := Fq ! Coefficient(f, 4);
    f2 := Fq ! Coefficient(f, 3);
    f3 := Fq ! Coefficient(f, 2);
    f4 := Fq ! Coefficient(f, 1);
    f5 := Fq ! Coefficient(f, 0);
    
    A := u1^4 - f1*u1^3 + (-3*u2 + f2)*u1^2 +
         (2*f1*u2 + (v0^2 - f3))*u1 + (u2^2 - f2*u2 + (-2*v1*v0 + f4));

    B := u2*u1^3 - f1*u2*u1^2 + (-2*u2^2 + f2*u2)*u1 +
	 (f1*u2^2 + (v0^2 - f3)*u2 + (-v1^2 + f5));

    U0 := v0^6+(2*u1^3-2*f1*u1^2+(-8*u2+2*f2)*u1+(4*f1*u2-2*f3))*v0^4+
          (6*v1*u1^2-4*f1*v1*u1+(-4*u2+2*f2)*v1)*v0^3+(u1^6-2*f1*u1^5+
	  (-8*u2+(f1^2+2*f2))*u1^4+(12*f1*u2+(-2*f2*f1-2*f3))*u1^3+(16*u2^2+
	  (-4*f1^2-8*f2)*u2+(2*f3*f1+f2^2))*u1^2+(-16*f1*u2^2+
	  (4*f2*f1+8*f3)*u2-2*f3*f2)*u1+(4*f1^2*u2^2-4*f3*f1*u2+f3^2))*v0^2+
	  (6*v1*u1^5-10*f1*v1*u1^4+(-28*u2+(4*f1^2+8*f2))*v1*u1^3+(32*f1*u2+
	  (-6*f2*f1-6*f3))*v1*u1^2+(16*u2^2+(-8*f1^2-12*f2)*u2+
	  (4*f3*f1+2*f2^2))*v1*u1+(-8*f1*u2^2+(4*f2*f1+4*f3)*u2-
	  2*f3*f2)*v1)*v0+(9*v1^2*u1^4-12*f1*v1^2*u1^3+(-12*u2+(4*f1^2+
	  6*f2))*v1^2*u1^2+(8*f1*u2-4*f2*f1)*v1^2*u1+(4*u2^2-4*f2*u2+
	  f2^2)*v1^2);
	  
    U1 := 2*(u1*v0^6-v1*v0^5+(2*u1^4-2*f1*u1^3+(-5*u2+2*f2)*u1^2+
          (2*f1*u2-2*f3)*u1+(-4*u2^2+f2*u2))*v0^4+(v1*u1^3+(10*u2-f2)*v1*u1+
	  (-4*f1*u2+2*f3)*v1)*v0^3+(u1^7-2*f1*u1^6+(-5*u2+(f1^2+2*f2))*u1^5+
	  (7*f1*u2+(-2*f2*f1-2*f3))*u1^4+(2*u2^2+(-2*f1^2-4*f2)*u2+(2*f3*f1+
	  f2^2))*u1^3+(-5*v1^2+((f2*f1+5*f3)*u2-2*f3*f2))*u1^2+(2*f1*v1^2+
	  (8*u2^3-6*f2*u2^2+(-2*f3*f1+f2^2)*u2+f3^2))*u1+((-2*u2-f2)*v1^2+
	  (-4*f1*u2^3+(2*f2*f1+2*f3)*u2^2-f3*f2*u2)))*v0^2+(2*v1*u1^6-
	  3*f1*v1*u1^5+(3*u2+(f1^2+2*f2))*v1*u1^4+(-8*f1*u2+(-f2*f1-
	  f3))*v1*u1^3+(-20*u2^2+(4*f1^2+8*f2)*u2)*v1*u1^2+(4*v1^3+
	  (20*f1*u2^2+(-6*f2*f1-6*f3)*u2+f3*f2)*v1)*u1+(4*u2^3+(-4*f1^2-
	  4*f2)*u2^2+(4*f3*f1+f2^2)*u2-f3^2)*v1)*v0+(-3*v1^2*u1^5+
	  5*f1*v1^2*u1^4+(14*u2+(-2*f1^2-4*f2))*v1^2*u1^3+(-16*f1*u2+
	  (3*f2*f1+3*f3))*v1^2*u1^2+(-8*u2^2+(4*f1^2+6*f2)*u2+(-2*f3*f1-
	  f2^2))*v1^2*u1+(-2*v1^4+(4*f1*u2^2+(-2*f2*f1-2*f3)*u2+f3*f2)*v1^2)));

    U2 := (u1^2+4*u2)*v0^6-6*v1*u1*v0^5+(2*u1^5-2*f1*u1^4+(2*u2+2*f2)*u1^3+
          (-4*f1*u2-2*f3)*u1^2+(-12*u2^2+6*f2*u2)*u1+(5*v1^2+(4*f1*u2^2-
	  4*f3*u2)))*v0^4+(-8*v1*u1^4+8*f1*v1*u1^3+(22*u2-8*f2)*v1*u1^2+
	  (-12*f1*u2+8*f3)*v1*u1+(-4*u2^2+2*f2*u2)*v1)*v0^3+(u1^8-2*f1*u1^7+
	  (-2*u2+(f1^2+2*f2))*u1^6+(2*f1*u2+(-2*f2*f1-2*f3))*u1^5+(-3*u2^2+
	  (2*f3*f1+f2^2))*u1^4+(2*v1^2+(4*f1*u2^2+(-2*f2*f1+2*f3)*u2-
	  2*f3*f2))*u1^3+(-2*f1*v1^2+(4*u2^3-6*f2*u2^2+2*f2^2*u2+f3^2))*u1^2+
	  (2*f2*v1^2+(4*f3*u2^2-2*f3*f2*u2))*u1+((4*f1*u2-6*f3)*v1^2+
	  (4*u2^4-4*f2*u2^3+f2^2*u2^2)))*v0^2+(-2*v1*u1^7+4*f1*v1*u1^6+
	  (10*u2+(-2*f1^2-4*f2))*v1*u1^5+(-14*f1*u2+(4*f2*f1+4*f3))*v1*u1^4+
	  (-4*u2^2+(4*f1^2+8*f2)*u2+(-4*f3*f1-2*f2^2))*v1*u1^3+(-4*v1^3+
	  ((-2*f2*f1-10*f3)*u2+4*f3*f2)*v1)*u1^2+(-16*u2^3+12*f2*u2^2+
	  (4*f3*f1-2*f2^2)*u2-2*f3^2)*v1*u1+((-8*u2+4*f2)*v1^3+(8*f1*u2^3+
	  (-4*f2*f1-4*f3)*u2^2+2*f3*f2*u2)*v1))*v0+(v1^2*u1^6-2*f1*v1^2*u1^5+
	  (-8*u2+(f1^2+2*f2))*v1^2*u1^4+(12*f1*u2+(-2*f2*f1-2*f3))*v1^2*u1^3+
	  (16*u2^2+(-4*f1^2-8*f2)*u2+(2*f3*f1+f2^2))*v1^2*u1^2+(8*v1^4+
	  (-16*f1*u2^2+(4*f2*f1+8*f3)*u2-2*f3*f2)*v1^2)*u1+(-4*f1*v1^4+
	  (4*f1^2*u2^2-4*f3*f1*u2+f3^2)*v1^2));

    c1 := PP4!Coefficient(P[1], 0);

    V := U2 - c1*U1;

    I := ideal<PP4 | U0, V, A, B>;

    tps := Cputime();
    vprintf JacHypCnt, 3 :  "Computing the Groebner basis...\n";
    gb := GroebnerBasis(I);
    vprintf JacHypCnt, 3 :  "  done in %o sec\n", Cputime()-tps;
  
    Pu2 := gb[#gb];
    if not Degree(UnivariatePolynomial(Pu2)) in {44, 52} then
	vprintf JacHypCnt, 3 :  "non generic\n";
	return J!0;
    end if;
    tps := Cputime();
    vprintf JacHypCnt, 3 :  "Factoring the polynomial...\n";
    Pu2Fact := Factorization(UnivariatePolynomial(Pu2));
    vprintf JacHypCnt, 3 :  "  done in %o sec\n", Cputime()-tps;

    Div := Parent(P)!0;
    
    for fact in Pu2Fact do
	vprintf JacHypCnt, 3 :  "deal with factor %o\n", fact[1];

	Fact := fact[1];
	if Degree(Fact) eq 1 then
	    Fext := Fq;
	    solu2 := Fext!(-Coefficient(Fact, 0));
	else
	    Fext := ext<FqBase | Degree(Fact)*DegFq>;
	    Embed(Fq, Fext);
	    _, solu2 := HasRoot(PolynomialRing(Fext)!Fact);
	end if;
	
	Sol := PropagateSolution(gb, solu2, FqBase);
	if Sol eq [] then
	    vprintf JacHypCnt, 3 :  "Failed: had to go to an extension\n";
	else
	    Fext := Parent(Sol[1]);
	    Jext := BaseExtend(J, Fext);
	    PPext := PolynomialRing(Fext); X := PPext.1;
	    Div := Jext![X^2+Sol[2]*X+Sol[1], Sol[4]*X+Sol[3]];
	    if IsZero(2*Div) or 2*Div ne Parent(Div)!P then
		vprintf JacHypCnt, 3 :  "wrong divisor\n";
	    else
		return Div;
	    end if;
	end if;
    end for;
    
/*
    for fact in Pu2Fact do
	printf "deal with factor %o\n", fact[1];
	IndentPush();
	Fact := fact[1];
	if Degree(Fact) eq 1 then
	    Fext := Fq;
	    solu2 := Fext!(-Coefficient(Fact, 0));
	else
	    Fext := ext<FqBase | Degree(Fact)*DegFq>;
	    Embed(Fq, Fext);
	    _, solu2 := HasRoot(PolynomialRing(Fext)!Fact);
	end if;
	PPext4<v00, v11, u11, u22> := PolynomialRing(Parent(solu2), 4);
	
	Pu1 := PPext4!gb[#gb-1];
	Pu1 := UnivariatePolynomial(Evaluate(Pu1, u22, solu2));
	if Degree(Pu1) eq 1 then
	    _, solu1 := HasRoot(Pu1);
	else
	    assert Degree(UnivariatePolynomial(Pu2)) eq 44;
	    assert Pu1 eq 0;
	    Pu1 := PPext4 ! gb[#gb-2];
	    Pu1 := UnivariatePolynomial(Evaluate(Pu1, u22, solu2));
	    assert Degree(Pu1) eq 2;
	    tt, solu1 := HasRoot(Pu1);
	    assert tt;
	end if;

	if Degree(UnivariatePolynomial(Pu2)) eq 52 then
	    Pv1 := PPext4!gb[#gb-3];
	else
	    Pv1 := PPext4!gb[#gb-4];
	end if;
	Pv1 := UnivariatePolynomial(Evaluate(Pv1, u22, solu2));
	assert Degree(Pv1) eq 2 and Coefficient(Pv1, 2) eq 1 and
	Coefficient(Pv1, 1) eq 0;
	
	cPv1 := -Coefficient(Pv1, 0);
	test, solv1 := IsSquare(Fext!(cPv1));
	
	if not test then
	    printf "Have to go to a quadratic extension\n";
	    Fext := ext<FqBase | 2*Degree(Fext, FqBase)>;
	    test, solv1 := IsSquare(Fext!(-cPv1));
	    assert test;
	    PPext4<v00, v11, u11, u22> := PolynomialRing(Fext, 4);
	end if;
	
	if solv1 eq 0 then
	    printf "Trivial solution, skip it...\n";
	    IndentPop();
	    continue;
	end if;

	if Degree(UnivariatePolynomial(Pu2)) eq 52 then
	    rk := 4;
	else
	    rk := 5;
	end if;
	repeat 
	    Pv0 := PPext4!gb[#gb-rk];
	    Pv0 := Evaluate(Pv0, u22, solu2);
	    Pv0 := Evaluate(Pv0, u11, solu1);
	    Pv0 := Evaluate(Pv0, v11, solv1);
	    Pv0 := UnivariatePolynomial(Pv0);
	    assert Degree(Pv0) le 1;
	until Coefficient(Pv0, 1) ne 0;

	solv0 := Fext!(-Coefficient(Pv0, 0))/
	(Fext!(Coefficient(Pv0, 1)));
	
	AA := Evaluate(A, [Fext!solv0, Fext!solv1, Fext!solu1, Fext!solu2]);
	if AA ne 0 then
	    printf "A failed\n";
	    IndentPop();
	    continue;
	end if;
	BB := Evaluate(B, [Fext| solv0, solv1, solu1, solu2]);
	if BB ne 0 then
	    printf "B failed\n";
	    IndentPop();
	    continue;
	end if;
	
	PPext := PolynomialRing(Fext); X := PPext.1;
	Jext := BaseExtend(J, Fext);
	Div := Jext![X^2+solu1*X+solu2, solv0*X+solv1];
	twoDiv := 2*Div;
	if twoDiv eq Jext!P then
	    IndentPop();
	    return Div;
	end if;
	if twoDiv eq -Jext!P then
	    IndentPop();
	    return -Div;
	end if;
	
	IndentPop();
    end for;

*/
    
    return J!0;
end function;


// intrinsic HalveWeightTwoDivisor(P::JacHypPt, J::JacHyp) -> JacHypPt
//     { Returns one of the halves of P.  The others can be obtained by
//     adding the 15 non-zero 2-torsion elements.  It must be given the
//     Jacobian J defined over the small definition field. }

function HalveWeightTwoDivisor(P, J)
    // note: we assume that the extension fields are always the
    // canonical ones (given by ext<Fq|n>), so that it is easy
    // possible to compare elements.

    f, h := HyperellipticPolynomials(Curve(J));
    assert h eq 0 and Degree(f) eq 5 and Coefficient(f, 5) eq 1;
    FqBase := BaseRing(J);
        
    Fq := BaseRing(Parent(P));
    DegFq := Degree(Fq, FqBase);
    PP := PolynomialRing(Fq); x := PP.1;
    PP4<v0, v1,u1, u2> := PolynomialRing(Fq, 4);
    f1 := Fq ! Coefficient(f, 4);
    f2 := Fq ! Coefficient(f, 3);
    f3 := Fq ! Coefficient(f, 2);
    f4 := Fq ! Coefficient(f, 1);
    f5 := Fq ! Coefficient(f, 0);
    
    A := u1^4 - f1*u1^3 + (-3*u2 + f2)*u1^2 +
         (2*f1*u2 + (v0^2 - f3))*u1 + (u2^2 - f2*u2 + (-2*v1*v0 + f4));

    B := u2*u1^3 - f1*u2*u1^2 + (-2*u2^2 + f2*u2)*u1 +
	 (f1*u2^2 + (v0^2 - f3)*u2 + (-v1^2 + f5));

    U0 := v0^6+(2*u1^3-2*f1*u1^2+(-8*u2+2*f2)*u1+(4*f1*u2-2*f3))*v0^4+
          (6*v1*u1^2-4*f1*v1*u1+(-4*u2+2*f2)*v1)*v0^3+(u1^6-2*f1*u1^5+
	  (-8*u2+(f1^2+2*f2))*u1^4+(12*f1*u2+(-2*f2*f1-2*f3))*u1^3+(16*u2^2+
	  (-4*f1^2-8*f2)*u2+(2*f3*f1+f2^2))*u1^2+(-16*f1*u2^2+
	  (4*f2*f1+8*f3)*u2-2*f3*f2)*u1+(4*f1^2*u2^2-4*f3*f1*u2+f3^2))*v0^2+
	  (6*v1*u1^5-10*f1*v1*u1^4+(-28*u2+(4*f1^2+8*f2))*v1*u1^3+(32*f1*u2+
	  (-6*f2*f1-6*f3))*v1*u1^2+(16*u2^2+(-8*f1^2-12*f2)*u2+
	  (4*f3*f1+2*f2^2))*v1*u1+(-8*f1*u2^2+(4*f2*f1+4*f3)*u2-
	  2*f3*f2)*v1)*v0+(9*v1^2*u1^4-12*f1*v1^2*u1^3+(-12*u2+(4*f1^2+
	  6*f2))*v1^2*u1^2+(8*f1*u2-4*f2*f1)*v1^2*u1+(4*u2^2-4*f2*u2+
	  f2^2)*v1^2);
	  
    U1 := 2*(u1*v0^6-v1*v0^5+(2*u1^4-2*f1*u1^3+(-5*u2+2*f2)*u1^2+
          (2*f1*u2-2*f3)*u1+(-4*u2^2+f2*u2))*v0^4+(v1*u1^3+(10*u2-f2)*v1*u1+
	  (-4*f1*u2+2*f3)*v1)*v0^3+(u1^7-2*f1*u1^6+(-5*u2+(f1^2+2*f2))*u1^5+
	  (7*f1*u2+(-2*f2*f1-2*f3))*u1^4+(2*u2^2+(-2*f1^2-4*f2)*u2+(2*f3*f1+
	  f2^2))*u1^3+(-5*v1^2+((f2*f1+5*f3)*u2-2*f3*f2))*u1^2+(2*f1*v1^2+
	  (8*u2^3-6*f2*u2^2+(-2*f3*f1+f2^2)*u2+f3^2))*u1+((-2*u2-f2)*v1^2+
	  (-4*f1*u2^3+(2*f2*f1+2*f3)*u2^2-f3*f2*u2)))*v0^2+(2*v1*u1^6-
	  3*f1*v1*u1^5+(3*u2+(f1^2+2*f2))*v1*u1^4+(-8*f1*u2+(-f2*f1-
	  f3))*v1*u1^3+(-20*u2^2+(4*f1^2+8*f2)*u2)*v1*u1^2+(4*v1^3+
	  (20*f1*u2^2+(-6*f2*f1-6*f3)*u2+f3*f2)*v1)*u1+(4*u2^3+(-4*f1^2-
	  4*f2)*u2^2+(4*f3*f1+f2^2)*u2-f3^2)*v1)*v0+(-3*v1^2*u1^5+
	  5*f1*v1^2*u1^4+(14*u2+(-2*f1^2-4*f2))*v1^2*u1^3+(-16*f1*u2+
	  (3*f2*f1+3*f3))*v1^2*u1^2+(-8*u2^2+(4*f1^2+6*f2)*u2+(-2*f3*f1-
	  f2^2))*v1^2*u1+(-2*v1^4+(4*f1*u2^2+(-2*f2*f1-2*f3)*u2+f3*f2)*v1^2)));

    U2 := (u1^2+4*u2)*v0^6-6*v1*u1*v0^5+(2*u1^5-2*f1*u1^4+(2*u2+2*f2)*u1^3+
          (-4*f1*u2-2*f3)*u1^2+(-12*u2^2+6*f2*u2)*u1+(5*v1^2+(4*f1*u2^2-
	  4*f3*u2)))*v0^4+(-8*v1*u1^4+8*f1*v1*u1^3+(22*u2-8*f2)*v1*u1^2+
	  (-12*f1*u2+8*f3)*v1*u1+(-4*u2^2+2*f2*u2)*v1)*v0^3+(u1^8-2*f1*u1^7+
	  (-2*u2+(f1^2+2*f2))*u1^6+(2*f1*u2+(-2*f2*f1-2*f3))*u1^5+(-3*u2^2+
	  (2*f3*f1+f2^2))*u1^4+(2*v1^2+(4*f1*u2^2+(-2*f2*f1+2*f3)*u2-
	  2*f3*f2))*u1^3+(-2*f1*v1^2+(4*u2^3-6*f2*u2^2+2*f2^2*u2+f3^2))*u1^2+
	  (2*f2*v1^2+(4*f3*u2^2-2*f3*f2*u2))*u1+((4*f1*u2-6*f3)*v1^2+
	  (4*u2^4-4*f2*u2^3+f2^2*u2^2)))*v0^2+(-2*v1*u1^7+4*f1*v1*u1^6+
	  (10*u2+(-2*f1^2-4*f2))*v1*u1^5+(-14*f1*u2+(4*f2*f1+4*f3))*v1*u1^4+
	  (-4*u2^2+(4*f1^2+8*f2)*u2+(-4*f3*f1-2*f2^2))*v1*u1^3+(-4*v1^3+
	  ((-2*f2*f1-10*f3)*u2+4*f3*f2)*v1)*u1^2+(-16*u2^3+12*f2*u2^2+
	  (4*f3*f1-2*f2^2)*u2-2*f3^2)*v1*u1+((-8*u2+4*f2)*v1^3+(8*f1*u2^3+
	  (-4*f2*f1-4*f3)*u2^2+2*f3*f2*u2)*v1))*v0+(v1^2*u1^6-2*f1*v1^2*u1^5+
	  (-8*u2+(f1^2+2*f2))*v1^2*u1^4+(12*f1*u2+(-2*f2*f1-2*f3))*v1^2*u1^3+
	  (16*u2^2+(-4*f1^2-8*f2)*u2+(2*f3*f1+f2^2))*v1^2*u1^2+(8*v1^4+
	  (-16*f1*u2^2+(4*f2*f1+8*f3)*u2-2*f3*f2)*v1^2)*u1+(-4*f1*v1^4+
	  (4*f1^2*u2^2-4*f3*f1*u2+f3^2)*v1^2));


    c1 := PP4!Coefficient(P[1],1);
    c2 := PP4!Coefficient(P[1],0);

    U := U1 - c1*U0;
    V := U2 - c2*U0;
    
    I := ideal<PP4 | U, V, A, B>;
  
    tps := Cputime();
    vprintf JacHypCnt, 3 :  "Computing the Groebner basis...\n";
    gb := GroebnerBasis(I);
    vprintf JacHypCnt, 3 :  "  done in %o sec\n", Cputime()-tps;
  

    Pu2 := UnivariatePolynomial(gb[#gb]);
    if Degree(Pu2) ne 52 then
	vprintf JacHypCnt, 3 :  "Non generic.\n";
	return J!0;
    end if;
    tps := Cputime();
    // TODO: speed up the factorization !!!!!!!
    vprintf JacHypCnt, 3 :  "Factoring the polynomial...\n";
    Pu2Fact := Factorization(Pu2);
    vprintf JacHypCnt, 3 :  "  done in %o sec\n", Cputime()-tps;

    for fact in Pu2Fact do
	vprintf JacHypCnt, 3 :  "deal with factor %o\n", fact[1];
	IndentPush();
	Fact := fact[1];
	if Degree(Fact) eq 1 then
	    Fext := Fq;
	    solu2 := Fext!(-Coefficient(Fact, 0));
	else
	    Fext := ext<FqBase | Degree(Fact)*DegFq>;
	    Embed(Fq, Fext);
	    _, solu2 := HasRoot(PolynomialRing(Fext)!Fact);
	end if;
	PPext4<v00, v11, u11, u22> := PolynomialRing(Parent(solu2), 4);
	
	
	Pu1 := PPext4!gb[#gb-1];
	Pu1 := UnivariatePolynomial(Evaluate(Pu1, u22, solu2));
	if not (Coefficient(Pu1, 1) eq 1 and Degree(Pu1) eq 1) then
	    vprintf JacHypCnt, 3 :  "Non generic.\n";
	    return J!0;
	end if;
	solu1 := Fext!(-Coefficient(Pu1, 0));

	Pv1 := PPext4!gb[#gb-3];
	Pv1 := UnivariatePolynomial(Evaluate(Pv1, u22, solu2));
	if not (Coefficient(Pv1, 2) eq 1 and Coefficient(Pv1, 1) eq 0
	       and Degree(Pv1) eq 2) then
	    vprintf JacHypCnt, 3 :  "Non generic.\n";
	    return J!0;
	end if;
	if not IsSquare(Fext!(-Coefficient(Pv1, 0))) then
	    vprintf JacHypCnt, 3 :  "The square root does not exist. skip this sol...\n";
	    IndentPop();
	    continue;
	end if;
	solv1 := SquareRoot(Fext!(-Coefficient(Pv1, 0)));
	if solv1 eq 0 then
	    vprintf JacHypCnt, 3 :  "Trivial solution, skip it...\n";
	    IndentPop();
	    continue;
	end if;
    
	Pv0 := PPext4!gb[#gb-4];
	Pv0 := Evaluate(Pv0, u22, solu2);
	Pv0 := UnivariatePolynomial(Evaluate(Pv0, v11, solv1));

	if not (Degree(Pv0) eq 1) then
	    vprintf JacHypCnt, 3 :  "Non generic.\n";
	    return J!0;
	end if;
	solv0 := Fext!(-Coefficient(Pv0, 0))/(Fext!(Coefficient(Pv0, 1)));
	
	PPext := PolynomialRing(Fext); X := PPext.1;
	Jext := BaseExtend(J, Fext);


	test, Div := IsCoercible(Jext, [X^2+solu1*X+solu2, solv0*X+solv1]);
	if not test then
	    IndentPop();
	    continue;
	end if;
	twoDiv := 2*Div;
	if twoDiv eq Jext!P then
	    IndentPop();
	    return Div;
	end if;
	if twoDiv eq -Jext!P then
	    IndentPop();
	    return -Div;
	end if;
	
	IndentPop();
    end for;
    return J!0;
end function;


// intrinsic TwoTorsionPoints(J::JacHyp) -> List
//    { The list of the 1-weight 2-torsion divisors.}

function TwoTorsionPoints(J)
    f, h := HyperellipticPolynomials(Curve(J));
    assert h eq 0 and Degree(f) eq 5;

    L := [* *];
    Fact := Factorization(f);
    for fact in Fact do
	ff := fact[1];
	if Degree(ff) eq 1 then
	    Append(~L, J![ff, 0]);
	else
            /* Changed by Steve, Nov 2008
	    Fext := ext<BaseRing(J) | Degree(ff) >;
	    _, t := HasRoot(PolynomialRing(Fext)!ff);
            */
            Fext := ext<BaseRing(J) | ff : Check:=false>;
            t := Fext.1;
            assert Evaluate(ff,t) eq 0;
	    Append(~L, BaseExtend(J, Fext)![PolynomialRing(Fext).1-t, 0]);
	end if;
    end for;
    return L;
end function;


////////  Lift a Table of candidates for (a1, a2) mod r to
///       a list of candidates of (a1,a2) mod 2r

// intrinsic LiftTableA(Table::SeqEnum, r::RngIntElt) -> SeqEnum

function LiftTableA(Table, r)
    NewTable:=[];
    for pair in Table do
	Append(~NewTable, [pair[1], pair[2]]);
	Append(~NewTable, [pair[1]+r, pair[2]]);
	Append(~NewTable, [pair[1], pair[2]+r]);
	Append(~NewTable, [pair[1]+r, pair[2]+r]);
    end for;
    return NewTable;
end function;


//////  This function try all the pairs (a1,a2) mod r, with the
//////  r-torsion divisor Div. It returns another TableA, which can
//////  be smaller if the procedure succeded (part of the Schoof algorithm)

// intrinsic EliminatePairsA1A2(TableA::SeqEnum, Div::JacHypPt, J::JacHyp, r::RngIntElt) -> SeqEnum

function EliminatePairsA1A2(TableA, Div, J, r) 
    Jext := Parent(Div);
    Fext := BaseRing(Jext);
    Fq := BaseRing(J);
    q := #Fq;
    NewTable := [];
  
    // Precompute some divisors:
    timePrec := Cputime();
    vprintf JacHypCnt, 3 :  "Precomputing some divisors...\n";
    FrDiv1 := Frobenius(Div,    Fq);
    FrDiv2 := Frobenius(FrDiv1, Fq);
    FrDiv3 := Frobenius(FrDiv2, Fq);
    FrDiv4 := Frobenius(FrDiv3, Fq);
    A := ((q^2) mod r)*Div + FrDiv4;
    B := (q mod r)*FrDiv1 + FrDiv3;
    timePrec := Cputime() - timePrec;
    vprintf JacHypCnt, 3 :  "done  in %o sec\n", timePrec;

    for pair in TableA do
	a1 := pair[1]; a2 := pair[2];
	a1B := a1*B;
	a2FrD2 := a2*FrDiv2;
	ZDiv := a1B + A + a2FrD2;
	if IsZero(ZDiv) then
	    Append(~NewTable, [a1, a2]);
	end if;    
    end for;
    return NewTable;
end function;


// intrinsic TravelInTateModule(J::JacHyp, LimitDegree::RngIntElt) -> SetEnum
   
function TravelInTateModule(J, LimitDegree)
    Fq := BaseRing(J);
    q := #Fq;
    
    S2list := TwoTorsionPoints(J);

    S2 := [* *];
    for s in S2list do
	Append(~S2, <s, true>);
    end for;
        
    TableA := [ [0, 0] ]; r := 1;
    TableA := LiftTableA(TableA, r);
    r *:= 2;

    for s in S2list do
	TableA := EliminatePairsA1A2(TableA, s, J, r);
	if #TableA eq 1 then break; end if;
    end for;
   
    S := [ S2 ];

    while true do
	// select the smallest degree not yet halved
	rk := 0; idx := 0; smallest := Infinity();
	for r := 1 to #S do
	    for id := 1 to #S[r] do
		if S[r][id][2] then
		    deg := Degree(BaseRing(Parent(S[r][id][1])));
		    if deg lt smallest then
			smallest := deg;
			rk := r;
			idx := id;
		    end if;
		end if;
	    end for;
	end for;
	if rk eq 0 or smallest gt LimitDegree then break; end if;
	
	// halve it!
	vprintf JacHypCnt, 3 :  "Halving a divisor of 2^%o torsion, defined over an ext of deg %o\n", rk, smallest;
	vprintf JacHypCnt, 3 :  "current value of r is %o\n", r;
	S[rk][idx][2] := false; // mark it as already treated
	P := S[rk][idx][1];
	if Degree(P[1]) eq 1 then
	    hP := HalveWeightOneDivisor(P, J);
	else
	    assert Degree(P[1]) eq 2;
	    hP := HalveWeightTwoDivisor(P, J);
	end if;
	if IsZero(hP) then continue; end if;

	if r eq 2^rk then
	    // start a new level in S
	    TableA := LiftTableA(TableA, r);
	    r *:= 2;
	    Append(~S, [* <hP, true> *]);
	else
	    Append(~S[rk+1], <hP, true>);
	end if;
	TableA := EliminatePairsA1A2(TableA, hP, J, r);
	SJ := {};
	for pair in TableA do
	    Include(~SJ, (q^2+(q+1)*pair[1]+pair[2]+1) mod r);
	end for;
	vprintf JacHypCnt, 3 :  "here, we have mod %o:\n", r;
	vprint JacHypCnt, 3 : TableA;
	vprintf JacHypCnt, 3 :  "and #J mod r in ";
	vprint JacHypCnt, 3 : SJ;
    end while;

    SJ := {};
    for pair in TableA do
	Include(~SJ, (q^2+(q+1)*pair[1]+pair[2]+1) mod r);
    end for;

    return SJ, r;
end function;



///////////////////////////////////////////////////////////////////////////
//
//  Tools for doing the computation incrementally:
//    store all the information in a Rec and then one can call
//    ClimbTwoTateModuleNext() which process one step
//
///////////////////////////////////////////////////////////////////////////

TwoTateModuleFormat := recformat <
    J : JacHyp,                          // the Jacobian
    r : RngIntElt,                       // the current modulo
    TableA : SeqEnum,                    // table of remaining candidates
                                         //   (a_1,a_2)  mod r
    DivisorList : SeqEnum >;             // seq of list of 2^k-divisors
                                         // with a boolean to mark if they
					 // already have been halved


//intrinsic InitTwoTateModule(J::JacHyp) -> Rec
  
function InitTwoTateModule(J)
    TTM := rec < TwoTateModuleFormat | J := J, r := 2 >;
    S2list := TwoTorsionPoints(J);
        
    // purge one of the elements, if possible, according to the fact. pattern
    // (5)
    // (4)(1)
    // (3)(2)
    // (3)(1)(1)       -> (3)(1)
    // (2)(2)(1)       -> (2)(2)  (but is it interesting?)
    // (2)(1)(1)(1)    -> (2)(1)(1)
    // (1)(1)(1)(1)(1) -> (1)(1)(1)(1)

    listedeg := [ Degree(BaseRing(Parent(s)), BaseRing(J)) : s in S2list ];
    case listedeg :
        when [1, 1, 3] :
	    S2list := [* S2list[2], S2list[3] *];
	when [1, 2, 2] :
	    S2list := S2list;  // do nothing
	when [1, 1, 1, 2] :
	    S2list := [* S2list[2], S2list[3], S2list[4] *];
	when [1, 1, 1, 1, 1] :
	    S2list := [* S2list[2], S2list[3], S2list[4], S2list[5] *];
    end case;
    
    S2 := [* *];
    for s in S2list do
	Append(~S2, <s, true>);
    end for;

    TableA := [ [0, 0] ]; 
    TableA := LiftTableA(TableA, 1);
    for s in S2list do
	TableA := EliminatePairsA1A2(TableA, s, J, 2);
	if #TableA eq 1 then break; end if;
    end for;
   
    TTM`DivisorList := [ S2 ];
    TTM`TableA := TableA;
    return TTM;
end function;

    
// intrinsic TTMNextSmallestDegree(TTM::Rec) -> RngIntElt, RngIntElt, RngIntElt

function TTMNextSmallestDegree(TTM)
    S := TTM`DivisorList;
    
    // select the smallest degree not yet halved
    rk := 0; idx := 0; smallest := Infinity();
    for r := 1 to #S do
	for id := 1 to #S[r] do
	    if S[r][id][2] then
		deg := Degree(BaseRing(Parent(S[r][id][1])), BaseRing(TTM`J));
		// note : le instead of lt in order to begin with
		// higher torsion when the degree are equal
		if deg le smallest then
		    smallest := deg;
		    rk := r;
		    idx := id;
		end if;
	    end if;
	end for;
    end for;
    
    return smallest, rk, idx;
end function;

// intrinsic ClimbTwoTateModuleNext(~TTM::Rec)

procedure ClimbTwoTateModuleNext(~TTM)
    J := TTM`J; 
    smallest, rk, idx := TTMNextSmallestDegree(TTM);
    vprintf JacHypCnt, 3 :  "Halving a divisor of 2^%o torsion, defined over an ext of deg %o\n", rk, smallest;
    vprintf JacHypCnt, 3 :  "current value of r is ";
    vprint JacHypCnt, 3 : TTM`r;
    
    TTM`DivisorList[rk][idx][2] := false; // mark it as treated
    P := TTM`DivisorList[rk][idx][1];
    if Degree(P[1]) eq 1 then
	hP := HalveWeightOneDivisor(P, J);
    else
	assert Degree(P[1]) eq 2;
	hP := HalveWeightTwoDivisor(P, J);
    end if;
    if IsZero(hP) then
	vprintf JacHypCnt, 3 :  "Failed!\n";
	return;
    end if;

    if TTM`r eq 2^rk then
	// start a new level in DivisorList
	TTM`TableA := LiftTableA(TTM`TableA, TTM`r);
	TTM`r *:= 2;
	Append(~(TTM`DivisorList), [* <hP, true> *]);
    else
	Append(~(TTM`DivisorList[rk+1]), <hP, true>);
    end if;
    TTM`TableA := EliminatePairsA1A2(TTM`TableA, hP, J, TTM`r);

    q := #BaseRing(J);
    SJ := {};
    for pair in TTM`TableA do
	Include(~SJ, (q^2+(q+1)*pair[1]+pair[2]+1) mod TTM`r);
    end for;
    vprintf JacHypCnt, 3 :  "here, we have mod %o:\n", TTM`r;
    vprint JacHypCnt, 3 : TTM`TableA;
    vprintf JacHypCnt, 3 :  "and #J mod r in ";
    vprint JacHypCnt, 3 : SJ;
end procedure;


//intrinsic ExtractInfoFromTTM(TTM::Rec) -> RngIntElt, RngIntElt

function  ExtractInfoFromTTM(TTM)
    q := #BaseRing(TTM`J);
    SJ := {};
    for pair in TTM`TableA do
	Include(~SJ, (q^2+(q+1)*pair[1]+pair[2]+1) mod TTM`r);
    end for;

    r := TTM`r;
    while #SJ gt 1 do
	r div:= 2;
	SJ := { sj mod r : sj in SJ };
    end while;

    return Rep(SJ), r;
end function;


///////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////////
//
//  The following functions are for debugging purpose only !
//
///////////////////////////////////////////////////////////////////////////

function MyDivAdd(D1, D2, Fq)
    Fq1 := BaseRing(Parent(D1));
    Fq2 := BaseRing(Parent(D2));
    if #Fq1 eq #Fq2 then
	Embed(Fq1, Fq2);
	Sum := D1 + Parent(D1)!D2;
    else
	deg1 := Degree(Fq1, Fq);
	deg2 := Degree(Fq2, Fq);
	deg := LCM(deg1, deg2);
	if deg eq deg1 then
	    Fq := Fq1;
	    Embed(Fq2, Fq1);
	    DD1 := D1;
	    DD2 := Parent(D1)!D2;
	elif deg eq deg2 then
	    Fq := Fq2;
	    Embed(Fq1, Fq2);
	    DD2 := D2;
	    DD1 := Parent(D2)!D1;
	else
	    Fq := ext <Fq | deg>;
	    Embed(Fq1, Fq);
	    Embed(Fq2, Fq);
	    J := BaseChange(Parent(D1), Fq);
	    DD1 := J! D1;
	    DD2 := J! D2;
	end if;
	Sum := DD1 + DD2;
    end if;
    
    // find the smallest subfield where it is defined...
    deg := Degree(BaseRing(Parent(Sum)), Fq);
    J := BaseChange(Parent(Sum), Fq);
    for d in Divisors(deg) do
	Jd := BaseExtend(J, d);
	t, NSum := IsCoercible(Jd, Sum);
	if t then
	    Sum := NSum;
	    break;
	end if;
    end for;
    
    return Sum;
end function;


function IsIn(x, S)
    for y in S do
	if x cmpeq y then return true; end if;
    end for;
    return false;
end function;


function NextGeneration(S, Fq)
    T := S;
    oldct := #T;
    for i in S do
	for j in S do
	    k := MyDivAdd(i, j, Fq);
	    if not IsIn(k, T) then Append(~T, k); end if;
	    k := MyDivAdd(Frobenius(i, Fq), j, Fq);
	    if not IsIn(k, T) then Append(~T, k); end if;
	    if #T gt oldct then vprintf JacHypCnt, 3 :  "  new : %o\n", #T; end if;
	    oldct := #T;
	end for;
    end for;
    return T;
end function;


// intrinsic GeneratedSubGroup(S::List, Fq::FldFin, B::RngIntElt) -> List
//     { Subgroup generated by elements of S. Group and Frobenius
//     action. }

function GeneratedSubGroup(S, Fq, B)
    T := [* *];
    i := 0;
    while #T ne #S do
	T := S;
	S := NextGeneration(S, Fq);
	vprintf JacHypCnt, 3 :  "current size: %o\n", #S;
	i +:= 1;
	if i eq B then break; end if;
    end while;
    return S;
end function;

