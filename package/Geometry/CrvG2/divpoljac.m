freeze;

///////////////////////////////////////////////////////////////////////////
//
//       Division polynomial for genus 2 curves with car K>2
//                  cf Cantor 94, CRELLE
//
// P. Gaudry (March 2001)
//
///////////////////////////////////////////////////////////////////////////
//
// it is implemented only for genus 2 curves of the form y^2=f(x) with
// deg(f) = 5 and f monic. (in char != 2)
//
// TODO : extend this to
//    . higher genus
//    . general form of the curve
//    . char 2
// TODO : find better names for functions (non exported at present time)
//
///////////////////////////////////////////////////////////////////////////
/*
CHANGES:
 
 
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 fix Curve
  ------------------------------------------------------------------*/
 


// declare attributes to store the information

declare attributes JacHyp :
    PsiDivPol,      //  These polynomials Psi, Alpha and Gamma are
    GammaDivPol,    //      described in Cantor's paper
    AlphaDivPol;    //  each attribute is a [ RngUPolElt ]


///////////////////////////////////////////////////////////////////////////
/////////////// Computation of the psi division polynomial
///////////////////////////////////////////////////////////////////////////

// intrinsic PsiDivPol(J::JacHyp, n::RngIntElt) -> RngUPolElt
//     { Compute the Cantor Psi division polynomial of a genus 2 curve }
//     require n ge 0 : "require n>=0.";
//     require Dimension(J) eq 2 : "Only available for genus 2 curves.";
//     require Characteristic(BaseRing(J)) ne 2 : "Not available in charac 2.";
//     require (h eq 0) and (Degree(f) eq 5) and (Coefficient(f, 5) eq 1) :
//         "The equation of the curve must be of the form y^2 = x^5 + ...";

function PsiDivPol(J, n)
    f, h := HyperellipticPolynomials(Curve(J));

    assert n ge 0;
    assert Dimension(J) eq 2;
    assert Characteristic(BaseRing(J)) ne 2;
    assert (h eq 0) and (Degree(f) eq 5) and (Coefficient(f, 5) eq 1);
   
    PP := Parent(f);
    x := PP.1;

    if not assigned J`PsiDivPol then
	J`PsiDivPol := [PP!0];
    end if;
    
    if n eq 0 then return PP!0; end if;
    
    if IsDefined(J`PsiDivPol, n) then
	return J`PsiDivPol[n];
    end if;
    
    // compute the result
    f1 := Coefficient(f,4);
    f2 := Coefficient(f,3);
    f3 := Coefficient(f,2);
    f4 := Coefficient(f,1);
    f5 := Coefficient(f,0);
    if n eq 2 then
	result := PP!1;
    elif n eq 3 then
	result := 4*f;
    elif n eq 4 then
	p1 := -f2-4*f1*x-10*x^2;
	p2 := (-3*f2*x^2-5*x^4-4*f1*x^3-2*f3*x-f4)*(3*f2*x+f3+6*f1*x^2+10*x^3);
	p3 := (-3*f2*x^2-5*x^4-4*f1*x^3-2*f3*x-f4)^3;
	result := -2*(p3-4*f*(p2-2*p1*f));
    elif n eq 5 then
	fp := -Derivative(f);
	p1 := f1+5*x;
	p2 := -f2-4*f1*x-10*x^2;
	p3 := (3*f2*x+f3+6*f1*x^2+10*x^3)^2;
	p4 := (3*f2*x+f3+6*f1*x^2+10*x^3);
	result := -4*f*(-5*fp^4+8*f*(3*p4*fp^2+2*f*(-p3-2*fp*p2+4*p1*f)));
    elif n eq 6 then
	p1 := f;
	p2 := -Derivative(f);
	p3 := 3*f2*x+f3+6*f1*x^2+10*x^3;
	p4 := -(10*x^2+4*f1*x+f2);
	p5 := f1+5*x;
	s3445 :=
	  -4*(8*f^2*p4-4*p2*f*p3+p2^3)*(128*f^4+64*p3*p4*f^3+64*f^3*p2*p5-
	  48*f^2*p2^2*p4-48*f^2*p2*p3^2+40*p2^3*p3*f-7*p2^5)
	  -(-32*f^2*p4*p2-5*p2^4+24*f*p2^2*p3-16*p3^2*f^2+64*p5*f^3)^2;
	result := s3445;
    elif n eq 7 then 
	fp := -3*f2*x^2-5*x^4-4*f1*x^3-2*f3*x-f4;
	fp2 := 3*f2*x+f3+6*f1*x^2+10*x^3;
	fp3 := -f2-4*f1*x-10*x^2;
	fp4 := f1+5*x;
	s4556 :=
	  -8*f * (256*f^4*fp4*fp2-256*f^4*fp+128*f^4*fp3^2-192*f^3*fp4*fp^2
	  -384*fp2*fp3*f^3*fp-64*f^3*fp2^3+160*fp3*f^2*fp^3+240*fp2^2*f^2*fp^2
	  -140*fp2*f*fp^4+21*fp^6)
	  * (64*f^3*fp4-5*fp^4-32*f^2*fp*fp3+24*fp2*f*fp^2-16*f^2*fp2^2)
	  -16*f * (64*f^3*fp4*fp-7*fp^5+40*f*fp^3*fp2-48*f^2*fp^2*fp3
	  -48*f^2*fp2^2*fp+128*f^4+64*f^3*fp2*fp3)^2;
	result := s4556;
    else
	r := Floor(n/2.0);
	s := Ceiling(n/2.0);
	if r eq s then r := r-1; s := s+1; end if;
	if r eq s-1 then r := r-1; s := s+1; end if;
	
	// TODO : this computation could be made faster, I guess...
	M := Matrix(3, 3,
	[ PsiDivPol(J, s)*PsiDivPol(J, r-2),
              PsiDivPol(J, s+1)*PsiDivPol(J, r-1),
                  PsiDivPol(J, s+2)*PsiDivPol(J, r), 
	  PsiDivPol(J, s-1)*PsiDivPol(J, r-1),
	      PsiDivPol(J, s)*PsiDivPol(J, r),
		  PsiDivPol(J, s+1)*PsiDivPol(J, r+1), 
	  PsiDivPol(J, s-2)*PsiDivPol(J, r),
	      PsiDivPol(J, s-1)*PsiDivPol(J, r+1),
		  PsiDivPol(J, s)*PsiDivPol(J, r+2)
	]
	);
	Det := -Determinant(M);
	Denom := PsiDivPol(J, s)*PsiDivPol(J, r)*PsiDivPol(J, s-r);
	result := Det div Denom;
    end if;
  
    // store the result
    J`PsiDivPol[n] := result;
    // and return it
    return result;
end function;


///////////////////////////////////////////////////////////////////////////
//
//    Computation of the gamma1 division polynomial  
//
///////////////////////////////////////////////////////////////////////////

// intrinsic GammaDivPol(J::JacHyp, n::RngIntElt) -> RngUPolElt
//     { Compute the Cantor Gamma division polynomial of a genus 2 curve }
//     require n ge 0 : "require n>=0.";
//     require Dimension(J) eq 2 : "Only available for genus 2 curves.";
//     require Characteristic(BaseRing(J)) ne 2 : "Not available in charac 2.";
//     require (h eq 0) and (Degree(f) eq 5) and (Coefficient(f, 5) eq 1) :
//         "The equation of the curve must be of the form y^2 = x^5 + ...";

function GammaDivPol(J, n)
    f, h := HyperellipticPolynomials(Curve(J));

    PP := Parent(f);
    x := PP.1;
    
    if not assigned J`GammaDivPol then
	J`GammaDivPol := [PP!1];
    end if;
    
    if n eq 0 then return PP!1; end if;
    
    if IsDefined(J`GammaDivPol, n) then
	return J`GammaDivPol[n];
    end if;
    
    if n gt 6 then   
	P := PsiDivPol(J, n+1)*GammaDivPol(J, n-1)
	   + PsiDivPol(J, n-1)*PsiDivPol(J, n+2);
	result := P div PsiDivPol(J, n);
    else
	f1 := Coefficient(f,4); f2 := Coefficient(f,3); f3 := Coefficient(f,2);
	f4 := Coefficient(f,1); f5 := Coefficient(f,0);
	fp := -3*f2*x^2-5*x^4-4*f1*x^3-2*f3*x-f4;
	fp2 := 3*f2*x+f3+6*f1*x^2+10*x^3;
	fp3 := -f2-4*f1*x-10*x^2;
	fp4 := f1+5*x;
    
	if n eq 2 then result := 4*f;
	elif n eq 3 then
	    result := -64*fp4*f^3+32*fp*fp3*f^2+16*fp2^2*f^2
	      -24*fp^2*fp2*f+5*fp^4;
	elif n eq 4 then
	    result := 1024*f^5+512*f^4*fp*fp4+512*f^4*fp2*fp3
	      -384*f^3*fp^2*fp3-384*f^3*fp*fp2^2+320*f^2*fp^3*fp2-56*f*fp^5;
	elif n eq 5 then
	    result :=-4096*f^6*fp2^2+2048*f^5*fp^2*fp2+16384*f^7*fp4
	      -256*f^4*fp^4-4096*f^6*fp3^3-14*fp^9-2560*f^4*fp3^2*fp^3
	      -384*f^2*fp3*fp^6+512*f^4*fp*fp2^4+512*f^3*fp^3*fp2^3
	      -576*f^2*fp^5*fp2^2+160*f*fp^7*fp2-768*f^3*fp^5*fp4
	      +8192*f^6*fp4^2*fp-4096*f^5*fp3*fp^2*fp4+10240*f^5*fp3^2*fp*fp2
	      -6144*f^4*fp3*fp^2*fp2^2+3072*f^3*fp3*fp^4*fp2
	      -4096*f^5*fp*fp2^2*fp4+4096*f^4*fp^3*fp2*fp4; 
	elif n eq 6 then
	    result := 524288*f^9*fp-262144*f^9*fp3^2-40960*f^5*fp^6
	      -288*f*fp^11-327680*f^7*fp^3*fp3-393216*f^7*fp^2*fp2^2
	      +262144*f^8*fp^2*fp4+262144*f^6*fp^4*fp2-131072*f^7*fp4^2*fp^3
	      -524288*f^9*fp4^2*fp3+16384*f^4*fp4*fp^7-36864*f^5*fp^5*fp3^2
	      -98304*f^7*fp^2*fp3^3-5248*f^3*fp^8*fp3+36864*f^4*fp2^3*fp^5
	      -40960*f^5*fp2^4*fp^3+32768*f^6*fp2^5*fp-32768*f^7*fp2^4*fp3
	      -17408*f^3*fp2^2*fp^7+3712*f^2*fp^9*fp2-131072*f^8*fp2*fp3^3
	      +786432*f^8*fp*fp2*fp3-147456*f^5*fp4*fp^5*fp2
	      +180224*f^6*fp4*fp^4*fp3+393216*f^6*fp4*fp^3*fp2^2
	      -786432*f^7*fp4*fp^2*fp2*fp3-262144*f^7*fp4*fp2^3*fp
	      +524288*f^8*fp4^2*fp*fp2+524288*f^8*fp4*fp3^2*fp
	      +262144*f^8*fp4*fp3*fp2^2+38912*f^4*fp^6*fp3*fp2
	      -61440*f^5*fp^4*fp3*fp2^2+98304*f^6*fp^3*fp3^2*fp2
	      -32768*f^6*fp^2*fp3*fp2^3+196608*f^7*fp*fp3^2*fp2^2;
	end if;
    end if;
    // store the result
    J`GammaDivPol[n] := result;
    return result;
end function;


///////////////////////////////////////////////////////////////////////////
//
//  Computation of the alpha1 division polynomial  
//
///////////////////////////////////////////////////////////////////////////


// intrinsic AlphaDivPol(J::JacHyp, n::RngIntElt) -> RngUPolElt
//     { Compute the Cantor Alpha division polynomial of a genus 2 curve }
//     require n ge 0 : "require n>=0.";
//     require Dimension(J) eq 2 : "Only available for genus 2 curves.";
//     require Characteristic(BaseRing(J)) ne 2 : "Not available in charac 2.";
//     require (h eq 0) and (Degree(f) eq 5) and (Coefficient(f, 5) eq 1) :
//        "The equation of the curve must be of the form y^2 = x^5 + ...";

function AlphaDivPol(J, n)
    f, h := HyperellipticPolynomials(Curve(J));
    PP := Parent(f);
    x := PP.1;
    
    if not assigned J`AlphaDivPol then
	J`AlphaDivPol := [PP!-2];
    end if;
    
    if n eq 0 then return PP!-2; end if;
    
    if IsDefined(J`AlphaDivPol, n) then
	return J`AlphaDivPol[n];
    end if;

    if n gt 6 then
	P := PsiDivPol(J, n-1)*AlphaDivPol(J, n-1)
	   + PsiDivPol(J, n)*PsiDivPol(J, n-3);
	result := P div PsiDivPol(J, n-2);
    else
	f1 := Coefficient(f,4); f2 := Coefficient(f,3); f3 := Coefficient(f,2);
	f4 := Coefficient(f,1); f5 := Coefficient(f,0);
	fp := -3*f2*x^2-5*x^4-4*f1*x^3-2*f3*x-f4;
	fp2 := 3*f2*x+f3+6*f1*x^2+10*x^3;
	fp3 := -f2-4*f1*x-10*x^2;
	fp4 := f1+5*x;
    
	if n eq 2 then result := PP!0;
	elif n eq 3 then result := -2*fp;
	elif n eq 4 then result := -8*f*fp;
	elif n eq 5 then
	    result := 64*fp*fp3*f^2-40*fp^2*fp2*f+9*fp^4-64*fp4*f^3
	      +16*fp2^2*f^2;
	elif n eq 6 then
	    result := 1024*f^4*fp*fp4-640*f^3*fp^2*fp3-512*f^3*fp*fp2^2
	      +512*f^2*fp^3*fp2-96*f*fp^5+1024*f^5+512*f^4*fp2*fp3;
        end if;
    end if;
    // store the result
    J`AlphaDivPol[n] := result;

    return result;
end function;


/////////////////////////////////////////////////////////////////////////
//
//    delta division polynomial
//
/////////////////////////////////////////////////////////////////////////

//// return a triple: ( d0, d1, d2) such that
////    delta = d0 + d1*Z + d2*Z^2
//// (before renormalization)

// intrinsic DeltaDivPol(J::JacHyp, n::RngIntElt)
//                 ->  RngUPolElt, RngUPolElt, RngUPolElt
//     { Compute the Cantor Delta division polynomial. }
//     require n ge 2 : "require n>=2";
//     require Dimension(J) eq 2 : "Only available for genus 2 curves.";
//     require Characteristic(BaseRing(J)) ne 2 : "Not available in charac 2.";
//     require (h eq 0) and (Degree(f) eq 5) and (Coefficient(f, 5) eq 1) :
//        "The equation of the curve must be of the form y^2 = x^5 + ...";

function DeltaDivPol(J, n);
    f, h := HyperellipticPolynomials(Curve(J));
    d0 := -PsiDivPol(J, n-1)*PsiDivPol(J, n+1);
    d1 := -PsiDivPol(J, n-1)*GammaDivPol(J, n)
        + PsiDivPol(J, n+1)*AlphaDivPol(J, n);
    d2 := -16*f^2*PsiDivPol(J, n)^2;
    return d0, d1, d2;
end function;


////////////////////////////////////////////////////
//
//     epsilon division polynomial
//
////////////////////////////////////////////////////

//// return a triple: ( eps0, eps1, denom) such that
////    epsilon = y/denom * (eps0 + eps1*Z)
//// (before renormalization)

// intrinsic EpsilonDivPol(J::JacHyp, n::RngIntElt)
//                   ->  RngUPolElt, RngUPolElt, RngUPolElt
//     { Compute the Cantor Delta division polynomial. }
//     require n ge 2 : "require n>=2";
//     require Dimension(J) eq 2 : "Only available for genus 2 curves.";
//     require Characteristic(BaseRing(J)) ne 2 : "Not available in charac 2.";
//     require (h eq 0) and (Degree(f) eq 5) and (Coefficient(f, 5) eq 1) :
//         "The equation of the curve must be of the form y^2 = x^5 + ...";

function EpsilonDivPol(J, n)
    f, h := HyperellipticPolynomials(Curve(J));
    d0, d1, d2 := DeltaDivPol(J, n);
    d0_prec, d1_prec, d2_prec := DeltaDivPol(J, n-1);
    d0_next, d1_next, d2_next := DeltaDivPol(J, n+1);
  
    denom := -PsiDivPol(J, n-1)*PsiDivPol(J, n)^2*PsiDivPol(J, n+1)*d2^2;
    Pp2 := PsiDivPol(J, n-1)^2;
    Pn2 := PsiDivPol(J, n+1)^2;
    
    eps0 := (-d2*Pp2*d1_next+d2*Pn2*d1_prec+d1*Pp2*d2_next-d1*Pn2*d2_prec)*d0;
    eps1 := d2^2*Pp2*d0_next-d2^2*Pn2*d0_prec-d2*d0*Pp2*d2_next+
        d2*d0*Pn2*d2_prec-d1*d2*Pp2*d1_next+d1*d2*Pn2*d1_prec+
	d1^2*Pp2*d2_next-d1^2*Pn2*d2_prec;
    Thegcd := GCD(eps0, denom);
    Thegcd := GCD(eps1, Thegcd);
    if Degree(Thegcd) ge 1 then
	denom := Quotrem(denom, Thegcd);
	eps0 := Quotrem(eps0, Thegcd);
	eps1 := Quotrem(eps1, Thegcd);
    end if;
    return eps0, eps1, denom;
end function;

