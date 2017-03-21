freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!

////////////////////////////////////////////////////////////////////////
//                                                                    
//  Implementing Mestre's algo: creating a curve
//  from given invariants
//
//  P. Gaudry (March 2001)
//                                                                    
////////////////////////////////////////////////////////////////////////
//
//  exported intrinsics:
//
//     CurveFromICInv(IgusaClebsch::SeqEnum) -> CrvHyp
//     
////////////////////////////////////////////////////////////////////////
//
// CHANGES
// =======
//
//   M. Stoll, 2001-05-25:
//
//     Cleaned up ReduceCurveToDegree5 (always returns a CrvHyp now,
//       checks that curve has form y^2 = f(x)).
//
//     Cleaned up FindPointOnConic (S[3] was tacitly assumed to be 1)
//
//     Removed ReduceCurveToDegree5; check out HasOddDegreeModel in
//       models.m .
//
/////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////
/*
CHANGES:
 
   2001-06:
 
   Scheme merge.
   HasReducedProjectiveSolution replaced by HasReducedPoint
      (kernel intrinsic)
   
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
   

   2001-07: Paulette
   CurveFromICInv replaced by HyperellipticCurveFromIgusaClebsch

   2002-05: David Kohel
   Verbose flag Igusa
   WamelenReduction imported from wam_red.m
   Parameter Reduce -> WamelenReduction applied to
       HyperellipticCurveFromIgusaClebsch
   ReducedProjectiveSolution -> ReducedPoint

   2002-08: Paul van Wamelen
   HyperellipticCurveFromIgusaClebsch will now also work if the curve is split
     and/or has more automorphisms. This is based on work of Cardona/Quer and
     Shaska/Volklein, see references below.
   Simplified the "intersection of conic and cubic" thing. The curve is simply
     the parametrization of the conic substituted in the cubic.
   Before HyperellipticCurveFromIgusaClebsch gave an error if there was no 
     curve over the rationals with given invariants. As finding this out might
     be one of the uses of this function, it shouldn't give an error. It now 
     returns a curve defined over some quadratic extension of the rationals.
   Added the intrinsic GeometricAutomorphismGroup   

   2003-10: Nicole Sutherland
   HasReducedPoint -> HasRationalPoint

   2008-10: Mike Harrison
   Removed GeometricAutomorphismGroup. This has been replaced by the
   intrinsic of Lercier & Ritzenthaler in g2twists.m, which works in
   all characteristics.
   --------------------------------------------------------------------------
*/

/* Mestre's algorithm.

@InProceedings{Mestre91,
  author = 	 {J.-F. Mestre},
  title = 	 {Construction de courbes de genre $2$ {\`a} partir de
                  leurs modules},
  booktitle = 	 {Effective methods in algebraic geometry},
  editor =	 {T. Mora and C. Traverso},
  volume =	 94,
  series =	 {Progress in mathematics},
  year =	 1991,
  publisher =	 {Birkh{\"a}user},
  pages =	 {313--334},
  note =	 {Proc. Congress in Livorno, Italy, April 17--21, 1990}
}

Cardona's formulas for the split case:
  Gabriel Cardona and Jordi Quer "Field of moduli and field of definition for 
  curves of genus 2" (preprint). See http://au.arxiv.org/abs/math.NT/0207015
  and also Cardona's thesis: http://dmi.uib.es/~gcardona/

Shaska's classification of possible geometric automorphism groups:
  T. Shaska and H. Volklein "Elliptic subfields and automorphisms of genus
  2 function fields" in Proceeding of the Conference on Algebraic Geometry 
  with Applications: The celebration of the seventieth birthday of Professor
  S.S. Abhyankar, Springer-Verlag, 2001. Also 
  http://au.arxiv.org/abs/math.AG/0107142
*/



declare verbose Igusa, 2; 

import "wam_red.m" : WamelenReduction;

forward ConicLAndCubicM, FindPointOnConic, GeoAutGroup, CardonaCurve;

intrinsic HyperellipticCurveFromIgusaClebsch(
    IgC::[FldElt] : Reduce := false) -> CrvHyp 
    {Try to build a curve of genus 2 with the given Igusa-Clebsch invariants
    by Mestre's algorithm (and Cardona's in case of non-hyperelliptic 
    involutions) defined over the field in which the invariants lie. Currently 
    this field must be the rationals or a finite field of characteristic 
    bigger than 5. In case such a curve does not exist a curve defined over 
    some quadratic extension is returned.}

    // Length of sequence???
    require #IgC eq 4 :
        "Argument must be a sequence of four Igusa-Clebsch invariants.";
    F := Universe(IgC);
    if Type(F) eq FldFin then
      require not Characteristic(F) in {2,3} :
        "Igusa-Clebsch invariants invalid in characteristics 2 and 3.";
      require Characteristic(F) ne 5 :
        "Not yet implemented in characteristic 5.";
    end if;
    // First check whether the curve has many automorphisms
    G,ind := GeoAutGroup(IgC);
    P := PolynomialRing(F); x := P.1;
    if (ind eq <240,90>) then return HyperellipticCurve(x^5-x); end if;
    if (ind eq <10,2>)   then return HyperellipticCurve(x^5-1); end if;
    if (ind eq <24,8>)   then return HyperellipticCurve(x^6-1); end if;
    if (ind eq <48,29>)  then return HyperellipticCurve(x^5-x); end if;
    I2,I4,I6,I10 := Explode(IgC);
    if (ind eq <8,3>) then
        t := (3*(36000*I10 + I2^3*I4 + 44*I2*I4^2 + 6*I2^2*I6 - 480*I4*I6))/
             (10800000*I10 + 9*I2^5 + 700*I2^3*I4 - 12400*I2*I4^2 - 
             3600*I2^2*I6 + 48000*I4*I6);
        f := x^5+x^3+t*x;
        return HyperellipticCurve(f);
    end if;
    if (ind eq <12,4>) then
        t := (2*I2*I4 - 20*I6)/(3*I2^3 + 140*I2*I4 - 800*I6);
        f := x^6 + x^3 + t;
        return HyperellipticCurve(f);
    end if;
    if (ind eq <4,2>) then
       return CardonaCurve(IgC);
    end if;

    // OK, no extra automorphisms so Mestre will work...
    require Type(F) in {FldFin,RngInt,FldRat,FldNum} :
      "For Mestre's algorithm the field must be a number field or finite field";

    if Reduce then
	require Type(Universe(IgC)) in {FldRat,RngInt} : 
            "Argument must have universe the rationals if Reduce";
    end if;
    // Build conic and cubic
    L, M := Explode(ConicLAndCubicM(IgC));

    
    // Solve the conic
    if Type(F) in {FldFin,RngInt,FldRat,FldNum} then
      xi, eta := FindPointOnConic(L);
    else
      assert false;
    end if;

    vprintf Igusa: "Found conic point:\n";
    vprintf Igusa: "(%o, %o)\n", xi, eta;

    // Parametrize conic.
    K := Parent(xi);
    UP := PolynomialRing(K); x := UP.1;
    TP<t,m> := PolynomialRing(K,2);
    pol := Evaluate(L,[xi + m*t, eta + t,1]);
    a := Coefficient(pol,t,2);
    b := Coefficient(pol,t,1);
    // now Evaluate(L,[xi*a-m*b,a*eta-b,a]) is zero
    f := UP!UnivariatePolynomial(Evaluate(M,[xi*a-m*b,a*eta-b,a]));
    if Reduce and Type(K) in {FldRat,RngInt} then
	f := WamelenReduction(f);
    end if;
    return HyperellipticCurve(f);
end intrinsic;

function GeoAutGroup(IgusaClebsch)
    // Returns the automorphism group (over Q bar) of the genus 2 curve with 
    // the given invariants. See Shaska/Volklein.
    I2,I4,I6,I10 := Explode(IgusaClebsch);

    // curve is y^2 = x^5-1
    if (I2 eq 0) and (I4 eq 0) and (I6 eq 0) then
        if Characteristic(Parent(I2)) eq 5 then
            return SmallGroup(240,90),<240,90>;
        else
            return CyclicGroup(10), <10,2>;
        end if;
    end if;
    i1 := I2^5/I10;
    i2 := I2^3*I4/I10;
    i3 := I2^2*I6/I10;

    // y^2 = x^6-1
    if (i1 eq 51200000/3) and (i2 eq 480000) and (i3 eq 148000) then
        return SmallGroup(24,8), <24,8>;
    end if;

    // y^2 = x^5-x;
    if (i1 eq 400000) and (i2 eq -20000) and (i3 eq -2000) then
        return SmallGroup(48,29), <48,29>; // This is Gl_2(3)
    end if;

    // y^2 = x^5+x^3+t*x (See Bolza's paper)
    if (72000*I10 + I2^3*I4 - 82*I2*I4^2 - 3*I2^2*I6 + 240*I4*I6 eq 0)
       and
       (-270000*I10*I2 + 3*I2^4*I4 + 734*I2^2*I4^2 + 640*I4^3 - 
        9*I2^3*I6 - 4620*I2*I4*I6 + 7200*I6^2 eq 0) then
      return DihedralGroup(4),<8,3>;
    end if;

    // y^2 = x^6 + x^3 + t; (Equivalent to Bolza's formulas)
    if (108000*I10 + I2^3*I4 - 208*I2*I4^2 - 12*I2^2*I6 + 960*I4*I6 eq 0)
       and
       (5400*I10*I2 - 13*I2^2*I4^2 + 4*I4^3 + 96*I2*I4*I6 - 180*I6^2 eq 0) then
      return DihedralGroup(6),<12,4>;
    end if;

    R2 := 125971200000*I10^3+236196*I10^2*I2^5+19245600*I10^2*I2^3*I4-
        507384000*I10^2*I2*I4^2-972*I10*I2^6*I4^2-77436*I10*I2^4*I4^3+
        592272*I10*I2^2*I4^4+I2^7*I4^4-41472*I10*I4^5+78*I2^5*I4^5-
        159*I2^3*I4^6+80*I2*I4^7-104976000*I10^2*I2^2*I6+
        2099520000*I10^2*I4*I6+5832*I10*I2^5*I4*I6+870912*I10*I2^3*I4^2*I6-
        4743360*I10*I2*I4^3*I6-12*I2^6*I4^3*I6-1332*I2^4*I4^4*I6+
        1728*I2^2*I4^5*I6-384*I4^6*I6-8748*I10*I2^4*I6^2-
        3090960*I10*I2^2*I4*I6^2+9331200*I10*I4^2*I6^2+54*I2^5*I4^2*I6^2+
        8910*I2^3*I4^3*I6^2-6048*I2*I4^4*I6^2+3499200*I10*I2*I6^3-
        108*I2^4*I4*I6^3-29376*I2^2*I4^2*I6^3+6912*I4^3*I6^3+81*I2^3*I6^4+
        47952*I2*I4*I6^4-31104*I6^5;
    if R2 eq 0 then return SmallGroup(4,2),<4,2>; end if;
    return CyclicGroup(2),<2,1>;
end function;

/******************************************* 
   removed mch in 08 - this has been replaced by the Lercier/Ritzenthaler
   intrinsic in g2twists.m that also works in chars 2 and 3.
intrinsic GeometricAutomorphismGroup(C::CrvHyp) -> Grp, Tup
    {Returns the automorphism group of the genus 2 curve over the algebraic 
     closure of its field of definition as the first return value. The second 
     is the index of this group in the database of small groups as would be 
     returned by IdentifyGroup. The characteristic of the field can not be 2 
     or 3}
    // but characteristic 3 should be doable if we used Igusa invariants 
    // instead of IgusaClebsch...
    require Genus(C) eq 2 : "C must have genus 2";
    IgusaClebsch := IgusaClebschInvariants(C);
    F := Parent(IgusaClebsch[1]);
    if Type(F) eq FldFin then
      require not Characteristic(F) in {2,3} :
        "Characteristic 2 and 3 can not be done yet.";
    end if;
      return GeoAutGroup(IgusaClebsch);
end intrinsic;
*******************************************/

function CardonaCurve(IgC)
    // Build a curve of genus 2 with automorphism group V_4 with the given 
    // Igusa-Clebsch invariants using Cardona's formulas

    A,B,C,D := Explode(IgusaClebschToClebsch(IgC));

    A11 := 2*C+A*B/3;
    A12 := 2*B^2/3+2*A*C/3;
    A22 := D;
    A33 := C*D-2/9*B^4+1/6*A*B*D-4/9*A*B^2*C-2/9*A^2*C^2;
    a111 := 4/75*D-8/225*B*C+4/675*A^2*C;
    a112 := (4*B^3)/675 + (8*A*B*C)/675 + (8*C^2)/225 + (2*A*D)/225;
    a122 := (2*A*B^3)/675 + (8*A^2*B*C)/2025 + (8*B^2*C)/675 + (4*A*C^2)/225 + 
           (2*B*D)/225;
    a133 := -(A^2*B^4)/2025 + (8*B^5)/2025 - (4*A^3*B^2*C)/6075 + 
           (14*A*B^3*C)/2025 + (2*A^2*B*C^2)/2025 + (8*B^2*C^2)/675 +
           (4*A*C^3)/675 + (A*B^2*D)/225 + (2*A^2*C*D)/675 + (2*B*C*D)/225 - 
           (2*D^2)/75;
    a222 := (2*B^4)/225 + (4*A*B^2*C)/225 + (16*A^2*C^2)/2025 + (4*B*C^2)/675 -
           (2*C*D)/225;
    a233 := (A*B^5)/2025 + (2*A^2*B^3*C)/1215 - (2*B^4*C)/2025 +
           (8*A^3*B*C^2)/6075 + (2*A*B^2*C^2)/2025 + (8*A^2*C^3)/2025 -
           (4*B*C^3)/675 + (2*B^3*D)/675 + (A*B*C*D)/675 - (2*C^2*D)/225 -
           (A*D^2)/225;
    P := PolynomialRing(Parent(IgC[1])); x := P.1;
    if (A22 ne 0) then
        P1 := -2*A12-2*A22*x;
        P2 := A11-A22*x^2;
        P3 := A11+2*A12*x+A22*x^2;
        f := -A33*a111*P1^3-3*A33*a112*P1^2*P2-3*A33*a122*P1*P2^2+
             3*A22*a133*P1*P3^2-A33*a222*P2^3+3*A22*a233*P2*P3^2;
        return HyperellipticCurve(f);
    else
        P1 := -A11*x^2;
        P2 := -2*(A12 + A11*x);
        P3 := x*(2*A12 + A11*x);
        f := -(a111*A33*P1^3) - 3*a112*A33*P1^2*P2 - 3*a122*A33*P1*P2^2 - 
             a222*A33*P2^3 + 3*A11*a133*P1*P3^2 + 3*A11*a233*P2*P3^2;
        return HyperellipticCurve(f);
    end if;
end function;


function ConicLAndCubicM(ICInv) 
    // Compute the conic L and the cubic M for the Igusa-Clebsch
    // invariants; tool for Mestre's algorithm.

    AP, BP, CP, DP := Explode(ICInv);
    Inv := IgusaClebschToClebsch(ICInv);
    A, B, C, D := Explode(Inv);
  
    if A ne 0 then U := A^6 ;
    elif B ne 0 then U := B^3 ;
    else U := C^2 ;
    end if;

    K := Parent(A);
  
    A11 := 2*C+A*B/3 ;
    A22 := D;
    A33 := B*D/2+2*C*(B^2+A*C)/9 ;
    A23 := B*(B^2+A*C)/3+C*(2*C+A*B/3)/3 ;
    A31 := D;
    A12 := 2*(B^2+A*C)/3 ;
    A32 := A23;  A13 := A31;  A21 := A12;
    
    C11 := A11*U^2*DP^8/DP^11 ;
    C22 := A22*DP^10/DP^11 ;
    C33 := A33*U^8/DP^11 ;
    C23 := A23*DP^5*U^4/DP^11 ;
    C31 := A31*DP^4*U^5/DP^11 ;
    C12 := A12*U*DP^9/DP^11 ;
    C32 := C23;  C13 := C31;  C21 := C12;

    a111 := 8*(A^2*C-6*B*C+9*D)/36 ;
    a112 := 4*(2*B^3+4*A*B*C+12*C^2+3*A*D)/36 ;
    a113 := 4*(A*B^3+4*A^2*B*C/3+4*B^2*C+6*A*C^2+3*B*D)/36 ;
    a122 := a113;
    a123 := 2*(2*B^4+4*A*B^2*C+4*A^2*C^2/3+4*B*C^2+3*A*B*D+12*C*D)/36 ;
    a133 := 2*(A*B^4+4*A^2*B^2*C/3+16*B^3*C/3+26*A*B*C^2/3+
            8*C^3+3*B^2*D+2*A*C*D)/36 ;
    a222 := 4*(3*B^4+6*A*B^2*C+8*A^2*C^2/3+2*B*C^2-3*C*D)/36 ;
    a223 := 2*(-2*B^3*C/3-4*A*B*C^2/3-4*C^3+9*B^2*D+8*A*C*D)/36 ;
    a233 := 2*(B^5+2*A*B^3*C+8*A^2*B*C^2/9+2*B^2*C^2/3
            -B*C*D+9*D^2)/36 ;
    a333 := 1*(-2*B^4*C-4*A*B^2*C^2-16*A^2*C^3/9-4*B*C^3/3
            +9*B^3*D+12*A*B*C*D+20*C^2*D)/36 ;
    P := U^(-18)*DP^5 ;
    
    c111 := a111*P*U^3*DP^12 ;
    c112 := a112*P*U^2*DP^13 ;
    c113 := a113*P*U^6*DP^8 ;
    c122 := a122*P*U*DP^14 ;
    c123 := a123*P*U^5*DP^9 ;
    c133 := a133*P*U^9*DP^4 ;
    c222 := a222*P*DP^15 ;
    c223 := a223*P*U^4*DP^10 ;
    c233 := a233*P*U^8*DP^5 ;
    c333 := a333*P*U^12 ;

    PP<X1,X2,X3> := PolynomialRing(K,3);
    L := C11*X1^2+C22*X2^2+C33*X3^2+2*C12*X1*X2+2*C13*X1*X3+2*C23*X2*X3;
    
    M := c111*X1^3+c222*X2^3+c333*X3^3+3*c112*X1^2*X2+3*c113*X1^2*X3+
         3*c122*X1*X2^2+3*c133*X1*X3^2+3*c233*X2*X3^2+3*c223*X2^2*X3+
	 6*c123*X1*X2*X3;

     return [L,M];
end function;

// This might be usefull one day...
/*
function ConicLAndCubicFromIgusaInvariants(JInv) 
    // Compute the conic L and the cubic M for the Igusa
    // invariants; tool for Mestre's algorithm.

    J2, J4, J6, J8, J10 := Explode(JInv);

    K := Parent(J2);
    PP<X1,X2,X3> := PolynomialRing(K,3);

    L := J2*J4*X1^2+J4^2*X1*X2+2*J10*X2^2+2*J2^3*J4*X2^2+J2*J4^2*X2^2+
         J2^2*J6*X2^2+J10*X1*X3+J2^3*J4*X1*X3+2*J2*J4^2*X1*X3+
         2*J2^2*J6*X1*X3+J2^4*J4*X2*X3+J2^2*J4^2*X2*X3+2*J4^3*X2*X3+
         J2*J4*J6*X2*X3+J10*J4*X3^2+2*J2^3*J4^2*X3^2+2*J2^2*J4*J6*X3^2+
         J4^2*J6*X3^2;
    
    M := (2*J2^5+J2^3*J4+J2*J4^2+2*J10)*X1^3+(J2^8+J2^5*J6+
         J2^4*J4^2+2*J2^3*J4*J6+J2^3*J10+2*J2^2*J4^3+2*J2*J4^2*J6+
         J2*J4*J10+2*J4^4+J6*J10)*X2^3+(2*J2^11+2*J2^9*J4+J2^8*J6
         +J2^7*J4^2+J2^6*J4*J6+2*J2^6*J10+2*J2^5*J6^2+J2^4*J4^2*J6
         +J2^3*J4^4+2*J2^3*J4*J6^2+J2^3*J6*J10+2*J2^2*J4^3*J6+
         J2^2*J4^2*J10+J2*J4^2*J6^2+J4^4*J6+J4^3*J10+
         2*J6^2*J10)*X3^3;

     return [L,M];
end function;
*/

function CheapIntegerSquareFreePart(i)
     Q := Factorization(i: ECMLimit := 10, MPQSLimit := 0);
     _,af := SquarefreeFactorization(Q);
     a := FactorizationToInteger(af);
     return i div a^2, a;
end function;

function CheapRationalSquareFreePart(r)
     an, bn := CheapIntegerSquareFreePart(Numerator(r));
     ad, bd := CheapIntegerSquareFreePart(Denominator(r));
  return an*ad, bn/(ad*bd);
end function;

function FindPointOnConic(L) // ::RngMPolElt) 
    // Find an affine point (x,y,1) on the projective conic L.
    K := BaseRing(Parent(L));
    UP := PolynomialRing(K : Global := false); x := UP.1;
    if Type(K) eq FldFin then
	repeat
	    x1 := Random(K); x3 := K!1;
	    LL := Evaluate(L, [UP | x1,x,x3]);
	    t, x2 := HasRoot(LL);
	until t;
	return x1,x2;
    elif Type(K) in {FldRat,FldNum} then
	P<x,y,z> := ProjectiveSpace(K, 2);
	C := Conic(P, L);
	bool, S := HasRationalPoint(C);
	if not bool then
	  if Type(K) eq FldNum then
	    error if true, "Not implemented for curves over number fields not defined over their fields of definition.";
	  end if;
	  LC,m := LegendreModel(C);
          LL := DefiningPolynomial(LC);
          i1 := K!Coefficient(LL,x,2);
          i2 := K!Coefficient(LL,y,2);
          i3 := K!Coefficient(LL,z,2);
          b1, a1 := CheapRationalSquareFreePart(-i3/i1);
          b2, a2 := CheapRationalSquareFreePart(-i3/i2);
          if Abs(b1) lt Abs(b2) then
            S := QuadraticField(b1); b := S.1;
            Lsol := [a1*b, 0, 1];
          else
            S := QuadraticField(b2); b := S.1;
            Lsol := [0, a2*b, 1];
          end if;
          sol := [Evaluate(p,Lsol) : p in DefiningPolynomials(Inverse(m))];
          return sol[1]/sol[3],sol[2]/sol[3];
        else
	  if Type(K) eq FldRat then  
	    S := ReducedPoint(C);
	  end if;
          assert Evaluate(L, Eltseq(S)) eq 0;
          if S[3] eq 0 then
            pol := Evaluate(L, [UP | S[1],S[2],UP.1]); // pol = c*x*(x-t)
            s3 := -Coefficient(pol, 1)/Coefficient(pol, 2);
            if s3 ne 0 then return S[1]/s3, S[2]/s3; end if;
            // There is only one tangent line...
            if S[1] eq 0 then
              pol := Evaluate(L, [UP | S[1]+UP.1,S[2],UP.1]);// pol = c*x*(x-t)
            else
              pol := Evaluate(L, [UP | S[1],S[2]+UP.1,UP.1]);// pol = c*x*(x-t)
            end if;
            s3 := -Coefficient(pol, 1)/Coefficient(pol, 2);
            error if s3 eq 0, "Error in FindPointOnConic in mestre.m!";
            assert Evaluate(L, [S[1],S[2],s3]) eq 0;
            return S[1]/s3, S[2]/s3;
          else
  	    return S[1]/S[3], S[2]/S[3];
          end if;
        end if;
      else
        error "Algorithm not available for this type of field.\n";
      end if;
end function;

