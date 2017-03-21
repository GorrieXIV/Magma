// *********************************************************************
// * Package: delpezzo.mag                                             *
// * =====================                                             *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 10.12.2007                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Compute parametrizations of Del Pezzo surfaces.                 *
// *                                                                   *
// * TODO:                                                             *
// * -----                                                             *
// *                                                                   *
// *   - Reuse procomputed lines when recursing to higher degree!      *
// *                                                                   *
// *                                                                   *
// *********************************************************************
freeze;
import "classify.m": myInvertible, CrossMultiply;




// ==================================================
// = How to produce SQUARE1 and SQUARE2 (see below) =
// ==================================================
// 
// Q := Rationals();
// Pb<b0,b1,b2,b3> := PolynomialRing(Q,4);
// AFF1 := AffineSpace(Pb);
// Pa<a0,a1,a2,a3,a4,a5,a6> := PolynomialRing(Q, 7);
// AFF2 := AffineSpace(Pa);
// Pbt := PolynomialRing(Pb); t := Pbt.1;
// m := map<AFF1 -> AFF2 | Coefficients((b0 + b1*t + b2*t^2 + b3*t^3)^2)>;
// SQUARE1 := Image(m);
// 
// Q := Rationals();
// Pb<b0,b1,b2> := PolynomialRing(Q,3);
// AFF1 := AffineSpace(Pb);
// Pa<a0,a1,a2,a3,a4> := PolynomialRing(Q,5);
// AFF2 := AffineSpace(Pa);
// Pbt := PolynomialRing(Pb); t := Pbt.1;
// m := map<AFF1 -> AFF2 | Coefficients((b0 + b1*t + b2*t^2)^2)>;
// SQUARE2 := Image(m);


// ======================================
// = Auxiliary functions (not exported) =
// ======================================

// find lines on degree one Del Pezzo
// ----------------------------------
// input : a homogeneous polynomial 'F' (Tschirnhausen, in suitable grading)
//         defining a Del Pezzo of degree one
// output: an incomplete sequence of parametrizations of lines, but containing
//         all contractible lines (each line is a tuple of coordinates and
//         an adjustment parameter, see description of 'ContractLineDeg1or2')
function FindLinesDeg1(F : ExtName := "alpha", ExtCount := 0)
	Px := Parent(F); Q := BaseRing(Px);
	Pc<c0,c1,c2> := PolynomialRing(Q, 3); Pcx := ChangeRing(Px, Pc);
	
	// square relations
	Pa<a0,a1,a2,a3,a4,a5,a6> := PolynomialRing(Q, 7);
	AFF1 := AffineSpace(Pa);
	SQUARE1 := Scheme(AFF1, ideal<Pa | a2*a6^3 - 1/2*a3*a5*a6^2 -
	    1/4*a4^2*a6^2 + 3/8*a4*a5^2*a6 - 5/64*a5^4, a1*a6^3 +
	    1/5*a2*a5*a6^2 - 1/2*a3*a4*a6^2 + 1/40*a3*a5^2*a6 +
	    1/5*a4^2*a5*a6 - 1/20*a4*a5^3, a1*a5*a6^2 - 16/25*a2*a4*a6^2 +
	    1/5*a2*a5^2*a6 - 9/50*a3*a4*a5*a6 + 1/40*a3*a5^3 + 4/25*a4^3*a6 -
	    1/25*a4^2*a5^2, a0*a6^3 + 4/25*a2*a4*a6^2 - 1/20*a2*a5^2*a6 -
	    1/4*a3^2*a6^2 + 17/100*a3*a4*a5*a6 - 3/80*a3*a5^3 - 1/25*a4^3*a6 +
	    1/100*a4^2*a5^2, a1*a4*a6^2 - 5/4*a1*a5^2*a6 - 2/5*a2*a3*a6^2 +
	    a2*a4*a5*a6 - 1/4*a2*a5^3 + 1/5*a3^2*a5*a6 - 2/5*a3*a4^2*a6 +
	    1/10*a3*a4*a5^2, a0*a5*a6^2 + 1/4*a1*a5^2*a6 - 2/5*a2*a3*a6^2 -
	    1/20*a3^2*a5*a6 + 1/10*a3*a4^2*a6 - 1/40*a3*a4*a5^2, a0*a5^2*a6 +
	    1/4*a1*a4*a5*a6 - 1/16*a1*a5^3 - 4/5*a2^2*a6^2 - 1/10*a2*a3*a5*a6 +
	    1/5*a2*a4^2*a6 - 1/20*a2*a4*a5^2, a1*a3*a6^2 + 1/2*a1*a4*a5*a6 -
	    5/8*a1*a5^3 - 8/5*a2^2*a6^2 + 4/5*a2*a3*a5*a6 + 2/5*a2*a4^2*a6 -
	    1/10*a2*a4*a5^2 - 1/2*a3^2*a4*a6 + 1/8*a3^2*a5^2, a0*a4*a6^2 +
	    9/16*a1*a4*a5*a6 - 25/64*a1*a5^3 - a2^2*a6^2 + 3/8*a2*a3*a5*a6 +
	    1/4*a2*a4^2*a6 - 1/16*a2*a4*a5^2 - 1/4*a3^2*a4*a6 + 1/16*a3^2*a5^2,
	    a0*a4*a5*a6 - 5/4*a1*a2*a6^2 + 1/4*a1*a4^2*a6 - 1/16*a1*a4*a5^2 -
	    1/4*a2^2*a5*a6 + 1/8*a2*a3*a4*a6 - 1/32*a2*a3*a5^2, a0*a5^3 -
	    9/5*a1*a2*a6^2 + 2/5*a1*a3*a5*a6 + 1/5*a1*a4^2*a6 -
	    1/20*a1*a4*a5^2 - a2^2*a5*a6 + 1/2*a2*a3*a4*a6 - 1/8*a2*a3*a5^2,
	    a0*a3*a6^2 - 5/2*a1*a2*a6^2 + 3/2*a1*a3*a5*a6 + 1/2*a1*a4^2*a6 -
	    5/8*a1*a4*a5^2 - 1/2*a2^2*a5*a6 + 1/4*a2*a3*a4*a6 +
	    3/16*a2*a3*a5^2 - 1/4*a3^3*a6, a0*a3*a5*a6 - 25/8*a1^2*a6^2 -
	    5/4*a1*a2*a5*a6 + 7/4*a1*a3*a4*a6 + 1/4*a1*a3*a5^2 -
	    1/2*a1*a4^2*a5 - 1/8*a2^2*a5^2 - 3/8*a2*a3^2*a6 + 1/4*a2*a3*a4*a5 -
	    1/16*a3^3*a5, a0*a4^2*a6 - 125/64*a1^2*a6^2 - 25/32*a1*a2*a5*a6 +
	    15/32*a1*a3*a4*a6 - 1/16*a1*a4^2*a5 - 5/64*a2^2*a5^2 +
	    1/64*a2*a3^2*a6 + 1/32*a2*a3*a4*a5 - 1/128*a3^3*a5, a0*a4*a5^2 -
	    45/16*a1^2*a6^2 - 17/8*a1*a2*a5*a6 + 11/8*a1*a3*a4*a6 +
	    1/8*a1*a3*a5^2 - 1/4*a1*a4^2*a5 - 5/16*a2^2*a5^2 +
	    1/16*a2*a3^2*a6 + 1/8*a2*a3*a4*a5 - 1/32*a3^3*a5, a0*a2*a6^2 -
	    25/16*a1^2*a6^2 - 3/8*a1*a2*a5*a6 + 3/4*a1*a3*a4*a6 +
	    5/32*a1*a3*a5^2 - 1/4*a1*a4^2*a5 - 1/16*a2^2*a5^2 -
	    3/16*a2*a3^2*a6 + 1/8*a2*a3*a4*a5 - 1/32*a3^3*a5, a0*a2*a5*a6 -
	    4/9*a0*a4^2*a5 - 25/144*a1^2*a5*a6 + 19/36*a1*a2*a4*a6 +
	    31/144*a1*a2*a5^2 + 1/36*a1*a3^2*a6 + 7/72*a1*a3*a4*a5 -
	    1/9*a1*a4^3 - 7/18*a2^2*a3*a6 + 1/12*a2^2*a4*a5 -
	    7/144*a2*a3^2*a5 + 1/18*a2*a3*a4^2 - 1/72*a3^3*a4, a0*a3*a5^2 -
	    8/5*a0*a4^2*a5 + 5/2*a1^2*a5*a6 + 2/5*a1*a2*a4*a6 +
	    1/2*a1*a2*a5^2 - 1/5*a1*a3*a4*a5 - 4/5*a2^2*a3*a6 +
	    2/5*a2^2*a4*a5 - 1/10*a2*a3^2*a5, a0*a3*a4*a6 - 10/9*a0*a4^2*a5 +
	    125/36*a1^2*a5*a6 - 5/9*a1*a2*a4*a6 + 25/36*a1*a2*a5^2 -
	    5/9*a1*a3^2*a6 - 4/9*a1*a3*a4*a5 + 2/9*a1*a4^3 - 2/9*a2^2*a3*a6 +
	    1/3*a2^2*a4*a5 - 1/36*a2*a3^2*a5 - 1/9*a2*a3*a4^2 + 1/36*a3^3*a4,
	    a0*a1*a6^2 - 16/45*a0*a4^2*a5 + 241/144*a1^2*a5*a6 -
	    59/180*a1*a2*a4*a6 + 41/144*a1*a2*a5^2 - 5/18*a1*a3^2*a6 -
	    71/360*a1*a3*a4*a5 + 1/9*a1*a4^3 - 1/90*a2^2*a3*a6 +
	    7/60*a2^2*a4*a5 - 1/720*a2*a3^2*a5 - 1/18*a2*a3*a4^2 +
	    1/72*a3^3*a4, a0*a1*a4*a6 + 5/9*a0*a2*a4*a5 + 1/36*a0*a3^2*a5 -
	    4/9*a0*a3*a4^2 + 5/72*a1^2*a3*a6 + 1/4*a1^2*a4*a5 -
	    5/9*a1*a2^2*a6 + 1/12*a1*a2*a3*a5 + 1/9*a1*a2*a4^2 -
	    1/18*a1*a3^2*a4 - 1/9*a2^3*a5 + 1/18*a2^2*a3*a4 - 1/72*a2*a3^3,
	    a0*a1*a5*a6 - 7/30*a0*a3*a4*a5 + 4/45*a0*a4^3 + 11/144*a1^2*a5^2 -
	    7/30*a1*a2*a3*a6 + 1/18*a1*a2*a4*a5 - 1/45*a1*a3^2*a5 +
	    1/90*a1*a3*a4^2 + 4/45*a2^3*a6 + 1/90*a2^2*a3*a5 - 1/45*a2^2*a4^2 +
	    1/180*a2*a3^2*a4, a0*a2*a4*a6 - 5/24*a0*a3*a4*a5 - 1/9*a0*a4^3 +
	    125/576*a1^2*a5^2 - 5/24*a1*a2*a3*a6 + 13/72*a1*a2*a4*a5 -
	    5/144*a1*a3^2*a5 - 1/72*a1*a3*a4^2 - 1/9*a2^3*a6 -
	    1/72*a2^2*a3*a5 + 1/36*a2^2*a4^2 - 1/144*a2*a3^2*a4, a0*a2*a5^2 +
	    1/10*a0*a3*a4*a5 - 4/5*a0*a4^3 + a1^2*a4*a6 + 5/16*a1^2*a5^2 +
	    1/10*a1*a2*a3*a6 + 1/2*a1*a2*a4*a5 - 1/20*a1*a3^2*a5 -
	    1/10*a1*a3*a4^2 - 4/5*a2^3*a6 - 1/10*a2^2*a3*a5 + 1/5*a2^2*a4^2 -
	    1/20*a2*a3^2*a4, a0*a3^2*a6 - 10/3*a0*a3*a4*a5 + 32/9*a0*a4^3 -
	    125/18*a1^2*a5^2 - 10/3*a1*a2*a3*a6 + 20/9*a1*a2*a4*a5 +
	    47/18*a1*a3^2*a5 - 14/9*a1*a3*a4^2 + 32/9*a2^3*a6 -
	    14/9*a2^2*a3*a5 - 8/9*a2^2*a4^2 + 11/9*a2*a3^2*a4 - 1/4*a3^4,
	    a0^2*a6^2 - 43/60*a0*a3*a4*a5 + 38/45*a0*a4^3 - 493/288*a1^2*a5^2 -
	    43/60*a1*a2*a3*a6 + 19/36*a1*a2*a4*a5 + 239/360*a1*a3^2*a5 -
	    71/180*a1*a3*a4^2 + 38/45*a2^3*a6 - 71/180*a2^2*a3*a5 -
	    19/90*a2^2*a4^2 + 109/360*a2*a3^2*a4 - 1/16*a3^4, a0*a1*a5^2 +
	    4/25*a0*a2*a4*a5 - 8/25*a0*a3*a4^2 + 2/5*a1^2*a3*a6 +
	    1/5*a1^2*a4*a5 - 16/25*a1*a2^2*a6 - 2/25*a1*a2*a3*a5 +
	    4/25*a1*a2*a4^2 - 1/25*a1*a3^2*a4, a0*a2*a3*a6 - 10/9*a0*a2*a4*a5 -
	    5/9*a0*a3^2*a5 + 8/9*a0*a3*a4^2 - 25/18*a1^2*a3*a6 +
	    10/9*a1*a2^2*a6 - 1/6*a1*a2*a3*a5 - 2/9*a1*a2*a4^2 +
	    1/9*a1*a3^2*a4 + 2/9*a2^3*a5 - 1/9*a2^2*a3*a4 + 1/36*a2*a3^3,
	    a0^2*a5*a6 - 134/225*a0*a2*a4*a5 - 5/18*a0*a3^2*a5 +
	    118/225*a0*a3*a4^2 - 241/360*a1^2*a3*a6 - 1/20*a1^2*a4*a5 +
	    161/225*a1*a2^2*a6 - 19/300*a1*a2*a3*a5 - 34/225*a1*a2*a4^2 +
	    59/900*a1*a3^2*a4 + 1/9*a2^3*a5 - 1/18*a2^2*a3*a4 + 1/72*a2*a3^3,
	    a0^2*a5^2 - 136/125*a0*a2^2*a6 + 1/25*a0*a2*a3*a5 +
	    1/125*a0*a3^2*a4 + 2/5*a1^2*a2*a6 + 1/20*a1^2*a3*a5 -
	    1/25*a1^2*a4^2 - 4/125*a1*a2^2*a5 + 2/125*a1*a2*a3*a4 -
	    1/250*a1*a3^3, a0*a1*a3*a6 - 8/5*a0*a2^2*a6 + a0*a2*a3*a5 -
	    2/5*a0*a3^2*a4 + 1/4*a1^2*a3*a5 - 2/5*a1*a2^2*a5 +
	    1/5*a1*a2*a3*a4 - 1/20*a1*a3^3, a0*a1*a4*a5 + 36/25*a0*a2^2*a6 -
	    7/10*a0*a2*a3*a5 - 1/25*a0*a3^2*a4 - a1^2*a2*a6 - 1/8*a1^2*a3*a5 +
	    1/5*a1^2*a4^2 + 4/25*a1*a2^2*a5 - 2/25*a1*a2*a3*a4 + 1/50*a1*a3^3,
	    a0^2*a4*a6 - 29/25*a0*a2^2*a6 + 11/20*a0*a2*a3*a5 -
	    19/100*a0*a3^2*a4 + 1/4*a1^2*a2*a6 + 3/16*a1^2*a3*a5 -
	    1/20*a1^2*a4^2 - 6/25*a1*a2^2*a5 + 3/25*a1*a2*a3*a4 -
	    3/100*a1*a3^3, a0*a1*a2*a6 - 5/18*a0*a1*a3*a5 + 4/9*a0*a1*a4^2 +
	    1/9*a0*a2^2*a5 - 2/9*a0*a2*a3*a4 - 25/36*a1^3*a6 -
	    1/36*a1^2*a2*a5 + 1/18*a1^2*a3*a4, a0^2*a4*a5 - 2/9*a0*a1*a3*a5 +
	    5/9*a0*a1*a4^2 - 1/9*a0*a2^2*a5 - 5/18*a0*a2*a3*a4 - 5/9*a1^3*a6 +
	    1/36*a1^2*a2*a5 + 5/72*a1^2*a3*a4, a0^2*a3*a6 + 17/18*a0*a1*a3*a5 +
	    8/9*a0*a1*a4^2 + 2/9*a0*a2^2*a5 - 4/9*a0*a2*a3*a4 - 1/4*a0*a3^3 -
	    25/18*a1^3*a6 - 5/9*a1^2*a2*a5 + 13/36*a1^2*a3*a4, a0^2*a4^2 -
	    5/4*a0*a1^2*a6 - 5/16*a0*a1*a2*a5 + 1/8*a0*a1*a3*a4 -
	    1/4*a0*a2^2*a4 + 5/64*a1^3*a5 + 1/16*a1^2*a2*a4, a0^2*a3*a5 -
	    2*a0*a1^2*a6 + a0*a1*a3*a4 - 1/2*a0*a2*a3^2 - 1/2*a1^3*a5 +
	    1/8*a1^2*a3^2, a0^2*a2*a6 - 5/4*a0*a1^2*a6 + 1/4*a0*a1*a2*a5 +
	    1/2*a0*a1*a3*a4 - 1/4*a0*a2*a3^2 - 5/16*a1^3*a5 + 1/16*a1^2*a3^2,
	    a0^2*a2*a5 - 2/5*a0^2*a3*a4 - 5/4*a0*a1^2*a5 + a0*a1*a2*a4 +
	    1/5*a0*a1*a3^2 - 2/5*a0*a2^2*a3 - 1/4*a1^3*a4 + 1/10*a1^2*a2*a3,
	    a0^2*a1*a6 - 2/5*a0^2*a3*a4 + 1/4*a0*a1^2*a5 - 1/20*a0*a1*a3^2 +
	    1/10*a0*a2^2*a3 - 1/40*a1^2*a2*a3, a0^2*a1*a5 - 16/25*a0^2*a2*a4 +
	    1/5*a0*a1^2*a4 - 9/50*a0*a1*a2*a3 + 4/25*a0*a2^3 + 1/40*a1^3*a3 -
	    1/25*a1^2*a2^2, a0^3*a6 + 4/25*a0^2*a2*a4 - 1/4*a0^2*a3^2 -
	    1/20*a0*a1^2*a4 + 17/100*a0*a1*a2*a3 - 1/25*a0*a2^3 -
	    3/80*a1^3*a3 + 1/100*a1^2*a2^2, a0^3*a5 + 1/5*a0^2*a1*a4 -
	    1/2*a0^2*a2*a3 + 1/40*a0*a1^2*a3 + 1/5*a0*a1*a2^2 - 1/20*a1^3*a2,
	    a0^3*a4 - 1/2*a0^2*a1*a3 - 1/4*a0^2*a2^2 + 3/8*a0*a1^2*a2 -
	    5/64*a1^4>);
	
	// compute equation modulo some line
	Fm := Evaluate(F,[Pcx.1,Pcx.2,c0*Pcx.1^2+c1*Pcx.1*Pcx.2+c2*Pcx.2^2,0]);
	M := [Pcx.1^6,Pcx.1^5*Pcx.2,Pcx.1^4*Pcx.2^2,Pcx.1^3*Pcx.2^3,
	      Pcx.1^2*Pcx.2^4,Pcx.1*Pcx.2^5,Pcx.2^6];
	
	// pullback square relations
	AFF2 := AffineSpace(Pc);
	id := DefiningIdeal(Pullback(map<AFF2 -> AFF1 |
	    [MonomialCoefficient(Fm, b) : b in M]>, SQUARE1));
	
	// solve for suitable lines
	vprintf Classify : "Solving for real lines...";
	rts, ExtCount := SolveZeroDimIdeal(id : ExtName := ExtName,
	     ExtCount := ExtCount);
	lcfs := [* rt[1] : rt in rts *];
	vprintf Classify : " Done!\n";
	
	// construct parametrized lines
	res := [**];
	for lcf in lcfs do
		E := Universe(lcf);
		PE := ChangeRing(Px, E);
		PA := PolynomialRing(E);
		
		// we can at most blow down 8 lines
		if Degree(E, Q) gt 8 then continue; end if;
		
		Fn := hom<Px -> PE | PE.1, PE.2, lcf[1]*PE.1^2 +
		     lcf[2]*PE.1*PE.2 + lcf[3]*PE.2^2, PE.4>(F);
		for fact in Factorization(Fn) do
			f := fact[1];
			if not Degree(f,4) eq 1 then continue; end if;
			p := cfs[1] div -cfs[2] where cfs := Coefficients(f,4);
			// WHY IS FIRST COORDINATE ALWAYS 1???
			Append(~res, <[1, PA.1,
			     lcf[1] + lcf[2]*PA.1 + lcf[3]*PA.1^2,
			     Evaluate(p, [1, PA.1, lcf[1] + lcf[2]*PA.1 +
			     lcf[3]*PA.1^2, 0])], 0>);
		end for;
	end for;
	
	// now find degenerate lines: the singularities of the intersection
	// with the cone P112 (except the vertex itself)
	// ----------------------------------------------------------------
	
	// charts 1 and 2 in projection (3rd chart contains only the vertex)
	P<u,v> := PolynomialRing(Q, 2);
	F1 := Evaluate(F, [1,u,v,0]);
	F2 := Evaluate(F, [v,1,u,0]);
	
	// find singularities
	vprintf Classify : "Solving for degenerate lines (F = %o)...", F;
	Id1 := ideal<P | F1, Derivative(F1, 1), Derivative(F1, 2)>;
	Id2 := ideal<P | F2, Derivative(F2, 1), Derivative(F2, 2), v>;
	assert Dimension(Id1) lt 1; assert Dimension(Id2) lt 1;
	pts := [* [1, r[1][1], r[1][2], 0] : r in SolveZeroDimIdeal(Id1) *] cat
	       [* [r[1][2], 1, r[1][1], 0] : r in SolveZeroDimIdeal(Id2) *];
	vprintf Classify : " Done: %o\n", pts;
	
	// fake lines
	res := res cat [* <[F ! c : c in p], 1>
	    where F := PolynomialRing(Universe(p)) : p in pts *];
	
	return res;
end function;


// find lines on degree two Del Pezzo
// ----------------------------------
// input : a homogeneous polynomial 'F' (Tschirnhausen, in suitable grading)
//         defining a Del Pezzo of degree two
// output: an incomplete sequence of parametrizations of lines, but containing
//         all contractible lines (each line is a tuple of coordinates and
//         an adjustment parameter, see description of 'ContractLineDeg1or2')
function FindLinesDeg2(F : ExtName := "alpha", ExtCount := 0)
	Px := Parent(F); Q := BaseRing(Px);
	Pc<c0,c1> := PolynomialRing(Q, 2); Pcx := ChangeRing(Px, Pc);
	
	// square relations
	Pa<a0,a1,a2,a3,a4> := PolynomialRing(Q, 5);
	AFF1 := AffineSpace(Pa);
	SQUARE2 := Scheme(AFF1, ideal<Pa | 8*a0^2*a3 - 4*a0*a1*a2 + a1^3,
	    16*a0^2*a4 + 2*a0*a1*a3 - 4*a0*a2^2 + a1^2*a2,
	    8*a0*a1*a4 - 4*a0*a2*a3 + a1^2*a3, a0*a3^2 - a1^2*a4,
	    8*a0*a3*a4 - 4*a1*a2*a4 + a1*a3^2,
	    16*a0*a4^2 + 2*a1*a3*a4 - 4*a2^2*a4 + a2*a3^2,
	    8*a1*a4^2 - 4*a2*a3*a4 + a3^3>);
	
	// compute equation modulo some line
	M1 := [Pcx.1^4,Pcx.1^3*Pcx.2,Pcx.1^2*Pcx.2^2,Pcx.1*Pcx.2^3,Pcx.2^4];
	M2 := [Pcx.1^4,Pcx.1^3*Pcx.3,Pcx.1^2*Pcx.3^2,Pcx.1*Pcx.3^3,Pcx.3^4];
	M3 := [Pcx.3^4,Pcx.3^3*Pcx.2,Pcx.3^2*Pcx.2^2,Pcx.3*Pcx.2^3,Pcx.2^4];
	Fm1 := Evaluate(F,[Pcx.1,Pcx.2,c0*Pcx.1+c1*Pcx.2,0]);
	Fm2 := Evaluate(F,[Pcx.1,c0*Pcx.1,Pcx.3,0]);
	Fm3 := Evaluate(F,[0,Pcx.2,Pcx.3,0]);
	
	// pullback square relations
	AFF2 := AffineSpace(Pc);
	id1 := DefiningIdeal(Pullback(map<AFF2 -> AFF1 |
	    [MonomialCoefficient(Fm1, b) : b in M1]>, SQUARE2));
	id2 := ideal<Pc | c1> + DefiningIdeal(Pullback(map<AFF2 -> AFF1 |
	    [MonomialCoefficient(Fm2, b) : b in M2]>, SQUARE2));
	id3 := ideal<Pc | c0, c1> + DefiningIdeal(Pullback(map<AFF2 -> AFF1 |
	    [MonomialCoefficient(Fm3, b) : b in M3]>, SQUARE2));
	
	// solve for suitable lines
	rts1, ExtCount := SolveZeroDimIdeal(id1 : ExtName := ExtName,
	     ExtCount := ExtCount);
	rts2, ExtCount := SolveZeroDimIdeal(id2 : ExtName := ExtName,
	     ExtCount := ExtCount);
	rts3, ExtCount := SolveZeroDimIdeal(id3 : ExtName := ExtName,
	     ExtCount := ExtCount);
	lcfs1 := [* rt[1] : rt in rts1 *];
	lcfs2 := [* rt[1] : rt in rts2 *];
	lcfs3 := [* rt[1] : rt in rts3 *];
	
	// construct parametrized lines
	res := [**];
	for lcf in lcfs1 do
		E := Universe(lcf);
		PE := ChangeRing(Px, E);
		PA := PolynomialRing(E);
		
		// we can at most blow down 7 lines
		if Degree(E, Q) gt 7 then continue; end if;
		
		Fn := hom<Px -> PE |
		    PE.1, PE.2, lcf[1]*PE.1 + lcf[2]*PE.2, PE.4>(F);
		for fact in Factorization(Fn) do
			f := fact[1];
			if not Degree(f,4) eq 1 then continue; end if;
			p := cfs[1] div -cfs[2] where cfs := Coefficients(f,4);
			Append(~res, <[1, PA.1, lcf[1] + lcf[2]*PA.1,
			 Evaluate(p, [1, PA.1, lcf[1] + lcf[2]*PA.1, 0])], 0>);
		end for;
	end for;
	for lcf in lcfs2 do
		E := Universe(lcf);
		PE := ChangeRing(Px, E);
		PA := PolynomialRing(E);
		
		// we can at most blow down 8 lines
		if Degree(E, Q) gt 8 then continue; end if;
		
		Fn := hom<Px -> PE | PE.1, lcf[1]*PE.1, PE.3, PE.4>(F);
		for fact in Factorization(Fn) do
			f := fact[1];
			if not Degree(f,4) eq 1 then continue; end if;
			p := cfs[1] div -cfs[2] where cfs := Coefficients(f,4);
			Append(~res, <[PA.1, lcf[1]*PA.1, 1,
			    Evaluate(p, [PA.1, lcf[1]*PA.1, 1, 0])], 0>);
		end for;
	end for;
	for lcf in lcfs3 do
		PA := PolynomialRing(Q);
		Append(~res, <[0, PA.1, 1, 0], 0>);
	end for;
	
	return res;
end function;


// restrict linear system
// ----------------------
// input : a linear system 'ls', a parametrization 'l' of subset 'L' and
//         a multiplicity 'mult'
// output: the subsystem of 'ls' vanishing on 'L' with multiplicity 'mult'
function RestrictSystem(ls, l, mult)
	PROJ := AmbientSpace(ls); P := CoordinateRing(PROJ); Q := BaseRing(P);
	n := Rank(P); F := FieldOfFractions(Universe(l));
	
	// compute basis and sufficiently high order of derivatives;
	basis := Sections(ls); basis_derivs := [];
	for i in [1..mult] do
		new_derivs := [[[Derivative(b, i) : b in row]
		    : i in [1..n]] : row in basis_derivs];
		basis_derivs := [basis];
		for row in new_derivs do
			basis_derivs := basis_derivs cat row;
		end for;
	end for;
	
	// compute constraints
	con := [];
	for row in basis_derivs do
		evl := VectorSpace(F, #basis) ! [Evaluate(b, l) : b in row];
		con := con cat TransformRelations(Q, [evl]);
	end for;
	
	// restrict system
	rels := Transpose(Matrix(con));
	nb := [&+[sol[i]*basis[i] : i in [1..#basis]] where sol := Eltseq(b)
	       : b in Basis(Nullspace(rels))];
	return LinearSystem(ls, nb);
end function;


// contract line on Del Pezzo of degree one or two
// -----------------------------------------------
// input : a Del Pezzo 'X' of degree 'dp_deg', a parametrized "line" 'l' and an
//         adjustment parameter 'adjust' ('adjust = 0' if 'l' is a real line or
//         'adjust = 1' if it is a point, i.e. a degenerate line)
// output: the image 'Y' after contraction and a birational morphism 'X -> Y'
//         or 'false, 0, 0' if line is not contractible
function ContractLineDeg1or2(X, l, dp_deg, adjust)
	PROJ := AmbientSpace(X); P := CoordinateRing(PROJ); Q := BaseRing(P);
	I := DefiningIdeal(X); r := Degree(BaseRing(Universe(l)));
	F := FieldOfFractions(Universe(l));
	
	// linear system of degree r+3-dp_deg vanishing on l
	ls := LinearSystem(PROJ, r+3-dp_deg-adjust);
	cls := RestrictSystem(ls, l, 1);
	nls := Complement(cls, LinearSystem(cls, X));
	
	// get new coordinates
	new := Sections(nls);
	
	// is (possibly) contractible?
	if not (r+dp_deg+1 eq #new) then
		return false, 0, 0;
	end if;
	
	// possibly find extra coordinate
	if (dp_deg eq 1) and (r eq 1) then
		// system of degree 2*(r+2-adjust) vanishing 2 times on l
		ls := LinearSystem(PROJ, 2*(r+2-adjust));
		cls := RestrictSystem(ls, l, 2);
		nls := Complement(cls, LinearSystem(cls, X));
		
		// find linearly independent one
		als := LinearSystem(ls, CrossMultiply(P ! 0, [new, new]));
		als := Complement(als, LinearSystem(als, X));
		als := Complement(nls, als);
		new2 := Sections(als);
		
		// is contractible?
		if not (1 eq #new2) then
			return false, 0, 0;
		end if;
		
		// add weighted coordinate
		new := Append(new, new2[1]);
	end if;
	
	// compute map and image
	if (dp_deg eq 1) and (r eq 1) then
		PROJ2 := ProjectiveSpace(Q, [1,1,1,2]);
	else
		PROJ2 := ProjectiveSpace(Q, r+dp_deg);
	end if;
	m := map<X -> PROJ2 | new>; Y := Image(m); m := map<X -> Y | new>;
	
	return true, Y, m;
end function;


// reduce Del Pezzo of degree one or two
// -------------------------------------
// input : a Del Pezzo surface 'X' of degree one or two
// output: a birational Del Pezzo 'Y' of degree greater or equal 3
//         together with morphism 'X -> Y', or 'false, 0, 0' if none exists
function ReduceDelPezzoDeg1or2(X, dp_deg)
	PROJ := AmbientSpace(X); P := CoordinateRing(PROJ);
	Q := BaseRing(P); F := DefiningPolynomial(X);
	
	// produce nice equation w.r.t. last coordinate
	coeffs := Coefficients(F, 4);
	assert #coeffs eq 3; // must be quadratic in that variable
	a := -1/((Q! coeffs[3])*2)*coeffs[2];
	Fh := Evaluate(F, [P.1,P.2,P.3,P.4+a]);
	Xh := Scheme(PROJ, Fh);
	mh := map<X -> Xh | [P.1,P.2,P.3,P.4-a], [P.1,P.2,P.3,P.4+a]>;
	X := Xh; m := mh; F := 1/(Q! coeffs[3])*Fh;
	
	// maybe produce nice equation w.r.t. second but last coordinate
	if (dp_deg eq 1) then
		coeffs := Coefficients(F, 3);
		assert #coeffs eq 4; // must be cubic in that variable
		a := -1/((Q! coeffs[4])*3)*coeffs[3];
		Fh := Evaluate(F, [P.1,P.2,P.3+a,P.4]);
		Xh := Scheme(PROJ, Fh);
		mh := map<X -> Xh | [P.1,P.2,P.3-a,P.4], [P.1,P.2,P.3+a,P.4]>;
		X := Xh; m := m*mh; F := Fh;
	end if;
	
	// find lines on surface
	vprintf Classify: "Searching lines...";
	lines := (dp_deg eq 1) select FindLinesDeg1(F) else FindLinesDeg2(F);
	vprintf Classify: "Done!\n";
	
	// try to find first contractible line
	for line_and_adjust in lines do
		line, adjust := Explode(line_and_adjust);
		vprintf Classify: "Trying line of degree %o...",
		    Degree(BaseRing(Universe(line)),Q);
		isred, Xh, mh := ContractLineDeg1or2(X, line, dp_deg, adjust);
		vprintf Classify: "Done!\n";
		if isred then return true, Xh, m*mh; end if;
	end for;
	
	// no contractible lines!
	return false, 0, 0;
end function;

// compute self-intersection numbers
// ---------------------------------
// input : parametrization 'param' and ideal 'impl' of a "line" on projective
//         surface defined by 'I'
// output: self-intersection number of "line"
function SelfInt(param, impl, I)
        P := Universe(Basis(impl)); Q := BaseRing(P); n := Rank(P);
        F := FieldOfFractions(Universe(param));
        E := BaseRing(Universe(param)); deg := Degree(E, Q);

        // choose a form vanishing on the line
	//  added mch - 02/10 - check that the divisor of the form on
	//  the surface contains the line with multiplicity 1.
        for b in Reverse(GroebnerBasis(impl)) do
	  if b in I then continue; end if;
          deg2 := TotalDegree(b);
          // compute intersection number
          J := ColonIdeal(ideal<P | b> + I, impl) + impl;
          if Dimension(J) gt 1 then continue; end if;
	  intnum := deg*deg2;
          if not 1 in J then
                intnum := intnum - Degree(Scheme(ProjectiveSpace(P), J));
          end if;
	  break;
        end for;

        return intnum;
end function;

// find image relations of a parametrized line
// -------------------------------------------
// input:  parametrization 'p' of a line in 'ProjectiveSpace(P)'
// output: defining ideal of this line
function ImplicitizeParam(p, P)
	R := Universe(p); E := BaseRing(R); Q := BaseRing(P);
	
	// convert univariate polynomial ring to multivariate ring and ideal
	F := E; B := PolynomialRing(F, 1); I := ideal<B | 0>;
	h := hom<R -> B | B.1>; deg := Degree(F, Q);
	while deg gt 1 do
		// resolve one algebraic equation
		G := GroundField(F);
		dpol := DefiningPolynomial(F); rd := Degree(dpol);
		C := PolynomialRing(G, Rank(B)+1);
		chom := map<F -> C | x :->
		  &+[cf[i]*(C.1)^(i-1) : i in [1..rd]] where cf is Eltseq(x)>;
		phom := hom<B -> C | chom, [C.(i+1) : i in [1..Rank(B)]]>;
		
		// combine data
		h := h*phom;
		I := ideal<C | [phom(b) : b in Basis(I)]>
		     + ideal<C | &+[cf[i]*(C.1)^(i-1) : i in [1..rd+1]]
		                 where cf is Eltseq(DefiningPolynomial(F))>;
		
		// next round
		F := G; B := C; deg := Degree(F, Q);
	end while;
	
	// produce algebra and convert mapping sequence
	alg := quo<B | I>; param := [alg ! h(e) : e in p];
	
	// compute image of corresponding scheme map
	m := map<Spec(alg) -> ProjectiveSpace(P) | param>;
	return ideal<P | DefiningPolynomials(Image(m))>;
end function;

// find lines on a variety
// -----------------------
// input : a homogeneous ideal 'I' defining a surface with finitely many
//         lines in some projective space
// output: a sequence of parametrizations of lines (small degrees first)
forward FindLinesAux;
function FindLines(I : ExtName := "alpha", ExtCount := 0)
	P := Universe(Basis(I)); Q := BaseRing(P); n := Rank(P);
	
	// compute point pairs
	sols, ExtCount := FindLinesAux(I : ExtName := ExtName,
	    ExtCount := ExtCount);
	
	// sort solutions (small degrees first)
	solsaux := [[*l*] : l in sols];
	Sort(~solsaux, func<x, y | + Degree(Universe(x[1]), Q)
	                           - Degree(Universe(y[1]), Q)>);
	sols := [*l[1] : l in solsaux*];
	
	// produce nice output tuples
	res := [* *];
	for sol in sols do
		// produce parametrization
		E := Universe(sol); M := PolynomialRing(E); s := M.1;
		param := [sol[i]*(1-s) + sol[n+i]*s : i in [1..n]];
		Append(~res, param);
	end for;
	
	return res, ExtCount;
end function;
function FindLinesAux(I : ExtName := "alpha", ExtCount := 0, rest := [* *])
	P := Universe(Basis(I)); Q := BaseRing(P); n := Rank(P);
	
	// rings for lines with indetermined coefficients
	A := PolynomialRing(Q, 2*n); B := PolynomialRing(Q, 2*n+1);
	P2B := hom<P->B | [B.i*(1-B.(2*n+1))+ B.(n+i)*B.(2*n+1): i in [1..n]]>;
	B2A := hom<B->A | [A.i : i in [1..2*n]] cat [0]>;
	
	// compute defining equations
	id := ideal<A | Flat([B2A(Coefficients(P2B(b), B.(2*n+1)))
	                      : b in Basis(I)])>;
	
	// a dice roller
	myrand := function() return Random(6) - 3; end function;
	
	if IsEmpty(rest) then
		// guess two good hyperplanes
		while (true) do
			r1 := [myrand() : i in [1..n]];
			r2 := [myrand() : i in [1..n]];
			p1 := &+[r1[i]*A.i : i in [1..n]];
			p2 := &+[r2[i]*A.(n+i) : i in [1..n]];
			id2 := id + ideal<A | [p1, p2]>;
			
			// we need two different well-defined planes
			if p1*p2 eq 0 then continue; end if;
			if IsDivisibleBy(p1,p2) then continue; end if;
			
			// planes may not contain lines
			if not Dimension(id2) le 2 then continue; end if;
			
			break;
		end while;
		
		// solve for roots in projective space product
		sols := SolveInProductSpace(id2 : seq := [0, n, 2*n],
		    ExtName := ExtName, ExtCount := ExtCount);
	else
		sols := [* *];
		for r in rest do
			E := Universe(r); PE := PolynomialRing(E, n);
			A2PE := hom<A -> PE | [r[i] : i in [1..n]]
			                      cat [PE.i : i in [1..n]]>;
			id2 := ideal<PE | [A2PE(b) : b in Basis(id)]>;
			
			// guess one good hyperplane
			while (true) do
				p := &+[myrand()*PE.i : i in [1..n]];
				id3 := id2 + ideal<PE | p>;
				
				// we need a real plane
				if p eq 0 then continue; end if;
				
				// plane may not pass through special point
				if Evaluate(p, r) eq 0 then
					continue;
				end if;
				
				// plane may not contain lines
				if not Dimension(id3) le 1 then
					continue;
				end if;
				
				break;
			end while;
			
			// solve for roots in simple projective space
			roots, ExtCount := SolveInProductSpace(id3
			    : seq := [0, n], ExtName := ExtName,
			      ExtCount := ExtCount);
			sols := sols cat [* [Universe(rt) | r[i] : i in [1..n]]
			     cat rt : rt in roots *];
		end for;
	end if;
	
	// sort out degenerate lines
	solsaux := [* *]; diag := [* *];
	for s in sols do
		if &and[s[i] eq s[n+i] : i in [1..n]] then
			Append(~diag, s[1..n]);
		else
			Append(~solsaux, s);
		end if;
	end for;
	sols := solsaux;
	
	// maybe treat points on diagonal
	if IsEmpty(rest) then
		solsextra := FindLinesAux(I : ExtName := ExtName,
		    ExtCount := ExtCount, rest := diag);
		sols := sols cat solsextra;
	end if;
	
	return sols, ExtCount;
end function;


// contract line on Del Pezzo
// --------------------------
// input : a Del Pezzo surface 'X' and a contractible line 'L' on it
// output: the image 'Y' after contraction and a birational morphism 'X -> Y'
function ContractLine(X, L)
	PROJ := AmbientSpace(X); P := CoordinateRing(PROJ); Q := BaseRing(P);
	I := DefiningIdeal(X); J := DefiningIdeal(L); r := Degree(L);
	
	// find a low degree form
	e := Infinity();
	for b in Basis(J) do
		if (TotalDegree(b) lt e) and not b in I then
			e := TotalDegree(b); F := b;
		end if;
	end for;
	
	// find remainder divisor
	K := ColonIdeal(I + ideal<P | F>, J);
	
	// start with complete linear system on ambient space
	ls := LinearSystem(PROJ, e+1);
	
	// geometric constraint
	cls := LinearSystem(ls, Scheme(PROJ, K));
	
	// compute complement to trivial subsystem and vanishing subsystem
	triv := [F*P.i : i in [1..Rank(P)]];
	vanish := Sections(LinearSystem(cls, X));
	nls := Complement(cls, LinearSystem(ls, triv cat vanish));
	
	// get new coordinates
	new := Sections(nls);
	
	// is contractible?
	if not (r eq #new) then
		return false, 0, 0;
	end if;
	
	// compute map and image
	P2 := PolynomialRing(Q, Rank(P)+r); PROJ2 := ProjectiveSpace(P2);
	m := map<X -> PROJ2 | triv cat new>; Y := Image(m);
	m := map<X -> Y | triv cat new, [P2.i : i in [1..Rank(P)]]>;
	
	return true, Y, m;
end function;

// reduce higher degree Del Pezzo
// ------------------------------
// input : a Del Pezzo 'X' surface of degree greater two in some (ordinary)
//         projective space and a degree 'd'
// output: a birational Del Pezzo 'Y' of degree greater or equal 'd'
//         together with morphism 'X -> Y'
function ReduceDelPezzo(X, d)
	PROJ := AmbientSpace(X); P := CoordinateRing(PROJ); Q := BaseRing(P);
	I := DefiningIdeal(X); dp_deg := Dimension(PROJ);
	
	// early abort?
	if dp_deg ge d then return true, X, IdentityMap(X); end if;
	
	// find lines on Del Pezzo surface
	vprintf Classify: "Searching lines...";
	lines := FindLines(I);
	vprintf Classify: "Done!\n";
	
	// implicitize lines and sort out contractible ones
	linesaux := [**]; mdeg := 0;
	vprintf Classify: "Impliziting lines...";
	for param in lines do
		E := BaseRing(Universe(param));
		
		// we can at most blow down 9 - dp_deg lines
		if Degree(E, Q) gt (9 - dp_deg) then continue; end if;
		
		impl := ImplicitizeParam(param, P); // implicite equation
		deg := Degree(E, Q);                // number of lines
		sint := SelfInt(param, impl, I);    // self-intersection number
		nsing := IsNonSingular(Scheme(PROJ, impl));
		                                    // non-singular?
		if (deg eq -sint) and nsing then    // is contractible?
			Append(~linesaux, <param, impl, deg, sint, nsing>);
			mdeg := Max(mdeg, deg);
		end if;
	end for;
	vprintf Classify: "Done!\n";
	
	// heuristic: Can we do it in one stroke?
	if mdeg + Dimension(PROJ) ge d then
		lines := [* l : l in linesaux | l[3] + Dimension(PROJ) ge d *];
	else
		lines := linesaux;
	end if; 
	
	// choose a contractible line if possible 
	for line in lines do
		param, impl, deg, sint, nsing := Explode(line);
		
		// blow it down
		vprintf Classify: "Contracting line of degree %o...", deg;
		iscontr, Y, m := ContractLine(X, Scheme(PROJ, impl));
		assert iscontr;
		vprintf Classify: "Done!\n";
		
		// minimize recursively
		isred, Yh, mh := ReduceDelPezzo(Y, d);
		if isred then
			return true, Yh, m*mh;
		end if;
	end for;
	
	// no contractible lines!
	return false, 0, 0;
end function;



// ======================
// = Exported functions =
// ======================

intrinsic ParametrizeDelPezzo(X::Sch, P2::Prj)
-> BoolElt, MapSch
{
Given a Del Pezzo surface embedded in some weighted projective space.
Return 'false' if 'X' is not parametrizable over the rationals, otherwise
return 'true' and a parametrization.
}
	vprint Classify: "------------ Entering DelPezzo -------------";
	Y := X; m := IdentityMap(Y);
	
	// try to reduce Del Pezzos of degree 1
	if not IsOrdinaryProjective(AmbientSpace(Y)) and
	    &*Gradings(AmbientSpace(Y))[1] eq 6 then
		vprintf Classify: "Trying to reduce degree 1 Del Pezzo...\n";
		isred, Yh, mh := ReduceDelPezzoDeg1or2(Y, 1);
		if not isred then return false, _; end if;
		// compute and store inverse (bugfix!)
		_, mhinv := myInvertible(mh); _, mh := myInvertible(mhinv);
		Y := Yh; m := m*mh;
	end if;
	
	// try to reduce Del Pezzos of degree 2
	if not IsOrdinaryProjective(AmbientSpace(Y)) and
	    &*Gradings(AmbientSpace(Y))[1] eq 2 then
		vprintf Classify: "Trying to reduce degree 2 Del Pezzo...\n";
		isred, Yh, mh := ReduceDelPezzoDeg1or2(Y, 2);
		if not isred then return false, _; end if;
		// compute and store inverse (bugfix!)
		_, mhinv := myInvertible(mh); _, mh := myInvertible(mhinv);
		Y := Yh; m := m*mh;
	end if;

	// for singular degree 3/4 Del Pezzos, call specialised parameter code
	dima := Dimension(AmbientSpace(Y));
	if IsOrdinaryProjective(AmbientSpace(Y)) and ((dima eq 3) or (dima eq 4)) then
	    Ysng := SingularSubscheme(Y);
	    if not IsEmpty(Ysng) then
	      if dima eq 4 then
		vprintf Classify: "Using routines for singular degree 4 Del Pezzo...\n";
		ispara,param := ParametrizeSingularDegree4DelPezzo(Y,P2);
	      else
		vprintf Classify: "Using routines for singular degree 3 Del Pezzo...\n";
		ispara,param := ParametrizeSingularDegree3DelPezzo(Y,P2);
	      end if;
	      if ispara then
		return true, Expand(param*m^(-1));
	      else
		return false, _;
	      end if;
	    end if;
	end if;
 	
	// try to reduce Del Pezzos of higher degree
	vprintf Classify: "Trying to reduce degree %o Del Pezzo...\n",
	     Dimension(AmbientSpace(Y));
	isred, Yh, mh := ReduceDelPezzo(Y, 5);
	if not isred then return false, _; end if;
	Y := Yh; m := m*mh;
	
	// compute parametrizations for certain degrees
	case Dimension(AmbientSpace(Y)):
		when 5:
			ispara := true;
			param := ParametrizeDegree5DelPezzo(Y);
		when 6:
			ispara, param := ParametrizeDelPezzoDeg6(Y);
		when 7:
			ispara := true;
			param := ParametrizeDegree7DelPezzo(Y);
		when 8:
			ispara, param := ParametrizeDegree8DelPezzo(Y);
		when 9:
			ispara, param := ParametrizeDelPezzoDeg9(Y);
		else:
			error "Encountered Del Pezzo in too large an ambient "*
			      "space!";
	end case;
	
	vprint Classify: "------------ Leaving DelPezzo -------------";
	if ispara then
		iso := map<P2 -> D | [P2.1, P2.2, P2.3],[D.1,D.2,D.3]>
		   where D is Domain(param) ;
		return true, iso*param*m^(-1);
	else
		return false, _;
	end if;
end intrinsic;
