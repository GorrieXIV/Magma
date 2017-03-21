freeze;

/***
 *  Twists of Genus 2 Curves.
 *
 *  Distributed under the terms of the GNU Lesser General Public License (L-GPL)
 *                  http://www.gnu.org/licenses/
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation; either version 2.1 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 *  Copyright 2007-2009 R. Lercier & C. Ritzenthaler
 */

/***
 *
 * This file provides tools to obtain, in any fields, models of genus 2 curves
 * from absolute invariants, and automorphism groups from invariants or
 * genus 2 curves.
 *  
 * In the geometric setting, i.e. when only one model is requested, routines
 * of this kind are available, except for very few cases in characteristic
 * 2 or 5 finite fields, in Kohel's CrvG2 package (cf D. Kohel's web page),
 * and in a less complete preliminary implementation by Howe et al.
 * (cf. MAGMA package). In the arithmetic case, that is when all the
 * twists are requested, we are not aware of any other implementation.
 *
 * All of this is based on numerous results due to Mestre, Cardona, Nart, etc.
 * Precise references are given in the enclosed bibliography and in the code.
 *
 *********************************************************************/

/***
 * Changes.
 *
 * 2007-09-26, v0.0 : R. Lercier, C. Ritzenthaler, 
 *             Initial version.
 *
 * 2007-10-19, v1.0 : R. Lercier, C. Ritzenthaler, 
 *             Placed under the Lesser General Public License
 *
 * 2009-02-25, v1.1 : R. Lercier, C. Ritzenthaler, 
 *             Feedback by M. Harrison and E. Gonzalez-Jimenez.
 *
 * 2010-11-23, v1.2 : R. Lercier, C. Ritzenthaler, 
 *             Feedback by J. Cannon.
 *
 ********************************************************************/

/***
 * Bibliography
 *
 * [Mestre91] "Construction de courbes de genre 2 \`a partir de leurs modules"
 * Jean-Fran\,cois Mestre, in "Effective Methods in Algebraic Geometry",
 * vol 94 of Progress in Mathematics, 313-334, Birkhauser, 1991.
 *
 * [Cardona2003] "On the number of curves of genus 2 over a finite field",
 * G. Cardona, Finite Fields and Their Applications 9 (4), 505-526, 2003
 *
 * [ShVo2004] "Elliptic subfields and automorphisms of genus 2
 * function fields", T. Shaska, H. Volklein, Algebra, Arithmetic and
 * Geometry with Applications (West Lafayette, IN, 2000),703-723,
 * Springer, 2004
 *
 * [CaNaPu2005] "Curves of genus two over fields of even characteristic",
 * G. Cardona, E. Nart and J. Pujolas, Mathematische Zeitschrift,
 * 250, 177-201, Springer, 2005
 *
 * [CaQu2005] "Field of moduli and field of definition for curves of genus 2",
 * G. Cardona, J. Quer, Computational aspects of algebraic curves,  71-83,
 * Lecture Notes Ser. Comput., 13, World Sci. Publ., Hackensack, NJ, 2005.
 *
 * [CaNa2007] "Zeta Function and Cryptographic Exponent of Supersingular
 * Curves of Genus 2", G. Cardona, E. Nart, ArXiv e-prints 0704.1951C, 2007.
 *
 *********************************************************************/

/***
 * Exported intrinsics.
 *
 * intrinsic IgusaToG2Invariants(JI::SeqEnum) -> SeqEnum
 * intrinsic G2ToIgusaInvariants(GI::SeqEnum) -> SeqEnum
 * intrinsic G2Invariants(H::CrvHyp) -> SeqEnum
 * intrinsic HyperellipticCurveFromG2Invariants(GI::SeqEnum) -> CrvHyp, GrpPerm
 * intrinsic Twists(GI::SeqEnum) -> SeqEnum[CrvHyp], GrpPerm
 * intrinsic Twists(H::CrvHyp) -> SeqEnum[CrvHyp], GrpPerm
 * intrinsic GeometricAutomorphismGroup(GI:SeqEnum) -> GrpPerm
 * intrinsic GeometricAutomorphismGroup(H::CrvHyp) -> GrpPerm
 * intrinsic GeometricAutomorphismGroupClassification(FF::FldFin) -> SeqEnum,SeqEnum
 *
 ********************************************************************/

import "../CrvHyp/g3twists/g3twists.m": G3Models;

 /***
  *
  * Twists stuff in Characteristic 2 finite fields,
  * see [CaNaPu2005].
  *
  ********************************************************************/
TraceOneElement := function(FF)
    if IsOdd(Degree(FF)) then
      return FF!1;
    end if;
    repeat
      x := Random(FF);
      t := Trace(x);
    until t ne 0;
    return x/t;
end function;

G2ModelsInChar2FF_C2 := function(GI : geometric := false)

    FF := Universe(GI);
    g1, g2, g3 := Explode(GI);
    x := PolynomialRing(FF).1;
    if not geometric then o := TraceOneElement(FF); end if;
    
    if g1 eq 0 then
	H1 := HyperellipticCurve([g2*x^5+g3*x^3+x,x]);
	if geometric then return [H1]; end if;
	H2 := HyperellipticCurve([g2*x^5+g3*x^3+o*x^2+x,x]);
	return [H1, H2];
    end if;
    F := Factorization(x^3+g3*x^2+g2*x+g1);
    splitF := Max([Degree(f[1]) : f in F]);
    if splitF eq 1 then
	rts := []; for f in F do
	    for i := 1 to f[2] do Append(~rts,Coefficient(f[1], 0)); end for;
	end for;
	a, b, c := Explode(rts);
	H1 := HyperellipticCurve([a*x^5+2*a*x^4+(c+b+a)*x^3+(2*b+c)*x^2+b*x,x*(x+1)]);
	if geometric then return [H1]; end if;
	H2 := HyperellipticCurve([a*x^5+(2*a+o)*x^4+(c+b+2*o+a)*x^3+(2*b+c+o)*x^2+b*x,x*(x+1)]);
	return [H1, H2];
    end if;
    if splitF eq 2 then
	for f in F do
	    if Degree(f[1]) eq 1 then
		a := Coefficient(f[1], 0);
	    else
		v := Coefficient(f[1], 0);
		u := Coefficient(f[1], 1);
	    end if;
	end for;
	H1 := HyperellipticCurve([a*x*(x^2+x+v/u^2)^2+(u*x+u)*(x^2+x+v/u^2), x^2+x+v/u^2]);
	if geometric then return [H1]; end if;
	H2 := HyperellipticCurve([(a*x+o)*(x^2+x+v/u^2)^2+(u*x+u)*(x^2+x+v/u^2), x^2+x+v/u^2]);
	return [H1, H2];
    end if;
    if g2 eq g3^2 then
	s := g1+g2*g3; t := 0; a := 0; b := g1+g2*g3; c := g3*(g1+g2*g3);
    else
	den := (g1+g2*g3);
	s := (g2+g3^2)^3/den^2; t := s; a := (g1+g3^3)*(g2+g3^2)^2/den^2; b := a;
	c := (g2+g3^2)^3*(g1*(g2+g3^2)^2+g3*(g1+g3^3)^2)/den^4;
    end if;
    H1 := HyperellipticCurve([a*x^5+b*x^4+(c+a*t)*x^3+(a*s+b*t)*x^2+(c*t+b*s)*x+c*s,x^3+t*x+s]);
    if geometric then return [H1]; end if;
    H2 := HyperellipticCurve([o*x^6+a*x^5+(2*o*t+b)*x^4+(2*o*s+a*t+c)*x^3+(a*s+t*(o*t+b))*x^2+(s*(o*t+b)+t*(o*s+c))*x+s*(o*s+c), x^3+t*x+s]);
    return [H1, H2];
end function;

G2ModelsInChar2FF_C2bis := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    _, g2, _ := Explode(GI);
    
    H1 := HyperellipticCurve([g2*x^5+x,x]);
    if geometric then return [H1]; end if;

    o := TraceOneElement(FF);
    H2 := HyperellipticCurve([g2*x^5+o*x^2+x,x]);
    return [H1, H2];
end function;

G2ModelsInChar2FF_C2xC2 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;

    _, g2, g3 := Explode(GI);    
    a := g3; b := Sqrt(g2); c := b;
    
    H := HyperellipticCurve([a*x^5+2*a*x^4+a*x^3+c*x^2+c*x, x^2+x]);
    if geometric then return [H]; end if;

    o := TraceOneElement(FF);
    
    if Trace(g3) eq 0 then
	return [H,
	    HyperellipticCurve([a*x^5+(o+2*a)*x^4+(2*o+a)*x^3+(c+o)*x^2+c*x,x^2+x]),
	    HyperellipticCurve([a*x^5+2*a*x^4+(2*a*o+a)*x^3+(c+2*a*o)*x^2+(c+a*o^2)*x+c*o, x^2+x+o]),
	    HyperellipticCurve([a*x^5+(o+2*a)*x^4+(2*o+2*a*o+a)*x^3+(o^2+c+o+a*o+(o+a)*o)*x^2+(o^2+c+(o+a*o)*o)*x+(o^2+c)*o, x^2+x+o])
	    ];
    end if;
    return [H,
	HyperellipticCurve([a*x^5+2*a*x^4+(2*a*o+a)*x^3+(c+2*a*o)*x^2+(c+a*o^2)*x+c*o, x^2+x+o])
	];
end function;

G2ModelsInChar2FF_C2xS3 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    _, _, g3 := Explode(GI);
    
    a := g3; b := a; c := b;

    H := HyperellipticCurve([a*x^5+2*a*x^4+a*x^3+c*x^2+c*x, x^2+x]);
    if geometric then return [H]; end if;

    o := TraceOneElement(FF);
    
    if Trace(g3) eq 0 then
	quads := [H,
	    HyperellipticCurve([a*x^5+(o+2*a)*x^4+(2*o+a)*x^3+(c+o)*x^2+c*x,x^2+x]),
	    HyperellipticCurve([a*x^5+2*a*x^4+(2*a*o+a)*x^3+(c+2*a*o)*x^2+(c+a*o^2)*x+c*o, x^2+x+o]),
	    HyperellipticCurve([a*x^5+(o+2*a)*x^4+(2*o+2*a*o+a)*x^3+(o^2+c+o+a*o+(o+a)*o)*x^2+(o^2+c+(o+a*o)*o)*x+(o^2+c)*o, x^2+x+o])
	    ];
    else
	quads := [H,
	    HyperellipticCurve([a*x^5+2*a*x^4+(2*a*o+a)*x^3+(c+2*a*o)*x^2+(c+a*o^2)*x+c*o, x^2+x+o])
	    ];
    end if;

    S := Random(FF);
    while not IsIrreducible(x^3+S*x+S) do S := Random(FF); end while;

    t := S; s := S; a := g3*S; b := g3*S; c := g3*S*(S+1);
    cubs := [
	HyperellipticCurve([a*x^5+b*x^4+(c+a*t)*x^3+(a*s+b*t)*x^2+(c*t+b*s)*x+c*s, x^3+t*x+s]), 
	HyperellipticCurve([o*x^6+a*x^5+(2*o*t+b)*x^4+(2*o*s+a*t+c)*x^3+(a*s+t*(o*t+b))*x^2+(s*(o*t+b)+t*(o*s+c))*x+s*(o*s+c), x^3+t*x+s])
	];
    
    return quads cat cubs;
end function;

G2ModelsInChar2FF_M32 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    
    _, _, g3 := Explode(GI);
    sg3 := Sqrt(g3);    
    if geometric then return [HyperellipticCurve([sg3*x^5+sg3*x^3, 1])]; end if;

    o := TraceOneElement(FF);
    
    E := sg3^4*x^16+sg3^4*x^8+sg3^2*x^2+sg3*x;
    KE := Roots(E);
    V := VectorSpace(GF(2),Degree(FF));
    W, pi := quo< V | [ V!Eltseq(Evaluate(E,x)) where x is FF!Eltseq(v) : v in Basis(V) ] >;
    K := [FF!Eltseq(w@@pi) : w in W];

    twists := [];
    for b in K do
	H := HyperellipticCurve([sg3*x^5+b*x^4+sg3*x^3, 1]);
	twists cat:= [H];

	notwists := false;
	for k in KE do
	    if Trace(sg3*k[1]^5+b*k[1]^4+sg3*k[1]^3) eq 1 then notwists := true; break; end if;
	end for;

	if notwists eq false then
	    twists cat:= [HyperellipticCurve([sg3*x^5+b*x^4+sg3*x^3+o, 1])];
	end if;
    end for;

    return twists;
end function;

G2ModelsInChar2FF_M160 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;

    if geometric then return [HyperellipticCurve([x^5, 1])]; end if;
    
    o := TraceOneElement(FF);
    prim := PrimitiveElement(FF);

    if (Degree(FF) mod 4) ne 0 then
	if (Degree(FF) mod 2) ne 0 then
	    H := HyperellipticCurve([x^5, 1]);
	    return [H,
		HyperellipticCurve([x^5+x^4, 1]),
		HyperellipticCurve([x^5+x^4+1, 1])
		];
	end if;
	F4 := GF(2^2); Embed(F4, FF); u := FF!F4.1;
	H := HyperellipticCurve([x^5, 1]);
	return [H,
	    HyperellipticCurve([x^5+x^4, 1]),
	    HyperellipticCurve([x^5+u*x^4, 1]),
	    HyperellipticCurve([x^5+(u+1)*x^4, 1]),
	    HyperellipticCurve([x^5+x^4+u, 1])
	    ];
    end if;

    A := Setseq(Seqset([prim^i : i in [0..4]]));
    MU5 := [r[1] : r in Roots(x^5-1)];

    twists := [];
    for a in A do
	H := HyperellipticCurve([a*x^5, 1]);
	twists cat:= [H];
	twists cat:= [HyperellipticCurve([a*x^5+o, 1])];
    end for;

    E1 := x^16+x;
    V := VectorSpace(GF(2),Degree(FF));
    W, pi := quo< V | [ V!Eltseq(Evaluate(E1,x)) where x is FF!Eltseq(v) : v in Basis(V) ] >;

    W := [w : w in W | w ne W!0];
    for i := 1 to 3 do
	a := FF!Eltseq(W[1]@@pi);
	H := HyperellipticCurve([x^5+a*x^4, 1]);
	twists cat:= [H];
	for mu in MU5 do
	    W := Setseq(Seqset(W) diff {pi(V!Eltseq(a*mu))});
	end for;
    end for;

    return twists;
end function;

/*
 * Genus 2 HyperElliptic Curves Twists in finite fields of characteristic > 2
 *
 ***************************************************************************/
G2NonIsomorphic := function(Ecs)
   crvs := [];
   for E1 in Ecs do
       old := &or[ IsIsomorphic(E1,E0) : E0 in crvs ];
       if not old then Append(~crvs,E1); end if;
  end for;
  return crvs;
end function;

function CheapIntegerSquareFreePart(i)
     Q := Factorization(i: ECMLimit := 10, MPQSLimit := 0);
     _,af := Squarefree(Q);
     a := FactorizationToInteger(af);
     return i div a^2, a;
end function;

function CheapRationalSquareFreePart(r)
     an, bn := CheapIntegerSquareFreePart(Numerator(r));
     ad, bd := CheapIntegerSquareFreePart(Denominator(r));
  return an*ad, bn/(ad*bd);
end function;

function MestreFindPointOnConic(L) // ::RngMPolElt) 
    // Find an affine point (x,y,1) on the projective conic L.
    K := BaseRing(Parent(L));
    UP := PolynomialRing(K : Global := false); u := UP.1;
    if Type(K) eq FldFin then
	repeat
	    x1 := Random(K); x3 := K!1;
	    LL := Evaluate(L, [UP | x1,u,x3]);
	    t, x2 := HasRoot(LL);
	until t;
	return x1,x2;
    elif Type(K) eq FldRat then
	P := ProjectiveSpace(K, 2);
	x := P.1; y := P.2; z := P.3;
	C := Conic(P, L);
	if not HasRationalPoint(C) then
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
	    found := false;
	    repeat
		S := Reduction(Random(C));
		if S[3] ne 0 then
		    found := true;
		else
		    pol := Evaluate(L, [UP | S[1],S[2],u]); // pol = c*u*(u-t)
		    if Coefficient(pol, 2) ne 0 then
			s3 := -Coefficient(pol, 1)/Coefficient(pol, 2);
			found := true;
		    end if;
		end if;
	    until found;
	    assert Evaluate(L, Eltseq(S)) eq 0;
	    if S[3] eq 0 then
		if s3 ne 0 then return S[1]/s3, S[2]/s3; end if;
		// There is only one tangent line...
		if S[1] eq 0 then
		    pol := Evaluate(L, [UP | S[1]+u,S[2],u]); // pol = c*u*(u-t)
		else
		    pol := Evaluate(L, [UP | S[1],S[2]+u,u]); // pol = c*u*(u-t)
		end if;
		s3 := -Coefficient(pol, 1)/Coefficient(pol, 2);
		error if s3 eq 0, "Error in MestreFindPointOnConic";
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

ClebschMestreConicAndCubic := function(GI)

    FF := Universe(GI);
    J2,J4,J6,_,J10 := Explode(G2ToIgusaInvariants(GI));

    p := Characteristic(Parent(J2));
    P3 := PolynomialRing(Parent(J2), 3); x1 := P3.1; x2 := P3.2; x3 := P3.3;

    /* Clebsch-Mestres conics & cubics, as a function of Igusa Invariants */
    if p eq 5 then

	if J2 eq 0 then

	    /* J4 <> 0 */
	    R2 := J6^5+3*J10*J4^5+3*J6^3*J4^3+J6*J4^6;
	    if not IsSquare(R2) then
		J4 *:= R2^2; J6 *:= R2^3; J10 *:= R2^5; R2 *:= R2^15;
	    end if;
	    R := Sqrt(R2);
	    L := J6*x1^2+4*J4^2*x2*x1+4*x3^2*J4^2;
	    M := (3*J4^4+4*J6^2*J4)*x1^2*x2+(4*J4^4+3*J6^2*J4)*x1*x3^2+
		2*J4^5*x2^3+J6*J4^2*x1^3+4*x1*J6*J4^3*x2^2+4*x3*x1^2*R;
	else

	    L := J2*x1^2+((J4*J2^2+2*J4^2+J2^4+4*J2*J6)*x2+(2*J2*J4^2+J6*J4+4*J2^5)*x3)*x1+(J4^
		2*J2^3+4*J2^7+3*J6*J4^2+3*J4*J2^5+2*J4^3*J2)*x2^2+(3*J2^3*J10+(3*J4+3*J2^2)*J6
		^2+(J2*J4^2+4*J2^5+J2^3*J4)*J6+2*J2^8+2*J2^6*J4+3*J2^2*J4^3+2*J2^4*J4^2)*x3*x2
		+((4*J4*J2^2+3*J2^4)*J10+2*J6^3+3*J6^2*J2^3+(2*J4*J2^4+3*J2^6+3*J4^2*J2^2)*J6+
		4*J2^9+J4^3*J2^3)*x3^2;

	    M := (3*J4*J2+3*J2^3)*x1^3+(((2*J2^3+2*J4*J2)*J6+3*J4*J2^4+J2^6+2*J4^3+2*J4^2*J2^2)
		*x2+(4*J6^2*J2+(J4^2+3*J4*J2^2+J2^4)*J6+2*J4^3*J2+J4^2*J2^3+4*J4*J2^5+J2^7)*x3
		)*x1^2+((4*J10*J2^4+2*J6^2*J2^3+(4*J2^6+3*J4^3+J4^2*J2^2+2*J4*J2^4)*J6+2*J4^2*
		J2^5+J4^4*J2+3*J4^3*J2^3+J4*J2^7)*x2^2+((4*J2^5+3*J2^3*J4)*J10+(J4*J2^2+2*J2^4
		+3*J4^2)*J6^2+(3*J4*J2^5+3*J2^7+2*J4^2*J2^3+J4^3*J2)*J6+2*J2^10+2*J4^4*J2^2+J4
		*J2^8+3*J4^2*J2^6)*x3*x2+((4*J4^2*J2^2+J4*J2^4+3*J6*J2^3)*J10+(2*J4+4*J2^2)*J6
		^3+(4*J2*J4^2+2*J2^5)*J6^2+(J2^2*J4^3+2*J2^4*J4^2+J2^6*J4)*J6+3*J2^11+2*J4^3*
		J2^5+J4^4*J2^3+2*J4^2*J2^7)*x3^2)*x1+((J4*J2^5+J2^7+J6*J2^4)*J10+(3*J2^6+2*J4^
		2*J2^2+J4*J2^4)*J6^2+(3*J4^3*J2^3+J2^9+2*J4^2*J2^5)*J6+2*J4*J2^10+2*J2^12+3*J4
		^3*J2^6+4*J4^5*J2^2+3*J4^2*J2^8)*x2^3+(((4*J2^5+2*J2^3*J4)*J6+J2^6*J4+4*J2^8+
		J2^2*J4^3+4*J2^4*J4^2)*J10+(2*J2^4+2*J4*J2^2)*J6^3+(J4*J2^5+4*J2^7+J4^2*J2^3+4
		*J4^3*J2)*J6^2+(4*J2^4*J4^3+2*J2^10+2*J4^2*J2^6+4*J4^4*J2^2+3*J4*J2^8)*J6+J4^5
		*J2^3+3*J4^2*J2^9+3*J4^3*J2^7+2*J2^13)*x3*x2^2+((J6^2*J2^3+(J4^2*J2^2+2*J2^6+2
		*J4*J2^4)*J6+2*J4^3*J2^3+J2^9+4*J4*J2^7)*J10+3*J6^4*J2^2+(2*J2^3*J4+J2^5+4*J2*
		J4^2)*J6^3+(3*J2^8+4*J2^4*J4^2+3*J2^2*J4^3)*J6^2+(J2^11+J4*J2^9+3*J4^4*J2^3)*
		J6+2*J4^5*J2^4+3*J4^4*J2^6+2*J4^2*J2^10)*x3^2*x2+(3*J10^2*J2^5+((4*J4*J2^2+2*
		J2^4)*J6^2+(3*J4*J2^5+3*J4^2*J2^3+J2^7)*J6+J4^2*J2^6+3*J2^4*J4^3+2*J4*J2^8+3*
		J2^10)*J10+(J2^3+J4*J2)*J6^4+(J4^2*J2^2+3*J2^6+3*J4*J2^4)*J6^3+(2*J4^2*J2^5+2*
		J4^3*J2^3+4*J4*J2^7+J2^9)*J6^2+(3*J4^2*J2^8+4*J4^3*J2^6+4*J4^4*J2^4)*J6+J2^15+
		3*J4*J2^13+3*J4^2*J2^11+J4^4*J2^7+2*J4^3*J2^9)*x3^3;
	end if;
    else
	
	L :=
	    (-3600*J6-160*J4*J2+
	    3*J2^3)*x1^2+
	    (6000*J6*J2+6400*J4^2-360*J4*J2^2+6*J2^4)*x1*x2+
	    (-1600000*J10+(-96000*J4-800*J2^2)*J6-400*J4*J2^3+6400*J4^2*J2+6*J2^5)*x1*x3+
	    (-800000*J10+(-48000*J4-400*J2^2)*J6-200*J4*J2^3+3200*J4^2*J2+3*J2^5)*x2^2+
	    (360000*J6^2+(-8000*J4*J2+2400*J2^3)*J6+10000*J4^2*J2^2-
	    440*J4*J2^4+6*J2^6-64000*J4^3)*x2*x3+
	    ((-600000*J2^2+8000000*J4)*J10-150000*J6^2*J2+(300*J2^4-38000*J4*J2^2+320000*J4^2)*J6+
	    3*J2^7-240*J4*J2^5+6100*J4^2*J2^3-48000*J4^3*J2)*x3^2;

	M :=
	    (-3200000*J10+(-288000*J4+600*J2^2)*J6-100*J4*J2^3+3200*J4^2*J2+J2^5)*x1^3+
	    (4000000*J10*J2+2160000*J6^2+(-1600*J2^3+432000*J4*J2)*J6-128000*J4^3-
	    320*J4*J2^4+3*J2^6+10400*J4^2*J2^2)*x1^2*x2+
	    ((32000000*J4-2400000*J2^2)*J10-160000*J4^3*J2+13000*J4^2*J2^3-2700000*J6^2*J2-
	    180000*J6*J4*J2^2-340*J4*J2^5+3*J2^7)*x1^2*x3+
	    ((32000000*J4-2400000*J2^2)*J10-160000*J4^3*J2+13000*J4^2*J2^3-2700000*J6^2*J2-
	    180000*J6*J4*J2^2-340*J4*J2^5+3*J2^7)*x1*x2^2+
	    ((16000000*J4*J2+1200000*J2^3+960000000*J6)*J10+(43200000*J4+3060000*J2^2)*J6^2+
	    (-1800*J2^5+260000*J4*J2^3-960000*J4^2*J2)*J6+2560000*J4^4-496000*J4^3*J2^2+
	    29800*J4^2*J2^4+6*J2^8-720*J4*J2^6)*x1*x2*x3+
	    ((-800000*J2^4-200000000*J6*J2-320000000*J4^2+28000000*J4*J2^2)*J10-108000000*J6^3+
	    (-5400000*J4*J2-1405000*J2^3)*J6^2+(-880000*J4^2*J2^2-3000*J4*J2^4-550*J2^6+
	    6400000*J4^3)*J6+17350*J4^2*J2^5-380*J4*J2^7+3*J2^9+
	    2240000*J4^4*J2-334000*J4^3*J2^3)*x1*x3^2+
	    ((-8000000*J4*J2+400000*J2^3-80000000*J6)*J10+(-7200000*J4+1140000*J2^2)*J6^2+
	    (2200*J2^5-100000*J4*J2^3+1760000*J4^2*J2)*J6+1280000*J4^4-136000*J4^3*J2^2+
	    5800*J4^2*J2^4+J2^8-120*J4*J2^6)*x2^3+
	    ((-1400000*J2^4-800000000*J6*J2-960000000*J4^2+64000000*J4*J2^2)*J10+54000000*J6^3+
	    (-37800000*J4*J2-760000*J2^3)*J6^2+(7700000*J4^2*J2^2-318000*J4*J2^4+3200*J2^6-
	    60800000*J4^3)*J6+18600*J4^2*J2^5-380*J4*J2^7+3*J2^9+3520000*J4^4*J2-
	    414000*J4^3*J2^3)*x3*x2^2+
	    (160000000000*J10^2+((20000000000*J4+100000000*J2^2)*J6+70000000*J4*J2^3-
	    1200000000*J4^2*J2-900000*J2^5)*J10+(648000000*J4^2-7200000*J4*J2^2+
	    895000*J2^4)*J6^2+(6480000*J4^2*J2^3-129000*J4*J2^5+1050*J2^7-94400000*J4^3*J2)*J6-
	    12800000*J4^5+4880000*J4^4*J2^2-480000*J4^3*J2^4+20350*J4^2*J2^6-
	    400*J4*J2^8+3*J2^10)*x3^2*x2+
	    ((3200000000*J4^3-20000000000*J6^2+24000000*J4*J2^4-350000*J2^6-100000000*J6*J2^3-
	    520000000*J4^2*J2^2)*J10+(19500000*J2^2-1260000000*J4)*J6^3+(-80000*J2^5-
	    10250000*J4*J2^3+122000000*J4^2*J2)*J6^2+(-29000000*J4^3*J2^2+1325000*J4^2*J2^4+
	    50*J2^8+224000000*J4^4-23500*J4*J2^6)*J6+J2^11+2300000*J4^4*J2^3-
	    193500*J4^3*J2^5+7550*J4^2*J2^7-9600000*J4^5*J2-140*J4*J2^9)*x3^3;
    end if;
	
    xi, eta := MestreFindPointOnConic(L);
    P3 := PolynomialRing(Parent(xi), 3); x1 := P3.1; x2 := P3.2; x3 := P3.3;
    pol := Evaluate(L,[xi + x2*x1, eta + x1,1]);
    a := Coefficient(pol,x1,2);
    b := Coefficient(pol,x1,1);
    f := UnivariatePolynomial(Evaluate(M,[xi*a-x2*b,a*eta-b,a]));
    return HyperellipticCurve(f);
end function;

/*
   y^2 = x^6 - 1 in char <> 3, 5,
   see [CaNa2007].
*/
G2ModelsInFF_2D12 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    
    H0 := HyperellipticCurve(x^6 - 1);
    if geometric then return [H0]; end if;

    twists := [H0, QuadraticTwist(H0)];

    q := #FF;
    prim := PrimitiveElement(FF);
    t := prim;
    H := HyperellipticCurve(x^6 - t^3);
    twists cat:= [H,  QuadraticTwist(H)];

    t := prim;
    H := HyperellipticCurve(x*(t*x^2+3)*(3*t*x^2+1));
    twists cat:= [H,  QuadraticTwist(H)];
    
    Fq4 := GF(q^4); t := PrimitiveElement(Fq4);
    a := t^((q^2+1) div 2); b := a^q; c := -b; d := a;
    Ctwist := (Transformation(ChangeRing(H0,Fq4),[a,b,c,d]));
    pol := HyperellipticPolynomials(Ctwist);
    H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
    twists cat:= [H,  QuadraticTwist(H)];

    if IsSquare(FF!-3) then

	t := prim;
	H := HyperellipticCurve(x^6 - t^2);
	twists cat:= [H,  QuadraticTwist(H)];

	t := prim;
	H := HyperellipticCurve(x^6 - t);
	twists cat:= [H,  QuadraticTwist(H)];

    else

	Fq6 := GF(q^6); t := PrimitiveElement(Fq6);
	a := t^((q^4+q^2+1) div 3); b := a^4; c := a^q*t^((q^6-1) div 3); d := b^q*t^(((q^6-1) div 3));
	Fq6Pol := PolynomialRing(Fq6); X := Fq6Pol.1;
        pol := (a*X+b)^6-(c*X+d)^6;
        H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];

	Fq12 := GF(q^12); t := PrimitiveElement(Fq12);
	a := t^(((q^4+q^2+1)*(q^6+1)) div 6); b := a^7;
	c := a^q*t^((q^12-1) div 6); d := b^q*t^(((q^12-1) div 6)); 
	Fq12Pol := PolynomialRing(Fq12); X := Fq12Pol.1;
        pol := (a*X+b)^6-(c*X+d)^6;
        H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];
    end if;

    return G2NonIsomorphic(twists);
end function;

/*
   y^2 = x^5 - x in char 5,
   see [CaNa2007].
 */
G2ModelsInChar5FF_G240 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    deg := Degree(FF);
    
    H0 := HyperellipticCurve(x^5 - x);
    twists := [H0];
    if geometric then return twists; end if;

    prim := PrimitiveElement(FF);
    t := TraceOneElement(FF);
    H := HyperellipticCurve(x^5-x-t);
    twists cat:= [H,  QuadraticTwist(H)];

    ok := false;
    while not ok do
	t := Random(FF);
	pol := x^6+t*x^5+(1-t)*x+2;
	ok := IsIrreducible(pol);
    end while;
    H1 := HyperellipticCurve(pol);
    twists cat:= [H1];

    if (deg mod 2) eq 1 then

	twists cat:= [HyperellipticCurve(x^5 - 2*x)];
	twists cat:= [HyperellipticCurve(x^5 - 4*x)];
	twists cat:= [HyperellipticCurve((x^2+2)*(x^2+4*x+2)*(x^2-4*x+2))];

	ok := false;
	while not ok do
	    t := Random(FF);
	    p1 := x^3-t*x^2+(t-3)*x+1;
	    ok := IsIrreducible(p1);
	end while;
	t := (3+2*t)/(3+3*t);
	p2 := x^3-t*x^2+(t-3)*x+1;
	twists cat:= [HyperellipticCurve(p1*p2)];

	return twists;
    end if;

    twists cat:= [QuadraticTwist(H0)];
    twists cat:= [QuadraticTwist(H1)];
    twists cat:= [HyperellipticCurve(x^5-prim^2*x)];

    H := HyperellipticCurve(x^5-prim*x);
    twists cat:= [H,  QuadraticTwist(H)];

    t := prim;
    H := HyperellipticCurve((x^2-t)*(x^4+6*t*x^2+t^2));
    twists cat:= [H];

    sq := Roots(x^2-3)[1][1];
    H := HyperellipticCurve((x^3-prim)*(x^3-(15*sq-26)*prim));
    twists cat:= [H,  QuadraticTwist(H)];

    return twists;
end function;

forward G2ModelsInFF_G48;

/*
   y^2 = x^5 - x in char <> 5,
   see [CaNa2007].
*/
G2ModelsInFF_G48 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;

    H0 := HyperellipticCurve(x^5 - x);
    if geometric then return [H0]; end if;

    twists := [H0, QuadraticTwist(H0)];

    q := #FF;
    prim := PrimitiveElement(FF);
    ret, sqr := IsSquare(FF!-1);
    if ret then

	t := prim;
	H := HyperellipticCurve(x^5 -t*x);
	twists cat:= [H,  QuadraticTwist(H)];

	t := prim;
	H := HyperellipticCurve(x^5 -t^2*x);
	twists cat:= [H,  QuadraticTwist(H)];

	Fq8 := GF(q^8); t := PrimitiveElement(Fq8);
	a := t^((q^2+1)*(q^4+1) div 4); i := a^(q^2-1);
	b := a^5; c := a^q/i; d := b^q/i;
	Fq8Pol := PolynomialRing(Fq8); X := Fq8Pol.1;
	pol := (a*X+b)^5*(c*X+d)-(a*X+b)*(c*X+d)^5;
	H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];

	ok := false;
	while not ok do
	    t := Random(FF);
	    p1 := x^3-t*x^2+(t-3)*x+1;
	    ok := IsIrreducible(p1);
	end while;
	t := FF!((18+(5*sqr-3)*t)/((5*sqr+3)-2*t));
	p2 := x^3-t*x^2+(t-3)*x+1;
	H := HyperellipticCurve(p1*p2);
	twists cat:= [H,  QuadraticTwist(H)];

    else
	
	H := HyperellipticCurve(x^5 + x);
	twists cat:= [H,  QuadraticTwist(H)];
	
	Fq4 := GF(q^4); t := PrimitiveElement(Fq4);
	a := t^((q^2+1) div 2); b := a^q; c := -b; d := a;
	Ctwist := (Transformation(ChangeRing(H0,Fq4),[a,b,c,d]));
	pol := HyperellipticPolynomials(Ctwist);
	H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];
	
	Fq8 := GF(q^8); t := PrimitiveElement(Fq8);
	a := t^((q^2+1)*(q^4+1) div 4); i := -a^(q^2-1);
	b := a^5; c := a^q/i; d := b^q/i;
	Fq8Pol := PolynomialRing(Fq8); X := Fq8Pol.1;
	pol := (a*X+b)^5*(c*X+d)-(a*X+b)*(c*X+d)^5;
	H := HyperellipticCurve(Parent(x)!(pol/Coefficient(pol, Degree(pol))));
	twists cat:= [H,  QuadraticTwist(H)];

	repeat
	    repeat
		t := Random(FF);
		ret, s := IsSquare(-2-t^2);
	    until ret;
	    pol := x^6-(t+3)*x^5+5*(2+t-s)/2*x^4+5*(s-1)*x^3+5*(2-t-s)/2*x^2+(t-3)*x+1;
	    ok := IsIrreducible(pol);
	until ok;
	H := HyperellipticCurve(pol);
	twists cat:= [H,  QuadraticTwist(H)];
   end if;

   return G2NonIsomorphic(twists);
end function;

/*
   y^2 = x^5 - 1,
   see [CaNa2007].
*/
G2ModelsInFF_C10 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    
    H1 := HyperellipticCurve(x^5 - 1);
    if geometric then return [H1]; end if;

    prim := PrimitiveElement(FF);
    H2 := QuadraticTwist(H1);
    twists :=  [H1, H2];
    if (GF(5)!Characteristic(FF))^Degree(FF) ne 1 then
	return twists;
    end if;

    A := Setseq(Seqset([prim^i : i in [0..4]]));
    for a in A do
	H1 := HyperellipticCurve(a*x^5-1);
	H2 := QuadraticTwist(H1);
	twists cat:=  [H1, H2];
    end for;

    return G2NonIsomorphic(twists);
    
end function;

/* y^2 = 1/t*x^6+x^4+x^2+1 in char 3, and its twists */
G2ModelsInChar3FF_D12 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    J2, J4, J6, _, J10 := Explode(G2ToIgusaInvariants(GI));

    _, t := IsPower(-J2^3/J6, 3);

    H0 := HyperellipticCurve(x^6+t*x^4+(t-1)*x^3+t*x^2+1);
    if geometric then return [H0]; end if;
    
    twists := [H0, QuadraticTwist(H0)];

    q := #FF; Fq2 := GF(q^2);
    a := PrimitiveElement(Fq2); b := a^q; c := b; d := a;
    Ctwist := (Transformation(ChangeRing(H0,Fq2),[a,b,c,d]));
    H := HyperellipticCurve(Parent(x)!(HyperellipticPolynomials(Ctwist)));
    twists cat:= [H,  QuadraticTwist(H)];

    ok := false;
    while not ok do
	a0 := Random(FF);
	a1 := Random(FF);
	pol := x^3 + a1*x + a0;
	ok := IsIrreducible(pol);
    end while;
    Fq3 := ext<FF | pol>;
    a := Fq3.1; b:=-a^q-a; c:=a^q; d:=-c^q-c;
    Ctwist:=(Transformation(ChangeRing(H0,Fq3),[a,b,c,d]));
    H := HyperellipticCurve(Parent(x)!(HyperellipticPolynomials(Ctwist)));
    twists cat:= [H,  QuadraticTwist(H)];

    return twists;
end function;

/*
   y^2 = x^6 + x^3 + t in char <> 3,
   see [CaNa2007].
*/
G2ModelsInFF_D12 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    p := Characteristic(FF);
    
    J2, J4, J6, _, J10 := Explode(G2ToIgusaInvariants(GI));
    if p eq 5 then
	a := -1-J4/J2^2;
    else
	C2, C4, C6, C10 := Explode(
	    IgusaClebschToClebsch([8*J2,4*J2^2-96*J4,8*J2^3-160*J2*J4-576*J6, 4096*J10]));
	a := (3*C4*C6-C10)/50/C10;
    end if;

    H := HyperellipticCurve(x^6+x^3+a);
    twists := [H];
    if geometric then return twists; end if;

    n := Degree(FF);    
    prim := PrimitiveElement(FF);
    q := #FF;
    
    if q mod 3 eq 2 then

	if IsSquare(a) then
	    twists cat:= [QuadraticTwist(H)];
	end if;

	A := Roots(x^3-a)[1][1];
	ok := false;
	while not ok do
	    t := Random(FF);
	    delta := t^2-4/A;
	    ok := not IsSquare(delta);
	end while;
	/* To be improved, but ok. */
	Fq2 := GF(q^2); Pq2 := PolynomialRing(Fq2); X := Pq2.1;
	sq := Sqrt(Fq2!delta);
	theta1 := (t+sq)/2;
	theta2 := (t-sq)/2;
	f := Parent(x)!((X-theta1)^6/theta1^3-(X^2-t*X+1/A)^3+a*theta1^3*(X-theta2)^6);
	H := HyperellipticCurve(f);
	twists cat:= [H];
	if IsSquare(a) then
	    twists cat:= [QuadraticTwist(H)];
	end if;
	
	ok := false;
	while not ok do
	    t := Random(FF);
	    delta := t^2-4*a;
	    if not IsSquare(delta) then
		sq := Sqrt(Fq2!delta);
		theta := (t+sq)/2;
		ok := IsIrreducible(X^3-theta);
	    end if;
	end while;
	/* To be improved, but ok. */
	eta :=  Roots(X^2+X+1)[1][1];
	f := Parent(x)!((X-eta)^6*theta-(X^2+X+1)^3+a*(X-eta^2)^6/theta);
	H := HyperellipticCurve(f);
	twists cat:= [H, QuadraticTwist(H)];
	
	return twists;
    end if;

    if IsPower(a, 3) then
	if IsSquare(a) then
	    twists cat:= [QuadraticTwist(H)];
	end if;
    else
	twists cat:= [QuadraticTwist(H)];
    end if;
    
    if not IsPower(a, 3) then
	t := a;
    else
	t :=  prim;
    end if;
    
    H := HyperellipticCurve(x^6 + t * x^3 + a * t^2);
    twists cat:= [H];
    if IsPower(a, 3) then
	twists cat:= [QuadraticTwist(H)];
    else
	if IsSquare(a) then
	    twists cat:= [QuadraticTwist(H)];
	end if;
    end if;
    
    if IsPower(a, 3) then
	A := Roots(x^3-a)[1][1];
	ok := false;
	while not ok do
	    t := Random(FF);
	    delta := t^2-4/A;
	    ok := not IsSquare(delta);
	end while;
	/* To be improved, but ok. */
	Fq2 := GF(q^2); Pq2 := PolynomialRing(Fq2); X := Pq2.1;
	sq := Sqrt(Fq2!delta);
	theta1 := (t+sq)/2;
	theta2 := (t-sq)/2;
	f := Parent(x)!((X-theta1)^6/theta1^3-(X^2-t*X+1/A)^3+a*theta1^3*(X-theta2)^6);
	H := HyperellipticCurve(f);
	twists cat:= [H];
    else
	ok := false;
	while not ok do
	    t := Random(FF);
	    delta := t^2-4/a;
	    ok := not IsSquare(delta);
	end while;
	/* To be improved, but ok. */
	Fq2 := GF(q^2); Pq2 := PolynomialRing(Fq2); X := Pq2.1;
	sq := Sqrt(Fq2!delta);
	theta1 := (t+sq)/2;
	theta2 := (t-sq)/2;
	f := Parent(x)!((X-theta1)^6/theta1-(X^2-t*X+1/a)^3+a*theta1*(X-theta2)^6);
	H := HyperellipticCurve(f);
	twists cat:= [H];
    end if;
	
    if IsSquare(a) then
	twists cat:= [QuadraticTwist(H)];
    end if;

    return twists;

end function;

/*
   y^2 = x^5 + x^3 + t*x,
   see [CaNa2007].
*/
G2ModelsInFF_D8 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    p := Characteristic(FF);
    
    J2, J4, J6, _, J10 := Explode(G2ToIgusaInvariants(GI));

    if p eq 3 then
	t := -J2^2/J4;
    elif p eq 5 then
	t:= 1+J4/J2^2;
    else
	C2, C4, C6, C10 := Explode(
	    IgusaClebschToClebsch([8*J2, 4*J2^2-96*J4,8*J2^3-160*J2*J4-576*J6, 4096*J10]));
	t := (8*C6*(6*C4-C2^2)+9*C10)/900/C10;
    end if;
    
    if geometric then return [HyperellipticCurve(x^5+x^3+t*x)]; end if;

    if IsSquare(t) then
	/* 1-z0^2*t = s0^2*t*v */
	
	/* v a square */
	v := 1;  z0 := 1/Sqrt(t); s0 := 0;

	Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	    v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));

	prim := PrimitiveElement(FF);
	Cpt:=QuadraticTwist(Cp);
	twists := [Cp, Cpt];

	ok := false;
	while not ok do
	    v := Random(FF);
	    if v eq 0 or not IsSquare(v) then continue; end if;
	    z0 := Random(FF);
	    if z0^2*t eq 1 or not IsSquare(1-z0^2*t) then continue; end if;
	    if IsSquare((1-z0*Sqrt(t))/2) then continue; end if;
	    ok := true;
	end while;
	s0 := Sqrt((1-z0^2*t)/v/t);

	Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	    v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));
	twists cat:= [Cp];

	/* v not a square */
	v := prim; s0 := 0; z0 := 1/Sqrt(t);

	Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	    v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));
	Cm:=HyperellipticCurve((1-2*t*z0)*x^6+(8*s0*t*v)*x^5+v*(3+10*t*z0)*x^4+
	    v^2*(3+10*t*z0)*x^2-8*s0*t*v^3*x+v^3*(1-2*t*z0));
	twists cat:= [Cp, Cm];

	return twists;
    end if;

    /* 1-z0^2*t = s0^2*t*v (To be improved) */
    AS:=AffineSpace(FF,2); s := AS.1; z := AS.2;
    v := 1; 
    Q:=Curve(AS, s^2*t*v+z^2*t-1);
    pt:=Random(Points(Q));
    s0:=pt[1];z0:=pt[2];

    Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));

    prim := PrimitiveElement(FF);

    Cpt:=QuadraticTwist(Cp);
    twists := [Cp, Cpt];

    v := prim;
    Q:=Curve(AS, s^2*t*v+z^2*t-1);
    pt:=Random(Points(Q));
    s0:=pt[1];z0:=pt[2];

    Cp:=HyperellipticCurve((1+2*t*z0)*x^6-(8*s0*t*v)*x^5+v*(3-10*t*z0)*x^4+
	v^2*(3-10*t*z0)*x^2+8*s0*t*v^3*x+v^3*(1+2*t*z0));
    twists cat:= [Cp];

    return twists;
end function;


/* V4 case,
   see [ShVo2004], [CaQu2005] */
G2ModelsInFF_V4 := function(GI : geometric := false)

    FF := Universe(GI);

    x := PolynomialRing(FF).1;
    J2, J4, J6, _, J10 := Explode(G2ToIgusaInvariants(GI));

    Au:=J2^5*J4^2-64*J2^3*J4^3+1024*J2*J4^4+3*J2^6*J6-202*J2^4*J4*J6+4014*J2^2*J4^2*J6
	-20160*J4^3*J6+666*J2^3*J6^2-20520*J2*J4*J6^2+48600*J6^3-30*J2^4*J10+2800*J2^2*J4*J10
	-192000*J4^2*J10-360000*J2*J6*J10;

    Bu:=2*J2^4*J4*J6-114*J2^2*J4^2*J6+1344*J4^3*J6+6*J2^3*J6^2+216*J2*J4*J6^2-3240*J6^3+
	18*J2^4*J10-1040*J2^2*J4*J10+12800*J4^2*J10+4800*J2*J6*J10;

    Av:=J2^6*J4^2-96*J2^4*J4^3+3072*J2^2*J4^4-32768*J4^5+3*J2^7*J6-164*J2^5*J4*J6
	+1250*J2^3*J4^2*J6+29760*J2*J4^3*J6+858*J2^4*J6^2-22680*J2^2*J4*J6^2
	-172800*J4^2*J6^2+81000*J2*J6^3+1176*J2^5*J10-79600*J2^3*J4*J10
	+1344000*J2*J4^2*J10-72000*J2^2*J6*J10-12960000*J4*J6*J10-134400000*J10^2;

    Bv:=3*J2^3*J4^2*J6-160*J2*J4^3*J6+J2^4*J6^2-36*J2^2*J4*J6^2+3456*J4^2*J6^2-1188*J2*J6^3
	+24*J2^3*J4*J10-1280*J2*J4^2*J10+160*J2^2*J6*J10+105600*J4*J6*J10+640000*J10^2;

    u:=Au/Bu;v:=Av/Bv;
    if u ne 0 then
	t:=v^2-4*u^3;
	a0:=v^2+u^2*v-2*u^3;
	a1:=2*(u^2+3*v)*(v^2-4*u^3);
	a2:=(15*v^2-u^2*v-30*u^3)*(v^2-4*u^3);
	a3:=4*(5*v-u^2)*(v^2-4*u^3)^2;
    else
	t:=FF!1;
	a0:=1+2*v;
	a1:=2*(3-4*v);
	a2:=15+14*v;
	a3:=4*(5-4*v);
    end if;
    
    H1 := HyperellipticCurve(a0*x^6+a1*x^5+a2*x^4+a3*x^3+t*a2*x^2+t^2*a1*x+t^3*a0);
    if geometric then return [H1]; end if;

    q := #FF;
    
    if IsSquare(t) then 
	Fq2 := GF(q^2);
	a:=PrimitiveElement(Fq2);
	b:=a^q*Sqrt(t);c:=a^q;d:=a*Sqrt(t);
	C2:=ChangeRing(H1,Fq2);
	Ctwist:=(Transformation(C2,[a,b,c,d]));
	f2:=Parent(x)!(HyperellipticPolynomials(Ctwist));
	H2:=HyperellipticCurve(f2);
	return [H1, QuadraticTwist(H1),
	        H2, QuadraticTwist(H2)];
    end if;
    
    Fq4 := GF(q^4);
    s:=PrimitiveElement(Fq4);
    a := s^((q^2+1) div 2);
    sq := Sqrt(Fq4!t);
    c := a^q;
    b := sq*c;
    d := sq*c^q;
    C2:=ChangeRing(H1,Fq4);
    Ctwist:=(Transformation(C2,[a,b,c,d]));
    f2:=Parent(x)!(HyperellipticPolynomials(Ctwist));
    H2:=HyperellipticCurve(f2);
    return [H1, H2];
    
end function;

/*
   Generic case.

   Everything here is based on [Mestre91], especially the conic and
   cubic used in finite fields of characteristic 3 or > 5.
  
   In characteristic 5, we had to face difficulties, mostly because
   the covariants used to define the cubics and conics given
   in [Mestre91] are no more a basis, and we had to consider other covariants.
   This yields new conics and cubics that we use here.
  
 */
G2ModelsInFF_C2 := function(GI : geometric := false)

    FF := Universe(GI);
    x := PolynomialRing(FF).1;
    p := Characteristic(FF);;
    J2, J4, J6, _, J10 := Explode(G2ToIgusaInvariants(GI));
    _, _, g3 := Explode(GI);

    if p eq 5 and J2 eq 0 and J4 eq 0 then
	repeat
	    c := Random(FF);
	    ret, a := IsPower(3*c^2/g3, 3);
	until c ne 0 and ret;
	H := HyperellipticCurve(x^5+c*x^2+a*c);
    else
	H := ClebschMestreConicAndCubic(GI);
    end if;
    if geometric then return [H]; end if;

    return [H, QuadraticTwist(H)];
end function;

/* Switching routine
 *******************/
G2Models := function(GI : geometric := false, models := true)

    FF := Universe(GI);
    g1, g2, g3 := Explode(GI);
    p := Characteristic(FF);
    twists := [];

    if p eq 2 then
	if   g1 ne g2*g3                               then
	    if models then
		twists := G2ModelsInChar2FF_C2(GI : geometric := geometric);
	    end if;
	    aut := CyclicGroup(2);
	elif g1 eq 0     and g2 ne 0    and g3 eq 0    then
	    if models then
		twists := G2ModelsInChar2FF_C2bis(GI : geometric := geometric);
	    end if;
	    aut := CyclicGroup(2);
	elif g1 eq g2*g3 and g1 ne 0    and g2 ne g3^2 then
	    if models then
		twists := G2ModelsInChar2FF_C2xC2(GI : geometric := geometric);
	    end if;
	    aut := DirectProduct(CyclicGroup(2), CyclicGroup(2));
	elif g1 eq g3^3  and g2 eq g3^2 and g3 ne 0    then
	    if models then
		twists := G2ModelsInChar2FF_C2xS3(GI : geometric := geometric);
	    end if;
	    aut := DirectProduct(SymmetricGroup(3), CyclicGroup(2));
	elif g1 eq 0     and g2 eq 0    and g3 ne 0    then
	    if models then
		if models then
		    twists := G2ModelsInChar2FF_M32(GI : geometric := geometric);
		end if;
	    end if;
	    aut := DirectProduct([CyclicGroup(2): i in [1..5]]);
	else
	    if models then
		twists := G2ModelsInChar2FF_M160(GI : geometric := geometric);
	    end if;
	    aut := DirectProduct(CyclicGroup(2),
		sub<SymmetricGroup(16)|[1,16,14,3,10,7,5,12,2,15,13,4,9,8,6,11],
		[9,10,11,12,13,14,15,16,1,2,3,4,5,6,7,8]>);
	end if;
	return twists, aut;
    end if;

    /* y^2 = x^6-1 */
    if p ne 3 and p ne 5 and GI eq [ FF!6400000/3, FF!440000/9, FF!-32000/81 ] then
	if models then
	    twists := G2ModelsInFF_2D12(GI : geometric := geometric);
	end if;
	return twists,
	    sub<SymmetricGroup(12)|[1,3,2,4,6,5,10,12,11,7,9,8],
	                                   [9,8,7,12,11,10,6,5,4,3,2,1]>;
    end if;

    /* y^2 = x^5-x */
   if GI eq [ 50000, 3750, -125 ] then
       if p eq 5 then
	   if models then
	       twists := G2ModelsInChar5FF_G240(GI : geometric := geometric);
	   end if;
	   return twists, SmallGroup(240,90);
       end if;
       if models then
	   twists := G2ModelsInFF_G48(GI : geometric := geometric);
       end if;
       return twists, sub<SymmetricGroup(8)|[2,1,3,4,7,8,5,6],[3,4,5,6,1,2,7,8]>;
    end if;

    /* y^2 = x^5-1, p <> 5 */
    if GI eq [ 0, 0, 0 ] then
	if models then
	    twists := G2ModelsInFF_C10(GI : geometric := geometric);
	end if;
       return twists, CyclicGroup(10);
   end if;

   J2, J4, J6, _, J10 := Explode(G2ToIgusaInvariants(GI));

   if p eq 3 then
       /* y^2 = 1/t*x^6+x^4+x^2+1 */
       if J4 eq 0 and J10 + 2*J6*J2^2 eq 0 then
	   if models then
	       twists := G2ModelsInChar3FF_D12(GI : geometric := geometric);
	   end if;
	   return twists, DihedralGroup(6);
       end if;
   elif p eq 5 then
       /* y^2 = x^6+x^3+t */
       if J10*J4*J2^2 + J6^3 + 3*J6*J4^3 + 2*J4^4*J2 eq 0 and
	   J10*J2^3 + 3*J6^2*J4 + 4*J4^4 + 2*J4^3*J2^2 eq 0 and
	   J6*J2 + 2*J4^2 eq 0 then
	   if models then
	       twists := G2ModelsInFF_D12(GI : geometric := geometric);
	   end if;
	   return twists, DihedralGroup(6);
       end if;
   else
       /* y^2 = x^6+x^3+t */
       if 750*J10+90*J6*J4-3*J6*J2^2-J4^2*J2 eq 0 and
	   2700*J6^2+540*J6*J4*J2-27*J6*J2^3+160*J4^3-9*J4^2*J2^2 eq 0 then
	   if models then
	       twists := G2ModelsInFF_D12(GI : geometric := geometric);
	   end if;
	   return twists, DihedralGroup(6);
       end if;
   end if;

   /* y^2 = x^5+x^3+t*x */
   if p ne 5 then
       if 172800*J6^2-23040*J6*J4*J2+592*J6*J2^3-40960*J4^3+3584*J4^2*J2^2-104*J4*J2^4+J2^6 eq 0
	   and 128000*J10+5760*J6*J4-192*J6*J2^2-1024*J4^2*J2+64*J4*J2^3-J2^5 eq 0 then
	   if models then
	       twists := G2ModelsInFF_D8(GI : geometric := geometric);
	   end if;
	   return twists, DihedralGroup(4);
       end if;
   else
       if [
	   J10*J4^5 + 4*J6^5 + 2*J6^3*J4^3 + 2*J4^6*J2^3 + 2*J4^4*J2^7 + 4*J4^3*J2^9 + 2*J2^15,
	   J10*J4^3*J2 + 2*J6^4 + 3*J6^2*J4^3 + 3*J4^6 + J4^5*J2^2 + 3*J4^4*J2^4 + 2*J4^3*J2^6 + J4^2*J2^8 + 2*J4*J2^10 + 3*J2^12,
	   J10*J4*J2^2 + J6^3 + 3*J4^4*J2 + 2*J4^2*J2^5 + 4*J4*J2^7 + 2*J2^9,
	   J10*J2^3 + 3*J6^2*J4 + 3*J4^4 + J4^2*J2^4 + 3*J2^8,
	   J6*J2 + 2*J4^2 + 3*J4*J2^2 + 3*J2^4
	   ]
	   eq [0,0,0,0,0] then
	   if models then
	       twists := G2ModelsInFF_D8(GI : geometric := geometric);
	   end if;
	   return twists, DihedralGroup(4);
       end if;
   end if;

    R := J2^6*J6^3 - 2*J2^5*J4^2*J6^2 - 72*J2^5*J4*J6*J10 - 432*J2^5*J10^2 + J2^4*J4^4*J6
	+ 8*J2^4*J4^3*J10 - 72*J2^4*J4*J6^3 - 48*J2^4*J6^2*J10 + 136*J2^3*J4^3*J6^2 
	+ 4816*J2^3*J4^2*J6*J10 + 28800*J2^3*J4*J10^2 + 216*J2^3*J6^4 - 
	64*J2^2*J4^5*J6 - 512*J2^2*J4^4*J10 + 1080*J2^2*J4^2*J6^3 - 
	12960*J2^2*J4*J6^2*J10 - 96000*J2^2*J6*J10^2 - 2304*J2*J4^4*J6^2 - 
	84480*J2*J4^3*J6*J10 - 512000*J2*J4^2*J10^2 - 7776*J2*J4*J6^4 - 
	129600*J2*J6^3*J10 + 1024*J4^6*J6 + 8192*J4^5*J10 + 6912*J4^3*J6^3 + 
	691200*J4^2*J6^2*J10 + 11520000*J4*J6*J10^2 + 11664*J6^5 + 51200000*J10^3;

    if R eq 0 then
	if models then
	    twists := G2ModelsInFF_V4(GI : geometric := geometric);
	end if;
	return twists, DirectProduct(CyclicGroup(2),CyclicGroup(2));
    end if;
    
    if models then
	twists := G2ModelsInFF_C2(GI : geometric := geometric);
    end if;
    return twists, CyclicGroup(2);

end function;

 /***
  * 
  * Cardona-Quer-Nart-Pujola invariants stuff
  * see [CaNaPu2005], [CaQu2005].
  *
  ********************************************************************/
intrinsic IgusaToG2Invariants(JI::SeqEnum) -> SeqEnum
    {Convert Igusa invariants to  Cardona-Quer-Nart-Pujolas absolute invariants.}

    require #JI eq 5 :
	"Argument must be a sequence of five Igusa J invariants.";    
    FF := Universe(JI);
    if FF cmpeq Integers() then
        JI := ChangeUniverse(JI,Rationals());
        FF := Rationals();
    end if;
    require ISA(Category(FF), Fld) : 
	"Argument must be defined over a field.";
    J2, J4, J6, J8, J10 := Explode(JI);

    /* Characteristic 2 fields */
    if Characteristic(FF) eq 2 then
	if J2 ne 0 then
	    return [Sqrt(J10/J2^5), Sqrt((J8/J2^4)-(J4/J2^2)^4-(J4/J2^2)^3), Sqrt(J4/J2^2)];
	end if;
	if J6 ne 0 then
	    return [0, Sqrt(J10^3/J6^5), Sqrt(Sqrt(Sqrt(J8*J10^4/J6^8)))];
	end if;	
	return [0, 0, Sqrt(Sqrt(Sqrt(J8^5/J10^4)))];
    end if;

    /* Other fields */
    if J2 ne 0 then
	return [J2^5/J10, J2^3*J4/J10, J2^2*J6/J10];
    end if;
    if J4 ne 0 then
	return [0, J4^5/J10^2, J4*J6/J10];
    end if;
    return [0, 0, J6^5/J10^3];

end intrinsic;

intrinsic G2ToIgusaInvariants(GI::SeqEnum) -> SeqEnum
    {Convert Igusa invariants to Cardona-Quer-Nart-Pujolas absolute invariants.}

    require #GI eq 3 :
	"Argument must be a sequence of three absolute invariants.";
    FF := Universe(GI);
    if FF cmpeq Integers() then
        GI := ChangeUniverse(GI,Rationals());
        FF := Rationals();
    end if;
    require ISA(Category(FF), Fld) : 
	"Argument must be defined over a field.";
    g1, g2, g3 := Explode(GI);

    /* Characteristic 2 fields */
    if Characteristic(FF) eq 2 then
	if g1 ne 0 then
	    return [1, g3^2, g3^4, g2^2+g3^8+g3^6, g1^2];
	end if;
	if g2 ne 0 then
	    return [0, 0, g2^2, g3^8, g2^4];
 	end if;
	if g3 ne 0 then
	    return [ 0, 0, 0, g3^4, g3^3];
	end if;
	return [ 0, 0, 0, 0, FF!1];
    end if;

    /* Other fields */
    if g1 ne 0 then
	return [g1, g1*g2, g1^2*g3, (g1^3*g3-g1^2*g2^2)/4, g1^4];
    end if;
    if g2 ne 0 then
	return [0, g2, g2*g3, -g2^2/4, g2^2];
    end if;
    if g3 ne 0 then
	return [0, 0, g3^2, 0, g3^3];
    end if;
    return [0, 0, 0, 0, FF!1];

end intrinsic;

intrinsic G2Invariants(H::CrvHyp) -> SeqEnum
    {Compute Cardona-Quer-Nart-Pujolas absolute invariants of a genus 2 curve.}

    require Genus(H) eq 2 :
	"Curve must be of genus 2.";

    return(IgusaToG2Invariants(IgusaInvariants(H)));

end intrinsic;

intrinsic HyperellipticCurveFromG2Invariants(GI::SeqEnum) -> CrvHyp, GrpPerm
    {Compute a hyperelliptic curve and its automorphism group from given
    Cardona-Quer-Nart-Pujolas absolute invariants.}

    require #GI eq 3 :
	"Argument must be a sequence of three absolute invariants.";
    if Universe(GI) cmpeq Integers() then
        GI := ChangeUniverse(GI,Rationals());
    end if;

    twists, aut := G2Models(GI : geometric := true);
    return twists[1], aut;
    
end intrinsic;

 /***
  * Twists
  *
  ********************************************************************/
intrinsic Twists(GI::SeqEnum[FldFinElt]) -> SeqEnum[CrvHyp], GrpPerm
    {Compute twisted  hyperelliptic curves and their automorphism group from
    given Cardona-Quer-Nart-Pujolas absolute invariants.}
    
    require #GI eq 3 :
	"Argument must be a sequence of three absolute invariants.";

    require Type(Universe(GI)) eq FldFin :
	"Twist computations only available in finite fields";
    
    twists, aut := G2Models(GI);
    return twists, aut;
    
end intrinsic;

intrinsic Twists(H::CrvHyp) -> SeqEnum[CrvHyp], GrpPerm
    {Compute all twists of a genus 2 or 3 hyperelliptic curve H over a finite field and also
     its abstract automorphism group. For genus 3, the characteristic must be at least 11
     and H in the form y^2=f(x). }


    require Type(CoefficientRing(H)) eq FldFin :
	"Twist computations only available in finite fields";

    g := Genus(H);
    require (g eq 2) or (g eq 3) :
	"Curve must be of genus 2 or 3.";

    if g eq 2 then   
      twists, aut := G2Models(G2Invariants(H));
    else //g = 3
       f, h := HyperellipticPolynomials(H);
       require (not (Characteristic(BaseRing(H)) in {2, 3, 5, 7})) and (h eq 0): 
        "For genus 3, the characteristic must be >=11 and the curve must be of form y^2 = f(x)";
       twists := HyperellipticPolynomialTwists(f, 8);
       twists := [HyperellipticCurve(f) : f in twists];
       _, aut := G3Models(ShiodaInvariants(H) : models := false);
    end if;
    return twists, aut;

end intrinsic;

 /***
  * Geometric Automorphism group
  *
  ********************************************************************/
intrinsic GeometricAutomorphismGroup(GI::SeqEnum) -> GrpPerm
    {Compute the automorphism group from
    given Cardona-Quer-Nart-Pujolas absolute invariants.}
    
    require #GI eq 3 :
	"Argument must be a sequence of three absolute invariants.";
    if Universe(GI) cmpeq Integers() then
        GI := ChangeUniverse(GI,Rationals());
    end if;
    
    _, aut := G2Models(GI : models := false);
    return aut;

end intrinsic;

intrinsic GeometricAutomorphismGroup(H::CrvHyp) -> GrpPerm
    {Compute the automorphism group of a hyperelliptic curve of genus 2 or 3.}

    g := Genus(H);    
    require (g eq 2) or (g eq 3) :
	"Curve must be of genus 2 or 3.";

    if g eq 2 then
      _, aut := G2Models(G2Invariants(H) : models := false);
    else //g=3
	require (not (Characteristic(BaseRing(H)) in {2, 3, 5, 7})): 
        "For genus 3, the characteristic must be 0 or >=11";
	_, aut := G3Models(ShiodaInvariants(H) : models := false);
    end if;
    return aut;

end intrinsic;

/* Geometric automorphism group classification
   see [Cardona2003] and [CaNaPu2005] */
intrinsic GeometricAutomorphismGroupGenus2Classification(FF::FldFin) -> SeqEnum, SeqEnum 
    {Give all possible automorphism groups of a genus 2 curve, and the
    corresponding number of curves (up to isomorphism and twists) with
    this group, defined over the finite field given in input.}

    p := Characteristic(FF); q := #FF;

    nbth_C2 := 0; nbth_C2xC2 := 0; nbth_C2xS3 := 0; nbth_M32 := 0;
    nbth_M160 := 0; nbth_2D12 := 0; nbth_G240 := 0; nbth_G48  := 0;
    nbth_C10  := 0; nbth_D12  := 0; nbth_D8   := 0; nbth_V4   := 0;
	
    if p eq 2 then
	nbth_C2    := q^3-q^2+q-1;
	nbth_C2xC2 := q^2-3*q+2;
	nbth_C2xS3 := q-1;
	nbth_M32   := q-1;
	nbth_M160  := 1; 
    end if;
    if p eq 3 then
	nbth_G48  := 1;
	nbth_C10  := 1;
	nbth_D12  := q-2;
	nbth_D8   := q-2;
	nbth_V4   := q^2-3*q+4;
	nbth_C2   := q^3-q^2+q-2;
    end if;
    if p eq 5 then
	nbth_G240 := 1;
	nbth_D12  := q-2;
	nbth_D8   := q-2;
	nbth_V4   := q^2-3*q+4;
	nbth_C2   := q^3-q^2+q-1;
    end if;
    if p ge 7 then
	nbth_2D12 := 1;
	nbth_G48  := 1;
	nbth_C10  := 1;
	nbth_D12  := q-3;
	nbth_D8   := q-3;
	nbth_V4   := q^2-3*q+5;
	nbth_C2   := q^3-q^2+q-2;
    end if;

    Grps := []; Nmbs := [];
    if nbth_C2 ne 0 then
	Grps cat:= [CyclicGroup(2)]; Nmbs cat:= [nbth_C2];
    end if;
    if nbth_C2xC2 ne 0 then
	Grps cat:= [DirectProduct(CyclicGroup(2),CyclicGroup(2))]; Nmbs cat:= [nbth_C2xC2];
    end if;
    if nbth_V4 ne 0 then
	Grps cat:= [DirectProduct(CyclicGroup(2),CyclicGroup(2))]; Nmbs cat:= [nbth_V4];
    end if;
    if nbth_C2xS3 ne 0 then
	Grps cat:= [DirectProduct(SymmetricGroup(3),CyclicGroup(2))]; Nmbs cat:= [nbth_C2xS3];
    end if;
    if nbth_D8 ne 0 then
	Grps cat:= [DihedralGroup(4)]; Nmbs cat:= [nbth_D8];
    end if;
    if nbth_C10 ne 0 then
	Grps cat:= [CyclicGroup(10)]; Nmbs cat:= [nbth_C10];
    end if;
    if nbth_D12 ne 0 then
	Grps cat:= [DihedralGroup(6)]; Nmbs cat:= [nbth_D12];
    end if;
    if nbth_2D12 ne 0 then
	Grps cat:= [sub<SymmetricGroup(12)|
	    [1,3,2,4,6,5,10,12,11,7,9,8],
	    [9,8,7,12,11,10,6,5,4,3,2,1]>]; Nmbs cat:= [nbth_2D12];
    end if;
    if nbth_M32 ne 0 then
	Grps cat:= [DirectProduct([CyclicGroup(2): i in [1..5]])]; Nmbs cat:= [nbth_M32];
    end if;
    if nbth_G48 ne 0 then
	Grps cat:= [sub<SymmetricGroup(8)|[2,1,3,4,7,8,5,6],[3,4,5,6,1,2,7,8]>]; Nmbs cat:= [nbth_G48];
    end if;
    if nbth_M160 ne 0 then
	Grps cat:= [DirectProduct( CyclicGroup(2),
	    sub<SymmetricGroup(16)|[1,16,14,3,10,7,5,12,2,15,13,4,9,8,6,11],
	    [9,10,11,12,13,14,15,16,1,2,3,4,5,6,7,8]>)]; Nmbs cat:= [nbth_M160];
    end if;
    if nbth_G240 ne 0 then
	Grps cat:= [SmallGroup(240,90)]; Nmbs cat:= [nbth_G240];
    end if;

    return Grps, Nmbs;

end intrinsic;
