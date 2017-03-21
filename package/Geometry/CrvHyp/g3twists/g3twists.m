freeze;

/***
 *  Genus 3 hyperelliptic curves and their invariants.
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
 *  Copyright 2011, R. Lercier & C. Ritzenthaler
 */

/***
 *
 * 
 * This library aims at reconstructing over perfect fields (at the moment of
 * characteristic 0 or greater than 7), models of genus 3 hyperelliptic curves
 * from invariants for binary forms of degree 8. Given a hyperelliptic curve, we
 * provide functions to compute the 9 weighted projective invariants introduced
 * by Shioda [Shioda1967], denoted J2, J3, ..., J10. And conversely, given Shioda
 * invariants, it is possible to obtain  models and the geometric automorphism
 * group.
 * 
 * Computing the twists of any genus 3 hyperelliptic curves defined over a finite
 * field, especially for curves with many automorphisms, is implemented too
 * 
 * Details about the algorithms implemented in this package can be found in
 * [LeRi2012].
 * 
 * Bibliography
 * 
 * [LeRi2012] "Hyperelliptic curves and their invariants: geometric, arithmetic
 * and algorithmic aspects", Journal of Algebra, Elsevier, 2012. To appear.
 * Available at http://dx.doi.org/10.1016/j.jalgebra.2012.07.054
 * 
 * [Maeda1990] "On the invariant fields of binary octavics", Takashi Maeda
 * Hiroshima Math. J., 20(1990), 619-632.
 * 
 * [MaShShVo2002] "The locus of curves with prescribed automorphism group",
 * K. Magaard, T. Shaska, S. Shpectorov and H. Volklein,
 * RIMS, Kyoto Technical Report series, Communications on Arithmetic
 * Fundamental Groups and Galois Theory, ed.: H. Nakamura, 112-141, 2002.
 * 
 * [Shioda1967] "On the Graded Ring of Invariants of Binary Octavics"
 * Tetsuji Shioda, American Journal of Mathematics, Vol. 89, No. 4 (Oct., 1967),
 * pp. 1022-1046
 * 
 *
 *********************************************************************/

 /***
 * Exported intrinsics.
 *
 * intrinsic ShiodaInvariants(f::RngUPolElt : normalize := false) -> SeqEnum, SeqEnum
 * intrinsic ShiodaInvariants(C::CrvHyp : normalize := false) -> SeqEnum, SeqEnum
 * intrinsic ShiodaAlgebraicInvariants(FreeJI::SeqEnum : ratsolve := true) -> SeqEnum
 * 
 * intrinsic ShiodaInvariantsEqual(V1::SeqEnum, V2::SeqEnum) -> BoolElt
 * 
 * intrinsic MaedaInvariants(f::RngUPolElt) -> SeqEnum
 * intrinsic MaedaInvariants(C::CrvHyp) -> SeqEnum
 * 
 * intrinsic DiscriminantFromShiodaInvariants(JI::SeqEnum) -> RngElt 
 * intrinsic HyperellipticCurveFromShiodaInvariants(JI::SeqEnum) -> CrvHyp, GrpPerm
 * intrinsic HyperellipticPolynomialFromShiodaInvariants(JI::SeqEnum) -> RngUPolElt, GrpPerm
 * 
 * intrinsic GeometricAutomorphismGroupFromShiodaInvariants(JI::SeqEnum) -> GrpPerm
 * intrinsic GeometricAutomorphismGroupFromGenus3HyperellipticPolynomial(f::RngUPolElt) -> GrpPerm
 * intrinsic GeometricAutomorphismGroupForGenus3HyperellipticCurve(H::CrvHyp) -> GrpPerm
 * 
 * intrinsic GeometricAutomorphismGroupClassificationForGenus3HyperellipticCurves(FF::FldFin) -> SeqEnum, SeqEnum
 * 
 ********************************************************************/
 
 /***
 * Changes.
 *
 * 2012-12-1,  Cosmetic changes - mch, Magma
 *
 * 2011-12-4,  v1.0 : R. Lercier, C. Ritzenthaler, 
 *             Twist computations added
 *
 * 2011-11-19, v0.1 : R. Lercier, C. Ritzenthaler, 
 *             IsDiagonal replaced by IsScalar in Glasby.
 *
 * 2011-11-17, v0.0 : R. Lercier, C. Ritzenthaler, 
 *             Initial version.
 *
 ********************************************************************/

import "sl2invtools.m"    : Transvectant;
import "g3d4.m"           : G3ModelsInCharFF_D4;
import "conic.m"          : Genus3ConicAndQuartic, Genus3ConicAndQuarticForC4;
import "hilbert90.m"      : MConj, MNorm, MActOnC, Glasby;

declare verbose G3Twists, 3;

 /***
  *
  * Shioda invariants, in fields of characteristic 0 or > 7,
  * see [Shioda1967].
  *
  ********************************************************************/
intrinsic ShiodaInvariants(f::RngUPolElt : normalize := false) -> SeqEnum, SeqEnum
    {Compute the Shioda invariants  'J2', 'J3', 'J4', 'J5', 'J6', 'J7',
    'J8', 'J9' and 'J10' of a polynomial of degree at most 8, considered as a
    binary form of degre 8 (see 1967 Shioda's  paper). Weights of these
    invariants are returned too.
    }

    require Degree(f) le 8: "Polynomial must have degree at most 8.";

    CR := CoefficientRing(Parent(f));
    require not Characteristic(CR) in {2, 3, 5, 7} : "2, 3, 5 and 7 must be invertible in the base ring.";
    
    f_cov := [* f, 1, 8 *];

    /*
     * Intermediary covariants */
    
    /* H = (f,f)_2 : order 2*d-4, degree 2 => (12, 2) */
    H_cov := Transvectant(f_cov, f_cov, 2);

    /* g = (f,f)_4 : order 2*d-8, degree 2 => (8, 2) */
    g_cov := Transvectant(f_cov, f_cov, 4);

    /* k = (f,f)_6 : order 2*d-12, degree 2 => (4, 2) */
    k_cov := Transvectant(f_cov, f_cov, 6);

    /* h := (k, k)_2 : order 4*d-28, degree 4 => (4, 4) */
    h_cov := Transvectant(k_cov, k_cov, 2);

    /* m := (f, k)_4 : order 3*d-20, degree 3 => (4, 3) */
    m_cov := Transvectant(f_cov, k_cov, 4);

    /* n := (f, h)_4 : order 5*d-36, degree 5 => (4, 5) */
    n_cov := Transvectant(f_cov, h_cov, 4);

    /* p := (g, k)_4 : order 4*d-28, degree 4 => (4, 4) */
    p_cov := Transvectant(g_cov, k_cov, 4);

    /* q := (g, h)_4 : order 6*d-44, degree 6 => (4, 6) */
    q_cov := Transvectant(g_cov, h_cov, 4);

     /*
      * Fundamental covariants */

    /* J2 = (f,f)_8 : order 2*d-16, degree 2  */
    J2 := Transvectant(f_cov, f_cov, 8);
     
    /* J3 = (f,g)_8 : order 3*d-24, degree 3  */
    J3 := Transvectant(f_cov, g_cov, 8);

    /* J4 = (k,k)_4 : order 4*d-32, degree 4  */
    J4 := Transvectant(k_cov, k_cov, 4);

    /* J5 = (m,k)_4 : order 5*d-40, degree 5  */
    J5 := Transvectant(m_cov, k_cov, 4);

    /* J6 = (k,h)_4 : order 6*d-48, degree 6  */
    J6 := Transvectant(k_cov, h_cov, 4);

    /* J7 = (m,h)_4 : order 7*d-56, degree 7  */
    J7 := Transvectant(m_cov, h_cov, 4);

    /* J8 = (p,h)_4 : order 8*d-64, degree 8  */
    J8 := Transvectant(p_cov, h_cov, 4);

    /* J9 = (n,h)_4 : order 9*d-72, degree 9  */
    J9 := Transvectant(n_cov, h_cov, 4);

    /* J10 = (q,h)_4 : order 10*d-80, degree 10  */
    J10 := Transvectant(q_cov, h_cov, 4);

      JI :=  [ Coefficient(J2[1], 0), Coefficient(J3[1], 0),
	  Coefficient(J4[1], 0), Coefficient(J5[1], 0), Coefficient(J6[1], 0),
	  Coefficient(J7[1], 0), Coefficient(J8[1], 0), Coefficient(J9[1], 0),
	  Coefficient(J10[1], 0)
	  ];

      if normalize eq false then return JI, [2, 3, 4, 5, 6, 7, 8, 9, 10]; end if;
      return WPSNormalize([2, 3, 4, 5, 6, 7, 8, 9, 10], JI), [2, 3, 4, 5, 6, 7, 8, 9, 10];

end intrinsic;

intrinsic ShiodaInvariants(fh::SeqEnum : normalize := false) -> SeqEnum, SeqEnum
    {Compute the Shioda invariants  'J2', 'J3', 'J4', 'J5', 'J6', 'J7', 'J8',
    'J9' and 'J10' of the hyperelliptic curve y^2 + h(x) * y = f(x) (see 1967 Shioda's
    paper). Weights of these invariants are returned too.
    }

    f, h := Explode(fh);
    K := CoefficientRing(Parent(f));
    
    require not Characteristic(K) in {2, 3, 5, 7} : "2, 3, 5 and 7 must be invertible in the base ring.";
    JI, Wght := ShiodaInvariants(f-(1/4)*h^2 : normalize := normalize);

    return JI, Wght;
    
end intrinsic;

intrinsic ShiodaInvariants(C::CrvHyp : normalize := false) -> SeqEnum, SeqEnum
    {Compute the Shioda invariants  'J2', 'J3', 'J4', 'J5', 'J6', 'J7', 'J8',
    'J9' and 'J10' of a genus 3 hyperelliptic curve (see 1967 Shioda's
    paper). Weights of these invariants are returned too.
    }
    
    require Genus(C) eq 3: "Curve must be of genus 3.";
    K := BaseField(C);
    R := PolynomialRing(K); x := R.1;
    
    require not Characteristic(K) in {2, 3, 5, 7} : "2, 3, 5 and 7 must be invertible in the base ring.";

    f, h := HyperellipticPolynomials(C);
    require (Degree(h) le 4) and (Degree(f) le 8): 
	"The curve must be of form y^2 + h(x) y = f(x), where f and h must have suitable degrees.";
    
    JI, Wght := ShiodaInvariants(f-(1/4)*h^2 : normalize := normalize);

    return JI, Wght;

end intrinsic;


intrinsic ShiodaInvariantsEqual(V1::SeqEnum, V2::SeqEnum) -> BoolElt
    {Check whether Shioda Invariants V1 en V2 of two genus 3 hyperelliptic curves or of
     two binary forms of degree 8 are equivalent.}

    require #V1 eq 9 and #V2 eq 9 : "V1, V2 must be of size 9 (J2, ..., J10)";

    return WPSEqual([2, 3, 4, 5, 6, 7, 8, 9, 10], V1, V2);
end intrinsic;


/*
  Coefficients of 5 syzygies R1, R2, R3, R4 and R5 of degrees 16, 17, 18, 19,
  and 20 between J8, J9 nd J10. See [Shioda1967].
*/
function ShiodaSyzygyes(J2, J3, J4, J5, J6, J7)

    A6  := (-2/27*J3^2+64/45*J6-8/45*J2*J4+1/405*J2^3);
    A7  := (1/30*J2*J5-2/5*J7+1/15*J3*J4);
    A8  := (-52/105*J4^2+2/15*J2*J6);
    A16 := 1/90*J3*J4^2*J5+1/36450*J2^4*J4^2-26/42525*J2^3*J4*J6-2/15*J5^2*J6-1/810*J2^2*J4^3-1/1215*J2*J3^2*J4^2+76/2835*J2*J4^2*J6+52/2835*J3^2*J4*J6-12/1225*J4^4+1/5*J4*J5*J7-1/30*J2*J7^2-2/15*J3*J6*J7+352/4725*J4*J6^2;
    
    B7  := (1/12*J3*J4-1/2*J7+1/24*J2*J5);
    B8  := (-1/12*J3*J5-8/135*J2*J6+1/540*J2^2*J4-1/9720*J2^4+2/105*J4^2+1/324*J2*J3^2);
    B9  := (-1/12*J2*J7-1/6*J3*J6);
    B17 := -1/2430*J2^3*J5*J6-17/315*J4*J6*J7-1/54*J3^2*J4*J7+1/81*J3^2*J5*J6+31/3780*J2*J4*J5*J6+1/972*J3^3*J4^2-1/29160*J2^3*J3*J4^2+1/1620*J2^3*J4*J7-1/2160*J2^2*J4^2*J5+1/180*J2^2*J6*J7+4/135*J5*J6^2+1/648*J2*J3*J4^3-1/140*J2*J4^2*J7+1/1134*J3*J4^2*J6+1/12*J3*J7^2;

    G   := -4/5;
    C8  := (1/180*J2^2*J4-18/35*J4^2+1/12*J3*J5+2/15*J2*J6);
    C9  := (-1/180*J2^2*J5-1/4860*J2^3*J3+2/5*J4*J5-34/135*J3*J6+1/162*J3^3+1/270*J2*J3*J4);
    C10 := (-1/27*J3^2*J4+314/315*J4*J6-1/6*J3*J7-1/10*J2*J4^2+1/810*J2^3*J4-1/90*J2^2*J6);
    C18 := 3/35*J3*J4^2*J7+1/14580*J2^2*J3^2*J4^2+113/17010*J2^2*J4^2*J6-4/15*J5*J6*J7+17/42525*J2*J4*J6^2+1/90*J2*J3*J6*J7-4/32805*J2^3*J3^2*J6+26/3645*J2*J3^2*J4*J6-1/1080*J2*J3*J4^2*J5-1/437400*J2^5*J4^2+41/136080*J2^3*J4^3-11/437400*J2^3*J6^2-13/54675*J2^4*J4*J6-3/350*J2*J4^4+4/2187*J3^4*J6-1/168*J3^2*J4^3+1/180*J2^2*J7^2-8/245*J4^3*J6+40/243*J6^3-3/70*J3*J4*J5*J6+11/14580*J3^2*J6^2+1/492075*J2^6*J6;

    D9 := (-1/576*J2^2*J5-1/288*J2*J3*J4-1/6*J3*J6-1/16*J2*J7);
    D10 := (-3/32*J5^2+1/6480*J2^3*J4+11/210*J4*J6+13/1620*J2^2*J6+1/24*J3*J7+1/233280*J2^5-1/7776*J2^2*J3^2+1/288*J2*J3*J5+1/720*J2*J4^2-1/144*J3^2*J4);
    D11 := (1/18*J3*J4^2+1/144*J2*J3*J6+1/288*J2^2*J7+1/48*J2*J4*J5-1/48*J5*J6-5/16*J4*J7);
    D19 := 1/699840*J2^4*J3*J4^2+7/8640*J2*J5*J6^2-47
    /30240*J2^2*J4^2*J7-1/38880*J2^4*J4*J7+3/280*J4^2*J5*J6+1/81*J3^2*
    J6*J7-5/7776*J2^3*J6*J7-1/15552*J2^2*J3*J4^3-1/288*J2*J3*J7^2-29/
    30240*J2^2*J4*J5*J6+1/1296*J2*J3^2*J4*J7-1/648*J2*J3^2*J5*J6-85/
    27216*J2*J3*J4^2*J6+3/896*J2*J4^3*J5-1/23328*J2*J3^3*J4^2+1/19440*
    J2^4*J5*J6-1/51840*J2^3*J4^2*J5-1/486*J3^3*J4*J6+1/864*J3^2*J4^2*
    J5+83/90720*J3*J4*J6^2+1/72*J3*J5^2*J6+1/14580*J2^3*J3*J4*J6-1/2240
    *J3*J4^4+3/32*J5*J7^2-25/432*J6^2*J7-9/1120*J4^3*J7-67/15120*J2*J4*
    J6*J7-1/48*J3*J4*J5*J7;

    E := 1/30;
    E10 := (-3/32*J5^2-1/288*J2*J3*J5-1/8*J3*J7-19/432*J3^2*J4+1/810*J2^3*J4-11/144*J2*J4^2+661/630*J4*J6-1/90*J2^2*J6);
    E11 := (-1/6480*J2^2*J3*J4+13/810*J2*J3*J6+1/116640*J2^4*J3+1/4320*J2^3*J5+1/360*J2^2*J7+2/45*J3*J4^2-1/3888*J2*J3^3-1/4*J4*J7-1/60*J5*J6);
    E12 := (17/216*J2*J4*J6+1/24*J3*J4*J5+1/144*J2*J3*J7-27/80*J4^3-25/216*J6^2+25/648*J3^2*J6+1/270*J2^2*J4^2-1/1215*J2^3*J6+3/16*J5*J7);
    E20 := -1/19440*J2^3*J3*J4*J7+1/9720*J2^3*J3*J5*J6-1/7290*J2^2*J3^2*J4*J6+1/25920*J2^2*J3*J4^2*J5-1/2160*J2^2*J3*J6*J7-1/720*J2^2*J4*J5*J7-47/15120*J2*J3*J4^2*J7-1/720*
J2*J5*J6*J7-331/3780*J3*J4*J6*J7+1/218700*J2^5*J4*J6+1/116640*J2^4*J4^3-377/907200*J2^2*J4^4-1/11664*J3^4*J4^2-1/144*J3^2*J7^2+19849/396900*J4^2*J6^2+1/349920*
J2^3*J3^2*J4^2-83/127575*J2^3*J4^2*J6+83/1360800*J2^2*J4*J6^2+1/1080*J2^2*J5^2*J6-9/1400*J4^5-1/2592*J2*J3^2*J4^3+449/22680*J2*J4^3*J6+1/960*J2*J4^2*J5^2-1/48*J2*J4*J7^2+1/
648*J3^3*J4*J7-1/324*J3^3*J5*J6+43/3240*J3^2*J4^2*J6+3/448*J3*J4^3*J5-29/15120*J2*J3*J4*J5*J6+7/4320*J3*J5*J6^2+9/70*J4^2*J5*J7-143/1680*J4*J5^2*J6;

    return
	A6, A7, A8, A16,
	B7, B8, B9, B17,
	G, C8, C9, C10, C18,
	D9, D10, D11, D19,
	E, E10, E11, E12, E20;

end function;

function ShiodaInvariantsAppend(LST, JI)
    old := false;
    for oldjis in LST do
	if ShiodaInvariantsEqual(oldjis, JI) then
	    old := true; break;
	end if;
    end for;
    if not old then return Append(LST, JI); end if;
    return LST;
end function;

function PowerRepresentativesInFiniteFields(FF, pow)
    R := [1]; NB := #AllRoots(FF!1, pow);
    for w in FF do
	if #R eq NB then break; end if;
	if &and[ not IsPower(w / r, pow) : r in R] then
	    Append(~R, w);
	end if;
    end for;
    return R;
end function;

intrinsic ShiodaAlgebraicInvariants(FreeJI::SeqEnum : ratsolve := true) -> SeqEnum
    {
    This function computes a degree 5 polynomial in J8 from the 6 free Shioda
    invariants J2, J3, J4, J5, J6 and J7. This function computes Shioda's
    relations too, that is 5 polynomials (of degree at most 2) whose  roots are
    respectivaly J9 and J10 (as functions of J8).

    By default (ratsolve := true), this function computes solutions to
    Shioda's system and returns them as a list of 9-uplet (J2, J3, J4, J5, J6,
    J7, J8, J9, J10). Otherwise (ratsolve := false), the system is returned as is.
    }

    require #FreeJI eq 6:
	"Argument must be a sequence of six free Shioda invariants J2, ..., J7.";
    if Universe(FreeJI) cmpeq Integers() then
	ChangeUniverse(~FreeJI, Rationals());
    end if;

    FF := Universe(FreeJI);
    require not Characteristic(FF) in {2, 3, 5, 7} : "2, 3, 5 and 7 must be invertible in the base ring.";

    P3 := PolynomialRing(FF, 3); J8 := P3.1; J9 := P3.2; J10 := P3.3;

    if ratsolve eq false or not IsFinite(FF) then
	g := 1; LG := [ FF!1 ];
    else
	Support := [i : i in [1..#FreeJI] | FreeJI[i] ne 0];
	if #Support eq 0 then
	    g := 1;
	else
	    g := Gcd([i+1 : i in Support]);
	end if;
	if g ne 1 then
	    LG := PowerRepresentativesInFiniteFields(FF, g);
	else
	    LG := [ FF!1 ];
	end if;
    end if;

    JIs := [];
    for L in LG do

	J2, J3, J4, J5, J6, J7 := Explode([L^((i+1) div g)*FreeJI[i] : i in [1..#FreeJI]]);

	A6, A7, A8, A16,
	    B7, B8, B9, B17,
	    G, C8, C9, C10, C18,
	    D9, D10, D11, D19,
	    E, E10, E11, E12, E20 := ShiodaSyzygyes(J2, J3, J4, J5, J6, J7);
	
	RES := [J8^5 +
	    
	    (A8 + 2*B8 + C8) * J8^4 +
	    
	    (-A6*C10 - A7*B9 + 2*A8*B8 + A8*C8 + A16 +
	    B7*B9*G + B7*G*D9 - B7*C9 + B8^2 + 2*B8*C8) * J8^3 +
	    
	    (-A6*B7*G*D11 - 2*A6*B8*C10 - A6*B9^2*G + A6*B9*C9 - A6*C18 + 
	    A7*B7*C10 - A7*B8*B9 - A7*B9*C8 - A7*B17 + A8*B7*B9*G + 
	    A8*B7*G*D9 - A8*B7*C9 + A8*B8^2 + 2*A8*B8*C8 + 2*A16*B8 + A16*C8 - 
	    B7^2*G*D10 + B7*B8*G*D9 - B7*B8*C9 + B7*B17*G + 
	    B8^2*C8) * J8^2 +

	    (-A6*B7*B8*G*D11 + A6*B7*B9*G*D10 - 
	    A6*B7*G*D19 - A6*B8^2*C10 + A6*B8*B9*C9 - 2*A6*B8*C18 - 
	    2*A6*B9*B17*G + A6*B17*C9 + A7*B7^2*G*D11 + A7*B7*B8*C10 - 
	    A7*B7*B9*G*D9 + A7*B7*C18 - A7*B8*B9*C8 - A7*B8*B17 - A7*B17*C8 - 
	    A8*B7^2*G*D10 + A8*B7*B8*G*D9 - A8*B7*B8*C9 + A8*B7*B17*G + 
	    A8*B8^2*C8 + A16*B7*B9*G + A16*B7*G*D9 - A16*B7*C9 + A16*B8^2 + 
	    2*A16*B8*C8) * J8 +

	    (- A6*B7*B8*G*D19 + A6*B7*B17*G*D10 - A6*B8^2*C18
	    + A6*B8*B17*C9 - A6*B17^2*G + A7*B7^2*G*D19 + A7*B7*B8*C18 - 
	    A7*B7*B17*G*D9 - A7*B8*B17*C8 - A16*B7^2*G*D10 + 
	    A16*B7*B8*G*D9 - A16*B7*B8*C9 + A16*B7*B17*G + A16*B8^2*C8)];

	
	R1 := J8^2                 +  A6*J10 +  A7*J9 +  A8*J8 + A16;
	R2 := J8*J9               +  B7*J10 +  B8*J9 +  B9*J8 + B17;
	R3 := J8*J10 + G*J9^2    +  C8*J10 +  C9*J9 + C10*J8 + C18;
	R4 := J9*J10             +  D9*J10 + D10*J9 + D11*J8 + D19;
	R5:=  J10^2  + E*J2*J9^2 + E10*J10 + E11*J9 + E12*J8 + E20;
	    
	RES cat:= [R1, R2, R3, R4, R5];
	
	if ratsolve eq false then return RES; end if;
    
	P2 := PolynomialRing(FF, 2); _J9 := P2.1; _J10 := P2.2;

	R8 := Roots(UnivariatePolynomial(RES[1]));
	for r8 in R8 do
	    j8 := r8[1];
	    dt  := A6*j8+A6*B8-B7*A7;
	    if dt ne 0 then
		j9  := (B7*j8^2-A6*B9*j8-A6*B17+B7*A8*j8+B7*A16)/dt;
		j10 := -(j8^3+j8^2*B8-A7*B9*j8-A7*B17+A8*j8^2+A8*j8*B8+A16*j8+A16*B8)/dt;
		NJI := [ J2, J3, J4, J5, J6, J7 ] cat [FF!j8, FF!j9, FF!j10 ];
		if g ne 1 then NJI := WPSNormalize([2..10], NJI); end if;
		JIs := ShiodaInvariantsAppend(JIs, NJI);
	    else

		R1 := j8^2                 +  A6*_J10 +  A7*_J9 +  A8*j8 + A16;
		R2 := j8*_J9               +  B7*_J10 +  B8*_J9 +  B9*j8 + B17;
		R3 := j8*_J10 + G*_J9^2    +  C8*_J10 +  C9*_J9 + C10*j8 + C18;
		R4 := _J9*_J10             +  D9*_J10 + D10*_J9 + D11*j8 + D19;
		R5:=  _J10^2  + E*J2*_J9^2 + E10*_J10 + E11*_J9 + E12*j8 + E20;
	    
		SYS := [R1, R2, R3, R4, R5];
		V := Variety(ideal<P2 | SYS>);
		for v in V do
		    NJI := [ J2, J3, J4, J5, J6, J7 ] cat [ FF!j8, FF!v[1], FF!v[2] ];
		    if g ne 1 then NJI := WPSNormalize([2..10], NJI); end if;	    
		    JIs := ShiodaInvariantsAppend(JIs, NJI);
		end for;
	    end if;
	
	end for;
    end for;
    return JIs;
    
end intrinsic;


 /***
  *
  * Maeda invariants in characteristic 0 or > 7
  * see [Maeda1997].
  *
  ********************************************************************/

intrinsic MaedaInvariants(f::RngUPolElt) -> SeqEnum
    {Compute the Maeda field invariants  'I2', 'I3', 'I4', 'I4p', 'I8' and
    'I9' of a polynomial of degree at most 8, considered as a binary form of
    degre 8 (see 1990 Maeda's paper).
    }

    require Degree(f) le 8: "Polynomial must have degree at most 8.";

    CR := CoefficientRing(Parent(f));
    require not Characteristic(CR) in {2, 3, 5, 7} : "2, 3, 5 and 7 must be invertible in the base ring.";
    
    f_cov := [* f, 1, 8 *];

    /* Q=(f,f)_6 : order 4, degree 2 */
    Q:=Transvectant(f_cov,f_cov,6);

    /* t=((Q,Q)_2,Q)_1 : order 6, degree 6 */
    t:=Transvectant(Transvectant(Q,Q,2),Q,1);

    /* theta=(f,t)_6 : order 2, degree 7 */
    theta:=Transvectant(f_cov,t,6);

    /* M=(f,f)_6 : order 0, degree 12 */
    M:=Transvectant(t,t,6);
    m:=M[1];

    /* j=((t,t)_2,t)_1 : order 12, degree 18 */
    j:=Transvectant(Transvectant(t,t,2),t,1);

    /* I2=(theta,theta)_2/M : order 0, degree 2  */
    I2n:=Transvectant(theta,theta,2);
    I2:=I2n[1]/m;

    /* I3=(theta^3,t)_6/M^2 : order 0, degree 3 */
    I3n:=Transvectant([* theta[1]^3, 3*theta[2], 3*theta[3] *], t, 6);
    I3:=I3n[1]/m^2;

    /* I4=(theta^4,(t,t)_2)_8/M^3 : order 0, degree 4 */
    I4n:=Transvectant([* theta[1]^4, 4*theta[2], 4*theta[3] *], Transvectant(t,t,2), 8);
    I4:=I4n[1]/m^3;

    /* J2=((theta,f)_1,(t,t)_2)_8*(theta^6,j)_12/M^6 : order 0, degree 8 : new notation I8 */
    I8n:=Transvectant(Transvectant(theta,f_cov,1),Transvectant(t,t,2),8)[1]
	*Transvectant([* theta[1]^6, 6*theta[2], 6*theta[3] *], j, 12)[1];
    I8:=I8n/m^6;

    /* J3=(36*(theta^2*f,j)_12/M^7+14*((theta^2,f)_3,t)_6/(9*M))*(theta^6,j)_12/M^5 :
       order 0, degree 3 */
    /* WARNING: it seems that there is a mistake and one should replace M^7 by M^2 
       so J3 is of degree 9. New notation I9 */
    I9:=(36*Transvectant([* theta[1]^2*f, 2*theta[2]+1, 2*theta[3]+8*],j,12)[1]/m^2+
    14*Transvectant(Transvectant([* theta[1]^2, 2*theta[2], 2*theta[3]*],f_cov,3),t,6)[1]/(9*m))
    *Transvectant([* theta[1]^6, 6*theta[2], 6*theta[3] *],j,12)[1]/m^5;

    /* J4=-2(f*theta^3,t*(t,t)_2)_14/m^3+5*((f,theta^3)_1,j)_12/(21*M^3)+140*((f,theta^3)_4,t)_6/(297*M^2) :
        order 0, degree 4. New notation Ip4 */
    Ip4:=-2*Transvectant([* f*theta[1]^3, 3*theta[2]+1, 3*theta[3]+8 *],
	[* t[1]*Transvectant(t,t,2)[1], 3*t[2], 14 *],14)[1]/m^3+
    5*Transvectant(Transvectant(f_cov,[* theta[1]^3, 3*theta[2], 3*theta[3] *],1),j,12)[1]/(21*m^3)
    +140*Transvectant(Transvectant(f_cov,[* theta[1]^3, 3*theta[2], 3*theta[3] *],4),t,6)[1]/(297*m^2);

    return [ CR!I2 , CR!I3 , CR!I4, CR!Ip4, CR!I8, CR!I9 ];
    
end intrinsic;

intrinsic MaedaInvariants(C::CrvHyp) -> SeqEnum 
    {Compute the Maeda field invariants  'I2', 'I3', 'I4', 'I4p', 'I8' and
    'I9' of a genus 3 hyperelliptic curve C.}
    
    require Genus(C) eq 3: "Curve must be of genus 3.";
    K := BaseField(C);
    R := PolynomialRing(K); x := R.1;
    f, h := HyperellipticPolynomials(C);
    require (h eq 0) and (Degree(f) le 8): 
    "The curve must be of form y^2 = f(x), where f has degree at most 8.";

    return MaedaInvariants(f);
end intrinsic;


 /***
  *
  * Reconstruction
  *
  ********************************************************************/
 
/* Case C2 x S4.

   y^2 = x^8 + 14*x^4 + 1 in  char > 7,
   see [MaShShVo2002].
*/
function G3ModelsInCharFF_G48_48(JI : geometric := false)
      
    FF := Universe(JI); x := PolynomialRing(FF).1;
    f := x^8 + 14*x^4 + 1;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);
end function;

/* Case V8.

   y^2 = x^8 - 1 in  char > 7,
   see [MaShShVo2002].
*/
function G3ModelsInCharFF_G32_9(JI : geometric := false)
      
    FF := Universe(JI); x := PolynomialRing(FF).1;
    f := x^8 - 1;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);
end function;

/* Case U6.

   y^2 = x (x^6 - 1) in  char > 7,
   see [MaShShVo2002].
*/
function G3ModelsInCharFF_G24_5(JI : geometric := false)
      
    FF := Universe(JI); x := PolynomialRing(FF).1;
    f := x * (x^6 - 1);
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);
end function;

/* Case C14.

   y^2 = x^7 - 1 in  char > 7,
   see [MaShShVo2002].
*/
function G3ModelsInCharFF_C14(JI : geometric := false)
      
    FF := Universe(JI); x := PolynomialRing(FF).1;
    f := x^7 - 1;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);
end function;

/* Case C2xD8

   y^2 = x^8 + a4*x^4 + a0 in  char > 7,

   a0 <> 0, a4^2-4*a0 <> 0 (Discrim = 0)

   see [MaShShVo2002].
*/
function G3ModelsInCharFF_G16_11(JI : geometric := false)
      
    FF := Universe(JI); x := PolynomialRing(FF).1;
    J2, J3, J4, J5, J6, J7, J8 := Explode(JI);

    if -30*J3^2+J2^3 ne 0 then
	a4 := 35/2*(J5*J2+6*J4*J3)/(-30*J3^2+J2^3);
    elif J4 ne 0 then
	a4 := 35/3*J5/J4;
    elif J5 ne 0 then
	a4 := 7/3*(6*J4*J2+30*J3^2-J2^3)/J5;
    else
	error "[G3Twists] G48_48 case trapped in G3ModelsInCharFF_G16_11 by error at JI = ", JI;
    end if;

    a0 := -1/140*a4^2+1/2*J2;
    
    f := x^8 + a4*x^4 + a0;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;

/* Case D12

   y^2 = x * (x^6 + a4*x^3 + a1)  in  char > 7,

   a1 <> 0, a4^2-4*a1 <> 0 (Discrim = 0)

   see [MaShShVo2002].
*/
function G3ModelsInCharFF_D12(JI : geometric := false)
      
    FF := Universe(JI); x := PolynomialRing(FF).1;
    J2, J3, J4, J5, J6, J7, J8 := Explode(JI);

    if 30*J3^2-J2^3 ne 0 then
	a4 := 280*(-J5*J2+4*J4*J3)/(30*J3^2-J2^3);
    elif J4 ne 0 then
	a4 := 35/3*J5/J4;
    elif J5 ne 0 then
	a4 := 7/108*(96*J4*J2+30*J3^2-J2^3)/J5;
    else
	error "[G3Twists] : G48_48 group trapped in G3ModelsInCharFF_D12()";
    end if;

    a1 := 2/35*a4^2-4*J2;
    
    f := x * (x^6 + a4*x^3 + a1);
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;

/* Case C2xC4

   y^2 = a^2*Z^8+2*a^2*Z^6+8*a*Z^2-16; in  char > 7,

   a <> 0, -4, (Discrim = 0)

   see [MaShShVo2002].
*/
function G3ModelsInCharFF_C2xC4(JI : geometric := false)

    FF := Universe(JI); x := PolynomialRing(FF).1;
    J2, J3, J4, J5, J6, J7, J8 := Explode(JI);

    if 6*J4-J2^2 eq 0 then
	a := FF!196/3;
    elif 96*J4-J2^2 eq 0 then
	a := FF!-196;
    elif 147*J4-2*J2^2 eq 0 then

	if J6-2/3087*J2^3 eq 0 then
	    if geometric then return [x*(x-1)*(x+1)*(x^2+1)^2]; end if;
	    
	    error "[G3Twists] currently, no twists computation done in G3ModelsInCharFF_C2xC4, sorry";
	    return [];
	end if;
	
	a := FF!-84;
    else
	
	a :=
	    98/9*(36288*J4^2-3906*J4*J2^2+14400*J6*J2+43*J2^4)/(96*J4-J2^2)/(147*J4-2*J2^2);
	
    end if;

    f := a^2*x^8+2*a^2*x^6+8*a*x^2-16;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;

/* Case C2^3

   y^2 = a0*x^8 + a2*x^6 + a4*x^4 + a2*x^2 + a0 in  char > 7,

   a0 <> 0, 2*a2+2*a0+a4 <>0, -2*a2+2*a0+a4 <>0, 8*a0^2+a2^2-4*a0*a4 <>0 (Discrim = 0).

   see [MaShShVo2002].
*/
function G3ModelsInCharFF_G8_5(JI : geometric := false)

    FF := Universe(JI); x := PolynomialRing(FF).1;
    J2, J3, J4, J5, J6, J7, J8 := Explode(JI);

    /*
      Polynomial trivial when a2 = 0, a4 = 14*a0-2*a2 or a4 = 14*a0+2*a2
      (but then the automorphism group is larger, C2xD8).
    */
    Pa4 := 
	192*(-60*J3^2+2*J2^3+18*J6-9*J4*J2)*x^3
	-90720*(3*J4*J3+3*J7-J5*J2)*x^2+
	294*(765*J4*J2^2+1440*J6*J2-5940*J5*J3-1782*J4^2+1140*J3^2*J2-38*J2^4)*x+
	6637050*J6*J3+1250235*J5*J4-833490*J5*J2^2+2932650*J4*J3*J2+2881200*J3^3-96040*J3*J2^3;
    
    if not IsIrreducible(Pa4) then
	
	/* Easy, we may find a rational model in this case */	
	a4 := [r[1] : r in Roots(Pa4)][1];

	la8 := (18*J6*a4-9*a4*J4*J2-60*a4*J3^2+2*a4*J2^3-810*J7+270*J5*J2-810*J4*J3)/(-18*J6+9*J4*J2+60*J3^2-2*J2^3)/10;
	a6 := (-28*la8^2-1/5*a4^2+14*J2);
	l := 1/a6; a8 := a6*la8;
	
	f := a8*x^8 + a6*x^6 + a4*x^4 + l*a6*x^2 + l^2*a8;
	if geometric then return [f]; end if;
	return HyperellipticPolynomialTwists(f, 8);
    end if;

    /* Let's go in a degree 3 extension */
    Pa4 /:= Coefficient(Pa4, Degree(Pa4));

    /* The difficult case, nothing done for now */
    if not IsFinite(FF) then

	if IsNumberField(FF) then K3 := ext<FF | Pa4>; else K3 := quo<Parent(x) | Pa4>; end if;
	 a4 := K3.1; x := PolynomialRing(K3).1;
	la8 := (18*J6*a4-9*a4*J4*J2-60*a4*J3^2+2*a4*J2^3-810*J7+270*J5*J2-810*J4*J3)/(-18*J6+9*J4*J2+60*J3^2-2*J2^3)/10;
	a6 := (-28*la8^2-1/5*a4^2+14*J2);
	l := 1/a6; a8 := a6*la8;
	if geometric then return [a8*x^8 + a6*x^6 + a4*x^4 + l*a6*x^2 + l^2*a8]; end if;
	
	error "[G3Twists] currently, no twists computation done over an infinite field, sorry";
	return [];
    end if;

    /* Finite field case */
    K3   := ExtensionField<FF, x | Pa4>; a4 := K3.1; x := PolynomialRing(K3).1;

    a0   := -a4/10-(81*J7-27*J5*J2+81*J4*J3)/(-2*J2^3-18*J6+9*J4*J2+60*J3^2);

    Pa2 := x^2+28*a0^2+1/5*a4^2-14*J2;
    if IsIrreducible(Pa2) then
	K6 := ExtensionField<K3, x | Pa2>; a2 := K6.1; x := PolynomialRing(K6).1;
    else
	K6 := K3;  a2 := [r[1] : r in Roots(Pa2)][1];
    end if;

    /*
    if not IsFinite(FF) then
	if geometric then return [a0*x^8 + a2*x^6 + a4*x^4 + a2*x^2 + a0]; end if;
	
	error "[G3Twists] currently, no twists computation done over an infinite field, sorry";
	return [];
    end if;
    */	
    
    /* Is Sqrt(-1) defined ? */
    PI := x^2+1;
    if IsIrreducible(PI) then
	K12<I> := ExtensionField<K6, x | PI>; I := K12.1; 
    else
	K12 := K6;  I := [r[1] : r in Roots(PI)][1];
    end if;
    x := PolynomialRing(K12).1;

    f := a0*x^8 + a2*x^6 + a4*x^4 + a2*x^2 + a0;

    sigma := map< K12 -> K12 | x :-> x^(#FF) >;
//    sigma := FrobeniusMap(K12, FF);
    fc := Parent(f)![sigma(el):el in Eltseq(f)];

    /* Let us determine M s.t. x' = M(x) with
    y^2 = f(x) and y'^2 = f(x') */    

    /* a faster version of that follows

    ret, MLc := IsGL2Equivalent(f, fc, 8);
    error if ret eq false,
	"[G3Twists] No galois geometric automorphism found in G3ModelsInCharFF_G8_5";
    M := Matrix(2, 2, MLc[1])^(-1);
    */

    M := Matrix(2, 2, [K12!0, 0, 0, 0]);
    for Mt in
	[
	    Matrix(2, 2, [K12!1, I, 1, -I]),
	    Matrix(2, 2, [K12!1, 1, I, -I])
	    ] do
	    fd  := MActOnC(f, 8, Mt);
	if Degree(fd/fc) eq 0 then M := Mt^(-1); break; end if;
    end for;
    error if M eq 0,
	"[G3Twists] No galois geometric automorphism found in G3ModelsInCharFF_G8_5 at JI =", JI;

    /* Then A s.t M = (A^sigma)^(-1) * A */
    A := Glasby(M, sigma, FF);
    error if A eq 0,
	"[G3Twists] No rational model found in G3ModelsInCharFF_G8_5 at JI =", JI;

    /* And ftilde */
    ftilde  := MActOnC(f, 8, A^(-1)); ftilde /:= Coefficient(ftilde, Degree(ftilde));
    ftilde  := PolynomialRing(FF)!Eltseq(ftilde);

    if geometric then return [ftilde]; end if;
    return HyperellipticPolynomialTwists(ftilde, 8);
end function;


function G3Models(JI: geometric := false, models := true)

    FF := Universe(JI);
    J2, J3, J4, J5, J6, J7, J8, J9, J10 := Explode(JI);
    p := Characteristic(FF);
    twists := [];
    
    /* Not yet implemented */
    if p in {2, 3, 5, 7} then		  
	error "[G3Twists] currently, no computation done in Finite Fields of char. 2, 3, 5 or 7, sorry";
	return [], <>;
    end if;

    /* Point at infinity*/
    if J2 eq 0 and J3 eq 0 and
	J4 eq 0 and J5 eq 0 and
	J6 eq 0 and J7 eq 0 and
	J8 eq 0 and J9 eq 0 and
	J10 eq 0 then
	
	aut := SmallGroup(1,1);/* FixMe: <1,1> is not the good choice here */
	if models then twists := [PolynomialRing(FF).1^8]; end if;
	if geometric or not models then return twists, aut; end if;
	error "[G3Twists] no possible twist computations for singular forms, sorry";	  
	return [], <>;
    end if;

    /*
     * Now, p >= 11
     *****************/
     
    /*** Zero dimensional cases ***/

    /* C2 x S4 : y^2 = x^8 + 14*x^4 + 1  */
    if J2^3-30*J3^2 eq 0 and J4 eq 0 and J5 eq 0 and J6 eq 0
	and J7 eq 0 and J8 eq 0 and J9 eq 0 and J10 eq 0 then
	vprintf G3Twists, 1 : "Automorphism group C2 x S4, curve y^2 = x^8 + 14*x^4 + 1\n";
	aut := SmallGroup(48, 48);
	if models then twists := G3ModelsInCharFF_G48_48(JI : geometric := geometric); end if;
	return twists, aut;
    end if;

    /* V8 : y^2 = x^8 - 1  */
    if J3 eq 0 and J2^2-6*J4 eq 0  and J5 eq 0 and J2^3+36*J6 eq 0 and
	J7 eq 0 and J2^4+420*J8 eq 0 and J9 eq 0 and 2520*J10 - J2^5 eq 0 then
	vprintf G3Twists, 1 : "Automorphism group V8, curve y^2 =  x^8 - 1\n";
	aut := SmallGroup(32, 9);
	if models then twists := G3ModelsInCharFF_G32_9(JI : geometric := geometric); end if;
	return twists, aut;
    end if;

    /* U6 : y^2 = x (x^6 - 1) */
    if J3 eq 0 and J2^2-96*J4 eq 0  and J5 eq 0 and J2^3+2304*J6 eq 0 and
	J7 eq 0 and J2^4-17920*J8 eq 0  and J9 eq 0 and 430080*J10+J2^5 eq 0 then
	vprintf G3Twists, 1 : "Automorphism group U6, curve y^2 = x (x^6 - 1)\n";
	aut := SmallGroup(24, 5);
	if models then twists := G3ModelsInCharFF_G24_5(JI : geometric := geometric); end if;
	return twists, aut;
    end if;

    /* C14 : y^2 = x^7 - 1 */
    if J2 eq 0 and J3 eq 0 and J4 eq 0 and J5 eq 0 and J6 eq 0 and
	J8 eq 0 and J9 eq 0 and J10 eq 0 then
	vprintf G3Twists, 1 : "Automorphism group C14, curve y^2 = x^7 - 1\n";
	aut := CyclicGroup(14); /* SmallGroup(14, 2) */
	if models then twists := G3ModelsInCharFF_C14(JI : geometric :=	geometric); end if;
	return twists, aut;
    end if;

    /*** One dimensional cases ***/
    
    /* C2 x D8 : y^2 = x^8 + a*x^4 + 1 or a*x^8 + a*x^4 + b*/
    if
	J4^3 - 3/2*J4^2*J2^2 - 20*J4*J3^2*J2 + 2/3*J4*J2^4 - 200/3*J3^4 + 40/9*J3^2*J2^3 - 2/27*J2^6 eq 0 and
	J5*J3 + 3/10*J4^2 - 1/4*J4*J2^2 - J3^2*J2 + 1/30*J2^4 eq 0 and
	J5*J4 - 2/3*J5*J2^2 + 5*J4*J3*J2 + 20*J3^3 - 2/3*J3*J2^3 eq 0 and
	J5^2 - 6/5*J4^2*J2 - 6*J4*J3^2 + 1/5*J4*J2^3 eq 0 and
	J6 -1/2*J4*J2 - 10/3*J3^2 + 1/9*J2^3 eq 0 and
	J7 - 1/3*J5*J2 + J4*J3 eq 0 and
	J8 - 1/70*J4^2 - 1/20*J4*J2^2 - 1/3*J3^2*J2 + 1/90*J2^4 eq 0 and
	J9 - 1/9*J5*J2^2 + 5/6*J4*J3*J2 + 10/3*J3^3 - 1/9*J3*J2^3 eq 0 and
	J10 - 1/42*J4^2*J2 - 1/21*J4*J3^2 + 1/630*J4*J2^3 eq 0
	then
	vprintf G3Twists, 1 : "Automorphism group C2xD8, curve y^2 = x^8 + a*x^4 + 1\n";
	aut := SmallGroup(16, 11);
	if models then twists := G3ModelsInCharFF_G16_11(JI : geometric := geometric); end if;
	return twists, aut;
    end if;

    /* D12 : y^2 = x * (x^6+a*x^3+1) */
    if
	J4^3 - 3/32*J4^2*J2^2 - 5/64*J4*J3^2*J2 + 1/384*J4*J2^4 - 25/1536*J3^4+5/4608*J3^2*J2^3 - 1/55296*J2^6 eq 0 and
        J5*J3 - 16/5*J4^2 + 1/6*J4*J2^2 + 1/24*J3^2*J2 - 1/720*J2^4 eq 0 and
	J5*J4 - 1/24*J5*J2^2 - 5/24*J4*J3*J2 - 5/96*J3^3 + 1/576*J3*J2^3 eq 0 and
	J5^2 - 8/15*J4^2*J2 - 1/6*J4*J3^2 + 1/180*J4*J2^3 eq 0 and
	J6 - 1/8*J4*J2 - 5/96*J3^2 + 1/576*J2^3 eq 0 and
	J7 - 1/12*J5*J2 - 1/6*J4*J3 eq 0 and
	J8 - 26/105*J4^2 + 1/120*J4*J2^2 + 1/288*J3^2*J2 - 1/8640*J2^4 eq 0 and
	J10 - 5/252*J4^2*J2 - 13/1008*J4*J3^2 + 13/30240*J4*J2^3 eq 0 and
	J9 - 1/144*J5*J2^2 - 5/144*J4*J3*J2 - 5/576*J3^3 + 1/3456*J3*J2^3 eq 0
	then
	vprintf G3Twists, 1 : "Automorphism group D12, curve y^2 * (x^6 + a*x^3 + 1)\n";
	aut := SmallGroup(12, 4);
	if models then twists := G3ModelsInCharFF_D12(JI : geometric := geometric); end if;
	return twists, aut;
    end if;

     /* C2 x C4 : y^2 = x * (x^2 - 1) * (x^4 + a * x^2 + 1) */
    if
	J3 eq 0 and J5 eq 0 and J7 eq 0 and
	J6^2 - 11/20*J6*J4*J2 + 19/2880*J6*J2^3 - 162/125*J4^3 + 929/8000*J4^2*J2^2 -
	161/72000*J4*J2^4 + 1/81000*J2^6 eq 0 and
	J8 + 22/135*J6*J2 + 78/175*J4^2 - 47/1350*J4*J2^2 + 2/6075*J2^4 eq 0 and
	J9 eq 0 and
	J10 + 173/630*J6*J4 + 7/6480*J6*J2^2 + 173/3600*J4^2*J2 - 89/32400*J4*J2^3 + 1/36450*J2^5 eq 0
	then
	vprintf G3Twists, 1 : "Automorphism group C2xC4, curve y^2 = x * (x^2 - 1) * (x^4 + a * x^2 + 1)\n";
	aut := DirectProduct(CyclicGroup(2), CyclicGroup(4));	/* SmallGroup(8, 2) */
	if models then twists := G3ModelsInCharFF_C2xC4(JI : geometric := geometric); end if;
	return twists, aut;
    end if;

    /*** Two dimensional cases ***/
    
    /* C2^3 : y^2 = a0*x^8 + a2*x^6 + a4*x^4 + a2*x^2 + a0 */
    if

	J10 + 421/1890*J6*J4 - 2/15*J5^2 + 67/2700*J4^2*J2 + 4/405*J4*J3^2 - 2/6075*J4*J2^3 eq 0 and
	
	J9 + 1/12*J7*J2 - 37/108*J6*J3 - 9/40*J5*J4 + 1/90*J5*J2^2 - 1/27*J4*J3*J2 - 2/81*J3^3 + 1/1215*J3*J2^3 eq 0 and
    
	85050*J8-11655*J6*J2+11340*J5*J3+2187*J4^2-1260*J4*J2^2-840*J3^2*J2+28*J2^4 eq 0 and

	546750*J7^2-963900*J6*J4^2+453600*J4*J6*J2^2+1404000*J6*J3^2*J2-46800*J2^4*J6+320760*J4*J5^2-196830*J2^2*J5^2+204120*J5*J4*J2*J3-680400*J5*J3^3+22680*J5*J2^3*J3-12312*J4^3*J2+537570*J4^2*J3^2+32301*J4^2*J2^3+157680*J4*J3^2*J2^2-5256*J4*J2^5+82800*J3^4*J2-5520*J3^2*J2^4+92*J2^7 eq 0 and

	145800*J7*J6+4050*J7*J2^3-64800*J6*J5*J2+83700*J6*J4*J3-16650*J6*J3*J2^2+77760*J5^2*J3+13122*J4^2*J5-5751*J5*J4*J2^2+8640*J2*J5*J3^2+252*J5*J2^4-10260*J2*J4^2*J3+2880*J3^3*J4-1896*J4*J3*J2^3-1200*J3^3*J2^2+40*J3*J2^5 eq 0 and

	18225*J7*J5+7425*J2*J6*J4+43200*J6*J3^2-1440*J6*J2^3-10935*J2*J5^2+42525*J5*J4*J3+5103*J4^3-675*J4^2*J2^2+2250*J4*J3^2*J2-75*J4*J2^4+1800*J3^4-120*J3^2*J2^3+2*J2^6 eq 0 and

	4860*J7*J4-810*J7*J2^2-1080*J6*J5+3330*J6*J3*J2-837*J5*J4*J2-2880*J5*J3^2-12*J5*J2^3+2916*J4^2*J3+360*J4*J3*J2^2+240*J3^3*J2-8*J3*J2^4 eq 0 and

	12150*J7*J3+7560*J6*J4-1665*J6*J2^2-2430*J5^2+1620*J5*J3*J2+837*J4^2*J2+1530*J4*J3^2-231*J4*J2^3-120*J3^2*J2^2+4*J2^5 eq 0 and

	32400*J6^2+28350*J2*J6*J4+87750*J6*J3^2-2925*J6*J2^3-21870*J2*J5^2+76545*J5*J4*J3+13122*J4^3-405*J4^2*J2^2+5130*J4*J3^2*J2-171*J4*J2^4+3600*J3^4-240*J3^2*J2^3+4*J2^6 eq 0 and

	194400*J6*J5^2+2034720*J6*J4^2*J2+2073600*J6*J4*J3^2-777870*J6*J4*J2^3-2193750*J6*J3^2*J2^2+73125*J6*J2^5-913680*J5^2*J4*J2+518400*J5^2*J3^2+179550*J5^2*J2^3+1516320*J5*J4^2*J3+419175*J5*J4*J2^2*J3+1555200*J5*J3^3*J2-51840*J5*J2^4*J3+244944*J4^4+112590*J4^3*J2^2-1170720*J4^2*J3^2*J2-80451*J4^2*J2^4+86400*J4*J3^4-306810*J4*J3^2*J2^3+10131*J4*J2^6-147600*J3^4*J2^2+9840*J3^2*J2^5-164*J2^8 eq 0 and

	22680*J6*J5*J4-4995*J6*J5*J2^2-14850*J6*J4*J3*J2-86400*J6*J3^3+2880*J6*J3*J2^3-7290*J5^3+26730*J5^2*J3*J2+2511*J5*J4^2*J2-80460*J4*J5*J3^2-693*J4*J5*J2^3-360*J2^2*J5*J3^2+12*J2^5*J5-10206*J4^3*J3+1350*J4^2*J3*J2^2-4500*J4*J3^3*J2+150*J4*J3*J2^4-3600*J3^5+240*J2^3*J3^3-4*J2^6*J3 eq 0 and

	22275*J5*J4*J2*J3-49950*J6*J3^2*J2-7650*J4*J3^2*J2^2-1440*J5*J2^3*J3-3600*J3^4*J2+240*J3^2*J2^4+43200*J5*J3^3-34560*J4^2*J3^2+45360*J6*J4^2-14580*J4*J5^2+5022*J4^3*J2-2223*J4^2*J2^3+255*J4*J2^5+1665*J2^4*J6+2430*J2^2*J5^2+16200*J6*J5*J3-17550*J4*J6*J2^2-4*J2^7 eq 0 and

	-64800*J4*J3^4*J2+1502550*J6*J3^2*J2^3+929070*J6*J4*J2^4-168480*J4^2*J3^2*J2^2+51840*J5*J3*J2^5+305370*J4*J3^2*J2^4-4626720*J6*J4^2*J2^2+16912800*J5*J4*J3^3+432000*J3^6-2449440*J5^2*J4^2+874800*J5^3*J3-4581360*J4^3*J3^2+7620480*J6*J4^3-6609600*J6*J4*J3^2*J2+3440880*J5*J4^2*J3*J2-982935*J5*J4*J3*J2^3+10368000*J6*J3^4-61605*J6*J2^6-89910*J5^2*J2^4+843696*J4^4*J2-559278*J4^3*J2^3+125091*J4^2*J2^5-10107*J4*J2^7+104400*J3^4*J2^3-8400*J3^2*J2^6+947700*J5^2*J4*J2^2-3207600*J5^2*J3^2*J2-1555200*J5*J3^3*J2^2+148*J2^9 eq 0 and

	-1336500*J5*J4^2*J3*J2^2-5427000*J5*J4*J3^3*J2+180900*J5*J4*J3*J2^4-437400*J5^2*J4^2*J2+2916000*J4*J5^2*J3^2+212625*J4*J5^2*J2^3-656100*J5^3*J3*J2+753300*J2^2*J5^2*J3^2+2494800*J5*J4^3*J3-186300*J4^3*J3^2*J2+151200*J4^2*J3^2*J2^3+351000*J4*J3^4*J2^2-23400*J4*J3^2*J2^5+201600*J3^3*J5*J2^3-25110*J2^5*J5^2-3024000*J3^5*J5+2592000*J3^4*J4^2+108000*J3^6*J2-10800*J3^4*J2^4+360*J3^2*J2^7+97200*J5^4-3360*J3*J2^6*J5-259200*J4^4*J2^2+66960*J4^3*J2^4-7920*J4^2*J2^6+390*J4*J2^8+381024*J4^5-4*J2^10 eq 0

	then
	vprintf G3Twists, 1 : "Automorphism group C2xC2xC2, curve y^2 = a0*x^8 + a2*x^6 + a4*x^4 + a2*x^2 + a0\n";
	aut := SmallGroup(8, 5);
	if models then twists := G3ModelsInCharFF_G8_5(JI : geometric := geometric); end if;
	return twists, aut;
    end if;


    
    /* C4 : y^2 = x*(x^2-1)*(x^4+a*x^2+b)  */ 
    if
	J3 eq 0 and J5 eq 0 and J7 eq 0 and J9 eq 0 and

	-5488*J2^9*J6+6174*J2^8*J4^2+1037232*J2^7*J4*J6-1091475*J2^6*J4^3-3333960*J2^6*J4*J8-3093174*J2^6*J6^2-60328800*J2^5*J4^2*J6+58796766*J2^4*J4^4+30005640*J2^5*J6*J8+540101520*J2^4*J4^2*J8+274718304*J2^4*J4*J6^2+1237946976*J2^3*J4^3*J6-1031704128*J2^2*J4^5-6631246440*J2^3*J4*J6*J8-405409536*J2^3*J6^3-23803045560*J2^2*J4^3*J8-5893679232*J2^2*J4^2*J6^2-9523422720*J2*J4^4*J6+5509980288*J4^6+6076142100*J2^2*J4*J8^2+36726903360*J2^2*J6^2*J8+231472080000*J2*J4^2*J6*J8+42247941120*J2*J4*J6^3+267846264000*J4^4*J8+8888527872*J4^3*J6^2+291654820800*J2*J6*J8^2-1104121821600*J4^2*J8^2-1469076134400*J4*J6^2*J8-256048128000*J6^4+1093705578000*J8^3	eq 0 and
	
	J10^2 + 23/420*J10*J4^2*J2 - 239/120960*J10*J4*J2^3 +     1/51840*J10*J2^5 - 661/896*J8^2*J4 + 1/128*J8^2*J2^2 -     25/216*J8*J6^2 - 1189/60480*J8*J6*J4*J2 + 17/77760*J8*J6*J2^3 +    131/4704*J8*J4^3 - 1/6048*J8*J4^2*J2^2 - 491/99225*J6^2*J4^2 +     5/7776*J6^2*J4*J2^2 + 13/635040*J6*J4^3*J2 +     113/11430720*J6*J4^2*J2^3 - 1/4898880*J6*J4*J2^5 +     219/274400*J4^5 + 709/1693440*J4^4*J2^2 - 29/1360800*J4^3*J2^4 +     1/4665600*J4^2*J2^6 eq 0 and

	J10*J8 - 18/35*J10*J4^2 + 1/45*J10*J4*J2^2 - 1/4320*J10*J2^4 -     3/32*J8^2*J2 + 314/315*J8*J6*J4 - 17/720*J8*J6*J2^2 -     3/56*J8*J4^2*J2 + 1/810*J8*J4*J2^3 + 40/243*J6^3 -     8/1215*J6^2*J4*J2 - 11/437400*J6^2*J2^3 - 8/245*J6*J4^3 +     281/68040*J6*J4^2*J2^2 - 221/1224720*J6*J4*J2^4 +     1/492075*J6*J2^6 - 3/392*J4^4*J2 + 227/544320*J4^3*J2^3 -     17/3499200*J4^2*J2^5 eq 0 and    

	J10*J6 - 1/8*J10*J4*J2 + 1/576*J10*J2^3 + 45/64*J8^2 +     3/32*J8*J6*J2 - 39/112*J8*J4^2 + 11/210*J6^2*J4 +     19/1008*J6*J4^2*J2 - 13/30240*J6*J4*J2^3 - 27/3920*J4^4 -     1/1152*J4^3*J2^2 + 1/51840*J4^2*J2^4 eq 0
    
	then
	vprintf G3Twists, 1 : "Automorphism group C4, curve y^2 = x*(x^2-1)*(x^4+a*x^2+b)\n";
	aut := SmallGroup(4, 1);
	if models then
	    f := Genus3ConicAndQuarticForC4(JI : models := models);
	    error if Type(f) eq BoolElt, "[G3Twists] None C4-model found at JI =", JI;
	    twists := [f];
	end if;
	if geometric or not models then return twists, aut; end if;
	return HyperellipticPolynomialTwists(f, 8), aut;
    end if;

    /*** Three dimensional case ***/
    
    /* D4 : y^2 = (x^2-1)*(x^6+a*x^4+b*x^2+c)  */    
    if
	1/36450*J2^4*J4^2 - 1/1215*J2*J3^2*J4^2 - 1/810*J2^2*J4^3 - 12/1225*J4^4 + 
	1/90*J3*J4^2*J5 - 26/42525*J2^3*J4*J6 + 52/2835*J3^2*J4*J6 + 
	76/2835*J2*J4^2*J6 - 2/15*J5^2*J6 + 352/4725*J4*J6^2 + 1/5*J4*J5*J7 - 
	2/15*J3*J6*J7 - 1/30*J2*J7^2 - 52/105*J4^2*J8 + 2/15*J2*J6*J8 + J8^2 + 
	1/15*J3*J4*J9 + 1/30*J2*J5*J9 - 2/5*J7*J9 + 1/405*J2^3*J10 - 
	2/27*J3^2*J10 - 8/45*J2*J4*J10 + 64/45*J6*J10 eq 0 and
	-1/29160*J2^3*J3*J4^2 + 1/972*J3^3*J4^2 + 1/648*J2*J3*J4^3 - 
	1/2160*J2^2*J4^2*J5 + 1/1134*J3*J4^2*J6 - 1/2430*J2^3*J5*J6 + 
	1/81*J3^2*J5*J6 + 31/3780*J2*J4*J5*J6 + 4/135*J5*J6^2 + 
	1/1620*J2^3*J4*J7 - 1/54*J3^2*J4*J7 - 1/140*J2*J4^2*J7 + 
	1/180*J2^2*J6*J7 - 17/315*J4*J6*J7 + 1/12*J3*J7^2 - 1/6*J3*J6*J8 - 
	1/12*J2*J7*J8 - 1/9720*J2^4*J9 + 1/324*J2*J3^2*J9 + 1/540*J2^2*J4*J9 + 
	2/105*J4^2*J9 - 1/12*J3*J5*J9 - 8/135*J2*J6*J9 + J8*J9 + 1/12*J3*J4*J10 
	+ 1/24*J2*J5*J10 - 1/2*J7*J10 eq 0 and
	1/972000*J2^7*J4 - 1/16200*J2^4*J3^2*J4 + 1/1080*J2*J3^4*J4 - 
	1/10800*J2^5*J4^2 + 1/360*J2^2*J3^2*J4^2 + 311/168000*J2^3*J4^3 + 
	39/5600*J3^2*J4^3 - 153/2800*J2*J4^4 + 1/1200*J2^3*J3*J4*J5 - 
	1/40*J3^3*J4*J5 - 3/80*J2*J3*J4^2*J5 + 9/1600*J2^2*J4*J5^2 + 
	729/5600*J4^2*J5^2 + 13/324000*J2^6*J6 - 13/5400*J2^3*J3^2*J6 + 
	13/360*J3^4*J6 - 3247/756000*J2^4*J4*J6 + 3247/25200*J2*J3^2*J4*J6 + 
	941/8400*J2^2*J4^2*J6 - 9/50*J4^3*J6 - 1551/5600*J3*J4*J5*J6 - 
	351/1600*J2*J5^2*J6 + 1/288*J2^3*J6^2 - 5/48*J3^2*J6^2 + 
	211/840*J2*J4*J6^2 + J6^3 + 513/800*J3*J4^2*J7 + 3/800*J2^3*J5*J7 - 
	9/80*J3^2*J5*J7 + 81/1600*J2*J4*J5*J7 - 27/16*J5*J6*J7 + 
	13/800*J2^3*J4*J8 - 39/80*J3^2*J4*J8 - 549/400*J2*J4^2*J8 + 
	243/160*J5^2*J8 + 9/2*J4*J6*J8 - 1/400*J2^3*J3*J9 + 3/40*J3^3*J9 + 
	9/80*J2*J3*J4*J9 - 27/800*J2^2*J5*J9 + 81/100*J4*J5*J9 - 9/4*J3*J6*J9 + 
	1/400*J2^4*J10 - 3/40*J2*J3^2*J10 - 9/80*J2^2*J4*J10 - 81/25*J4^2*J10 + 
	81/80*J3*J5*J10 + 9/4*J2*J6*J10 eq 0 and
	-11/118098000*J2^7*J4 + 11/1968300*J2^4*J3^2*J4 - 11/131220*J2*J3^4*J4 + 
	19/2624400*J2^5*J4^2 - 19/87480*J2^2*J3^2*J4^2 - 23/637875*J2^3*J4^3 - 
	43/14175*J3^2*J4^3 - 1/3780*J2*J4^4 - 11/145800*J2^3*J3*J4*J5 + 
	11/4860*J3^3*J4*J5 + 19/6480*J2*J3*J4^2*J5 - 11/21600*J2^2*J4*J5^2 + 
	1/1400*J4^2*J5^2 - 7/4374000*J2^6*J6 + 7/72900*J2^3*J3^2*J6 - 
	7/4860*J3^4*J6 + 15137/91854000*J2^4*J4*J6 - 15137/3061800*J2*J3^2*J4*J6
	- 4231/1020600*J2^2*J4^2*J6 - 86/33075*J4^3*J6 - 433/226800*J3*J4*J5*J6 
	+ 103/7200*J2*J5^2*J6 + 1/24300*J2^3*J6^2 - 1/810*J3^2*J6^2 - 
	511/18225*J2*J4*J6^2 - 103/25200*J3*J4^2*J7 - 11/32400*J2^3*J5*J7 + 
	11/1080*J3^2*J5*J7 + 3/800*J2*J4*J5*J7 + 1/180*J2*J3*J6*J7 + 
	1/360*J5*J6*J7 + 1/360*J2^2*J7^2 - 1/40*J4*J7^2 - 23/97200*J2^3*J4*J8 + 
	23/3240*J3^2*J4*J8 + 191/5400*J2*J4^2*J8 - 11/80*J5^2*J8 - 
	1/180*J2^2*J6*J8 + 61/189*J4*J6*J8 - 1/12*J3*J7*J8 + 1/8100*J2^3*J3*J9 -
	1/270*J3^3*J9 - 1/120*J2*J3*J4*J9 + 1/3600*J2^2*J5*J9 + 2/75*J4*J5*J9 + 
	2/45*J3*J6*J9 - 1/60*J2*J7*J9 - 11/48600*J2^4*J10 + 11/1620*J2*J3^2*J10 
	+ 7/540*J2^2*J4*J10 - 46/525*J4^2*J10 - 1/20*J3*J5*J10 - 
	14/135*J2*J6*J10 + J8*J10 eq 0 and
	1/10497600*J2^7*J4 - 1/174960*J2^4*J3^2*J4 + 1/11664*J2*J3^4*J4 - 
	1/139968*J2^5*J4^2 + 5/23328*J2^2*J3^2*J4^2 - 37/907200*J2^3*J4^3 + 
	461/90720*J3^2*J4^3 - 13/15120*J2*J4^4 + 1/12960*J2^3*J3*J4*J5 - 
	1/432*J3^3*J4*J5 - 5/1728*J2*J3*J4^2*J5 + 1/1920*J2^2*J4*J5^2 + 
	31/1120*J4^2*J5^2 + 13/3499200*J2^6*J6 - 13/58320*J2^3*J3^2*J6 + 
	13/3888*J3^4*J6 - 3107/8164800*J2^4*J4*J6 + 3107/272160*J2*J3^2*J4*J6 + 
	2603/272160*J2^2*J4^2*J6 + 1/1890*J4^3*J6 - 13/2240*J3*J4*J5*J6 - 
	157/5760*J2*J5^2*J6 + 31/38880*J2^3*J6^2 - 31/1296*J3^2*J6^2 + 
	61/3780*J2*J4*J6^2 + 397/20160*J3*J4^2*J7 + 1/2880*J2^3*J5*J7 - 
	1/96*J3^2*J5*J7 + 29/1920*J2*J4*J5*J7 - 1/144*J2*J3*J6*J7 - 
	1/96*J5*J6*J7 - 1/288*J2^2*J7^2 - 1/32*J4*J7^2 + 13/8640*J2^3*J4*J8 - 
	13/288*J3^2*J4*J8 - 163/1440*J2*J4^2*J8 + 9/64*J5^2*J8 + 
	1/144*J2^2*J6*J8 + 1/12*J4*J6*J8 + 5/48*J3*J7*J8 - 1/9720*J2^3*J3*J9 + 
	1/324*J3^3*J9 + 7/864*J2*J3*J4*J9 + 1/2880*J2^2*J5*J9 - 3/10*J4*J5*J9 - 
	5/54*J3*J6*J9 - 1/48*J2*J7*J9 + J9^2 + 1/4320*J2^4*J10 - 
	1/144*J2*J3^2*J10 - 1/72*J2^2*J4*J10 - 2/15*J4^2*J10 + 1/24*J3*J5*J10 + 
	1/6*J2*J6*J10 eq 0 and
	-1/492075*J2^6*J3*J4 + 4/32805*J2^3*J3^3*J4 - 4/2187*J3^5*J4 + 
	2/10935*J2^4*J3*J4^2 - 4/729*J2*J3^3*J4^2 - 1/243*J2^2*J3*J4^3 + 
	6/35*J3*J4^4 - 1/18225*J2^5*J4*J5 + 2/1215*J2^2*J3^2*J4*J5 + 
	509/85050*J2^3*J4^2*J5 - 299/2835*J3^2*J4^2*J5 - 104/675*J2*J4^3*J5 - 
	1/90*J2*J3*J4*J5^2 + 3/10*J4*J5^3 + 937/382725*J2^3*J3*J4*J6 - 
	1874/25515*J3^3*J4*J6 - 937/8505*J2*J3*J4^2*J6 + 59/18225*J2^4*J5*J6 - 
	118/1215*J2*J3^2*J5*J6 - 3193/28350*J2^2*J4*J5*J6 - 1892/4725*J4^2*J5*J6
	+ 59/45*J3*J5^2*J6 - 9272/8505*J3*J4*J6^2 + 20/81*J2*J5*J6^2 + 
	1/54675*J2^6*J7 - 4/3645*J2^3*J3^2*J7 + 4/243*J3^4*J7 - 
	119/36450*J2^4*J4*J7 + 119/1215*J2*J3^2*J4*J7 + 77/2025*J2^2*J4^2*J7 + 
	16/175*J4^3*J7 - 23/15*J3*J4*J5*J7 - 34/1215*J2^3*J6*J7 + 
	68/81*J3^2*J6*J7 + 1384/2835*J2*J4*J6*J7 + J5*J7^2 + 97/45*J3*J4^2*J8 + 
	1/135*J2^3*J5*J8 - 2/9*J3^2*J5*J8 + 49/90*J2*J4*J5*J8 - 6*J5*J6*J8 - 
	8/3*J4*J7*J8 + 1/6075*J2^5*J9 - 2/405*J2^2*J3^2*J9 - 8/675*J2^3*J4*J9 + 
	2/15*J3^2*J4*J9 + 148/225*J2*J4^2*J9 + 1/15*J2*J3*J5*J9 - 14/5*J5^2*J9 +
	32/135*J2^2*J6*J9 + 32/15*J4*J6*J9 + 4/3*J3*J7*J9 - 2/405*J2^3*J3*J10 + 
	4/27*J3^3*J10 + 2/9*J2*J3*J4*J10 - 1/15*J2^2*J5*J10 + 64/15*J4*J5*J10 - 
	64/9*J3*J6*J10 - 4/3*J2*J7*J10 eq 0 and
	-1/182250*J2^6*J3*J4 + 2/6075*J2^3*J3^3*J4 - 2/405*J3^5*J4 + 
	1/2025*J2^4*J3*J4^2 - 2/135*J2*J3^3*J4^2 - 1/90*J2^2*J3*J4^3 + 
	243/700*J3*J4^4 - 1/6750*J2^5*J4*J5 + 1/225*J2^2*J3^2*J4*J5 + 
	79/5250*J2^3*J4^2*J5 - 44/175*J3^2*J4^2*J5 - 2757/7000*J2*J4^3*J5 - 
	3/100*J2*J3*J4*J5^2 + 81/100*J4*J5^3 + 517/141750*J2^3*J3*J4*J6 - 
	517/4725*J3^3*J4*J6 - 517/3150*J2*J3*J4^2*J6 + 13/2250*J2^4*J5*J6 - 
	13/75*J2*J3^2*J5*J6 - 2213/10500*J2^2*J4*J5*J6 - 1086/875*J4^2*J5*J6 + 
	117/50*J3*J5^2*J6 - 1369/630*J3*J4*J6^2 + 1/4*J2*J5*J6^2 + 
	1/20250*J2^6*J7 - 2/675*J2^3*J3^2*J7 + 2/45*J3^4*J7 - 11/1500*J2^4*J4*J7
	+ 11/50*J2*J3^2*J4*J7 + 29/250*J2^2*J4^2*J7 + 81/250*J4^3*J7 - 
	117/50*J3*J4*J5*J7 - 2/45*J2^3*J6*J7 + 4/3*J3^2*J6*J7 + 6/5*J2*J4*J6*J7 
	+ J6^2*J7 + 171/50*J3*J4^2*J8 + 1/50*J2^3*J5*J8 - 3/5*J3^2*J5*J8 + 
	27/100*J2*J4*J5*J8 - 9*J5*J6*J8 + 1/2250*J2^5*J9 - 1/75*J2^2*J3^2*J9 - 
	29/750*J2^3*J4*J9 + 14/25*J3^2*J4*J9 + 177/125*J2*J4^2*J9 + 
	9/50*J2*J3*J5*J9 - 243/50*J5^2*J9 + 2/5*J2^2*J6*J9 + 24/5*J4*J6*J9 - 
	1/75*J2^3*J3*J10 + 2/5*J3^3*J10 + 3/5*J2*J3*J4*J10 - 9/50*J2^2*J5*J10 + 
	108/25*J4*J5*J10 - 12*J3*J6*J10 eq 0 and
	-1/7873200*J2^6*J3*J4 + 1/131220*J2^3*J3^3*J4 - 1/8748*J3^5*J4 + 
	1/77760*J2^4*J3*J4^2 - 1/2592*J2*J3^3*J4^2 - 5/15552*J2^2*J3*J4^3 + 
	1/280*J3*J4^4 - 1/291600*J2^5*J4*J5 + 1/9720*J2^2*J3^2*J4*J5 + 
	527/1814400*J2^3*J4^2*J5 - 53/15120*J3^2*J4^2*J5 - 1/200*J2*J4^3*J5 - 
	1/1440*J2*J3*J4*J5^2 + 3/160*J4*J5^3 + 307/6123600*J2^3*J3*J4*J6 - 
	307/204120*J3^3*J4*J6 - 13/5670*J2*J3*J4^2*J6 + 1/12150*J2^4*J5*J6 - 
	1/405*J2*J3^2*J5*J6 - 589/226800*J2^2*J4*J5*J6 - 33/1400*J4^2*J5*J6 + 
	19/720*J3*J5^2*J6 - 11/486*J3*J4*J6^2 - 17/2160*J2*J5*J6^2 + 
	1/874800*J2^6*J7 - 1/14580*J2^3*J3^2*J7 + 1/972*J3^4*J7 - 
	7/48600*J2^4*J4*J7 + 7/1620*J2*J3^2*J4*J7 + 241/151200*J2^2*J4^2*J7 + 
	3/1400*J4^3*J7 - 1/80*J3*J4*J5*J7 - 23/38880*J2^3*J6*J7 + 
	7/648*J3^2*J6*J7 + 97/5040*J2*J4*J6*J7 - 1/288*J2*J3*J7^2 + 
	37/720*J3*J4^2*J8 + 1/2160*J2^3*J5*J8 - 1/72*J3^2*J5*J8 - 
	7/480*J2*J4*J5*J8 + 1/144*J2*J3*J6*J8 + 1/48*J5*J6*J8 + 1/288*J2^2*J7*J8
	- 1/16*J4*J7*J8 + 17/1166400*J2^5*J9 - 17/38880*J2^2*J3^2*J9 - 
	7/7200*J2^3*J4*J9 + 7/540*J3^2*J4*J9 + 13/600*J2*J4^2*J9 + 
	11/1440*J2*J3*J5*J9 - 9/80*J5^2*J9 + 29/3240*J2^2*J6*J9 + 
	41/315*J4*J6*J9 - 1/12*J3*J7*J9 - 1/3240*J2^3*J3*J10 + 1/108*J3^3*J10 + 
	1/96*J2*J3*J4*J10 - 17/2880*J2^2*J5*J10 - 3/20*J4*J5*J10 - 
	7/36*J3*J6*J10 + 1/16*J2*J7*J10 + J9*J10 eq 0 and
	-1/295245000*J2^10 + 1/3280500*J2^7*J3^2 - 1/109350*J2^4*J3^4 + 
	1/10935*J2*J3^6 + 1/2187000*J2^8*J4 - 1/36450*J2^5*J3^2*J4 + 
	1/2430*J2^2*J3^4*J4 - 257/30618000*J2^6*J4^2 - 29/255150*J2^3*J3^2*J4^2 
	+ 373/34020*J3^4*J4^2 - 353/486000*J2^4*J4^3 + 503/16200*J2*J3^2*J4^3 + 
	23/1050*J2^2*J4^4 + 18/625*J4^5 - 1/243000*J2^6*J3*J5 + 
	1/4050*J2^3*J3^3*J5 - 1/270*J3^5*J5 + 1/2700*J2^4*J3*J4*J5 - 
	1/90*J2*J3^3*J4*J5 - 1/120*J2^2*J3*J4^2*J5 + 209/8400*J3*J4^3*J5 - 
	1/18000*J2^5*J5^2 + 1/600*J2^2*J3^2*J5^2 + 1/240*J2^3*J4*J5^2 - 
	1/20*J3^2*J4*J5^2 - 793/5600*J2*J4^2*J5^2 - 3/400*J2*J3*J5^3 + 
	81/400*J5^4 - 1/1049760*J2^7*J6 + 1/17496*J2^4*J3^2*J6 - 
	5/5832*J2*J3^4*J6 + 1/11664*J2^5*J4*J6 - 5/1944*J2^2*J3^2*J4*J6 - 
	349/85050*J2^3*J4^2*J6 + 2959/45360*J3^2*J4^2*J6 + 103/1350*J2*J4^3*J6 -
	1/1296*J2^3*J3*J5*J6 + 5/216*J3^3*J5*J6 + 5/144*J2*J3*J4*J5*J6 - 
	1/192*J2^2*J5^2*J6 - 41/140*J4*J5^2*J6 - 13/14580*J2^4*J6^2 + 
	13/486*J2*J3^2*J6^2 + 13/324*J2^2*J4*J6^2 + 88/945*J4^2*J6^2 - 
	13/36*J3*J5*J6^2 + 19/6480*J2^3*J3*J4*J7 - 19/216*J3^3*J4*J7 - 
	19/144*J2*J3*J4^2*J7 + 1/720*J2^4*J5*J7 - 1/24*J2*J3^2*J5*J7 - 
	11/480*J2^2*J4*J5*J7 - 3/8*J4^2*J5*J7 + 9/16*J3*J5^2*J7 + 
	19/72*J3*J4*J6*J7 + 1/16*J2*J5*J6*J7 + 1/19440*J2^6*J8 - 
	1/324*J2^3*J3^2*J8 + 5/108*J3^4*J8 - 49/6480*J2^4*J4*J8 + 
	49/216*J2*J3^2*J4*J8 + 17/72*J2^2*J4^2*J8 + 7/5*J4^3*J8 - 
	19/16*J3*J4*J5*J8 - 9/32*J2*J5^2*J8 + 1/216*J2^3*J6*J8 - 5/36*J3^2*J6*J8
	- 17/36*J2*J4*J6*J8 - 7/10*J3*J4^2*J9 - 1/180*J2^3*J5*J9 + 
	1/6*J3^2*J5*J9 + 1/20*J2*J4*J5*J9 + J5*J6*J9 - 2/135*J2^3*J4*J10 + 
	4/9*J3^2*J4*J10 + 41/30*J2*J4^2*J10 - 9/4*J5^2*J10 - 4/3*J4*J6*J10 eq 0 and
	11/3321506250*J2^10 - 11/36905625*J2^7*J3^2 + 22/2460375*J2^4*J3^4 - 
	44/492075*J2*J3^6 - 61/147622500*J2^8*J4 + 61/2460375*J2^5*J3^2*J4 - 
	61/164025*J2^2*J3^4*J4 + 62/9568125*J2^6*J4^2 + 
	236/1913625*J2^3*J3^2*J4^2 - 1216/127575*J3^4*J4^2 + 
	3733/5467500*J2^4*J4^3 - 2504/91125*J2*J3^2*J4^3 - 9623/425250*J2^2*J4^4
	- 88/3125*J4^5 + 11/2733750*J2^6*J3*J5 - 22/91125*J2^3*J3^3*J5 + 
	22/6075*J3^5*J5 - 61/182250*J2^4*J3*J4*J5 + 61/6075*J2*J3^3*J4*J5 + 
	14/2025*J2^2*J3*J4^2*J5 - 1619/94500*J3*J4^3*J5 + 11/202500*J2^5*J5^2 - 
	11/6750*J2^2*J3^2*J5^2 - 7/1800*J2^3*J4*J5^2 + 11/225*J3^2*J4*J5^2 + 
	8713/63000*J2*J4^2*J5^2 + 11/1500*J2*J3*J5^3 - 99/500*J5^4 + 
	181/59049000*J2^7*J6 - 181/984150*J2^4*J3^2*J6 + 181/65610*J2*J3^4*J6 - 
	202/637875*J2^5*J4*J6 + 404/42525*J2^2*J3^2*J4*J6 + 
	4111/425250*J2^3*J4^2*J6 - 8287/170100*J3^2*J4^2*J6 - 
	11182/212625*J2*J4^3*J6 + 7/8100*J2^3*J3*J5*J6 - 7/270*J3^3*J5*J6 - 
	1571/28350*J2*J3*J4*J5*J6 - 11/2160*J2^2*J5^2*J6 + 158/1575*J4*J5^2*J6 +
	134/164025*J2^4*J6^2 - 268/10935*J2*J3^2*J6^2 - 2372/127575*J2^2*J4*J6^2
	- 32/405*J4^2*J6^2 + 28/135*J3*J5*J6^2 - 71/24300*J2^3*J3*J4*J7 + 
	71/810*J3^3*J4*J7 + 113/675*J2*J3*J4^2*J7 - 1/810*J2^4*J5*J7 + 
	1/27*J2*J3^2*J5*J7 + 83/2700*J2^2*J4*J5*J7 + 587/1050*J4^2*J5*J7 - 
	11/20*J3*J5^2*J7 - 11/1890*J3*J4*J6*J7 - 3/20*J2*J5*J6*J7 + 
	1/270*J2^3*J7^2 - 1/9*J3^2*J7^2 - 11/90*J2*J4*J7^2 - 11/218700*J2^6*J8 +
	11/3645*J2^3*J3^2*J8 - 11/243*J3^4*J8 + 301/36450*J2^4*J4*J8 - 
	301/1215*J2*J3^2*J4*J8 - 619/2025*J2^2*J4^2*J8 - 364/225*J4^3*J8 + 
	193/180*J3*J4*J5*J8 + 13/40*J2*J5^2*J8 - 11/2430*J2^3*J6*J8 + 
	11/81*J3^2*J6*J8 + 241/405*J2*J4*J6*J8 + J5*J7*J8 - 1/12150*J2^4*J3*J9 +
	1/405*J2*J3^3*J9 + 1/270*J2^2*J3*J4*J9 + 8/15*J3*J4^2*J9 + 
	7/2700*J2^3*J5*J9 - 1/9*J3^2*J5*J9 + 16/225*J2*J4*J5*J9 - 
	16/135*J2*J3*J6*J9 - 1/45*J2^2*J7*J9 - 16/15*J4*J7*J9 + 1/12150*J2^5*J10
	- 1/405*J2^2*J3^2*J10 + 17/1215*J2^3*J4*J10 - 43/81*J3^2*J4*J10 - 
	1052/675*J2*J4^2*J10 + 1/30*J2*J3*J5*J10 + 2*J5^2*J10 + 
	16/135*J2^2*J6*J10 + 224/135*J4*J6*J10 + 2/3*J3*J7*J10 eq 0 and
	1/246037500*J2^10 - 1/2733750*J2^7*J3^2 + 1/91125*J2^4*J3^4 - 
	2/18225*J2*J3^6 - 23/65610000*J2^8*J4 + 23/1093500*J2^5*J3^2*J4 - 
	23/72900*J2^2*J3^4*J4 - 17/2551500*J2^6*J4^2 + 103/170100*J2^3*J3^2*J4^2
	- 23/1890*J3^4*J4^2 + 11819/11340000*J2^4*J4^3 - 
	3823/126000*J2*J3^2*J4^3 - 23/750*J2^2*J4^4 - 81/21875*J4^5 + 
	1/202500*J2^6*J3*J5 - 1/3375*J2^3*J3^3*J5 + 1/225*J3^5*J5 - 
	23/81000*J2^4*J3*J4*J5 + 23/2700*J2*J3^3*J4*J5 + 1/360*J2^2*J3*J4^2*J5 -
	57/875*J3*J4^3*J5 + 1/15000*J2^5*J5^2 - 1/500*J2^2*J3^2*J5^2 - 
	47/12000*J2^3*J4*J5^2 + 3/50*J3^2*J4*J5^2 + 189/1000*J2*J4^2*J5^2 + 
	9/1000*J2*J3*J5^3 - 243/1000*J5^4 + 89/10935000*J2^7*J6 - 
	89/182250*J2^4*J3^2*J6 + 89/12150*J2*J3^4*J6 - 44101/51030000*J2^5*J4*J6
	+ 44101/1701000*J2^2*J3^2*J4*J6 + 76333/2835000*J2^3*J4^2*J6 - 
	8537/63000*J3^2*J4^2*J6 - 464/2625*J2*J4^3*J6 + 1/3000*J2^3*J3*J5*J6 - 
	1/100*J3^3*J5*J6 - 8611/126000*J2*J3*J4*J5*J6 - 1/25*J2^2*J5^2*J6 + 
	963/1750*J4*J5^2*J6 + 149/97200*J2^4*J6^2 - 149/3240*J2*J3^2*J6^2 + 
	269/28350*J2^2*J4*J6^2 - 26/75*J4^2*J6^2 + 7/20*J3*J5*J6^2 - 
	29/9000*J2^3*J3*J4*J7 + 29/300*J3^3*J4*J7 + 537/2000*J2*J3*J4^2*J7 - 
	17/18000*J2^4*J5*J7 + 17/600*J2*J3^2*J5*J7 + 33/800*J2^2*J4*J5*J7 + 
	27/500*J4^2*J5*J7 - 27/40*J3*J5^2*J7 + 1/4*J3*J4*J6*J7 - 1/4*J2*J5*J6*J7
	- 1/16200*J2^6*J8 + 1/270*J2^3*J3^2*J8 - 1/18*J3^4*J8 + 
	643/54000*J2^4*J4*J8 - 643/1800*J2*J3^2*J4*J8 - 1603/3000*J2^2*J4^2*J8 -
	99/250*J4^3*J8 + 261/200*J3*J4*J5*J8 + 63/100*J2*J5^2*J8 + 
	1/180*J2^3*J6*J8 - 1/6*J3^2*J6*J8 + 11/30*J2*J4*J6*J8 + J6^2*J8 - 
	13/27000*J2^4*J3*J9 + 13/900*J2*J3^3*J9 + 13/600*J2^2*J3*J4*J9 + 
	72/125*J3*J4^2*J9 - 1/2000*J2^3*J5*J9 - 9/50*J3^2*J5*J9 + 
	3/250*J2*J4*J5*J9 - 13/30*J2*J3*J6*J9 + 13/27000*J2^5*J10 - 
	13/900*J2^2*J3^2*J10 - 37/3000*J2^3*J4*J10 - 7/25*J3^2*J4*J10 - 
	81/50*J2*J4^2*J10 + 39/200*J2*J3*J5*J10 + 243/100*J5^2*J10 + 
	13/30*J2^2*J6*J10 - 12/5*J4*J6*J10 eq 0 and
	11/738112500*J2^10 - 11/8201250*J2^7*J3^2 + 11/273375*J2^4*J3^4 - 
	22/54675*J2*J3^6 - 13/10935000*J2^8*J4 + 13/182250*J2^5*J3^2*J4 - 
	13/12150*J2^2*J3^4*J4 - 358/9568125*J2^6*J4^2 + 
	1747/637875*J2^3*J3^2*J4^2 - 2062/42525*J3^4*J4^2 + 
	36853/8505000*J2^4*J4^3 - 8557/70875*J2*J3^2*J4^3 - 423/3500*J2^2*J4^4 -
	972/21875*J4^5 + 11/607500*J2^6*J3*J5 - 11/10125*J2^3*J3^3*J5 + 
	11/675*J3^5*J5 - 13/13500*J2^4*J3*J4*J5 + 13/450*J2*J3^3*J4*J5 + 
	1/150*J2^2*J3*J4^2*J5 - 989/4200*J3*J4^3*J5 + 11/45000*J2^5*J5^2 - 
	11/1500*J2^2*J3^2*J5^2 - 83/6000*J2^3*J4*J5^2 + 11/50*J3^2*J4*J5^2 + 
	10027/14000*J2*J4^2*J5^2 + 33/1000*J2*J3*J5^3 - 891/1000*J5^4 + 
	2093/65610000*J2^7*J6 - 2093/1093500*J2^4*J3^2*J6 + 
	2093/72900*J2*J3^4*J6 - 42557/12757500*J2^5*J4*J6 + 
	42557/425250*J2^2*J3^2*J4*J6 + 420157/4252500*J2^3*J4^2*J6 - 
	226033/567000*J3^2*J4^2*J6 - 11897/23625*J2*J4^3*J6 + 
	187/81000*J2^3*J3*J5*J6 - 187/2700*J3^3*J5*J6 - 
	4601/15750*J2*J3*J4*J5*J6 - 573/4000*J2^2*J5^2*J6 + 1209/875*J4*J5^2*J6 
	+ 121/18225*J2^4*J6^2 - 242/1215*J2*J3^2*J6^2 + 82/14175*J2^2*J4*J6^2 - 
	944/945*J4^2*J6^2 + 86/45*J3*J5*J6^2 - 1001/81000*J2^3*J3*J4*J7 + 
	1001/2700*J3^3*J4*J7 + 4511/4500*J2*J3*J4^2*J7 - 7/2250*J2^4*J5*J7 + 
	7/75*J2*J3^2*J5*J7 + 173/1500*J2^2*J4*J5*J7 + 537/500*J4^2*J5*J7 - 
	99/40*J3*J5^2*J7 - 667/1260*J3*J4*J6*J7 - 41/40*J2*J5*J6*J7 - 
	1/180*J2^3*J7^2 + 1/6*J3^2*J7^2 + 1/20*J2*J4*J7^2 + J6*J7^2 - 
	11/48600*J2^6*J8 + 11/810*J2^3*J3^2*J8 - 11/54*J3^4*J8 + 
	901/20250*J2^4*J4*J8 - 901/675*J2*J3^2*J4*J8 - 2239/1125*J2^2*J4^2*J8 - 
	482/125*J4^3*J8 + 1101/200*J3*J4*J5*J8 + 981/400*J2*J5^2*J8 + 
	7/540*J2^3*J6*J8 - 7/18*J3^2*J6*J8 + 223/90*J2*J4*J6*J8 - 
	1/500*J2^4*J3*J9 + 3/50*J2*J3^3*J9 + 9/100*J2^2*J3*J4*J9 + 
	362/125*J3*J4^2*J9 - 1/1000*J2^3*J5*J9 - 39/50*J3^2*J5*J9 + 
	3/125*J2*J4*J5*J9 - 8/5*J2*J3*J6*J9 + 1/10*J2^2*J7*J9 - 12/5*J4*J7*J9 + 
	1/500*J2^5*J10 - 3/50*J2^2*J3^2*J10 - 397/6750*J2^3*J4*J10 - 
	421/450*J3^2*J4*J10 - 2378/375*J2*J4^2*J10 + 81/100*J2*J3*J5*J10 + 
	207/25*J5^2*J10 + 8/5*J2^2*J6*J10 + 16/15*J4*J6*J10 - 3*J3*J7*J10 eq 0 and
	-11/53144100000*J2^10 + 11/590490000*J2^7*J3^2 - 11/19683000*J2^4*J3^4 + 
	11/1968300*J2*J3^6 + 293/7085880000*J2^8*J4 - 293/118098000*J2^5*J3^2*J4
	+ 293/7873200*J2^2*J3^4*J4 - 20809/11022480000*J2^6*J4^2 + 
	14983/367416000*J2^3*J3^2*J4^2 + 971/2041200*J3^4*J4^2 - 
	23419/2449440000*J2^4*J4^3 + 4847/3024000*J2*J3^2*J4^3 + 
	3047/4536000*J2^2*J4^4 - 24/21875*J4^5 - 11/43740000*J2^6*J3*J5 + 
	11/729000*J2^3*J3^3*J5 - 11/48600*J3^5*J5 + 293/8748000*J2^4*J3*J4*J5 - 
	293/291600*J2*J3^3*J4*J5 - 761/777600*J2^2*J3*J4^2*J5 + 
	1403/504000*J3*J4^3*J5 - 11/3240000*J2^5*J5^2 + 11/108000*J2^2*J3^2*J5^2
	+ 17/51840*J2^3*J4*J5^2 - 11/3600*J3^2*J4*J5^2 - 529/84000*J2*J4^2*J5^2 
	- 11/24000*J2*J3*J5^3 + 99/8000*J5^4 + 43/188956800*J2^7*J6 - 
	43/3149280*J2^4*J3^2*J6 + 43/209952*J2*J3^4*J6 - 
	1513/68890500*J2^5*J4*J6 + 1513/2296350*J2^2*J3^2*J4*J6 + 
	3257/12247200*J2^3*J4^2*J6 + 1417/181440*J3^2*J4^2*J6 + 
	5927/567000*J2*J4^3*J6 - 13/388800*J2^3*J3*J5*J6 + 13/12960*J3^3*J5*J6 +
	227/170100*J2*J3*J4*J5*J6 - 37/19200*J2^2*J5^2*J6 - 379/8400*J4*J5^2*J6 
	- 361/20995200*J2^4*J6^2 + 361/699840*J2*J3^2*J6^2 + 
	11699/2449440*J2^2*J4*J6^2 + 521/19845*J4^2*J6^2 - 1/360*J3*J5*J6^2 + 
	67/388800*J2^3*J3*J4*J7 - 67/12960*J3^3*J4*J7 - 949/151200*J2*J3*J4^2*J7
	+ 13/97200*J2^4*J5*J7 - 13/3240*J2*J3^2*J5*J7 - 47/14400*J2^2*J4*J5*J7 +
	19/800*J4^2*J5*J7 + 11/320*J3*J5^2*J7 - 1/4320*J2^2*J3*J6*J7 - 
	1607/30240*J3*J4*J6*J7 - 7/8640*J2*J5*J6*J7 - 1/1728*J2^3*J7^2 + 
	1/72*J3^2*J7^2 + 1/320*J2*J4*J7^2 + 11/3499200*J2^6*J8 - 
	11/58320*J2^3*J3^2*J8 + 11/3888*J3^4*J8 - 101/291600*J2^4*J4*J8 + 
	101/9720*J2*J3^2*J4*J8 + 223/32400*J2^2*J4^2*J8 - 17/300*J4^3*J8 - 
	9/320*J3*J4*J5*J8 + 1/384*J2*J5^2*J8 + 1/1944*J2^3*J6*J8 - 
	11/1296*J3^2*J6*J8 - 7/6480*J2*J4*J6*J8 + 1/288*J2*J3*J7*J8 - 
	11/388800*J2^4*J3*J9 + 11/12960*J2*J3^3*J9 + 1/720*J2^2*J3*J4*J9 - 
	1/1800*J3*J4^2*J9 - 1/2400*J2^3*J5*J9 + 1/360*J3^2*J5*J9 - 
	1/900*J2*J4*J5*J9 - 19/2160*J2*J3*J6*J9 + 11/1440*J2^2*J7*J9 - 
	1/20*J4*J7*J9 + 19/583200*J2^5*J10 - 19/19440*J2^2*J3^2*J10 - 
	337/129600*J2^3*J4*J10 + 11/360*J3^2*J4*J10 + 1/18*J2*J4^2*J10 + 
	11/960*J2*J3*J5*J10 - 9/40*J5^2*J10 + 73/6480*J2^2*J6*J10 + 
	46/105*J4*J6*J10 - 1/4*J3*J7*J10 + J10^2 eq 0 and
	1/7873200*J2^7*J3*J4 - 1/131220*J2^4*J3^3*J4 + 1/8748*J2*J3^5*J4 - 
	1/87480*J2^5*J3*J4^2 + 1/2916*J2^2*J3^3*J4^2 + 7/34992*J2^3*J3*J4^3 + 
	5/2916*J3^3*J4^3 - 277/34020*J2*J3*J4^4 + 1/437400*J2^6*J4*J5 - 
	1/29160*J2^3*J3^2*J4*J5 - 1/972*J3^4*J4*J5 - 55/163296*J2^4*J4^2*J5 + 
	149/27216*J2*J3^2*J4^2*J5 + 359/37800*J2^2*J4^3*J5 + 9/350*J4^4*J5 + 
	1/1440*J2^2*J3*J4*J5^2 - 67/2520*J3*J4^2*J5^2 - 1/80*J2*J4*J5^3 + 
	7/2624400*J2^6*J3*J6 - 7/43740*J2^3*J3^3*J6 + 7/2916*J3^5*J6 - 
	2407/6123600*J2^4*J3*J4*J6 + 2407/204120*J2*J3^3*J4*J6 + 
	209/17010*J2^2*J3*J4^2*J6 + 5/3402*J3*J4^3*J6 - 19/145800*J2^5*J5*J6 + 
	19/4860*J2^2*J3^2*J5*J6 + 9761/2041200*J2^3*J4*J5*J6 - 
	803/27216*J3^2*J4*J5*J6 - 121/9450*J2*J4^2*J5*J6 - 97/1440*J2*J3*J5^2*J6
	+ 11/60*J5^3*J6 - 1/14580*J2^3*J3*J6^2 + 1/486*J3^3*J6^2 + 
	2423/34020*J2*J3*J4*J6^2 - 53/3240*J2^2*J5*J6^2 - 16/567*J4*J5*J6^2 - 
	1/1312200*J2^7*J7 + 1/21870*J2^4*J3^2*J7 - 1/1458*J2*J3^4*J7 + 
	13/97200*J2^5*J4*J7 - 13/3240*J2^2*J3^2*J4*J7 + 1/170100*J2^3*J4^2*J7 + 
	13/45360*J3^2*J4^2*J7 - 31/1050*J2*J4^3*J7 + 1/6480*J2^3*J3*J5*J7 - 
	1/216*J3^3*J5*J7 + 107/1440*J2*J3*J4*J5*J7 - 7/20*J4*J5^2*J7 + 
	17/14580*J2^4*J6*J7 - 17/486*J2*J3^2*J6*J7 + 23/5670*J2^2*J4*J6*J7 - 
	136/945*J4^2*J6*J7 + 7/72*J3*J5*J6*J7 + 19/72*J3*J4*J7^2 + 
	7/6480*J2^3*J3*J4*J8 - 7/216*J3^3*J4*J8 - 11/60*J2*J3*J4^2*J8 - 
	1/3240*J2^4*J5*J8 + 1/108*J2*J3^2*J5*J8 - 19/720*J2^2*J4*J5*J8 + 
	67/60*J4^2*J5*J8 + 1/16*J3*J5^2*J8 - 1/4*J3*J4*J6*J8 + 1/24*J2*J5*J6*J8 
	+ 1/216*J2^3*J7*J8 - 5/36*J3^2*J7*J8 - 11/36*J2*J4*J7*J8 - 
	1/291600*J2^6*J9 - 1/9720*J2^3*J3^2*J9 + 1/162*J3^4*J9 + 
	1/16200*J2^4*J4*J9 + 13/1080*J2*J3^2*J4*J9 - 19/675*J2^2*J4^2*J9 - 
	4/225*J4^3*J9 - 1/240*J2^2*J3*J5*J9 - 37/180*J3*J4*J5*J9 + 
	3/40*J2*J5^2*J9 - 1/81*J2^3*J6*J9 - 2/27*J3^2*J6*J9 - 1/9*J2*J4*J6*J9 - 
	1/12*J2*J3*J7*J9 + J5*J7*J9 + 1/3240*J2^4*J3*J10 - 1/108*J2*J3^3*J10 - 
	1/72*J2^2*J3*J4*J10 + 1/9*J3*J4^2*J10 - 1/2160*J2^3*J5*J10 + 
	5/36*J3^2*J5*J10 + 11/90*J2*J4*J5*J10 + 4/9*J2*J3*J6*J10 - 2*J5*J6*J10 +
	1/12*J2^2*J7*J10 - 4/3*J4*J7*J10 eq 0 and
	1/1399680*J2^7*J3*J4 - 1/23328*J2^4*J3^3*J4 + 5/7776*J2*J3^5*J4 - 
	1/15552*J2^5*J3*J4^2 + 5/2592*J2^2*J3^3*J4^2 + 1451/1209600*J2^3*J3*J4^3
	+ 299/40320*J3^3*J4^3 - 229/6720*J2*J3*J4^4 + 1/108000*J2^6*J4*J5 + 
	1/43200*J2^3*J3^2*J4*J5 - 13/1440*J3^4*J4*J5 - 251/252000*J2^4*J4^2*J5 +
	43/11200*J2*J3^2*J4^2*J5 + 279/11200*J2^2*J4^3*J5 + 81/3500*J4^4*J5 + 
	1/256*J2^2*J3*J4*J5^2 + 549/22400*J3*J4^2*J5^2 - 81/1600*J2*J4*J5^3 + 
	17/1296000*J2^6*J3*J6 - 17/21600*J2^3*J3^3*J6 + 17/1440*J3^5*J6 - 
	9011/5443200*J2^4*J3*J4*J6 + 9011/181440*J2*J3^3*J4*J6 + 
	2899/60480*J2^2*J3*J4^2*J6 + 1/840*J3*J4^3*J6 - 43/108000*J2^5*J5*J6 + 
	43/3600*J2^2*J3^2*J5*J6 + 1571/100800*J2^3*J4*J5*J6 - 
	47/384*J3^2*J4*J5*J6 - 3/700*J2*J4^2*J5*J6 - 1491/6400*J2*J3*J5^2*J6 + 
	81/400*J5^3*J6 + 1/1152*J2^3*J3*J6^2 - 5/192*J3^3*J6^2 + 
	1475/6048*J2*J3*J4*J6^2 - 1/48*J2^2*J5*J6^2 - 41/140*J4*J5*J6^2 - 
	1/324000*J2^7*J7 + 1/5400*J2^4*J3^2*J7 - 1/360*J2*J3^4*J7 + 
	103/216000*J2^5*J4*J7 - 103/7200*J2^2*J3^2*J4*J7 - 73/12000*J2^3*J4^2*J7
	+ 549/3200*J3^2*J4^2*J7 - 3/100*J2*J4^3*J7 + 13/9600*J2^3*J3*J5*J7 - 
	13/320*J3^3*J5*J7 + 1101/6400*J2*J3*J4*J5*J7 - 81/400*J4*J5^2*J7 + 
	1/288*J2^4*J6*J7 - 5/48*J2*J3^2*J6*J7 - 17/240*J2^2*J4*J6*J7 - 
	3/64*J3*J5*J6*J7 + 17/3200*J2^3*J3*J4*J8 - 51/320*J3^3*J4*J8 - 
	219/320*J2*J3*J4^2*J8 - 1/800*J2^4*J5*J8 + 3/80*J2*J3^2*J5*J8 - 
	39/1600*J2^2*J4*J5*J8 + 297/400*J4^2*J5*J8 + 351/640*J3*J5^2*J8 + 
	9/16*J3*J4*J6*J8 + 9/32*J2*J5*J6*J8 - 1/40500*J2^6*J9 - 
	11/43200*J2^3*J3^2*J9 + 43/1440*J3^4*J9 + 29/18000*J2^4*J4*J9 + 
	143/4800*J2*J3^2*J4*J9 - 3/40*J2^2*J4^2*J9 - 9/250*J4^3*J9 - 
	3/128*J2^2*J3*J5*J9 - 27/200*J3*J4*J5*J9 + 243/800*J2*J5^2*J9 - 
	13/360*J2^3*J6*J9 - 23/48*J3^2*J6*J9 - 1/20*J2*J4*J6*J9 + J6^2*J9 + 
	1/576*J2^4*J3*J10 - 5/96*J2*J3^3*J10 - 5/64*J2^2*J3*J4*J10 - 
	27/40*J3*J4^2*J10 + 1/80*J2^3*J5*J10 + 21/64*J3^2*J5*J10 - 
	9/80*J2*J4*J5*J10 + 25/16*J2*J3*J6*J10 - 9/4*J5*J6*J10 eq 0 and
	-193/196830000*J2^7*J3*J4 + 193/3280500*J2^4*J3^3*J4 - 193/218700*J2*J3^5*J4
	+ 193/2187000*J2^5*J3*J4^2 - 193/72900*J2^2*J3^3*J4^2 - 
	169/90000*J2^3*J3*J4^3 - 131/40500*J3^3*J4^3 + 1313/23625*J2*J3*J4^4 - 
	1/45000*J2^6*J4*J5 + 131/243000*J2^3*J3^2*J4*J5 + 31/8100*J3^4*J4*J5 + 
	25687/11340000*J2^4*J4^2*J5 - 451/14000*J2*J3^2*J4^2*J5 - 
	9269/157500*J2^2*J4^3*J5 + 27/8750*J4^4*J5 - 193/36000*J2^2*J3*J4*J5^2 -
	73/7000*J3*J4^2*J5^2 + 243/2000*J2*J4*J5^3 - 7/1458000*J2^6*J3*J6 + 
	7/24300*J2^3*J3^3*J6 - 7/1620*J3^5*J6 + 159631/153090000*J2^4*J3*J4*J6 -
	159631/5103000*J2*J3^3*J4*J6 - 31639/850500*J2^2*J3*J4^2*J6 - 
	131/47250*J3*J4^3*J6 + 349/405000*J2^5*J5*J6 - 349/13500*J2^2*J3^2*J5*J6
	- 61693/1890000*J2^3*J4*J5*J6 + 23899/378000*J3^2*J4*J5*J6 - 
	4279/39375*J2*J4^2*J5*J6 + 1501/4000*J2*J3*J5^2*J6 - 99/500*J5^3*J6 + 
	1/8100*J2^3*J3*J6^2 - 1/270*J3^3*J6^2 - 65179/170100*J2*J3*J4*J6^2 + 
	73/1800*J2^2*J5*J6^2 + 104/525*J4*J5*J6^2 + 1/135000*J2^7*J7 - 
	1/2250*J2^4*J3^2*J7 + 1/150*J2*J3^4*J7 - 889/810000*J2^5*J4*J7 + 
	889/27000*J2^2*J3^2*J4*J7 + 416/23625*J2^3*J4^2*J7 - 
	9377/126000*J3^2*J4^2*J7 + 96/4375*J2*J4^3*J7 - 31/54000*J2^3*J3*J5*J7 +
	31/1800*J3^3*J5*J7 - 4093/12000*J2*J3*J4*J5*J7 + 99/500*J4*J5^2*J7 - 
	1/150*J2^4*J6*J7 + 1/5*J2*J3^2*J6*J7 + 107/630*J2^2*J4*J6*J7 - 
	86/525*J4^2*J6*J7 - 17/120*J3*J5*J6*J7 + 1/8*J3*J4*J7^2 - 
	7/3600*J2^3*J3*J4*J8 + 7/120*J3^3*J4*J8 + 499/750*J2*J3*J4^2*J8 + 
	3/1000*J2^4*J5*J8 - 9/100*J2*J3^2*J5*J8 + 187/6000*J2^2*J4*J5*J8 - 
	213/500*J4^2*J5*J8 - 93/400*J3*J5^2*J8 + 3/20*J3*J4*J6*J8 - 
	41/40*J2*J5*J6*J8 + 1/360*J2^3*J7*J8 - 1/12*J3^2*J7*J8 - 
	3/20*J2*J4*J7*J8 + J6*J7*J8 + 163/2430000*J2^6*J9 - 
	133/81000*J2^3*J3^2*J9 - 1/90*J3^4*J9 - 461/81000*J2^4*J4*J9 + 
	343/5400*J2*J3^2*J4*J9 + 1183/5625*J2^2*J4^2*J9 - 28/625*J4^3*J9 + 
	193/6000*J2^2*J3*J5*J9 + 47/500*J3*J4*J5*J9 - 729/1000*J2*J5^2*J9 + 
	43/675*J2^3*J6*J9 + 2/15*J3^2*J6*J9 + 29/45*J2*J4*J6*J9 - 
	1/20*J2*J3*J7*J9 - 193/81000*J2^4*J3*J10 + 193/2700*J2*J3^3*J10 + 
	193/1800*J2^2*J3*J4*J10 + 14/125*J3*J4^2*J10 - 533/18000*J2^3*J5*J10 - 
	23/300*J3^2*J5*J10 + 68/125*J2*J4*J5*J10 - 92/45*J2*J3*J6*J10 + 
	2*J5*J6*J10 + 1/20*J2^2*J7*J10 - 6/5*J4*J7*J10 eq 0 and
	-241/49207500*J2^7*J3*J4 + 241/820125*J2^4*J3^3*J4 - 241/54675*J2*J3^5*J4 + 
	241/546750*J2^5*J3*J4^2 - 241/18225*J2^2*J3^3*J4^2 - 
	352361/38272500*J2^3*J3*J4^3 - 13607/637875*J3^3*J4^3 + 
	57713/212625*J2*J3*J4^4 - 91/911250*J2^6*J4*J5 + 
	41/20250*J2^3*J3^2*J4*J5 + 59/2025*J3^4*J4*J5 + 7411/729000*J2^4*J4^2*J5
	- 3073/24300*J2*J3^2*J4^2*J5 - 4587/17500*J2^2*J4^3*J5 + 28/625*J4^4*J5 
	- 241/9000*J2^2*J3*J4*J5^2 - 3701/31500*J3*J4^2*J5^2 + 
	273/500*J2*J4*J5^3 - 131/3280500*J2^6*J3*J6 + 131/54675*J2^3*J3^3*J6 - 
	131/3645*J3^5*J6 + 255847/38272500*J2^4*J3*J4*J6 - 
	255847/1275750*J2*J3^3*J4*J6 - 46768/212625*J2^2*J3*J4^2*J6 - 
	2152/212625*J3*J4^3*J6 + 1189/303750*J2^5*J5*J6 - 
	1189/10125*J2^2*J3^2*J5*J6 - 210857/1417500*J2^3*J4*J5*J6 + 
	40631/94500*J3^2*J4*J5*J6 - 22151/50625*J2*J4^2*J5*J6 + 
	5411/3000*J2*J3*J5^2*J6 - 253/375*J5^3*J6 - 16/18225*J2^3*J3*J6^2 + 
	32/1215*J3^3*J6^2 - 78982/42525*J2*J3*J4*J6^2 + 127/675*J2^2*J5*J6^2 + 
	16/21*J4*J5*J6^2 + 91/2733750*J2^7*J7 - 182/91125*J2^4*J3^2*J7 + 
	182/6075*J2*J3^4*J7 - 1003/202500*J2^5*J4*J7 + 1003/6750*J2^2*J3^2*J4*J7
	+ 9188/118125*J2^3*J4^2*J7 - 18533/31500*J3^2*J4^2*J7 + 
	14369/118125*J2*J4^3*J7 - 59/13500*J2^3*J3*J5*J7 + 59/450*J3^3*J5*J7 - 
	4721/3000*J2*J3*J4*J5*J7 + 127/250*J4*J5^2*J7 - 184/6075*J2^4*J6*J7 + 
	368/405*J2*J3^2*J6*J7 + 7043/9450*J2^2*J4*J6*J7 - 344/525*J4^2*J6*J7 + 
	1/10*J3*J5*J6*J7 + 1/3*J3*J4*J7^2 + J7^3 - 131/8100*J2^3*J3*J4*J8 + 
	131/270*J3^3*J4*J8 + 4103/1125*J2*J3*J4^2*J8 + 91/6750*J2^4*J5*J8 - 
	91/225*J2*J3^2*J5*J8 + 229/1500*J2^2*J4*J5*J8 - 686/375*J4^2*J5*J8 - 
	177/100*J3*J5^2*J8 - 34/45*J3*J4*J6*J8 - 139/30*J2*J5*J6*J8 + 
	1/90*J2^3*J7*J8 - 1/3*J3^2*J7*J8 - 13/30*J2*J4*J7*J8 + 
	181/607500*J2^6*J9 - 121/20250*J2^3*J3^2*J9 - 4/45*J3^4*J9 - 
	418/16875*J2^4*J4*J9 + 467/2250*J2*J3^2*J4*J9 + 1747/1875*J2^2*J4^2*J9 -
	1792/5625*J4^3*J9 + 241/1500*J2^2*J3*J5*J9 + 48/125*J3*J4*J5*J9 - 
	819/250*J2*J5^2*J9 + 8/27*J2^3*J6*J9 + 64/45*J3^2*J6*J9 + 
	8/3*J2*J4*J6*J9 - 1/5*J2*J3*J7*J9 - 241/20250*J2^4*J3*J10 + 
	241/675*J2*J3^3*J10 + 241/450*J2^2*J3*J4*J10 + 214/125*J3*J4^2*J10 - 
	599/4500*J2^3*J5*J10 - 62/75*J3^2*J5*J10 + 291/125*J2*J4*J5*J10 - 
	464/45*J2*J3*J6*J10 + 32/5*J5*J6*J10 + 1/5*J2^2*J7*J10 - 4/5*J4*J7*J10 eq 0 and
	-7/8857350000*J2^11 + 7/98415000*J2^8*J3^2 - 7/3280500*J2^5*J3^4 + 
	7/328050*J2^2*J3^6 + 373/3542940000*J2^9*J4 - 17/2460375*J2^6*J3^2*J4 + 
	19/145800*J2^3*J3^4*J4 - 7/13122*J3^6*J4 - 73303/24800580000*J2^7*J4^2 +
	37393/413343000*J2^4*J3^2*J4^2 - 1483/27556200*J2*J3^4*J4^2 - 
	193469/2755620000*J2^5*J4^3 + 136897/45927000*J2^2*J3^2*J4^3 + 
	117671/30618000*J2^3*J4^4 + 14989/680400*J3^2*J4^4 - 
	49561/3543750*J2*J4^5 - 7/7290000*J2^7*J3*J5 + 7/121500*J2^4*J3^3*J5 - 
	7/8100*J2*J3^5*J5 + 101/1458000*J2^5*J3*J4*J5 - 
	101/48600*J2^2*J3^3*J4*J5 - 5123/6123600*J2^3*J3*J4^2*J5 - 
	2059/204120*J3^3*J4^2*J5 - 52049/6804000*J2*J3*J4^3*J5 - 
	7/540000*J2^6*J5^2 + 7/18000*J2^3*J3^2*J5^2 + 109/129600*J2^4*J4*J5^2 - 
	121/10800*J2*J3^2*J4*J5^2 - 35083/1134000*J2^2*J4^2*J5^2 + 
	17/420*J4^3*J5^2 - 7/4000*J2^2*J3*J5^3 + 3/80*J3*J4*J5^3 + 
	189/4000*J2*J5^4 - 7/10497600*J2^8*J6 + 7/174960*J2^5*J3^2*J6 - 
	7/11664*J2^2*J3^4*J6 + 1973/27556200*J2^6*J4*J6 - 
	3179/1837080*J2^3*J3^2*J4*J6 - 767/61236*J3^4*J4*J6 - 
	143047/55112400*J2^4*J4^2*J6 + 21523/7348320*J2*J3^2*J4^2*J6 + 
	52666/1913625*J2^2*J4^3*J6 - 4148/70875*J4^4*J6 + 11/23328*J2^4*J3*J5*J6
	- 55/3888*J2*J3^3*J5*J6 - 247/22680*J2^2*J3*J4*J5*J6 - 
	36703/340200*J3*J4^2*J5*J6 + 301/155520*J2^3*J5^2*J6 + 
	157/648*J3^2*J5^2*J6 - 341/3600*J2*J4*J5^2*J6 - 43/218700*J2^5*J6^2 + 
	43/7290*J2^2*J3^2*J6^2 + 4957/765450*J2^3*J4*J6^2 - 
	6877/25515*J3^2*J4*J6^2 - 638/54675*J2*J4^2*J6^2 - 1/405*J2*J3*J5*J6^2 +
	11/135*J5^2*J6^2 + 7/1312200*J2^6*J3*J7 - 7/21870*J2^3*J3^3*J7 + 
	7/1458*J3^5*J7 - 71/583200*J2^4*J3*J4*J7 + 71/19440*J2*J3^3*J4*J7 - 
	1/36*J2^2*J3*J4^2*J7 + 4457/37800*J3*J4^3*J7 + 11/32400*J2^5*J5*J7 - 
	11/1080*J2^2*J3^2*J5*J7 - 421/38880*J2^3*J4*J5*J7 - 
	851/3240*J3^2*J4*J5*J7 + 17/180*J2*J4^2*J5*J7 + 67/480*J2*J3*J5^2*J7 - 
	9/40*J5^3*J7 - 37/7290*J2^3*J3*J6*J7 + 37/243*J3^3*J6*J7 + 
	247/5040*J2*J3*J4*J6*J7 + 127/4320*J2^2*J5*J6*J7 + 373/3780*J4*J5*J6*J7 
	- 1/1296*J2^4*J7^2 + 5/216*J2*J3^2*J7^2 + 5/432*J2^2*J4*J7^2 - 
	1/15*J4^2*J7^2 + 11/1049760*J2^7*J8 - 11/17496*J2^4*J3^2*J8 + 
	55/5832*J2*J3^4*J8 - 527/291600*J2^5*J4*J8 + 527/9720*J2^2*J3^2*J4*J8 + 
	286/3645*J2^3*J4^2*J8 + 239/1944*J3^2*J4^2*J8 - 2533/8100*J2*J4^3*J8 + 
	1/3240*J2^3*J3*J5*J8 - 1/108*J3^3*J5*J8 - 43/480*J2*J3*J4*J5*J8 - 
	27/320*J2^2*J5^2*J8 + 73/120*J4*J5^2*J8 + 19/58320*J2^4*J6*J8 - 
	19/1944*J2*J3^2*J6*J8 - 247/3240*J2^2*J4*J6*J8 + 142/405*J4^2*J6*J8 - 
	41/36*J3*J5*J6*J8 - 5/36*J3*J4*J7*J8 + 1/19440*J2^5*J3*J9 - 
	1/648*J2^2*J3^3*J9 - 469/97200*J2^3*J3*J4*J9 + 61/810*J3^3*J4*J9 + 
	61/675*J2*J3*J4^2*J9 - 7/4320*J2^4*J5*J9 + 5/72*J2*J3^2*J5*J9 + 
	11/540*J2^2*J4*J5*J9 + 8/45*J4^2*J5*J9 - 17/20*J3*J5^2*J9 + 
	2/27*J2^2*J3*J6*J9 + 20/27*J3*J4*J6*J9 + 11/1080*J2^3*J7*J9 + 
	1/9*J3^2*J7*J9 - 1/9*J2*J4*J7*J9 - 53/874800*J2^6*J10 + 
	61/29160*J2^3*J3^2*J10 - 2/243*J3^4*J10 + 43/16200*J2^4*J4*J10 - 
	11/1080*J2*J3^2*J4*J10 + 38/225*J2^2*J4^2*J10 - 176/225*J4^3*J10 - 
	1/48*J2^2*J3*J5*J10 + 119/90*J3*J4*J5*J10 - 7/20*J2*J5^2*J10 - 
	46/1215*J2^3*J6*J10 - 88/81*J3^2*J6*J10 + 28/135*J2*J4*J6*J10 - 
	5/12*J2*J3*J7*J10 + J5*J7*J10 eq 0 and
	-11/11809800000*J2^11 + 11/131220000*J2^8*J3^2 - 11/4374000*J2^5*J3^4 + 
	11/437400*J2^2*J3^6 + 569/6298560000*J2^9*J4 - 139/20995200*J2^6*J3^2*J4
	+ 1073/6998400*J2^3*J3^4*J4 - 7/6480*J3^6*J4 + 317/1224720000*J2^7*J4^2 
	+ 499/27216000*J2^4*J3^2*J4^2 - 2131/2721600*J2*J3^4*J4^2 - 
	206413/1088640000*J2^5*J4^3 + 132563/36288000*J2^2*J3^2*J4^3 + 
	1305533/211680000*J2^3*J4^4 + 155179/2352000*J3^2*J4^4 - 
	16721/2450000*J2*J4^5 - 11/9720000*J2^7*J3*J5 + 11/162000*J2^4*J3^3*J5 -
	11/10800*J2*J3^5*J5 + 317/7776000*J2^5*J3*J4*J5 - 
	317/259200*J2^2*J3^3*J4*J5 + 3889/2016000*J2^3*J3*J4^2*J5 - 
	4451/100800*J3^3*J4^2*J5 - 18721/336000*J2*J3*J4^3*J5 - 
	11/720000*J2^6*J5^2 + 11/24000*J2^3*J3^2*J5^2 + 
	1001/1152000*J2^4*J4*J5^2 - 57/3200*J2*J3^2*J4*J5^2 - 
	9221/224000*J2^2*J4^2*J5^2 + 162/6125*J4^3*J5^2 - 33/16000*J2^2*J3*J5^3 
	+ 459/3200*J3*J4*J5^3 + 891/16000*J2*J5^4 - 3457/2099520000*J2^8*J6 + 
	3457/34992000*J2^5*J3^2*J6 - 3457/2332800*J2^2*J3^4*J6 + 
	24431/139968000*J2^6*J4*J6 - 5909/1306368*J2^3*J3^2*J4*J6 - 
	647/30240*J3^4*J4*J6 - 1160029/211680000*J2^4*J4^2*J6 - 
	209539/63504000*J2*J3^2*J4^2*J6 + 196531/5292000*J2^2*J4^3*J6 - 
	299/8750*J4^4*J6 + 151/144000*J2^4*J3*J5*J6 - 151/4800*J2*J3^3*J5*J6 - 
	65041/2419200*J2^2*J3*J4*J5*J6 - 275189/1176000*J3*J4^2*J5*J6 + 
	593/76800*J2^3*J5^2*J6 + 741/1600*J3^2*J5^2*J6 - 
	2721/22400*J2*J4*J5^2*J6 - 3143/9331200*J2^5*J6^2 + 
	3143/311040*J2^2*J3^2*J6^2 + 149/217728*J2^3*J4*J6^2 - 
	133/288*J3^2*J4*J6^2 + 4573/66150*J2*J4^2*J6^2 - 1/30*J2*J3*J5*J6^2 + 
	7/648000*J2^6*J3*J7 - 7/10800*J2^3*J3^3*J7 + 7/720*J3^5*J7 - 
	43/54000*J2^4*J3*J4*J7 + 43/1800*J2*J3^3*J4*J7 - 
	423/12800*J2^2*J3*J4^2*J7 + 6099/56000*J3*J4^3*J7 + 
	461/1728000*J2^5*J5*J7 - 461/57600*J2^2*J3^2*J5*J7 - 
	1063/107520*J2^3*J4*J5*J7 - 5317/11200*J3^2*J4*J5*J7 + 
	747/22400*J2*J4^2*J5*J7 + 513/3200*J2*J3*J5^2*J7 - 243/1600*J5^3*J7 - 
	13/1440*J2^3*J3*J6*J7 + 13/48*J3^3*J6*J7 + 5/24*J2*J3*J4*J6*J7 + 
	187/3840*J2^2*J5*J6*J7 + 183/1120*J4*J5*J6*J7 + 17/1296000*J2^7*J8 - 
	17/21600*J2^4*J3^2*J8 + 17/1440*J2*J3^4*J8 - 13207/5184000*J2^5*J4*J8 + 
	13207/172800*J2^2*J3^2*J4*J8 + 635/5376*J2^3*J4^2*J8 + 
	3421/6720*J3^2*J4^2*J8 - 4637/28000*J2*J4^3*J8 + 1/320*J2^3*J3*J5*J8 - 
	3/32*J3^3*J5*J8 - 339/1600*J2*J3*J4*J5*J8 - 1803/12800*J2^2*J5^2*J8 + 
	297/448*J4*J5^2*J8 - 1/1440*J2^4*J6*J8 + 1/48*J2*J3^2*J6*J8 - 
	29/288*J2^2*J4*J6*J8 - 103/140*J4^2*J6*J8 - 27/16*J3*J5*J6*J8 + 
	19/103680*J2^5*J3*J9 - 19/3456*J2^2*J3^3*J9 - 
	26273/2016000*J2^3*J3*J4*J9 + 201/1400*J3^3*J4*J9 + 
	1059/5600*J2*J3*J4^2*J9 - 173/192000*J2^4*J5*J9 + 81/800*J2*J3^2*J5*J9 +
	571/28000*J2^2*J4*J5*J9 + 207/7000*J4^2*J5*J9 - 513/400*J3*J5^2*J9 + 
	95/576*J2^2*J3*J6*J9 + 369/280*J3*J4*J6*J9 - 323/2592000*J2^6*J10 + 
	19/9600*J2^3*J3^2*J10 + 19/360*J3^4*J10 + 11321/2016000*J2^4*J4*J10 + 
	221/2800*J2*J3^2*J4*J10 + 59/224*J2^2*J4^2*J10 - 198/875*J4^3*J10 - 
	19/256*J2^2*J3*J5*J10 + 7263/5600*J3*J4*J5*J10 - 81/200*J2*J5^2*J10 - 
	17/192*J2^3*J6*J10 - 55/24*J3^2*J6*J10 + 51/280*J2*J4*J6*J10 + J6^2*J10 eq 0 and
	-7/3936600000*J2^11 + 7/43740000*J2^8*J3^2 - 7/1458000*J2^5*J3^4 + 
	7/145800*J2^2*J3^6 + 97/524880000*J2^9*J4 - 17/1312200*J2^6*J3^2*J4 + 
	487/1749600*J2^3*J3^4*J4 - 49/29160*J3^6*J4 - 2069/3674160000*J2^7*J4^2 
	+ 1649/61236000*J2^4*J3^2*J4^2 - 1229/4082400*J2*J3^4*J4^2 - 
	142103/408240000*J2^5*J4^3 + 13891/1701000*J2^2*J3^2*J4^3 + 
	260963/22680000*J2^3*J4^4 + 135239/1512000*J3^2*J4^4 - 
	30361/1575000*J2*J4^5 - 7/3240000*J2^7*J3*J5 + 7/54000*J2^4*J3^3*J5 - 
	7/3600*J2*J3^5*J5 + 193/1944000*J2^5*J3*J4*J5 - 
	193/64800*J2^2*J3^3*J4*J5 + 2861/1512000*J2^3*J3*J4^2*J5 - 
	3001/50400*J3^3*J4^2*J5 - 71383/1008000*J2*J3*J4^3*J5 - 
	7/240000*J2^6*J5^2 + 7/8000*J2^3*J3^2*J5^2 + 11/6400*J2^4*J4*J5^2 - 
	151/4800*J2*J3^2*J4*J5^2 - 5281/67200*J2^2*J4^2*J5^2 + 
	1119/14000*J4^3*J5^2 - 63/16000*J2^2*J3*J5^3 + 333/1600*J3*J4*J5^3 + 
	1701/16000*J2*J5^4 - 307/116640000*J2^8*J6 + 307/1944000*J2^5*J3^2*J6 - 
	307/129600*J2^2*J3^4*J6 + 56459/204120000*J2^6*J4*J6 - 
	4657/637875*J2^3*J3^2*J4*J6 - 20353/680400*J3^4*J4*J6 - 
	1811459/204120000*J2^4*J4^2*J6 + 213761/27216000*J2*J3^2*J4^2*J6 + 
	4789/70875*J2^2*J4^3*J6 - 3121/39375*J4^4*J6 + 
	1847/1296000*J2^4*J3*J5*J6 - 1847/43200*J2*J3^3*J5*J6 - 
	10459/302400*J2^2*J3*J4*J5*J6 - 31739/84000*J3*J4^2*J5*J6 + 
	3893/345600*J2^3*J5^2*J6 + 4831/7200*J3^2*J5^2*J6 - 
	11971/56000*J2*J4*J5^2*J6 - 61/97200*J2^5*J6^2 + 61/3240*J2^2*J3^2*J6^2 
	+ 569/75600*J2^3*J4*J6^2 - 8327/11340*J3^2*J4*J6^2 + 
	1357/28350*J2*J4^2*J6^2 - 83/720*J2*J3*J5*J6^2 + 11/60*J5^2*J6^2 + 
	49/2916000*J2^6*J3*J7 - 49/48600*J2^3*J3^3*J7 + 49/3240*J3^5*J7 - 
	1151/1296000*J2^4*J3*J4*J7 + 1151/43200*J2*J3^3*J4*J7 - 
	101/1600*J2^2*J3*J4^2*J7 + 18769/84000*J3*J4^3*J7 + 1/1800*J2^5*J5*J7 - 
	1/60*J2^2*J3^2*J5*J7 - 103/6000*J2^3*J4*J5*J7 - 537/800*J3^2*J4*J5*J7 + 
	127/2000*J2*J4^2*J5*J7 + 981/3200*J2*J3*J5^2*J7 - 243/800*J5^3*J7 - 
	41/3240*J2^3*J3*J6*J7 + 41/108*J3^3*J6*J7 + 485/1344*J2*J3*J4*J6*J7 + 
	53/640*J2^2*J5*J6*J7 - 3/16*J4*J5*J6*J7 + 1/2880*J2^4*J7^2 - 
	1/96*J2*J3^2*J7^2 - 1/192*J2^2*J4*J7^2 - 3/40*J4^2*J7^2 + 
	97/3888000*J2^7*J8 - 97/64800*J2^4*J3^2*J8 + 97/4320*J2*J3^4*J8 - 
	251/54000*J2^5*J4*J8 + 251/1800*J2^2*J3^2*J4*J8 + 
	22483/108000*J2^3*J4^2*J8 + 4219/7200*J3^2*J4^2*J8 - 
	1931/6000*J2*J4^3*J8 + 31/7200*J2^3*J3*J5*J8 - 31/240*J3^3*J5*J8 - 
	1529/3200*J2*J3*J4*J5*J8 - 1611/6400*J2^2*J5^2*J8 + 963/800*J4*J5^2*J8 -
	7/8640*J2^4*J6*J8 + 7/288*J2*J3^2*J6*J8 - 97/480*J2^2*J4*J6*J8 + 
	13/30*J4^2*J6*J8 - 39/16*J3*J5*J6*J8 + 1/16*J3*J4*J7*J8 + 
	37/129600*J2^5*J3*J9 - 37/4320*J2^2*J3^3*J9 - 4507/216000*J2^3*J3*J4*J9 
	+ 433/1800*J3^3*J4*J9 + 21/100*J2*J3*J4^2*J9 - 359/144000*J2^4*J5*J9 + 
	457/2400*J2*J3^2*J5*J9 + 323/6000*J2^2*J4*J5*J9 + 18/125*J4^2*J5*J9 - 
	837/400*J3*J5^2*J9 + 11/45*J2^2*J3*J6*J9 + 61/30*J3*J4*J6*J9 - 
	1/288*J2^3*J7*J9 - 1/12*J3^2*J7*J9 + J6*J7*J9 - 137/648000*J2^6*J10 + 
	89/21600*J2^3*J3^2*J10 + 1/15*J3^4*J10 + 341/36000*J2^4*J4*J10 + 
	81/800*J2*J3^2*J4*J10 + 293/600*J2^2*J4^2*J10 - 124/125*J4^3*J10 - 
	37/320*J2^2*J3*J5*J10 + 203/100*J3*J4*J5*J10 - 297/400*J2*J5^2*J10 - 
	13/90*J2^3*J6*J10 - 3*J3^2*J6*J10 + 2/5*J2*J4*J6*J10 + 
	3/16*J2*J3*J7*J10 eq 0 and
	91/33215062500*J2^11 - 91/369056250*J2^8*J3^2 + 91/12301875*J2^5*J3^4 - 
	182/2460375*J2^2*J3^6 - 44/184528125*J2^9*J4 + 568/36905625*J2^6*J3^2*J4
	- 688/2460375*J2^3*J3^4*J4 + 32/32805*J3^6*J4 - 
	9233/2214337500*J2^7*J4^2 + 21931/73811250*J2^4*J3^2*J4^2 - 
	12698/2460375*J2*J3^4*J4^2 + 2341231/3444525000*J2^5*J4^3 - 
	2032531/114817500*J2^2*J3^2*J4^3 - 3863621/191362500*J2^3*J4^4 - 
	29713/607500*J3^2*J4^4 + 126187/8859375*J2*J4^5 + 91/27337500*J2^7*J3*J5
	- 91/455625*J2^4*J3^3*J5 + 91/30375*J2*J3^5*J5 - 
	224/1366875*J2^5*J3*J4*J5 + 448/91125*J2^2*J3^3*J4*J5 - 
	17209/38272500*J2^3*J3*J4^2*J5 + 20732/637875*J3^3*J4^2*J5 + 
	69997/8505000*J2*J3*J4^3*J5 + 91/2025000*J2^6*J5^2 - 
	91/67500*J2^3*J3^2*J5^2 - 509/202500*J2^4*J4*J5^2 + 
	19/450*J2*J3^2*J4*J5^2 + 357949/2835000*J2^2*J4^2*J5^2 - 
	1109/26250*J4^3*J5^2 + 91/15000*J2^2*J3*J5^3 - 13/125*J3*J4*J5^3 - 
	819/5000*J2*J5^4 + 16039/2952450000*J2^8*J6 - 
	16039/49207500*J2^5*J3^2*J6 + 16039/3280500*J2^2*J3^4*J6 - 
	219271/382725000*J2^6*J4*J6 + 1916969/114817500*J2^3*J3^2*J4*J6 + 
	5647/382725*J3^4*J4*J6 + 6060043/344452500*J2^4*J4^2*J6 - 
	571733/9185400*J2*J3^2*J4^2*J6 - 2085949/19136250*J2^2*J4^3*J6 + 
	115784/1771875*J4^4*J6 - 2053/3645000*J2^4*J3*J5*J6 + 
	2053/121500*J2*J3^3*J5*J6 - 18607/1215000*J2^2*J3*J4*J5*J6 + 
	1003211/4252500*J3*J4^2*J5*J6 - 123529/4860000*J2^3*J5^2*J6 - 
	3611/10125*J3^2*J5^2*J6 + 320273/945000*J2*J4*J5^2*J6 + 
	941/820125*J2^5*J6^2 - 1882/54675*J2^2*J3^2*J6^2 - 
	274/91125*J2^3*J4*J6^2 + 56926/127575*J3^2*J4*J6^2 - 
	56164/382725*J2*J4^2*J6^2 + 571/2025*J2*J3*J5*J6^2 - 22/135*J5^2*J6^2 - 
	8/820125*J2^6*J3*J7 + 32/54675*J2^3*J3^3*J7 - 32/3645*J3^5*J7 - 
	3281/3645000*J2^4*J3*J4*J7 + 3281/121500*J2*J3^3*J4*J7 + 
	779/5000*J2^2*J3*J4^2*J7 - 97039/472500*J3*J4^3*J7 - 
	811/1215000*J2^5*J5*J7 + 811/40500*J2^2*J3^2*J5*J7 + 
	2407/97200*J2^3*J4*J5*J7 + 61/162*J3^2*J4*J5*J7 + 
	269/15000*J2*J4^2*J5*J7 - 1393/3000*J2*J3*J5^2*J7 + 63/250*J5^3*J7 + 
	283/36450*J2^3*J3*J6*J7 - 283/1215*J3^3*J6*J7 - 
	4757/18900*J2*J3*J4*J6*J7 - 19/120*J2^2*J5*J6*J7 + 77/1350*J4*J5*J6*J7 -
	1/1350*J2^4*J7^2 + 1/45*J2*J3^2*J7^2 + 1/900*J2^2*J4*J7^2 + 
	11/210*J4^2*J7^2 - 1309/32805000*J2^7*J8 + 1309/546750*J2^4*J3^2*J8 - 
	1309/36450*J2*J3^4*J8 + 9539/1215000*J2^5*J4*J8 - 
	9539/40500*J2^2*J3^2*J4*J8 - 164492/455625*J2^3*J4^2*J8 - 
	511/2430*J3^2*J4^2*J8 + 1339/20250*J2*J4^3*J8 - 19/10125*J2^3*J3*J5*J8 +
	38/675*J3^3*J5*J8 + 7841/9000*J2*J3*J4*J5*J8 + 2641/6000*J2^2*J5^2*J8 - 
	1913/1500*J4*J5^2*J8 + 181/72900*J2^4*J6*J8 - 181/2430*J2*J3^2*J6*J8 + 
	1543/4050*J2^2*J4*J6*J8 - 172/405*J4^2*J6*J8 + 113/90*J3*J5*J6*J8 + 
	1/6*J3*J4*J7*J8 + J7^2*J8 - 371/911250*J2^5*J3*J9 + 
	371/30375*J2^2*J3^3*J9 + 1417/60750*J2^3*J3*J4*J9 - 304/2025*J3^3*J4*J9 
	+ 2998/16875*J2*J3*J4^2*J9 + 14/10125*J2^4*J5*J9 - 
	1393/6750*J2*J3^2*J5*J9 - 41/1250*J2^2*J4*J5*J9 - 1552/5625*J4^2*J5*J9 +
	331/250*J3*J5^2*J9 - 688/2025*J2^2*J3*J6*J9 - 728/675*J3*J4*J6*J9 + 
	1/75*J2^3*J7*J9 - 14/75*J2*J4*J7*J9 + 524/1366875*J2^6*J10 - 
	983/91125*J2^3*J3^2*J10 - 26/1215*J3^4*J10 - 187/12150*J2^4*J4*J10 - 
	178/2025*J2*J3^2*J4*J10 - 15877/16875*J2^2*J4^2*J10 + 5216/5625*J4^3*J10
	+ 371/2250*J2^2*J3*J5*J10 - 562/375*J3*J4*J5*J10 + 323/250*J2*J5^2*J10 +
	1736/6075*J2^3*J6*J10 + 656/405*J3^2*J6*J10 - 304/675*J2*J4*J6*J10 - 
	2/5*J2*J3*J7*J10 eq 0 and
	7/2952450000*J2^10*J3 - 7/32805000*J2^7*J3^3 + 7/1093500*J2^4*J3^5 - 
	7/109350*J2*J3^7 + 163/4723920000*J2^8*J3*J4 - 163/78732000*J2^5*J3^3*J4
	+ 163/5248800*J2^2*J3^5*J4 - 5273/204120000*J2^6*J3*J4^2 + 
	62749/61236000*J2^3*J3^3*J4^2 - 3823/510300*J3^5*J4^2 + 
	48761/45360000*J2^4*J3*J4^3 - 58481/3402000*J2*J3^3*J4^3 - 
	68851/2268000*J2^2*J3*J4^4 - 45921/1225000*J3*J4^5 + 
	7/2430000*J2^6*J3^2*J5 - 7/40500*J2^3*J3^4*J5 + 7/2700*J3^6*J5 + 
	1121/262440000*J2^7*J4*J5 - 799/3499200*J2^4*J3^2*J4*J5 + 
	1753/583200*J2*J3^4*J4*J5 - 350351/816480000*J2^5*J4^2*J5 + 
	157361/27216000*J2^2*J3^2*J4^2*J5 + 1638899/158760000*J2^3*J4^3*J5 - 
	38081/1764000*J3^2*J4^3*J5 + 8717/294000*J2*J4^4*J5 + 
	7/180000*J2^5*J3*J5^2 - 7/6000*J2^2*J3^3*J5^2 - 
	2711/2592000*J2^3*J3*J4*J5^2 + 1/27*J3^3*J4*J5^2 + 
	976/7875*J2*J3*J4^2*J5^2 + 21/4000*J2*J3^2*J5^3 - 233/9600*J2^2*J4*J5^3 
	- 297/5600*J4^2*J5^3 - 567/4000*J3*J5^4 + 3701/524880000*J2^7*J3*J6 - 
	3701/8748000*J2^4*J3^3*J6 + 3701/583200*J2*J3^5*J6 - 
	620621/734832000*J2^5*J3*J4*J6 + 620621/24494400*J2^2*J3^3*J4*J6 + 
	9086489/357210000*J2^3*J3*J4^2*J6 - 2443381/47628000*J3^3*J4^2*J6 - 
	243491/3969000*J2*J3*J4^3*J6 - 5017/29160000*J2^6*J5*J6 + 
	227/40500*J2^3*J3^2*J5*J6 - 431/32400*J3^4*J5*J6 + 
	2538449/408240000*J2^4*J4*J5*J6 - 1612963/27216000*J2*J3^2*J4*J5*J6 + 
	2244407/79380000*J2^2*J4^2*J5*J6 + 32257/367500*J4^3*J5*J6 - 
	29447/288000*J2^2*J3*J5^2*J6 + 683/36000*J3*J4*J5^2*J6 + 
	521/8000*J2*J5^3*J6 + 83/72900*J2^4*J3*J6^2 - 83/2430*J2*J3^3*J6^2 + 
	9623/116640*J2^2*J3*J4*J6^2 + 6709/198450*J3*J4^2*J6^2 - 
	221/25920*J2^3*J5*J6^2 + 46/135*J3^2*J5*J6^2 - 5851/56700*J2*J4*J5*J6^2 
	- 127/87480000*J2^8*J7 + 127/1458000*J2^5*J3^2*J7 - 
	127/97200*J2^2*J3^4*J7 + 86269/408240000*J2^6*J4*J7 - 
	37117/4536000*J2^3*J3^2*J4*J7 + 12541/226800*J3^4*J4*J7 - 
	15433/5670000*J2^4*J4^2*J7 + 507083/3024000*J2*J3^2*J4^2*J7 - 
	4231/315000*J2^2*J4^3*J7 - 261/8750*J4^4*J7 - 347/1296000*J2^4*J3*J5*J7 
	+ 347/43200*J2*J3^3*J5*J7 + 24487/288000*J2^2*J3*J4*J5*J7 + 
	11041/28000*J3*J4^2*J5*J7 - 11/36000*J2^3*J5^2*J7 - 
	923/2400*J3^2*J5^2*J7 - 411/8000*J2*J4*J5^2*J7 + 259/194400*J2^5*J6*J7 -
	259/6480*J2^2*J3^2*J6*J7 - 6313/226800*J2^3*J4*J6*J7 - 
	4031/15120*J3^2*J4*J6*J7 - 89/2100*J2*J4^2*J6*J7 - 83/576*J2*J3*J5*J6*J7
	- 7/80*J5^2*J6*J7 - 1/720*J2^3*J3*J7^2 + 1/24*J3^3*J7^2 + 
	1/960*J2*J3*J4*J7^2 - 7/194400*J2^6*J3*J8 + 7/3240*J2^3*J3^3*J8 - 
	7/216*J3^5*J8 + 10211/1296000*J2^4*J3*J4*J8 - 10211/43200*J2*J3^3*J4*J8 
	- 3469/7200*J2^2*J3*J4^2*J8 - 42041/42000*J3*J4^3*J8 - 
	127/216000*J2^5*J5*J8 + 127/7200*J2^2*J3^2*J5*J8 - 
	25967/3024000*J2^3*J4*J5*J8 + 49093/50400*J3^2*J4*J5*J8 + 
	5867/42000*J2*J4^2*J5*J8 + 1543/3200*J2*J3*J5^2*J8 - 99/800*J5^3*J8 + 
	1/432*J2^3*J3*J6*J8 - 5/72*J3^3*J6*J8 + 599/1440*J2*J3*J4*J6*J8 + 
	173/960*J2^2*J5*J6*J8 + 949/840*J4*J5*J6*J8 - 1/2880*J2^4*J7*J8 + 
	1/96*J2*J3^2*J7*J8 + 7/480*J2^2*J4*J7*J8 - 3/20*J4^2*J7*J8 - 
	149/11664000*J2^7*J9 - 37/388800*J2^4*J3^2*J9 + 31/2160*J2*J3^4*J9 + 
	13889/13608000*J2^5*J4*J9 + 7397/907200*J2^2*J3^2*J4*J9 - 
	298/7875*J2^3*J4^2*J9 + 833/1800*J3^2*J4^2*J9 - 359/3500*J2*J4^3*J9 - 
	199/28800*J2^3*J3*J5*J9 - 17/120*J3^3*J5*J9 - 997/16800*J2*J3*J4*J5*J9 +
	233/1600*J2^2*J5^2*J9 + 579/1400*J4*J5^2*J9 - 211/16200*J2^4*J6*J9 - 
	29/90*J2*J3^2*J6*J9 - 5797/37800*J2^2*J4*J6*J9 - 202/525*J4^2*J6*J9 + 
	1/32*J2^2*J3*J7*J9 - 7/20*J3*J4*J7*J9 + 67/77760*J2^5*J3*J10 - 
	67/2592*J2^2*J3^3*J10 - 50597/1512000*J2^3*J3*J4*J10 - 
	223/1400*J3^3*J4*J10 - 187/168*J2*J3*J4^2*J10 + 2399/432000*J2^4*J5*J10 
	+ 1313/7200*J2*J3^2*J5*J10 - 2747/42000*J2^2*J4*J5*J10 - 
	492/875*J4^2*J5*J10 + 237/200*J3*J5^2*J10 + 77/108*J2^2*J3*J6*J10 + 
	107/70*J3*J4*J6*J10 - 8/15*J2*J5*J6*J10 - 17/1440*J2^3*J7*J10 - 
	7/12*J3^2*J7*J10 + 1/5*J2*J4*J7*J10 + J6*J7*J10 eq 0 and
	41/13286025000*J2^10*J3 - 41/147622500*J2^7*J3^3 + 41/4920750*J2^4*J3^5 - 
	41/492075*J2*J3^7 + 233/1180980000*J2^8*J3*J4 - 
	233/19683000*J2^5*J3^3*J4 + 233/1312200*J2^2*J3^5*J4 - 
	198773/4133430000*J2^6*J3*J4^2 + 246661/137781000*J2^3*J3^3*J4^2 - 
	11972/1148175*J3^5*J4^2 + 1578841/918540000*J2^4*J3*J4^3 - 
	347633/15309000*J2*J3^3*J4^3 - 245459/5103000*J2^2*J3*J4^4 + 
	1178/65625*J3*J4^5 + 41/10935000*J2^6*J3^2*J5 - 41/182250*J2^3*J3^4*J5 +
	41/12150*J3^6*J5 + 49/6561000*J2^7*J4*J5 - 1261/4374000*J2^4*J3^2*J4*J5 
	+ 281/145800*J2*J3^4*J4*J5 - 19253/24494400*J2^5*J4^2*J5 + 
	35911/4082400*J2^2*J3^2*J4^2*J5 + 19951/945000*J2^3*J4^3*J5 - 
	86083/1134000*J3^2*J4^3*J5 - 1103/45000*J2*J4^4*J5 + 
	41/810000*J2^5*J3*J5^2 - 41/27000*J2^2*J3^3*J5^2 - 
	373/648000*J2^3*J3*J4*J5^2 + 67/1350*J3^3*J4*J5^2 + 
	124093/756000*J2*J3*J4^2*J5^2 + 41/6000*J2*J3^2*J5^3 - 
	16/375*J2^2*J4*J5^3 + 1033/14000*J4^2*J5^3 - 369/2000*J3*J5^4 + 
	7069/590490000*J2^7*J3*J6 - 7069/9841500*J2^4*J3^3*J6 + 
	7069/656100*J2*J3^5*J6 - 266597/183708000*J2^5*J3*J4*J6 + 
	266597/6123600*J2^2*J3^3*J4*J6 + 5091419/114817500*J2^3*J3*J4^2*J6 - 
	3014377/30618000*J3^3*J4^2*J6 - 32411/255150*J2*J3*J4^3*J6 - 
	10043/32805000*J2^6*J5*J6 + 42433/4374000*J2^3*J3^2*J5*J6 - 
	2261/145800*J3^4*J5*J6 + 3845543/306180000*J2^4*J4*J5*J6 - 
	2819701/20412000*J2*J3^2*J4*J5*J6 - 4489/607500*J2^2*J4^2*J5*J6 - 
	949/15750*J4^3*J5*J6 - 9853/54000*J2^2*J3*J5^2*J6 + 
	216049/378000*J3*J4*J5^2*J6 + 499/4000*J2*J5^3*J6 + 
	2191/1312200*J2^4*J3*J6^2 - 2191/43740*J2*J3^3*J6^2 + 
	10823/68040*J2^2*J3*J4*J6^2 - 1955/5103*J3*J4^2*J6^2 - 
	193/11664*J2^3*J5*J6^2 + 581/1215*J3^2*J5*J6^2 - 
	1073/17010*J2*J4*J5*J6^2 - 167/65610000*J2^8*J7 + 
	167/1093500*J2^5*J3^2*J7 - 167/72900*J2^2*J3^4*J7 + 
	50077/131220000*J2^6*J4*J7 - 30643/2187000*J2^3*J3^2*J4*J7 + 
	11209/145800*J3^4*J4*J7 - 156679/25515000*J2^4*J4^2*J7 + 
	1999247/6804000*J2*J3^2*J4^2*J7 - 6599/1417500*J2^2*J4^3*J7 + 
	19/1750*J4^4*J7 - 19/324000*J2^4*J3*J5*J7 + 19/10800*J2*J3^3*J5*J7 + 
	31717/216000*J2^2*J3*J4*J5*J7 - 773/6000*J3*J4^2*J5*J7 - 
	11/18000*J2^3*J5^2*J7 - 593/1200*J3^2*J5^2*J7 - 389/4000*J2*J4*J5^2*J7 +
	353/145800*J2^5*J6*J7 - 353/4860*J2^2*J3^2*J6*J7 - 
	29809/510300*J2^3*J4*J6*J7 - 3953/68040*J3^2*J4*J6*J7 + 
	6131/56700*J2*J4^2*J6*J7 - 5/24*J2*J3*J5*J6*J7 + 1/120*J5^2*J6*J7 - 
	7/3240*J2^3*J3*J7^2 + 7/108*J3^3*J7^2 + 17/720*J2*J3*J4*J7^2 - 
	41/874800*J2^6*J3*J8 + 41/14580*J2^3*J3^3*J8 - 41/972*J3^5*J8 + 
	33203/2916000*J2^4*J3*J4*J8 - 33203/97200*J2*J3^3*J4*J8 - 
	1564/2025*J2^2*J3*J4^2*J8 - 5311/13500*J3*J4^3*J8 - 
	167/162000*J2^5*J5*J8 + 167/5400*J2^2*J3^2*J5*J8 - 
	167/12960*J2^3*J4*J5*J8 + 12647/10800*J3^2*J4*J5*J8 + 
	917/1800*J2*J4^2*J5*J8 + 149/200*J2*J3*J5^2*J8 - 99/400*J5^3*J8 + 
	43/9720*J2^3*J3*J6*J8 - 43/324*J3^3*J6*J8 + 1889/3240*J2*J3*J4*J6*J8 + 
	73/240*J2^2*J5*J6*J8 - 11/12*J4*J5*J6*J8 - 1/6480*J2^4*J7*J8 + 
	1/216*J2*J3^2*J7*J8 - 1/360*J2^2*J4*J7*J8 - 19/60*J4^2*J7*J8 - 
	317/14580000*J2^7*J9 - 91/486000*J2^4*J3^2*J9 + 17/675*J2*J3^4*J9 + 
	12803/7290000*J2^5*J4*J9 + 7019/486000*J2^2*J3^2*J4*J9 - 
	10841/151875*J2^3*J4^2*J9 + 13409/20250*J3^2*J4^2*J9 + 
	1507/11250*J2*J4^3*J9 - 4409/324000*J2^3*J3*J5*J9 - 529/2700*J3^3*J5*J9 
	- 413/4500*J2*J3*J4*J5*J9 + 32/125*J2^2*J5^2*J9 - 301/500*J4*J5^2*J9 - 
	97/4050*J2^4*J6*J9 - 73/135*J2*J3^2*J6*J9 - 593/4050*J2^2*J4*J6*J9 + 
	44/135*J4^2*J6*J9 + 1/24*J2^2*J3*J7*J9 + 11/90*J3*J4*J7*J9 + J7^2*J9 + 
	29/19440*J2^5*J3*J10 - 29/648*J2^2*J3^3*J10 - 
	30839/486000*J2^3*J3*J4*J10 - 893/8100*J3^3*J4*J10 - 
	3889/2700*J2*J3*J4^2*J10 + 3077/324000*J2^4*J5*J10 + 
	431/1350*J2*J3^2*J5*J10 - 377/3000*J2^2*J4*J5*J10 + 96/125*J4^2*J5*J10 +
	36/25*J3*J5^2*J10 + 34/27*J2^2*J3*J6*J10 - 128/135*J3*J4*J6*J10 - 
	J2*J5*J6*J10 - 19/1080*J2^3*J7*J10 - 13/18*J3^2*J7*J10 - 
	17/90*J2*J4*J7*J10 eq 0 and
	-1/1660753125*J2^12 + 2/36905625*J2^9*J3^2 - 4/2460375*J2^6*J3^4 + 
	8/492075*J2^3*J3^6 + 31/574087500*J2^10*J4 - 
	111043/24800580000*J2^7*J3^2*J4 + 50779/413343000*J2^4*J3^4*J4 - 
	30691/27556200*J2*J3^6*J4 + 13193/24800580000*J2^8*J4^2 + 
	35879/826686000*J2^5*J3^2*J4^2 - 6134/3444525*J2^2*J3^4*J4^2 - 
	197611/1607445000*J2^6*J4^3 + 62879/51438240*J2^3*J3^2*J4^3 - 
	33493/21432600*J3^4*J4^3 + 4151597/1071630000*J2^4*J4^4 + 
	4982911/71442000*J2*J3^2*J4^4 - 29791/33075000*J2^2*J4^5 - 
	618/153125*J4^6 - 1/1366875*J2^8*J3*J5 + 4/91125*J2^5*J3^3*J5 - 
	4/6075*J2^2*J3^5*J5 + 20711/1377810000*J2^6*J3*J4*J5 - 
	54389/91854000*J2^3*J3^3*J4*J5 + 12967/3061800*J3^5*J4*J5 + 
	1321181/612360000*J2^4*J3*J4^2*J5 - 698531/20412000*J2*J3^3*J4^2*J5 - 
	30223/567000*J2^2*J3*J4^3*J5 + 461777/13230000*J3*J4^4*J5 - 
	1/101250*J2^7*J5^2 + 1/3375*J2^4*J3^2*J5^2 + 6683/12757500*J2^5*J4*J5^2 
	- 185401/13608000*J2^2*J3^2*J4*J5^2 - 593911/22680000*J2^3*J4^2*J5^2 - 
	13513/378000*J3^2*J4^2*J5^2 - 277327/8820000*J2*J4^3*J5^2 - 
	1/750*J2^3*J3*J5^3 + 6529/50400*J2*J3*J4*J5^3 + 9/250*J2^2*J5^4 + 
	1023/14000*J4*J5^4 - 869/738112500*J2^9*J6 + 
	24943/393660000*J2^6*J3^2*J6 - 4087/6561000*J2^3*J3^4*J6 - 
	191/29160*J3^6*J6 + 1684507/13778100000*J2^7*J4*J6 - 
	859367/393660000*J2^4*J3^2*J4*J6 - 4091473/91854000*J2*J3^4*J4*J6 - 
	87257509/24111675000*J2^5*J4^2*J6 - 14884333/401861250*J2^2*J3^2*J4^2*J\
	6 + 47775629/2679075000*J2^3*J4^3*J6 + 2803813/119070000*J3^2*J4^3*J6 + 
	638129/74418750*J2*J4^4*J6 + 21149/21870000*J2^5*J3*J5*J6 - 
	21149/729000*J2^2*J3^3*J5*J6 - 8585861/306180000*J2^3*J3*J4*J5*J6 + 
	203731/2916000*J3^3*J4*J5*J6 - 759257/4961250*J2*J3*J4^2*J5*J6 + 
	2383/405000*J2^4*J5^2*J6 + 3871/8640*J2*J3^2*J5^2*J6 - 
	244007/3240000*J2^2*J4*J5^2*J6 - 36577/275625*J4^2*J5^2*J6 - 
	61/3000*J3*J5^3*J6 - 199/820125*J2^6*J6^2 + 3127/437400*J2^3*J3^2*J6^2 +
	19/4860*J3^4*J6^2 + 1693/3827250*J2^4*J4*J6^2 - 
	1474783/3061800*J2*J3^2*J4*J6^2 + 213032/13395375*J2^2*J4^2*J6^2 + 
	120664/1488375*J4^3*J6^2 - 1273/97200*J2^2*J3*J5*J6^2 - 
	127/1575*J3*J4*J5*J6^2 + 119/1350*J2*J5^2*J6^2 + 617/65610000*J2^7*J3*J7
	- 617/1093500*J2^4*J3^3*J7 + 617/72900*J2*J3^5*J7 - 
	38369/43740000*J2^5*J3*J4*J7 + 38369/1458000*J2^2*J3^3*J4*J7 - 
	176243/10206000*J2^3*J3*J4^2*J7 - 152059/1360800*J3^3*J4^2*J7 + 
	119009/2835000*J2*J3*J4^3*J7 + 44/273375*J2^6*J5*J7 - 
	16517/2916000*J2^3*J3^2*J5*J7 + 2437/97200*J3^4*J5*J7 - 
	1603/243000*J2^4*J4*J5*J7 - 267799/648000*J2*J3^2*J4*J5*J7 + 
	8807/315000*J2^2*J4^2*J5*J7 + 3221/105000*J4^3*J5*J7 + 
	311/3000*J2^2*J3*J5^2*J7 + 4829/42000*J3*J4*J5^2*J7 - 99/1000*J2*J5^3*J7
	- 1193/145800*J2^4*J3*J6*J7 + 1193/4860*J2*J3^3*J6*J7 + 
	4709/24300*J2^2*J3*J4*J6*J7 - 45917/793800*J3*J4^2*J6*J7 + 
	757/24300*J2^3*J5*J6*J7 + 769/6480*J3^2*J5*J6*J7 + 
	7363/75600*J2*J4*J5*J6*J7 + 1/12150*J2^5*J7^2 - 1/405*J2^2*J3^2*J7^2 + 
	187/113400*J2^3*J4*J7^2 - 643/15120*J3^2*J4*J7^2 - 
	341/12600*J2*J4^2*J7^2 + 139/16402500*J2^8*J8 - 139/273375*J2^5*J3^2*J8 
	+ 139/18225*J2^2*J3^4*J8 - 257731/153090000*J2^6*J4*J8 + 
	965459/20412000*J2^3*J3^2*J4*J8 + 13093/136080*J3^4*J4*J8 + 
	498181/6378750*J2^4*J4^2*J8 + 1364197/1701000*J2*J3^2*J4^2*J8 - 
	3077/236250*J2^2*J4^3*J8 - 1987/39375*J4^4*J8 + 97/32400*J2^4*J3*J5*J8 -
	97/1080*J2*J3^3*J5*J8 - 14251/108000*J2^2*J3*J4*J5*J8 - 
	22387/42000*J3*J4^2*J5*J8 - 2587/27000*J2^3*J5^2*J8 - 
	2437/7200*J3^2*J5^2*J8 + 23047/84000*J2*J4*J5^2*J8 - 11/18225*J2^5*J6*J8
	+ 22/1215*J2^2*J3^2*J6*J8 - 3701/48600*J2^3*J4*J6*J8 - 
	25/648*J3^2*J4*J6*J8 + 3533/56700*J2*J4^2*J6*J8 - 191/144*J2*J3*J5*J6*J8
	- 37/60*J5^2*J6*J8 + 1/1296*J2^3*J3*J7*J8 - 5/216*J3^3*J7*J8 - 
	13/360*J2*J3*J4*J7*J8 + 433/2916000*J2^6*J3*J9 - 
	1141/291600*J2^3*J3^3*J9 - 79/4860*J3^5*J9 - 
	174191/17010000*J2^4*J3*J4*J9 + 93407/1134000*J2*J3^3*J4*J9 + 
	32681/189000*J2^2*J3*J4^2*J9 - 40577/236250*J3*J4^3*J9 - 
	74/151875*J2^5*J5*J9 + 26591/324000*J2^2*J3^2*J5*J9 + 
	69289/5670000*J2^3*J4*J5*J9 + 27329/189000*J3^2*J4*J5*J9 + 
	24127/157500*J2*J4^2*J5*J9 - 6359/6000*J2*J3*J5^2*J9 - 117/500*J5^3*J9 +
	557/4050*J2^3*J3*J6*J9 + 103/405*J3^3*J6*J9 + 363/350*J2*J3*J4*J6*J9 - 
	1/810*J2^4*J7*J9 - 23/1080*J2*J3^2*J7*J9 - 211/18900*J2^2*J4*J7*J9 + 
	59/525*J4^2*J7*J9 - 197/2187000*J2^7*J10 + 119/291600*J2^4*J3^2*J10 + 
	223/3240*J2*J3^4*J10 + 20891/5103000*J2^5*J4*J10 + 
	69421/680400*J2^2*J3^2*J4*J10 + 31067/170100*J2^3*J4^2*J10 + 
	6731/28350*J3^2*J4^2*J10 - 3053/23625*J2*J4^3*J10 - 
	809/12960*J2^3*J3*J5*J10 - 163/1080*J3^3*J5*J10 + 
	253/280*J2*J3*J4*J5*J10 - 307/1200*J2^2*J5^2*J10 - 9/350*J4*J5^2*J10 - 
	392/6075*J2^4*J6*J10 - 22/9*J2*J3^2*J6*J10 + 716/14175*J2^2*J4*J6*J10 + 
	328/945*J4^2*J6*J10 + 5/9*J3*J5*J6*J10 + 7/120*J2^2*J3*J7*J10 + 
	421/630*J3*J4*J7*J10 + J7^2*J10 eq 0
	then
	vprintf G3Twists, 1 : "Automorphism group D4, curve y^2 = (x^2-1)*(x^6+a*x^4+b*x^2+c)\n";
	aut := SmallGroup(4, 2);
	if models then twists := G3ModelsInCharFF_D4(JI: geometric := geometric); end if;
	return twists, aut;
    end if;

    /*** General case ***/
    vprintf G3Twists, 1 : "Automorphism group C2 \n";
    aut := CyclicGroup(2);
    f := Genus3ConicAndQuartic(JI : models := models);
    if models then
	error if Type(f) eq BoolElt, "[G3Twists] None C2-model found !\n(do J8, J9 and J10 satisfy Shioda algebraic relations ?)";
	twists := [f];
    end if;
    if geometric or not models then return twists, aut; end if;
    return [f, PrimitiveElement(FF)*f], aut;

end function;

intrinsic DiscriminantFromShiodaInvariants(JI::SeqEnum) -> RngElt
    {Compute the discriminant of a genus 3 hyperelliptic curve  with the given
    Shioda Invariants} 

    require #JI eq 9 : "JI must be of size 9 (J2, ..., J10)";
    FF := Universe(JI);
    require not Characteristic(FF) in {2, 3, 5, 7} : "2, 3, 5 and 7 must be invertible in the base ring.";
	
    J2, J3, J4, J5, J6, J7, J8, J9, J10 := Explode(JI);

    /* Discriminant */
    D14 := 
	369994358063104/492075*J2^7 - 364395343642624/10935*J2^5*J4 +  
	683055942467584/32805*J2^4*J3^2 - 10428636769288192/54675*J2^4*J6 -  
	163430755991552/1215*J2^3*J3*J5 + 773557223161856/1215*J2^3*J4^2 +  
	1930310469025792/405*J2^3*J8 + 16530764988416/243*J2^2*J3^2*J4 -  
	70934252748800/27*J2^2*J3*J7 + 3128790930685952/1215*J2^2*J4*J6 -  
	27296194379776/15*J2^2*J5^2 + 335549856481280/9*J2^2*J10 +  
	1727094849536/27*J2*J3^4 - 8473127331823616/3645*J2*J3^2*J6 +  
	6422633971712/9*J2*J3*J4*J5 - 138167587962880/9*J2*J3*J9 +  
	1328382667128832/675*J2*J4^3 + 2908427726618624/45*J2*J4*J8 -  
	89916875603968/5*J2*J5*J7 + 12048213670363136/1215*J2*J6^2 +  
	431773712384*J3^3*J5 + 27887955673088/81*J3^2*J4^2 +  
	5181284548608*J3^2*J8 - 469985685929984/45*J3*J4*J7 +  
	1257325050462208/135*J3*J5*J6 + 3773948974071808/675*J4^2*J6 +  
	884272562962432/15*J4*J10 - 221068140740608/5*J5*J9 -  
	55267035185152/9*J6*J8 - 215886856192*J7^2;

    return D14;

end intrinsic;

intrinsic HyperellipticCurveFromShiodaInvariants(JI::SeqEnum) -> CrvHyp, GrpPerm
    {Compute a genus 3 hyperelliptic curve and its automorphism group from given
    Shioda invariants if they are non-singular, "[], <>" is returned
    otherwise. For singular Shioda invariants, see the function
    "HyperellipticPolynomialFromShiodaInvariants".}

    require #JI eq 9:
	"Argument must be a sequence of nine Shioda invariants J2, ..., J10.";
    if Universe(JI) cmpeq Integers() then
	JI := ChangeUniverse(JI,Rationals());
    end if;

    if DiscriminantFromShiodaInvariants(JI) eq 0 then return [], <>; end if;
    
    twists, aut := G3Models(JI : geometric := true);
    error if Type(twists[1]) eq BoolElt, "G3Twists error: none hyperelliptic curve found at JI = ", JI;
	
    return HyperellipticCurve(twists[1]), aut;
end intrinsic;

intrinsic HyperellipticPolynomialFromShiodaInvariants(JI::SeqEnum) -> RngUPolElt, GrpPerm
    {Compute from given Shioda invariants a univariate polynomial f(x) with f of degree 8.
     This function also returns the automorphism group of the curve y^2 = f(x).}

    require #JI eq 9:
	"Argument must be a sequence of nine Shioda invariants J2, ..., J10.";
    if Universe(JI) cmpeq Integers() then
        JI := ChangeUniverse(JI,Rationals());
    end if;

    twists, aut := G3Models(JI : geometric := true);

    return twists[1], aut;
end intrinsic;

 /***
  * Twists
  *
  ********************************************************************/
intrinsic HyperellipticPolynomialsFromShiodaInvariants(JI::SeqEnum[FldFinElt]) -> SeqEnum[CrvHyp], GrpPerm
{}

    S, G := TwistedHyperellipticPolynomialsFromShiodaInvariants(JI);
    return S, G;
end intrinsic;
 
intrinsic TwistedHyperellipticPolynomialsFromShiodaInvariants(JI::SeqEnum[FldFinElt]) -> SeqEnum[CrvHyp], GrpPerm
    {Compute twisted  hyperelliptic polynomials and their automorphism groups from
    Shioda invariants.}
    
    require #JI eq 9 :
	"Argument must be a sequence of nine Shioda invariants.";

    require Type(Universe(JI)) eq FldFin :
	"Twist computations only available in finite fields";
    
    twists, aut := G3Models(JI);
    twists := [HyperellipticCurve(t) : t in twists];
    return twists, aut;
    
end intrinsic;
/* 
     mch 11/12 - First intrinsic merged with Twists. Second is redundant.
 
intrinsic TwistsOfGenus3HyperellipticCurve(H::CrvHyp) -> SeqEnum[CrvHyp], GrpPerm
    {Compute twisted  hyperelliptic curves and their automorphism groups from
    a genus 3 hyperelliptic curve.}

    require Type(CoefficientRing(H)) eq FldFin :
	"Twist computations only available in finite fields";

    f, _ := HyperellipticPolynomials(H);
    twists := HyperellipticPolynomialTwists(f, 8);
    return [HyperellipticCurve(f) : f in twists],
	GeometricAutomorphismGroupForGenus3HyperellipticCurve(H);

end intrinsic;

intrinsic TwistsOfGenus3HyperellipticPolynomials(f::RngUPolElt) -> SeqEnum[CrvHyp], GrpPerm
    {Compute twisted  hyperelliptic polynomials and their automorphism groups from
    a degree 8 hyperelliptic polynomial.}

    require Type(CoefficientRing(f)) eq FldFin :
	"Twist computations only available in finite fields";

    return HyperellipticPolynomialTwists(f, 8),
	GeometricAutomorphismGroupFromGenus3HyperellipticPolynomial(f);

end intrinsic;
*/

 /***
  * Geometric Automorphism group
  *
  ********************************************************************/
intrinsic GeometricAutomorphismGroupFromShiodaInvariants(JI::SeqEnum) -> GrpPerm
    {Compute the automorphism group from given Shioda invariants (i.e
    from invariants of genus 3 hyperelliptic curves).}
    
    require #JI eq 9 :
	"Argument must be a sequence of nine Shioda invariants J2, ..., J10.";

    if Universe(JI) cmpeq Integers() then
        JI := ChangeUniverse(JI,Rationals());
    end if;
    
    _, aut := G3Models(JI : models := false);
    return aut;

end intrinsic;

/* mch - 12/12 - removed from export. Is redundant. Doesn't actually compute
   the aut group of f (when ShiodaInvariants(f) are singular for example) but that of f
   extended by Z/2Z - as for y^2=f(x).
intrinsic GeometricAutomorphismGroupFromGenus3HyperellipticPolynomial(f::RngUPolElt) -> GrpPerm
    {Compute the automorphism group of the curve y^2 = f(x) where the
    polynomial f, of degree at most 8, is considered as a binary form of degree 8.}
    
    _, aut := G3Models(ShiodaInvariants(f) : models := false);
    return aut;

end intrinsic;

 - this one is now merged with the genus 2 GeometricAutomorphismGroup intrinsic
intrinsic GeometricAutomorphismGroupForGenus3HyperellipticCurve(H::CrvHyp) -> GrpPerm
    {Compute the automorphism group of a genus 3 hyperelliptic curve H.}

    _, aut := G3Models(ShiodaInvariants(H) : models := false);
    return aut;

end intrinsic;
*/

intrinsic GeometricAutomorphismGroupGenus3Classification(FF::FldFin) -> SeqEnum, SeqEnum 
    {Give all possible automorphism groups of a genus 3 hyperelliptic curve,
    and the corresponding number of curves (up to isomorphism and twists) with
    this group, defined over the finite field given in input.}

    p := Characteristic(FF); q := #FF;

    require not p in {2, 3, 5, 7} : "2, 3, 5 and 7 must be invertible in the base ring.";

    C14 := 1; U6 := 1; V8 := 1; C2S4 := 1;
    C2C4 := q-3; D12 := q-3; C2D8 := q-3;
    C4  := q^2-2*q+2; C2p3 := q^2-2*q+2;
    D4 := q^3-2*q^2+3; // Unproved
    C2 := q^5-q^3+q-2; // Unproved

    Grps := [**]; Nmbs := [];
    if C14 ne 0 then
	Grps cat:= [*CyclicGroup(14)*]; Nmbs cat:= [C14];
    end if;
    if U6 ne 0 then
	Grps cat:= [*SmallGroup(24, 5)*]; Nmbs cat:= [U6];
    end if;
    if V8 ne 0 then
	Grps cat:= [*SmallGroup(32, 9)*]; Nmbs cat:= [V8];
    end if;
    if C2S4 ne 0 then
	Grps cat:= [*SmallGroup(48, 48)*]; Nmbs cat:= [C2S4];
    end if;
    if C2C4 ne 0 then
	Grps cat:= [*DirectProduct(CyclicGroup(2), CyclicGroup(4))*]; Nmbs cat:= [C2C4];
    end if;
    if D12 ne 0 then
	Grps cat:= [*SmallGroup(12, 4)*]; Nmbs cat:= [D12];
    end if;
    if C2D8 ne 0 then
	Grps cat:= [*SmallGroup(16, 11)*]; Nmbs cat:= [C2D8];
    end if;
    if C4  ne 0 then
	Grps cat:= [*SmallGroup(4, 1)*]; Nmbs cat:= [C4];
    end if;
    if C2p3 ne 0 then
	Grps cat:= [*SmallGroup(8, 5)*]; Nmbs cat:= [C2p3];
    end if;
    if D4 ne 0 then
	Grps cat:= [*SmallGroup(4, 2)*]; Nmbs cat:= [D4];
    end if;
    if C2 ne 0 then
	Grps cat:= [*CyclicGroup(2)*]; Nmbs cat:= [C2];
    end if;

    return Grps, Nmbs;

end intrinsic;
