freeze;

/***
 *  Reconstruction of genus 3 hyperelliptic curves with automorphism group
 *  equal to D4
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

import "hilbert90.m"   : MConj, MNorm, MActOnC, Glasby;

/* Case D4

   y^2 = a8 * x^8 + a6 * x^6 + a4 * x^4 + a2 * x^2 + a0;
*/
function G3ModelsInCharFF_D4(JI : geometric := false)

    vprintf G3Twists, 2 : "\n[G3Twists] D4: JI = %o\n", JI;
     
    J2, J3, J4, J5, J6, J7, J8, J9, J10 := Explode(JI);
    FF := Universe(JI); x := PolynomialRing(FF).1;
    
    repeat

	/*
         * Let us look for a model of the form
	 *	 f := a0 * x^8 + a6 * x^6 + a4 * x^4 + a2 * x^2 + a0;
         * in some suitable extension.
        */ 

	Pa4 :=
	    (-11022480*J5*J4*J3+2933280*J4*J3^2*J2+784*J2^6+55339200*J6^2+4408992*J4^3+705600*J3^4-36741600*J9*J3-4286520*J5^2*J2+32315760*J6*J4*J2+36741600*J10*J2-64297800*J7*J5+10054800*J6*J3^2-335160*J6*J2^3-47040*J3^2*J2^3+2812320*J4^2*J2^2-97776*J4*J2^4)*x
	    -410791500*J7*J6-10716300*J9*J2^2+4365900*J7*J2^3+150793650*J6*J4*J3+39590775*J6*J5*J2-196465500*J7*J4*J2+10716300*J4^2*J3*J2+1205583750*J8*J5-1157360400*J9*J4+254435580*J5*J4^2+321489000*J10*J3-75014100*J5^2*J3-130977000*J7*J3^2+7144200*J4*J3^3+5120010*J5*J4*J2^2-238140*J4*J3*J2^3-185220*J5*J2^4+5556600*J5*J3^2*J2;

	if Pa4 eq 0 then		/* Pa4 = 0 */
	    vprintf G3Twists, 2 : "[G3Twists] D4: Pa4 = 0, switching to another degree 1 polynomial\n";
	    Pa4 :=
		(-483840*J4*J3^2*J2+2449440*J5*J4*J3-112*J2^6-9072000*J6^2-629856*J4^3-100800*J3^4+612360*J5^2*J2-6713280*J6*J4*J2+9185400*J7*J5-2797200*J6*J3^2+93240*J6*J2^3+6720*J3^2*J2^3-498960*J4^2*J2^2+16128*J4*J2^4+18370800*J8*J4)*x
		+89302500*J7*J6+26460*J5*J2^4-2381400*J4^2*J3*J2-22027950*J6*J4*J3-11013975*J6*J5*J2+41079150*J7*J4*J2+10716300*J5^2*J3-241116750*J8*J5+257191200*J9*J4-56030940*J5*J4^2+23814000*J7*J3^2-1587600*J4*J3^3-793800*J7*J2^3-793800*J5*J3^2*J2-476280*J5*J4*J2^2+52920*J4*J3*J2^3;
	end if;

	if Pa4 eq 0 or Degree(Pa4) eq 0 then
	    vprintf G3Twists, 2 : "[G3Twists] D4: none a4 found, let us skip to the singular case.";
	    break;
	end if;

	/* Ok, fix a4 */
	Pa4 /:= Coefficient(Pa4, Degree(Pa4)); a4 := - Coefficient(Pa4, 0); 
	vprintf G3Twists, 2 : "[G3Twists] D4: Found a4 = %o\n", a4;

	Pa0 :=
	    (-529079040*J5*J4*J3+1551156480*J6*J4*J2+140797440*J4*J3^2*J2-2257920*J3^2*J2^3-4693248*J4*J2^4-1763596800*J9*J3+1763596800*J10*J2+2656281600*J6^2+33868800*J3^4+37632*J2^6+211631616*J4^3+134991360*J4^2*J2^2-16087680*J6*J2^3-205752960*J5^2*J2+482630400*J6*J3^2-3086294400*J7*J5)*x^2
	    +8024365440*J10*J4+530456850*J5^2*J4-472252032*J6*J4^2-4089340080*J9*J5+39293100*J4^2*J3^2-16669800*J5*J3^3-400029840*J6^2*J2-114388848*J4^3*J2-3351600*J3^4*J2-206671500*J10*J2^2+27862380*J5^2*J2^2+10835370*J8*J2^3-15739920*J4^2*J2^3+4675923*J6*J2^4+223440*J3^2*J2^4+488250*J4*J2^5-325061100*J8*J3^2+1130212440*J6*J5*J3-382571910*J7*J4*J3+3472081200*J7^2+36996750*J5*J4*J3*J2+507952620*J7*J5*J2-105019740*J8*J4*J2+206671500*J9*J3*J2-140277690*J6*J3^2*J2-307355310*J6*J4*J2^2-14647500*J4*J3^2*J2^2+555660*J5*J3*J2^3-3724*J2^7-13974055200*J8*J6;

	if Pa0 eq 0 then		/* Pa0 = 0 */
	    vprintf G3Twists, 2 : "[G3Twists] D4: Pa0 = 0, switching to another degree 2 polynomial\n";
	    Pa0 :=
		(117573120*J5*J4*J3-322237440*J6*J4*J2-23224320*J4*J3^2*J2+322560*J3^2*J2^3+774144*J4*J2^4+881798400*J8*J4-435456000*J6^2-4838400*J3^4-5376*J2^6-30233088*J4^3-23950080*J4^2*J2^2+4475520*J6*J2^3+29393280*J5^2*J2-134265600*J6*J3^2+440899200*J7*J5)*x^2
		+1080203040*J9*J5-2469035520*J10*J4+62215776*J6*J4^2+46437300*J8*J3^2-11736900*J4^2*J3^2+2381400*J5*J3^3+20230560*J6^2*J2+15422724*J4^3*J2+478800*J3^4*J2-3980340*J5^2*J2^2-1547910*J8*J2^3+2999430*J4^2*J2^3-1161279*J6*J2^4-31920*J3^2*J2^4-96446700*J5^2*J4+3815002800*J8*J6-257905620*J6*J5*J3+151099830*J7*J4*J3-868020300*J7^2-10206000*J5*J4*J3*J2-72564660*J7*J5*J2-184779630*J8*J4*J2+34838370*J6*J3^2*J2+66418380*J6*J4*J2^2+2457000*J4*J3^2*J2^2-79380*J5*J3*J2^3+532*J2^7-81900*J4*J2^5;
	end if;
    
	if Pa0 eq 0 or Degree(Pa0) eq 0 then
	    vprintf G3Twists, 2 : "[G3Twists] D4: none a0 found, let us skip to the singular case.";
	    break;
	end if;

	/* Ok, fix a0 (any root, if any, works) */
	Fa0 := Sort(Factorization(Pa0), func<x, y| Degree(x[1]) - Degree(y[1])>);
	Pa0 := Fa0[1, 1]; Pa0 /:= Coefficient(Pa0, Degree(Pa0));
	if Degree(Pa0) eq 2 then
	    K2 := ExtensionField<FF, x | Pa0>; a0 := K2.1;
	    vprintf G3Twists, 2 : "[G3Twists] D4: Found Pa0 = %o\n", Pa0;
	else
	    K2 := FF;  a0 := - Coefficient(Pa0, 0); 
	    vprintf G3Twists, 2 : "[G3Twists] D4: Found a0 = %o\n", a0;
	end if;
	x := PolynomialRing(K2).1;

	Pa2 :=
	    x^4*a0+
	    (-392/9*J3+20/3*a0^2*a4+17/525*a4^3-22/15*a4*J2)*x^2
	-777/50*a0*a4^2*J2+224/5*a0^3*a4^2-686*a0^3*J2+24/125*a0*a4^4-1372/15*a0*a4*J3+4802/5*a0*J4+2744/15*a0*J2^2;
    
	if Pa2 eq 0 then		/* Pa2 = 0 */
	    vprintf G3Twists, 2 : "[G3Twists] D4: Pa2 = 0 (i.e a0 = 0), switching to a degree 1 polynomial\n";
	    Pa2 := x - 1;
	end if;
    
	if Pa2 eq 0 or Degree(Pa2) eq 0 then
	    vprintf G3Twists, 2 : "[G3Twists] D4: none a2 found, let us skip to the singular case.";
	    break;
	end if;

	/* Ok, fix a2 (any root, if any, works) */
	Fa2 := Sort(Factorization(Pa2), func<x, y| Degree(x[1]) - Degree(y[1])>);

	Pa2 := Fa2[1, 1]; Pa2 /:= Coefficient(Pa2, Degree(Pa2));
	if Degree(Pa2) ge 2 then
	    K8 := ExtensionField<K2, x | Pa2>; a2 := K8.1;
	    vprintf G3Twists, 2 : "[G3Twists] D4: Found Pa2 = %o\n", Pa2;
	else
	    K8 := K2;  a2 := - Coefficient(Pa2, 0); 
	    vprintf G3Twists, 2 : "[G3Twists] D4: Found a2 = %o\n", a2;
	end if;
	x := PolynomialRing(K8).1;

	if a2 ne 0 then
	    Pa6 := 5*x*a2+140*a0^2+a4^2-70*J2;
	else	
	    Pa6 := x^2*a0 - 8/525*a4^3 + 28/15*a4*J2 - 392/9*J3;	
	end if;

	if Pa6 eq 0 or Degree(Pa6) eq 0 then
	    vprintf G3Twists, 2 : "[G3Twists] D4: none a6 found, let us skip to the singular case.";
	    break;
	end if;
    
	Fa6 := Sort(Factorization(Pa6), func<x, y | Degree(x[1]) - Degree(y[1])>);
    
	Pa6 := Fa6[1, 1]; Pa6 /:= Coefficient(Pa6, Degree(Pa6));
	if Degree(Pa6) eq 2 then
	    K := ExtensionField<K8, x | Pa6>; a6 := K.1;
	    vprintf G3Twists, 2 : "[G3Twists] D4: Found Pa6 = %o\n", Pa6;
	else
	    K := K8;  a6 := - Coefficient(Pa6, 0); 
	    vprintf G3Twists, 2 : "[G3Twists] D4: Found a6 = %o\n", a6;
	end if;
	x := PolynomialRing(K).1;

	/* Adding a degree 2 extension (necessary for a rational model) */
	if IsFinite(FF) then
	    PI := IrreduciblePolynomial(K,2);
	    K16<I> := ExtensionField<K, x | PI>; I := K16.1;
	    x := PolynomialRing(K16).1;
	end if;
    
	f := a0 * x^8 + a6 * x^6 + a4 * x^4 + a2 * x^2 + a0;
    
	vprintf G3Twists, 2 : "[G3Twists] D4: Found f = %o\n", f;
	vprintf G3Twists, 3 : "[G3Twists] D4: ShiodaInvariants are    %o\n", ShiodaInvariants(f);
	vprintf G3Twists, 3 : "[G3Twists] D4: (to be compared to JI = %o)\n\n", JI;
        
	f /:= Coefficient(f, Degree(f));
    
	if &and[c in FF : c in Eltseq(f)] eq true then
	
	    f := PolynomialRing(FF)!Eltseq(f);
	    vprintf G3Twists, 2 : "[G3Twists] D4: *** f = %o\n", f;
	    if geometric then return [f]; end if;
	    return HyperellipticPolynomialTwists(f, 8);
	end if;
    
	if not IsFinite(FF) then
	    vprintf G3Twists, 2 : "[G3Twists] D4: *** f = %o\n", f;
	    if geometric then return [f]; end if;			  
	    error "[G3Twists] currently, no twists computation done in G3ModelsInCharFF_D4, sorry";
	    return [];
	end if;
    
	sigma := map< K16 -> K16 | x :-> x^(#FF) >;
	fc := Parent(f)![sigma(el):el in Eltseq(f)];
    
	/* Let us determine M s.t. x' = M(x) with
	        y^2 = f(x) and y'^2 = f(x') 

	ret, MLc := IsGL2Equivalent(f, fc, 8);
	vprintf G3Twists, 2 : "[G3Twists] D4: MLC is %o\n",
        [[MinimalPolynomial(p, FF) : p in Mc] : Mc in MLc];
	error if ret eq false,
		    "[G3Twists] D4: No galois geometric automorphism found\n";
	Mc := MLc[1];
	M := Matrix(2, 2, Mc)^(-1);
        */

	JR := [r[1] : r in Roots(x^4+1)]; I := Sqrt(K16!-1);
	M := Matrix(2, 2, [K16!0, 0, 0, 0]);
	for Mt in
	    [Matrix(2, 2, [K16!0, 1, J, 0]) : J in JR] cat
		[Matrix(2, 2, [K16!1, 0, 0, J]) : J in JR] cat
		[
		Matrix(2, 2, [K16!0, 1, I, 0]),
		Matrix(2, 2, [K16!1, 0, 0, I]),
		Matrix(2, 2, [K16!0, 1, 1, 0])
		] do
		fd  := MActOnC(f, 8, Mt);
	    if Degree(fd/fc) eq 0 then M := Mt^(-1); break; end if;
	end for;

	if M eq 0 then
	    ret, MLc := IsGL2Equivalent(f, fc, 8);
	    vprintf G3Twists, 2 : "[G3Twists] D4: MLC is\n", MLc, 
		[[MinimalPolynomial(p, FF) : p in Mc] : Mc in
		MLc];
	    error "[G3Twists] D4: But no galois geometric automorphism found ??\n";
	end if;

	vprintf G3Twists, 2 : "[G3Twists] D4: Using M =\n%o\n", M;

	/* Then A s.t M = (A^sigma)^(-1) * A */
	A := Glasby(M, sigma, FF);
	if A eq 0 then
	    vprintf G3Twists, 2 : "[G3Twists] D4: But no rational model found\n";
	    return [];			
	end if;
    
	/* And ftilde */
	ftilde  := MActOnC(f, 8, A^(-1));
	ftilde /:= Coefficient(ftilde, Degree(ftilde));
	ftilde  := PolynomialRing(FF)!Eltseq(ftilde);
	vprintf G3Twists, 2 : "[G3Twists] D4: *** f = %o\n", ftilde;

	if geometric then return [ftilde]; end if;
	return HyperellipticPolynomialTwists(ftilde, 8);			  
    until true;

    /* Singular invariants ? => let us first look for a singular model of the form
     *		 f := a8 * x^8 + a6 * x^6 + a4 * x^4 + a2 * x^2;
    */

    vprintf G3Twists, 2 : "[G3Twists] D4: Singular case\n";

    x := PolynomialRing(FF).1;
    Pa4 :=
	(11741206932*J7+7172848242*J4*J3-407219400*J3*J2^2-340313967*J5*J2)*x
	-770798216160*J8+48652305408*J6*J2-21652069824*J4^2-15830753400*J5*J3+1196327160*J4*J2^2-77421296*J2^4-6442857120*J3^2*J2;
    if Pa4 eq 0 then
	vprintf G3Twists, 2 : "[G3Twists] D4: Pa4 = 0, switching to another degree 1 polynomial\n";
	Pa4 :=
	    (488750830848*J4^2+19912489511040*J8+119825959260*J3^2*J2+272672590848*J4*J2^2-11523989242*J2^4)*x
	    +663046656007680*J9+29540232087660*J7*J2-147027580680960*J5*J4-238603106730240*J6*J3-32453930490450*J4*J3*J2+5621022644895*J5*J2^2+590440221000*J3*J2^3;
    end if;
    if Pa4 eq 0 then
	vprintf G3Twists, 2 : "[G3Twists] D4: Pa4 = 0, switching to another degree 1 polynomial\n";
	Pa4 :=
	    (7023805824*J6*J2-83616540*J3^2*J2+1090412288*J4*J2^2+1936166400*J4^2-40257382*J2^4)*x
	    +231759118080*J9-96001584000*J5*J4-23998355150*J4*J3*J2-191099623680*J6*J3-32526010860*J7*J2+310611000*J3*J2^3-617600655*J5*J2^2;
    end if;	
    if Pa4 eq 0 then
	Pa4 := x;
    end if;
	    
    if Degree(Pa4) eq 0 then /* This should not happen */
	error "[G3Twists] D4 : ARGHH, none a4 found ! I give up";
	return [];			
    end if;

    a4 := Roots(Pa4)[1, 1];
    vprintf G3Twists, 2 : "[G3Twists] D4: ... testing a4' = %o\n", a4;
    
    a8 := -17/525*a4^3+22/15*a4*J2+392/9*J3;	    
    a2 := FF!1;
    a6 := -1/5*(a4^2-70*J2)/a2;
    
    f := a8 * x^8 + a6 * x^6 + a4 * x^4 + a2 * x^2;
    
    vprintf G3Twists, 2 : "[G3Twists] D4: *** f = %o\n", f;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;
