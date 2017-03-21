freeze;

/***
 *  Mini Toolboox for handling binary form invariants.
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
 * Exported intrinsics.
 *
 * intrinsic WPSEnumInit(FF::FldFin, Wght::SeqEnum) -> Rec
 * intrinsic WPSEnumNext(~V, ~WPSCtxt::Rec)
 * intrinsic WPSEqual(Wght::SeqEnum, V1::SeqEnum, V2::SeqEnum) -> BoolElt
 * intrinsic WPSNormalize(Wght::SeqEnum, V::SeqEnum) -> SeqEnum
 *
 ********************************************************************/

 /*
   Given two covariants F an G, coded as lists of the form [pol, degree, order],
   return their transvectant of level r
*/
function Transvectant(F, G, r : scaled := true)

    Q, Qdeg, n := Explode(F);
    R, Rdeg, m := Explode(G);
    
    n := IntegerRing()!n;
    m := IntegerRing()!m;
    
    K := BaseRing(Parent(Q));
    
    h := Parent(Q)!0;
    for k := 0 to r do
	h +:= (-1)^k
	    * Binomial(m-k,r-k)  * Derivative(Q, r-k)
	    * Binomial(n-r+k, k) * Derivative(R, k);
    end for;

    if scaled eq true then
        coef := Factorial(r) * Factorial(m-r) * Factorial(n-r) / Factorial(m) / Factorial(n);
	h := (K!coef) * h;
    end if;
	
    return [* h, Qdeg + Rdeg, n + m - 2*r *];

end function;

/* Data structures */
WPSEnum  := recformat< FF, p, n, q, Wght,
    holes, x, Idx, Cp, first>;
FFEnum  := recformat< FF, p, t, x>;


/* Initialisation */
FFEnumInit := function(FF, t)
    FFCtxt := rec<FFEnum |
                  FF := FF,
                  p := Characteristic(FF),
		  t := t,
		  x := 0>;
   return FFCtxt;
end function;

/* Enumeration of a vector of finite fields elements */
FFEnumNext := procedure(~V, ~FFCtxt)
    p := FFCtxt`p;
    x := FFCtxt`x; t := FFCtxt`t;

    X := Intseq(x+p^t, p)[1..t];
    FFCtxt`x +:= 1;
    FFCtxt`x := FFCtxt`x mod p^(t);
    
    V := [FFCtxt`FF!X[1+k] : k in [0..(t-1)]];
end procedure;

intrinsic WPSEnumInit(FF::FldFin, Wght::SeqEnum) -> Rec
{ Internal function }
    //{Initialize a structure for use with WPSEnumNext in order to enumerate
    //points in weighted projective space defined over a finite field FF with
    //weights given by Wght.}

    WPSCtxt := rec<WPSEnum |
                  FF := FF,
		  p  := Characteristic(FF),
                  n  := Degree(FF),
		  q  := #FF,
		  
		  Wght := Wght,
		  holes := 0,
		  x  := 0,
		  Idx := [],
		  Cp := [],
		  first := 0>;

    return WPSCtxt;
end intrinsic;

/* A deterministic (but inefficient) version of XGCD */
function XGCDUnique(L)
    if #L eq 0 then
	return 0, [];
    end if;

    if #L eq 1 then
	return L[1], [Universe(L)!1];
    end if;

    g := GCD(L); C := [Universe(L)!0 : c in L];

    gc, C[1], C[2] := XGCD(L[1], L[2]); idx := 2;
    while gc ne g do
	idx +:= 1;
	gc, x, C[idx] := XGCD(gc, L[idx]);
	for i := 1 to idx-1 do
	    C[i] *:= x;
	end for;
    end while;

    return g, C;
end function;

/* A XGCD variant s.t
        _ &+[C[i]*L[i] : i in [1..#L]] = g mod n
        _ and one of the C_i is invertible mod n
*/
function XGCDUniqueMod(L, n)

    g, C := XGCDUnique(L);
    wght := [(c div g) mod n  : c in L];
    
    CF := C; II := [i : i in [1..#CF] | Gcd(CF[i], n) eq 1];
    if II eq [] then
	    
	FFCtxt := FFEnumInit(ResidueClassRing(n), #L-1);

	while II eq [] do
	    FFEnumNext(~cof, ~FFCtxt); CF  := C;
	    CF[1] +:= &+[(IntegerRing()!cof[i])*wght[i+1] : i in [1..#L-1]];
	    for  i := 2 to #L do
		CF[i] -:= cof[i-1]*wght[1];
	    end for;
	    II := [i : i in [1..#CF] | Gcd(CF[i], n) eq 1];
	end while;
    end if;
	
    return g, [c mod n : c in CF];
end function;

intrinsic WPSEnumNext(~V, ~WPSCtxt::Rec)
{ Internal function. }
    //{Compute the next representative points in a weighted projective space.}
    
    FF :=  WPSCtxt`FF; q := WPSCtxt`q; p := WPSCtxt`p; n := WPSCtxt`n;
    
    Wght := WPSCtxt`Wght;

    x := WPSCtxt`x; 
    holes := WPSCtxt`holes;
    Idx := WPSCtxt`Idx;
    Cp := WPSCtxt`Cp;
    first := WPSCtxt`first;
    
    if q eq 2 then

	V := [FF!v : v in Intseq(2^#Wght+holes, 2)[1..#Wght]];	

	WPSCtxt`holes +:= 1;
	WPSCtxt`holes := WPSCtxt`holes mod 2^#Wght;

	return;
    end if;

    V := [WPSCtxt`FF!0 : w in Wght];
    
    if holes eq 0 then
	WPSCtxt`holes +:= 1;
	WPSCtxt`holes := WPSCtxt`holes mod 2^#Wght;
	WPSCtxt`x := 0;

	return;
    end if;

    if x eq 0 then
	Vh := Intseq(2^#Wght+holes, 2)[1..#Wght];
	Idx := [i : i in [1..#Wght] | Vh[i] ne 0];

	if #Idx eq 1 then
	    WPSCtxt`holes +:= 1;
	    WPSCtxt`holes := WPSCtxt`holes mod 2^#Wght;

	    V [Idx[1]] := WPSCtxt`FF!1;

	    return;
	end if;
	
	g, C := XGCDUniqueMod([Wght[i] : i in Idx], #FF-1);
	first := Min([i : i in [1..#C] | Gcd(C[i], #FF-1) eq 1]);
	Cp := [IntegerRing()!ResidueClassRing(#FF-1)!(c/C[first]) : c in C];

	WPSCtxt`Idx := Idx;
	WPSCtxt`Cp  := Cp;
	WPSCtxt`first := first;	
    end if;

    t := #Idx-1;
    
    X := Intseq(x+(q-1)^t, q-1)[1..t];
    
    Vv := [WPSCtxt`FF!Intseq(1+a+p^n, p)[1..n] : a in X];

    J := FF!1; nb := 0;
    for i := 1 to #Idx do
	if i ne first then
	    nb +:= 1;
	    J *:= Vv[nb]^Cp[i];
	    V[Idx[i]] := Vv[nb];
	end if;
    end for;

    V[Idx[first]] := 1/J;
 
    WPSCtxt`x +:= 1;
    WPSCtxt`x := WPSCtxt`x mod (q-1)^t;

    if WPSCtxt`x eq 0 then
	WPSCtxt`holes +:= 1;
	WPSCtxt`holes := WPSCtxt`holes mod 2^#Wght;
    end if;

end intrinsic;

intrinsic WPSEqual(Wght::SeqEnum, V1::SeqEnum, V2::SeqEnum) -> BoolElt
{ Internal function. }
    //{Check that representatives of 2 points in a weighted projective space are
    //equivalent.} 
    
    require Universe(V1) eq Universe(V2):   "V1 and V2 must have the same definition field";
    require #V1 eq #V2 and #V1 eq #Wght:    "Wght, V1 and V2 must have same length";
    require Type(Universe(Wght)) eq RngInt: "Wght  must contain integers";
    
    Idx1 := [i : i in [1..#Wght] | IsUnit(V1[i]) ];
    Idx2 := [i : i in [1..#Wght] | IsUnit(V2[i]) ];

    if Idx1 ne Idx2 then return false; end if;

    g, C := XGCDUnique([Wght[i] : i in Idx1]);

    /* lbdpowg := 1; */
    /* for j := 1 to #Idx1 do */
    /* 	lbdpowg *:= (V1[Idx1[j]]/V2[Idx1[j]])^C[j]; */
    /* end for; */

    Nlbdpowg := 1;
    Dlbdpowg := 1;
    for j := 1 to #Idx1 do
	if C[j] gt 0 then
	    Nlbdpowg *:= V1[Idx1[j]]^C[j];
	    Dlbdpowg *:= V2[Idx1[j]]^C[j];
	else
	    Nlbdpowg *:= V2[Idx1[j]]^(-C[j]);
	    Dlbdpowg *:= V1[Idx1[j]]^(-C[j]);
	end if;
    end for;

    /* check := true; */
    /* for i in Idx1 do */
    /* 	mu := (V1[i]/V2[i]); */
    /* 	if mu ne lbdpowg^(Wght[i] div g) then */
    /* 	    check := false; break; */
    /* 	end if; */
    /* end for; */

    check := true;
    
    Pows := [[i, (Wght[i] div g)] : i in Idx1];
    Sort(~Pows, func<x, y | x[2] - y[2]>);

    Nlbdpowg1 := 1;
    Dlbdpowg1 := 1;
    pow := 0;
    for p in Pows do
	if p[2] ne pow then 
	    Nlbdpowg1 *:= Nlbdpowg^(p[2]-pow);
	    Dlbdpowg1 *:= Dlbdpowg^(p[2]-pow);
	    pow := p[2];
	end if;
	EQ := V1[p[1]]*Dlbdpowg1 - Nlbdpowg1*V2[p[1]];
	if EQ ne 0 then check := false; break; end if;
    end for;
    
    return check;

end intrinsic;

intrinsic WPSNormalize(Wght::SeqEnum, V::SeqEnum) -> SeqEnum
{ Internal function. }
    //{Compute a normalized representative of a points in a weighted projective space.} 

    require #V eq #Wght:    "Wght, V and Wght must have same length";
    require Type(Universe(Wght)) eq RngInt: "Wght  must contain integers";

    Idx := [ i : i in [1..#Wght] | IsUnit(V[i]) ];

    if #Idx eq 0 then return V; end if;

    if Type(Universe(V)) eq FldFin then
	g, C := XGCDUniqueMod([Wght[i] : i in Idx], #Universe(V)-1);
    else
	g, C := XGCDUnique([Wght[i] : i in Idx]);
    end if;

    /* lbdpowg := 1; for j := 1 to #Idx do lbdpowg *:= V[Idx[j]]^C[j]; end for; */

    Nlbdpowg := 1; Dlbdpowg := 1;
    for j := 1 to #Idx do
	if C[j] gt 0 then
	    Nlbdpowg *:= V[Idx[j]]^C[j];
	else
	    Dlbdpowg *:= V[Idx[j]]^(-C[j]);
	end if;
    end for;
    Nlbdpowg := 1/Nlbdpowg;

    /* return [ V[i] / (lbdpowg^(Wght[i] div g)) : i in [1..#V]]; */

    Pows := [[i, (Wght[i] div g)] : i in Idx];
    Sort(~Pows, func<x, y | x[2] - y[2]>);

    W := V; Nlbdpowg1 := 1; Dlbdpowg1 := 1; pow := 0;
    for p in Pows do
	if p[2] ne pow then 
	    Nlbdpowg1 *:= Nlbdpowg^(p[2]-pow);
	    Dlbdpowg1 *:= Dlbdpowg^(p[2]-pow);
	    pow := p[2];
	end if;
	W[p[1]] := V[p[1]] * Nlbdpowg1 * Dlbdpowg1;
    end for;

    return W;
end intrinsic;
