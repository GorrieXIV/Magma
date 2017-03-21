freeze;

import "recognise_su3.m": RootElementOfSU3;
import "bbprelims.m": ElementHavingPrescribedNorm,
                    HyperbolicTransition,
                    BruteForceHomomorphism,
		    ElementHavingPrescribedTrace,
                    PreservesSesquilinearForm,
                    PGL2ActionOnTransvectionGroups, 
		    MyInsertBlock,
		    MyCoefficients,
		    MyEltseq,
                    IsHermitianForm;
import "bbsporadics.m": SporadicSU4;

/////////////////////////////////////////////////////////////
//                                                         //
// This file contains the generic constructive recognition //
// functions for central quotients of SU(4,q). The         //
// sporadic cases of q in {2, 3, 4, 5, 7} are              //
// are handled separately.                                 //
//                                                         //
/////////////////////////////////////////////////////////////



/*
   Return an element of order roughly q+1 that
   decomposes the underlying module as 1 + 3
*/

SU4_GOOD_ELEMENT := function (G, proc, q, limit)
     count := 0;
     o1 := q^3 + 1;
     good := [ o1 ];
     if (q + 1) mod 2 eq 0 then
        Append (~good, o1 div 2);
     end if;
     if (q + 1) mod 4 eq 0 then
        Append (~good, o1 div 4);
     end if;
     o2 := q^2 - q + 1;
     found := false;
     while ( (count lt limit) and (not found) ) do
	  count +:= 1;
          g, w := Random (proc);
          og := Order (g);
          if (og in good) then
	     a := g^(2 * o2);
             wa := w^(2 * o2);
             o := Order (a);
             if (o gt Max (2, q div 4)) then
	         found := true;
             end if;
          end if;
     end while;
     if (found) then 
         return true, a, wa; 
     else 
         return false, _, _; 
     end if;
end function;


/*
   Return a naturally embedded SL(2,q) subgroup of G.
*/

SU4_CONSTRUCT_L := function (G, proc, a, wa, q) 

     trials := 0;
     found := false;
     while ((not found) and (trials le 10)) do
	  trials +:= 1;
          
               g, w := Random (proc);
               b := a^g;
               wb := wa^w;
               A := sub < Generic (G) | [a, a^g] >;
               L, wL := DerivedGroupMonteCarlo (A);        
               flag, phiL, tauL, gammaL, deltaL := RecogniseSL2 (L, q);
               if (flag) then
	            found := true;
               end if;        
     end while;

     if (not found) then
     "failed to construct suitable L";
          return false, _, _;
     end if;

     // modify <wL> to give words in <G.i>
     wL := [ Evaluate (w, [wa, wb]) : w in wL ];

     // put together the constructions that we wish to return
     mu := PrimitiveElement (GF (q));
     S := SL (2, q)![ 1 , 0 , 1 , 1 ];
     T := SL (2, q)![ 1 , 1 , 0 , 1 ];
     H := SL (2, q)![ mu , 0 , 0 , 1/mu ];
     s := S @ tauL;
     t := T @ tauL;
     h := H @ tauL;
     ws := s @ gammaL;
     wt := t @ gammaL;   // words in <L.i>
     wh := h @ gammaL;
     ws := Evaluate (ws, wL);
     wt := Evaluate (wt, wL);   // words in <G.i>
     wh := Evaluate (wh, wL);

     L := sub < Generic (G) | [ s , t , h ] >;
     wL := [ ws , wt , wh ];

assert forall { i : i in [1..Ngens (L)] |
    Evaluate (wL[i], [ G.j : j in [1..Ngens (G)] ]) eq L.i };

return true, L, wL;   
end function;


/*
   Return a naturally embedded SU(3,q)-subgroup of G containing L.
*/

SU4_CONSTRUCT_NATURAL_SU3 := function (G, proc, L, wL, q)

     s := L.1;
     ws := wL[1];
     count := 0;
     repeat
         count +:= 1;
         g, w := Random (proc);
         u := s^g;
         wu := ws^w;
         J := sub < Generic (G) | 
                     [ L.i : i in [1..Ngens (L)] ] cat [ u ] >;
         if IsProbablyPerfect (J) then
	     // only do constructive recognition on "good" <J>s
             flag, phi, tau, gamma, delta := RecogniseSU3 (J, q);
         else
             flag := false;
         end if;
     until ((flag) or (count ge 12));

     if (not flag) then
         return false, _, _, _, _, _, _;
     end if;

     wJ := wL cat [ wu ];

return flag, J, wJ, phi, tau, gamma, delta;
end function;

/*
   Given opposite (non-commuting) transvections <S> and <T>
   in SU(3,<E>) find a change-of-basis matrix <C> such that
                  [ 1 0 0 ]                      [ 1 0 y ]
   <C><S><C>^-1 = [ 0 1 0 ]  and  <C><T><C>^-1 = [ 0 1 0 ]
                  [ x 0 1 ]                      [ 0 0 1 ]
   where <x> and <y> are (unspecified) trace-zero elements of <E>
*/
   
SU3_CHANGE_OF_BASIS_MATRIX := function (S, T)

     E := BaseRing (Parent (S));
     l := Degree (E);
assert l mod 2 eq 0;
     k := l div 2;
     F := GF (Characteristic (E)^k);
     MA := MatrixAlgebra (E, 3);
     form := MA![0,0,1,0,1,0,1,0,0];
     V := VectorSpace (E, 3);
     XS := MA!S - Identity (MA);
     XT := MA!T - Identity (MA);
     SS := sub < V | Image (XS) >;
     TT := sub < V | Image (XT) >;
     if Dimension (SS) * Dimension (TT) ne 1 then
        "problem with SU3-isomorphism(s)";
        return Identity (GL (3, E));
     end if;
     e := SS.1;   f := TT.1; 
     e := e / InnerProduct (e * form, FrobeniusImage (f, k));
     U := Nullspace (XS) meet Nullspace (XT);
assert Dimension (U) eq 1;
     u := U.1;
     a := InnerProduct (u * form, FrobeniusImage (u, k));
     b := ElementHavingPrescribedNorm (F, E, a);
     u := u / b;
     bas := [ V!e , V!u , V!f ];
     
return GU (3, E)!Matrix (bas);
end function;
   

/*
   Input:
     (1) <Qgens> 
     (2) An element <r> of the form
            [ 1   c  a  b ]
            [ 0   1  0  0 ]
            [ 0 -b^q 0  0 ]
            [ 0 -a^q 0  0 ]
         namely an element of the (matrix) group <Q>
   Output: a word in <Qgens> that evaluates to <r>
*/

NRSU4_QSLP := function (Qgens, r)  

     assert #Qgens mod 5 eq 0;
     e := #Qgens div 5;

     k := BaseRing (Parent (r));

     u := VectorSpace (k, 2)![ r[1][3] , r[1][4] ];
     Q := [ VectorSpace (k, 2)![ Qgens[i][1][3] , Qgens[i][1][4] ] :
	    	          i in [e+1..#Qgens] ];
     coeffs := MyCoefficients (Q, u);
     r0 := &*[ Qgens[e+i]^coeffs[i] : i in [1..#coeffs] ];
     t0 := r * r0^-1;

     c0 := t0[1][2];
     c := Qgens[1][1][2];
     q := Characteristic (k)^e;
     k0 := GF (q);
     B := [ k0!(Qgens[i][1][2]/c) : i in [1..e] ];
     d := k0!(c0/c);
     Tcoeffs := MyEltseq (B, d);
assert t0 eq &*[ Qgens[i]^Tcoeffs[i] : i in [1..e] ];

     pows := Tcoeffs cat coeffs;
     X := SLPGroup (5*e);

return &* [ (X.i)^pows[i] : i in [1..5*e] ];
end function;


su2_to_sl2 := function (alpha)
     K := Parent (alpha);
     e := Degree (K);
assert (e mod 2 eq 0);
     f := e div 2;
assert alpha + Frobenius (alpha, f) eq 0;
     su2 := SU (2, K);
     k := GF (Characteristic (K), f);
     sl2 := SL (2, k);
     image := function (x, d)
         y := MatrixAlgebra (BaseRing (Parent (x)), Degree (Parent (x)))!x;
         y[1][2] := y[1][2] * d;
         y[2][1] := y[2][1] / d;
         return y;
     end function;
return hom < su2 -> sl2 | x :-> sl2!image (x, alpha) >;
end function;

/*
   EOB function:
   g is element of G which is isomorphic to SU(d, q);
   solve for g as SLP in defining generators of G;
   X = the copy of the standard generators of SU(4, q) in G;
   X is obtained by evaluating words in the defining generators of G;
   first express g as an SLP in X, then evaluate the SLP in words
   to obtain an SLP for g in the defining generators of G
*/

ElementToSLP := function (G, words, X, d, q, g)
   flag, w := ClassicalRewrite (G, X, "SU", 4, q, g);
   if not flag then return false, _; end if;
   w := Evaluate (w, words);
   return true, w;
end function;


////////////////////////////////////////////////////////////////////////////
//  [Br] P. A. Brooksbank, Fast constructive recognition of black box 
//  unitary groups, LMS J. Comput. Math. 6 (2003), 1 -- 36. (Section 6.2)
//
// This is the main engine for the intrinsics to follow
////////////////////////////////////////////////////////////////////////////

IsBlackBoxSU4 := function (G, q)

     proc := RandomProcessWithWords (G);

     //////////////////////////////////////////////////// 
     // find a naturally embedded SL(2,q) subgroup <L> //
     //              ---- See [Br], Section 6.2.1 ---- //
     ////////////////////////////////////////////////////
     
     limit := 16 * Ceiling (Log (2, q));
     flag, a, wa := SU4_GOOD_ELEMENT (G, proc, q, limit);
     if (not flag) then
         return false, _;
     end if;
       
     flag, L, wL := SU4_CONSTRUCT_L (G, proc, a, wa, q);
     if (not flag) then
         return false, _;
     end if;
       
     ///////////////////////////////////////////// 
     // find two SU(3,q) subgroups containg <L> //
     //   ---- See [Br], Section 6.2.2 ----     //
     /////////////////////////////////////////////
     
     flag, J1, wJ1, phi1, tau1, gamma1, delta1 :=
                 SU4_CONSTRUCT_NATURAL_SU3 (G, proc, L, wL, q);
     if (not flag) then
         return false, _;
     end if;
       
     flag, J2, wJ2, phi2, tau2, gamma2, delta2 :=
                 SU4_CONSTRUCT_NATURAL_SU3 (G, proc, L, wL, q);
     if (not flag) then
         return false, _;
     end if;
     
     /////////////////////////////////////////////
     // the basic idea is to embed SU(3,<E>) in //
     // SU(4,<E>) using <phi1> and then to      //
     // modify <phi2> so that the the two maps  //
     // define consistent embeddings.           //
     /////////////////////////////////////////////
     F := GF (q);
     k := Degree (F);
     p := Characteristic (F);
     E := ext < F | 2 >;
     form := ClassicalForms (SU (3, E))`sesquilinearForm;
   
     s := L.1;
     t := L.2;
     ss := s @ phi1;
     tt := t @ phi1;
     if Order (ss) ne p or Order (tt) ne p then
        return false, _;
     end if;
     C1 := SU3_CHANGE_OF_BASIS_MATRIX (ss, tt);
     ss := s @ phi2;
     tt := t @ phi2;
     if Order (ss) ne p or Order (tt) ne p then
        return false, _;
     end if;
     C2 := SU3_CHANGE_OF_BASIS_MATRIX (ss, tt);
     iota1 := hom < GL (3, E) -> GL (4, E) | 
                          x :-> MyInsertBlock (x, 4, [1,2,4]) >;
     iota2 := hom < GL (3, E) -> GL (4, E) | 
                          x :-> MyInsertBlock (x, 4, [1,3,4]) >;
     psi1 := hom < Generic (J1) -> GL (4, E) | 
                          x :-> (C1 * (x @ phi1) * C1^-1) @ iota1 >;
     
     r := PrimitiveElement (E);
     hhh := SU (3, E)![r, 0, 0, 0, r^(q-1), 0, 0, 0, 1/r^q];  
     y1 := ElementHavingPrescribedTrace (F, E, -1);
     yr := ElementHavingPrescribedTrace (F, E, -r^(q+1));
     uuu := RootElementOfSU3 (E, 1, y1);
     www := RootElementOfSU3 (E, r, yr);
     u1 := (C1^-1 * uuu * C1) @ tau1;
     w1 := (C1^-1 * www * C1) @ tau1;
     u2 := (C2^-1 * uuu * C2) @ tau2;
     if (s, u1) ne Identity (G) or (s, u2) ne Identity (G) 
       or (s, w1) ne Identity (G) then
       return false, _;
     end if;
     h1 := (C1^-1 * hhh * C1) @ tau1;
     h2 := (C2^-1 * hhh * C2) @ tau2;
     
     if (h1, h2) eq Identity (G) then   
        return false, _;
     end if;

     z1 := h1^(q-1);   z2 := h2^(q-1);
       // <zi> is a generator for the centralizer in <Ji> of <L>
     A0 := sub < Generic (G) | [ z1 , z2 ] >;
     L0, wL0 := DerivedGroupMonteCarlo (A0);
     flag, phi0, tau0, gamma0, delta0 := RecogniseSL2 (L0, q);
     if (not flag) then
         return false, _;
     end if;

     //////////////////////////////////////////////////
     // Compute the action of <z1> and <z2> on <L0>: //
     // see Procedure 6.9, Steps 3 and 4.            //
     //////////////////////////////////////////////////
     flag, zz1, _ := PGL2ActionOnTransvectionGroups 
                         (L0, phi0, tau0, z1 : PSLAction := false);
     flag, zz2, _ := PGL2ActionOnTransvectionGroups 
                         (L0, phi0, tau0, z2 : PSLAction := false);
     zz1 := GL (2, E)!zz1;
     zz2 := GL (2, E)!zz2;
         // find an Hermitian form preserved by <zz1> and <zz2>
     X := [ zz1 , zz2 ];
     Y := [ FrobeniusImage (Transpose (x^-1), k) : x in X ];
     form_space := AHom (GModule (sub < GL (2, E) | X >),
                          GModule (sub < GL (2, E) | Y >));
assert Dimension (form_space) eq 1;
     M := MatrixAlgebra (E, 2)!(form_space.1);
assert exists (N){ x * M : x in E | IsHermitianForm (x * M) };
         // compute the eigenvectors of <zzi>
     evals1 := Eigenvalues (zz1);
     evals2 := Eigenvalues (zz2);
     evecs1 := [ Eigenspace (zz1, x[1]).1 : x in evals1 ];
     evecs2 := [ Eigenspace (zz2, x[1]).1 : x in evals2 ];
     
     //////////////////////////////////////////////////////
     // Compute <z> in <L0> conjugating <Q2> / <S> to a  //
     // vector of <Q> / <S> perpendicular to <Q1> / <S>: //
     //               see Procedure 6.9, Steps 5 and 6.  //
     //////////////////////////////////////////////////////

     B1 := [];
     for v in evecs1 do
         lambda := InnerProduct (v * N, FrobeniusImage (v, k));
         gamma := ElementHavingPrescribedNorm (F, E, lambda);
         Append (~B1, v / gamma);
     end for;
     B2 := [];
     for v in evecs2 do
         lambda := InnerProduct (v * N, FrobeniusImage (v, k));
         gamma := ElementHavingPrescribedNorm (F, E, lambda);
         Append (~B2, v / gamma);
     end for;
     Z1 := GL (2, E)!Matrix (B1);
     Z2 := GL (2, E)!Matrix (B2);
     Z1 := GL (2, E)!Matrix ([ B1[1] / Determinant (Z2^-1 * Z1) , B1[2] ]);
     zz := SL (2, F)!(Z2^-1 * Z1);
     z := zz @ tau0;
     if not ( (u1, u2^z) eq Identity (G) and (w1, u2^z) eq Identity (G) ) then
         Z1 := GL (2, E)!Matrix ([B1[2], B1[1]]);
         Z1 := GL (2, E)!Matrix ([ B1[2] / Determinant (Z2^-1 * Z1) , B1[1] ]);
         zz := SL (2, F)!(Z2^-1 * Z1);
         z := zz @ tau0;
assert ( (u1, u2^z) eq Identity (G) and (w1, u2^z) eq Identity (G) );
     end if;

     // write <z> as a word in defining gens  
     wz := z @ gamma0;
     wz := Evaluate (wz, wL0);
// "check wz word 1:", Evaluate (wz, [z1, z2]) eq z;
     wh1 := h1 @ gamma1;
     wh2 := h2 @ gamma2;
     wh1 := Evaluate (wh1, wJ1);
     wh2 := Evaluate (wh2, wJ2);
     wz := Evaluate (wz, [ wh1^(q-1) , wh2^(q-1) ]);
// "check wz word 2:", Evaluate (wz, [ G.i : i in [1..Ngens (G)] ]) eq z;

     ////////////////////////////////////////////////////
     // Compute the field automorphism needed to       // 
     // correct the second isomorphism <J2> -> SU(3,q).// 
     // This now differs slightly from Procedure 6.11. //
     ////////////////////////////////////////////////////
     
     K2 := sub < Generic (G) | [ (J2.i)^z : i in [1..Ngens (J2)] ] >;
     psi2 := hom < Generic (K2) -> GL (4, E) | x :-> 
                       (C2 * ((z * x * z^-1) @ phi2) * C2^-1) @ iota2 >;
     h := h2^z;
     w := u1^h;
     ww := w @ psi1;
assert exists (e){ j : j in [0..2*k-1] | r^(p^j) eq ww[2][1] };

     ///////////////////////////////////////////////
     // Find the final change-of-basis needed to  //
     // force <psi1> and <psi1> to coincide on<L> //
     ///////////////////////////////////////////////
     a1 := (s @ psi1)[4][1];
     b1 := (t @ psi1)[1][4];
     a2 := FrobeniusImage (s @ psi2, e)[4][1];
     b2 := FrobeniusImage (t @ psi2, e)[1][4]; 
     mu := a1 / a2;
assert mu in F;
assert mu * b1 eq b2;
     xi := ElementHavingPrescribedNorm (F, E, mu);
     D2 := GL (4, E)![1/xi,0,0,0,0,1,0,0,0,0,1,0,0,0,0,xi^q];
                         
     // modify <psi2>
     psi2 := hom < Generic (K2) -> GL (4, E) | 
                         x :-> D2 * FrobeniusImage (x @ psi2, e) * D2^-1 >;
       
// added by PAB on 11/07/2010:                                               
     ////////////////////////////////////////
     // Final transition to Eamonn's basis //
     ////////////////////////////////////////
     P := HyperbolicTransition (VectorSpace (E, 2));
     D3 := Identity (GL (4, E));
     InsertBlock (~D3, P, 2, 2);
     perm := SymmetricGroup (4)![1,4,2,3];
     D3 := GL (4, E)!PermutationMatrix (E, perm) * D3;
     psi1 := hom < Generic (J1) -> GL (4, E) | 
                         x :-> D3 * (x @ psi1) * D3^-1 >;
     psi2 := hom < Generic (K2) -> GL (4, E) | 
                         x :-> D3 * (x @ psi2) * D3^-1 >;
// end addition
                         
                         
     /////////////////////////////////////
     // Create images of new generators //
     /////////////////////////////////////
// added by PAB on 11/23/2010:

     // construct Eamonn's element <s>
     if (q mod 2 eq 1) then
         alpha := (E.1) ^ ((q+1) div 2);
     else 
         alpha := E!1;
     end if;
     sss := GL (3, E)![0,0,alpha,0,1,0,1/Frobenius (alpha, k),0,0];
     s := (C1^-1 * sss * C1) @ tau1;
     ws := s @ gamma1;
     ws := Evaluate (ws, wJ1);
// "check s word:", s eq Evaluate (ws, [ G.i : i in [1..Ngens (G)] ]);
     ss := s @ psi1;

     // construct Eamonn's element <t>
     ttt := GL (3, E)![1,0,alpha,0,1,0,0,0,1];
     t := (C1^-1 * ttt * C1) @ tau1;
     wt := t @ gamma1;
     wt := Evaluate (wt, wJ1);
     tt := t @ psi1;

     // construct Eamonn's element <delta>
     omega := E.1^(q+1);
     ddd := GL (3, E)![omega,0,0,0,1,0,0,0,1/omega];
     d := (C1^-1 * ddd * C1) @ tau1;
     wd := d @ gamma1;
     wd := Evaluate (wd, wJ1);
     dd := d @ psi1;
     
     // bring back my <h1> and make generators for <T>
     hh1 := h1 @ psi1;
     Tgens := [ t^(h1^(-i)) : i in [1..k] ];
     Tmats := [ tt^(hh1^(-i)) : i in [1..k] ];
     Twords := [ wt ^ (wh1^(-i)) : i in [1..k] ];
// "check Twords", 
// forall { i : i in [1..#Twords] |
//     Evaluate (Twords[i], [G.j : j in [1..Ngens (G)]]) eq Tgens[i] };

     // construct generators for Q(<f1>))
     RootElements := [ ];
     l := ElementHavingPrescribedTrace (F, E, -1);
     uuu := RootElementOfSU3 (E, E!1, l);
     for i in [1..2*k] do
	Append (~RootElements, uuu^(hhh^(i-1)));
     end for;

     Qe1gens1 := [ (C1^-1 * RootElements[i] * C1) @ tau1 : 
                                               i in [1..2*k] ];
     Qe1gens2 := [ (C2^-1 * RootElements[i] * C2) @ tau2 : 
                                               i in [1..2*k] ];
     Qe1mats1 := [ Qe1gens1[i] @ psi1 : i in [1..2*k] ];

     Qe1words1 := [ Qe1gens1[i] @ gamma1 : i in [1..2*k] ];
     Qe1words1 := [ Evaluate (Qe1words1[i], wJ1) : i in [1..2*k] ];
// "check Qe1words1",
// forall { i : i in [1..#Qe1words1] |
//      Evaluate (Qe1words1[i], [G.j : j in [1..Ngens (G)]]) eq Qe1gens1[i] };
     Qe1words2 := [ Qe1gens2[i] @ gamma2 : i in [1..2*k] ];
     Qe1words2 := [ Evaluate (Qe1words2[i], wJ2) : i in [1..2*k] ];
     Qe1words2 := [ Qe1words2[i]^wz : i in [1..2*k] ];
     Qe1gens2 := [ Qe1gens2[i]^z : i in [1..2*k] ];
// "check Qe1words2",
// forall { i : i in [1..#Qe1words2] |
//     Evaluate (Qe1words2[i], [G.j : j in [1..Ngens (G)]]) eq Qe1gens2[i] };
     Qe1mats2 := [ Qe1gens2[i] @ psi2 : i in [1..2*k] ];

     Qe1gens := Qe1gens1 cat Qe1gens2;
     Qe1words := Qe1words1 cat Qe1words2;
     Qe1mats := Qe1mats1 cat Qe1mats2;
     Qf1gens := [ Qe1gens[i]^s : i in [1..4*k] ];
     Qf1words := [ Qe1words[i]^ws : i in [1..4*k] ];
     Qf1mats := [ Qe1mats[i]^ss : i in [1..4*k] ];
     
     Qgens := Tgens cat Qf1gens;
     Qmats := Tmats cat Qf1mats;
     Qwords := Twords cat Qf1words;
// "check Qwords:", forall { i : i in [1..#Qwords] |
//     Evaluate (Qwords[i], [G.j : j in [1..Ngens (G)]]) eq Qgens[i] };

     // construct Eamonn's element <x>
     xx := GL (4, E)![1,0,1,0,0,1,0,0,0,0,1,0,0,-1,0,1];
     wx := NRSU4_QSLP (Qmats, xx);
// Evaluate (wx, Qmats) eq xx;
     x := Evaluate (wx, Qgens);
     wx := Evaluate (wx, Qwords);
// "check x word:", Evaluate (wx, [ G.i : i in [1..Ngens (G)] ]) eq x;

     // need two more elements to construct Eamonn's <v>
     xx1 := GL (4, E)![1,0,0,0,0,1,0,1,-1,0,1,0,0,0,0,1];
     xx1s := xx1^ss;
     wx1s := NRSU4_QSLP (Qmats, xx1s);
// Evaluate (wx1s, Qmats)^(ss^-1) eq xx1;
     x1s := Evaluate (wx1s, Qgens);
     wx1s := Evaluate (wx1s, Qwords);
     x1 := x1s^(s^-1);
     wx1 := wx1s ^ (ws^-1);
// "check x1 word:", Evaluate (wx1, [ G.i : i in [1..Ngens (G)] ]) eq x1; 

     if (q mod 2 eq 1) then
         vv0 := hh1^((q^2-1) div 2);
         v0 := h1^((q^2-1) div 2);
         wv0 := wh1^((q^2-1) div 2);
     else
         vv0 := Identity (GL (4, E));
         v0 := Identity (G);
         wv0 := Identity (WordGroup (G));
     end if;
     vv := vv0 * xx1^-1 * xx^-1 * xx1^-1;
     v := v0 * x1^-1 * x^-1 * x1^-1; 
     wv := wv0 * wx1^-1 * wx^-1 * wx1^-1;
     uu := vv;
     u := v;
     wu := wv;

     // finally Eamonn's <y> element
     Sgens := [ Tgens[i]^s : i in [1..#Tgens] ];
     Swords := [ Twords[i]^ws : i in [1..#Twords] ];
     Smats := [ Tmats[i]^ss : i in [1..#Tmats] ];
     L2gens := [ Tgens[i]^v : i in [1..#Tgens] ] cat
               [ Sgens[i]^v : i in [1..#Tgens] ];
     wL2 := [ Twords[i]^wv : i in [1..#Twords] ] cat
            [ Swords[i]^wv : i in [1..#Swords] ];
     L2mats := [ Tmats[i]^vv : i in [1..#Tmats] ] cat
               [ Smats[i]^vv : i in [1..#Tmats] ];
     su2mats := [ ExtractBlock (L2mats[i], 3, 3, 2, 2) :
                     i in [1..#L2mats] ];
     sumap := su2_to_sl2 (alpha);
     sl2mats := [ su2mats[i] @ sumap : i in [1..#su2mats] ];
     sl2 := sub < GL (2, q) | sl2mats >;
     isit, a, b, c := RecogniseSL2 (sl2);
// "isit?", isit;
        // <c> is a map to the word group on <sl2mats>
     yy := GL (4, E)![E.1,0,0,0,0,1/E.1^q,0,0,0,0,1/E.1,0,0,0,0,E.1^q];
     jj := yy * hh1^-1;
     jjj := ExtractBlock (jj, 3, 3, 2, 2);
     wj := (jjj @ sumap) @ c;
// "good?", Evaluate (wj, L2mats) eq jj;
     j := Evaluate (wj, L2gens);
     wj := Evaluate (wj, wL2);
// "check j:", Evaluate (wj, [ G.i : i in [1..Ngens (G)] ]) eq j;
     y := j * h1;
     wy := wj * wh1;
// "check y:", Evaluate (wy, [ G.i : i in [1..Ngens (G)] ]) eq y; 
     
     /////////////////////////////////
     // assemble the data structure //
     /////////////////////////////////

     // EOB list of generators 
     Generators := [ s , u, t , d , v , x , y ];
     Images := [ ss , uu, tt , dd , vv , xx , yy ];
     Words := [ ws , wu, wt , wd , wv , wx , wy ];
// "sanity check:", forall { i : i in [1..7] |
// Generators[i] eq Evaluate (Words[i], [G.j : j in [1..Ngens (G)]]) };
  
     rf := recformat < Generators, Images, Words >;
                          
     data := rec < rf | 
                         Generators := Generators,
                         Images := Images,
                         Words := Words
                 >;

     G`SU4DataStructure := data;

return true;
end function;

/*
   IsBlackBoxSU4 returns true or 
   false according to whether of not the input actually is a central  
   quotient of SU(4,q). If it is then a data structure 
   SU4DataStructure is attached to <G> containing the following fields:

   (1) Generators -- new generators for <G> that are the preimages
       of Eamonn's standard generators for SU(4,q);
   (2) Images -- Eamonn's standard generators; and
   (3) Words -- SLPs that evaluate from the user-defined generators
       to the new generators.
*/

////////////////////////////////////////////////////////////////
// This function sets up an isomorphism by constructing a new //
// generating set for <G> and identifying suitable images in  //
// SU(4,q). The output matrices in SU(4,q) are not written    //
// relative to a basis that Magma would regard as standard.   //
// Due to the natural construction of the generators, they    //
// written relative to a basis <e>, <v1>, <v2>, <f>, where    //
// <e> and <f> are a hyperrbolic pair, and <vi> satisfies     //
// (<vi>,<vi>) = 1, (<v1>,<v2>) = (<vi>,<e>) = (<vi>,<f>) = 0 //
////////////////////////////////////////////////////////////////

intrinsic RecogniseSU4 (G::Grp, q::RngIntElt) ->
                     BoolElt, Map, Map, Map, Map
     { given a central quotient G of SU(4,q), return
       inverse maps G -> SU(4,q) and SU(4,q) -> G that
       are isomorphisms modulo scalars. }

//"**** May 2012 Peter's new code for SU4";

     if assigned (G`RecognitionMaps) then
         maps := G`RecognitionMaps;
         return true, maps[1], maps[2], maps[3], maps[4];
     end if;

     if (q in { 2 , 3 , 4 , 5 , 7 }) then
          return SporadicSU4 (G, q);
     end if;
 
     i := 1;
     flag := false;
     while (i lt 10) and (not flag) do 
         i +:= 1;
         flag := IsBlackBoxSU4 (G, q);
     end while;
     if (not flag) then
          return false, _, _, _, _;
     end if;

     generic := Generic (G);
     W := WordGroup (G);

     // Set up maps using rewriting machinery
     LGOwords := G`SU4DataStructure`Words;
     E := Evaluate (LGOwords, [G.i: i in [1..Ngens (G)]]);
     SS := ClassicalStandardGenerators ("SU", 4, q);
     CB := GL(4, q^2)![ 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0 ];
     S := SS^(CB^-1);

     phi := hom<generic -> GL(4, q^2) | x :-> Evaluate (w where
                _, w := ClassicalRewrite (G, E, "SU", 4, q, x), S)>;

     tau := hom<GL(4, q^2) -> generic | x :-> Evaluate (w where
                _, w := ClassicalRewrite (SU(4, q), S, "SU", 4, q, x), E)>;

     gamma := hom<generic -> W | x :-> 
                  w where _, w := ElementToSLP (G, LGOwords, E, 4, q, x)>;

     delta := hom<W -> generic | x :->
                  Evaluate (x, [ G.i : i in [1..Ngens (G)] ]) >;

     // find a change-of-basis matrix to convert to Magma form
     H := sub < GL (4, q^2) | G`SU4DataStructure`Images >;
     M := MatrixAlgebra (GF (q^2), 4)![0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,0];
     assert forall { i : i in [1..Ngens (H)] | 
                      PreservesSesquilinearForm (M, H.i) };    
     C := TransformForm (M, "unitary");
     Images := [ C^-1 * G`SU4DataStructure`Images[i] * C :
                 i in [1..#G`SU4DataStructure`Images] ];
     Gens := G`SU4DataStructure`Generators;       
     assert #Gens eq #Images;

     /*
        Added 12/08/2010 after correspondence with D. Holt and J. Cannon
        
        At this stage a set of generators is stored, purportedly
        for G, but certainly for a subgroup of G isomorphic
        (mod scalars) to (P)SU(4,q). We must check that the 
        generators for G are in this subgroup.
     */

     flag := forall{i : i in [1..Ngens (G)] | 
                  ClassicalRewrite (G, E, "SU", 4, q, G.i) eq true};

     if (not flag) then
         return false, _, _, _, _;
     end if;
       
    G`RecognitionMaps := < phi, tau, gamma, delta >;
    return true, phi, tau, gamma, delta;
end intrinsic;

intrinsic SU4ElementToWord(G :: Grp, g :: GrpElt) -> BoolElt, GrpSLPElt
{
    if g is element of G which has been constructively recognised to have
    central quotient isomorphic to PSU(4, q), then return true and element
    of word group of G which evaluates to g, else false.
}
    data := G`SU4DataStructure; 
    field := BaseRing (Universe (data`Images));
    q := Isqrt (#field);
    if q in {2, 3, 4, 5, 7} then 
       flag := g in G;
       if g in G then 
          gamma := G`RecognitionMaps[3];
          w := gamma (g);
          return true, w;
       else
          return false, _; 
       end if;
    end if;
    words := G`SU4DataStructure`Words;
    E := data`Generators;
    flag, w := ElementToSLP (G, words, E, 4, q, g);
    if flag then return flag, w; else return false, _; end if;
end intrinsic;
