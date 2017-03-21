freeze;

declare verbose su3, 1;

import "white-prelims.m": ElementHavingPrescribedTrace, 
                          ElementHavingPrescribedNorm;
import "bbsporadics.m": SporadicSU3;
import "bbprelims.m": IsHermitianForm, 
                      PGL2ActionOnTransvectionGroups, 
		      SL2NormalisingToralElement, 
		      MyCoordinates;

import "su3_white.m": RecogniseSU3White;

import "../../recog/magma/centre.m" : EstimateCentre;

/////////////////////////////////////////////////////////////
//                                                         //
// This file contains the generic constructive recognition //
// functions for central quotients of SU(3, q). The         //
// sporadic cases of q in {2, 3, 4, 5, 8, 11, 17} are      //
// are handled separately.                                 //
//                                                         //
/////////////////////////////////////////////////////////////


/* The following function sets up a map that embeds 
                          [* 0 *]
   SL(2, q) in SU(3, q) as  [0 1 0]
                          [* 0 *]
   and also its inverse map
*/
SL2ToSU3 := function (F)
     E := ext <F | 2>;
     d := ElementHavingPrescribedTrace (E, F!0);
     G := SL (2, F);
     H := GL (3, E);
     phi := hom <G -> H | x :-> 
          H![x[1][1], 0, d*x[1][2], 0, 1, 0, x[2][1]/d, 0, x[2][2]]>;
     tau := hom <H -> G | x :-> G![F!(x[1][1]), F!(x[1][3]/d), 
                         F!(d*x[3][1]), F!(x[3][3])]>;
     return phi, tau;
end function;

////////////////////////////////////////////////////////////

/*
   Input:
      (1) A quadratic extension, E, of GF(q)
      (2) Elements x and y of E satisfying
              y + y^q + x^(q+1) = 0
   Output:
      The root element [1   0   0] of SU(3, q)
                       [x   1   0]
                       [y -x^q  1]
*/
RootElementOfSU3 := function (E, x, y)
     e := Degree (E);
     assert e mod 2 eq 0;
     f := e div 2;
     p := Characteristic (E);
     q := p^f;
assert y + y^q + x^(q+1) eq 0;
return GL(3, E)![1, 0, 0, x, 1, 0, y, -x^q, 1];
end function;

///////////////////////////////////////////////////////////////

/*
   Input:
     (1) <u>, an element of Q - T
     (2) <x> = diag(z, z^q/z, 1/z^q) with a in GF(q^2) - GF(q)
     (3) <Fpbasis> for GF(q) arising from the commutators
         [<u>, <u>^<x>]^(<x>^i)] lying in T 
     (4) An element <r> of <Q> of the form
            [1   0  0]
            [a   1  0]
            [b -a^q 0]
         
   Output: a word in {<u>, <x>} that evaluates to <r>
*/
NRSU3_QSLP_Generic := function (u, h, v)
     W := SLPGroup (2);
     E := BaseRing (Parent (h));
     e := Degree (E);
     assert e mod 2 eq 0;
     f := e div 2;
     p := Characteristic (E);
     q := p^f;
     nu := h[1][1];
     alpha := u[2][1];
     beta := nu^2 / nu^q;
     // first deal with <Q> / <T>
     x := v[2][1];
     coords := MyCoordinates ([beta^i : i in [0..e-1]], 
                                         GF (p), x / u[2][1]);
     assert #coords eq e;
     coords := [Integers ()!(coords[i]): i in [1..#coords]];

     v0 := &*[(u^(coords[i]))^(h^(i-1)): i in [1..e]];
     w0 := &*[((W.1)^(coords[i]))^((W.2)^(i-1)): i in [1..e]];
     // now deal with <T>
     t := v * v0^-1;
     assert t[2][1] eq 0;
     y := t[3][1];   
     coords := MyCoordinates ([beta^(i*q) - beta^i : i in [1..f]], 
                                         GF (p), y / alpha^(q+1));
     coords := [Integers ()!(coords[i]) : i in [1..#coords]];
     wt := &*[(W.1, (W.1)^((W.2)^i))^(coords[i]): i in [1..f]];
     
     return wt * w0;
end function;
 
verify := function (X, Y)
     W := SLPGroup (#X);
     procW := RandomProcess (W);
     for i in [1..5] do
         w := Random (procW);
         if Order (Evaluate (w, X)) ne Order (Evaluate (w, Y)) then
            return false;
         end if;
     end for;
return true;
end function;

is_nilpotent_class2 := function (G)
     isit := true;
     for i in [1..Ngens (G)] do
        for j in [1..Ngens (G)] do
           for k in [1..Ngens (G)] do
               isit and:= (G.i, (G.j, G.k)) eq Identity (G);
           end for;
        end for;
     end for;
return isit;
end function;

MatrixBlocks := function (G, g)
    if Type (G) eq GrpPerm or IsIrreducible (G) then return [g], true; end if;
    CF := G`CompositionFactors;
    COB := G`ChangeOfBasis;
    F := BaseRing (G);
    d := Degree (G);
    e := [* *];
    I := COB * g * COB^-1;
    offset := 0;
    for i in [1..#CF] do
        k := Dimension (CF[i]);
        block := ExtractBlock (I, offset + 1, offset + 1, k, k);
        flag := Determinant(block) eq 0;
        if flag then
            I := Identity(GL( k, F));
            return [I], false;
        end if;
        e[i] := GL (k, F) ! block;
        offset +:= k;
    end for;
    return e, true;
end function;
 
// convert Chevalley type to corresponding one
ConvertType := function (type, result, q)
   if type eq "2D" and result eq <"A", 1, q^2> then return <"2D", 2, q>;
   elif type eq "2D" and result eq <"2A", 2, q> then return <"2D", 3, q>;
   elif type eq "2D" and result eq <"A", 3, q> then return <"D", 3, q>;
   elif type eq "2D" and result eq <"2A", 3, q> then return <"2D", 3, q>;
   elif type eq "D" and result eq <"A", 3, q> then return <"D", 3, q>;
   elif type eq "D" and result eq <"A", 1, q> then return <"D", 1, q>;
   elif type eq "2A" and result eq <"A", 1, q> then return <"2A", 1, q>;
   elif type eq "B" and result eq <"A", 1, q> then return <"B", 1, q>;
   elif type eq "B" and result eq <"A", 3, q> then return <"D", 3, q>;
   elif type eq "B" and result eq <"C", 2, q> then return <"B", 2, q>;
   elif type eq "C" and result eq <"A", 1, q> then return <"C", 1, q>;
   else return result;
   end if;
end function;
 
// choose smallest section of X having faithful action
//Note : Optional Parameter turns of the check that the section has LieType = type.
SmallestFaithful := function (X, type : CheckType := true)
    if Type (X) eq GrpPerm then return true, X, 1, [X]; end if;
    q := type[3];
    F := GF (q);
    p := Characteristic (F);
    //function only designed to be used on SU(2,q) = SL(2,q) and SU(3,q);
    if type eq < "A", 1, q> then
        o := Gcd( 2, q-1);
    elif type eq < "2A", 2, q> then
        o:= Gcd(3, q+1);
    else 
        o := 1;
    end if;
    S, cob := Sections (X);
    cob := Generic (X) ! cob;
    Deg := [Degree (s): s in S];
    index := [i: i in [1..#Deg]];
    Sort (~Deg, ~perm);
    index := index^perm;
    for i in index do
        if Degree (S[i]) eq 1 then continue; end if;
        if Degree (S[i]) le 4 and p le 7 then
           prime := LieCharacteristic( S[i] : Verify := false);
           if type eq <"A", 1, 7> then
               good:= prime in {2, 7};
           else
               good:=prime eq p;
           end if;
           if not good then continue; end if;
        end if;
        if CheckType then
            flag, result := LieType (S[i], p);
	else
	    flag :=true;
            result := type;
        end if;
        if flag then
	value := ConvertType (type[1], result, q);
            if value eq type then
                if o gt 1 then 
                    Z:= EstimateCentre( S[i], o); 
                else 
                    Z:= sub< S[i]  | >; 
                end if;
                if #Z eq o then
                    return true, S[i], i, S;
                else 
		  vprint su3 : "bad section";
                end if;
            end if;
        end if;
    end for;

    //  possible that no section is recognised to be faithful
    return false, X, 1, [X];
end function;


///////////////////////////////////////////////////////////////

/*
   The following function is the generic (black box) constructive
   recognition function for central quotients of SU(3, q).
   The input is:
      (1) A black box group G
      (2) A prime power q not in {2, 3, 4, 5, 8, 11, 17}
   The output is:
      (0) a flag indicating success or failure
      (1) A record with the following fields:
        (a) LData = a record storing necessary data concerning a
                  constructively recognised SL(2, q) subgroup of <G>
        (b) LToSU3 = a map from that SL(2, q) to SU(3, q)
        (c) SU3ToL = its inverse
        (d) Generators = list of new generators for <G>
        (e) Words = corresponding list of SLPs from given gens
        (f) Images = list of generators for SU(3, q) such that
                            Generators -> Images 
                      defines a homomorphism modulo scalars

////////////////////////////////////////////////////////////////////////////
//  [SU] P. A. Brooksbank, Fast constructive recognition of black box     //
//  unitary groups, LMS J. Comput. Math. 6 (2003), 1 -- 36. (Section 6.1) //
////////////////////////////////////////////////////////////////////////////

*/

IsBlackBoxSU3 := function (G, q : Irreducible := false)
     //limit parameters
     limit1 := 128;         // from "finding tau"
     limit2 := 20;          // from "constructing L"
     limit3 := 10;                       
     proc := RandomProcessWithWords (G);
 
     _, p, k := IsPrimePower(q);

     /////////////////////////////////////////////////////////
     // first find an element <a> of order dividing (q + 1) //
     /////////////////////////////////////////////////////////
     n := q^2 - 1;
     if (q + 1) mod 3 eq 0 then
         m := n div 3;
     else 
         m := n;
     end if;
     i := 0;
     found := false;
     alt := [];
     walt := [];
     while (i lt limit1) and (not found) do
         i +:= 1;
         tau, wtau := Random (proc);
         a := tau^(2*(q-1));
         wa := wtau^(2*(q-1));
         o := Order (tau);
         if (o eq n) then
            found := true;
         elif (o eq m) and (#alt eq 0) then
	    Append (~alt, a);
            Append (~walt, wa);
         end if;
     end while;

     if found then
         if (q + 1) mod 3 eq 0 then
            simple := false; // PSU(3, q) has no element of order q^2-1 
         else
	    simple := true; 
         end if;
     elif (#alt eq 1) then
         simple := true;
         a := alt[1];
         wa := walt[1];
     else
         //"(i)";
	 return false;
     end if; 

     ///////////////////////////////////////////////////////////
     // next use <a> and a conjugate <b> to construct a group //
     // <A> that factors as the central product of an SL(2, q) //
     // group <L> and a cyclic group of order dividing (q + 1)//
     // generated by an element <z>                           //
     ///////////////////////////////////////////////////////////
     found := false;
     i := 0;
     while (i lt limit2) and (not found) do
         i +:= 1;
         g, wg := Random (proc);
         b := a^g;
         wb := wa^wg;
         A := sub <Generic (Parent (a)) | [a, b]>;
         L, wL := DerivedGroupMonteCarlo (A);
         type:= <"A", 1, q>;
         f,t := LieType(L , p) ;
         if not f then continue; end if;

/*
         if p le 7 then
              prime := LieCharacteristic (L : Verify := false);
              if type eq <"A", 1, 7> then
                  good := prime in {2, 7};
              else
                  good := prime eq p;
              end if;
              if not good then continue; end if;
         end if;
         f, t := LieType(L, p);
         if f then
             value := ConvertType (type[1], t, q);
         else
             continue;
         end if;
*/

         flag:= (t eq type);
         if not flag then
             continue;
         end if;
         //find (if it exists) the smallest section of LieType type
         FoundSection, LL, sectionsnum, sections := SmallestFaithful(L, type);
vprint su3 : "FoundSection =", FoundSection;
         flag := false;
         if FoundSection then
             if Type (LL) eq GrpMat and IsAbsolutelyIrreducible(LL) then 
                smallerfield, Ltilde := IsOverSmallerField(LL, k);
             else
                smallerfield := false;
             end if;
             //construct appropriate Ltilde for constructive recognition 
             if smallerfield then
		reducedimage := map<Generic(LL) -> Generic(Ltilde) |
		       x:-> SmallerFieldImage(LL , x)>;
                subLtilde := sub<Generic(Ltilde) |
                             [(LL.i @ reducedimage) : i in [1..Ngens(LL)]]>;
                Ltilde := subLtilde;
             else
	        Ltilde := LL;
                reducedimage := map<Generic(LL) -> Generic(Ltilde) |
                                                  x:-> x>;
             end if;

             if Type (G) eq GrpMat then 
                vprint su3: "Call RecogniseSL2 on group of dimension", 
                         Dimension(Ltilde), "over", BaseRing(Ltilde);
             else
                vprint su3: "Call RecogniseSL2"; 
             end if;
             flag, phiLtilde, tauLtilde, gammaLtilde, deltaLtilde := 
                                     RecogniseSL2(Ltilde, q);
	 else
             MB:= map< Generic(L) -> Generic(L) | g :-> g>;
             found, phiL, tauL, gammaL, deltaL := RecogniseSL2( L , q ) ;
             smallerfield:=false;
             Ltilde:= L;
         end if;
         if flag then found := true; end if;
     end while;
     if not found then
         return false;
     end if;
     if FoundSection then 
         // Now create constructive recognition maps for L
         Lgens := [L.i : i in [1..Ngens(L)]];
         MB := map<Generic(L) -> Generic(Ltilde) |
                  g:->((MatrixBlocks(L, g)[sectionsnum]) @ reducedimage)>;
         phiL := MB*phiLtilde;
         tauL := map<Generic(Domain(tauLtilde)) -> Generic(L) |
                     x:->Evaluate(((x @ tauLtilde) @ gammaLtilde), Lgens)>;
         gammaL := MB*gammaLtilde;
     end if;
     ZL := SL(2, q)![-1, 0, 0, -1];
     zL := ZL @ tauL;
     wzL := zL @ gammaL;
     wzL := Evaluate (wzL, wL);
     wzL := Evaluate (wzL, [wa, wb]);
     
     /////////////////////////////////////////////////////////
     // find the element <l> of L that acts on transvection //
     // groups of L in an identical manner to <a>. Then use //
     // this element to construct <z> centralising <L>      //
     /////////////////////////////////////////////////////////
     flag, ll, l := PGL2ActionOnTransvectionGroups (L, phiL, tauL, a);
     if not flag then 
         //"(II)";
         return false;
     end if;

     wl := l @ gammaL;  // a word in <wL>
     wl := Evaluate (wl, wL);   // a word in <wa>, <wb>
     wl := Evaluate (wl, [wa, wb]);   // a word in defining gens
     z := a * l^-1;
     wz := wa * wl^-1;
     mm := (q + 1) div Gcd ((q + 1), 3);
     if (Order (z) mod mm ne 0) then
        z := z * zL;
        wz := wz * wzL;
     end if;
     // modify <wL> to words from defining gens
     wL := [Evaluate (wL[i], [wa, wb]) : i in [1..#wL]];
     
     //////////////////////////////////////////////////////////
     // construct generators for Q, the unipotent radical of //
     // the normalizer in <G> of a transvection group <S>    //
     //////////////////////////////////////////////////////////
     ss := Generic ( Codomain(phiL))![1, 0, 1, 1]; 
     s := ss @ tauL;   // A transvection in L0
     ws := s @ gammaL;  // a word in <wL>
     ws := Evaluate (ws, wL);   // a word in defining gens
     // find a toral element of normalising <s> --- 
     h := SL2NormalisingToralElement (L, phiL, tauL, s, s^a);
     // <a> normalises no transvection group --- 
     wh := h @ gammaL;   // a word in <wL>
     wh := Evaluate (wh, wL);   // a word in defining gens
     // find a conjugate of <S> not in <L> --- 
     counter := 0;
     repeat
         g, w := Random (proc);
         s1 := s^g;
         ws1 := ws^w;
         if FoundSection then 
             s1tilde, inL := MatrixBlocks(L, s1);
         else 
             inL := true; 
             s1tilde := s1 ;
         end if;
         // if inL is false then we have established that s1 is not in L
         if inL then 
             if smallerfield then
     	         s1tilde := SmallerFieldImage(LL, s1tilde[sectionsnum]);
             else
                 if FoundSection then 
	             s1tilde := s1tilde[sectionsnum];
                 end if;
             end if;
             if Type(s1tilde) eq BoolElt then
                 inL := false;
             else 
                 inL, _ := SL2ElementToWord(Ltilde, s1tilde);
             end if;
        end if;
        counter +:= 1;
     until not inL or counter eq limit3;
     // EOB addition to pick up false 
     if counter ge limit3 then return false; end if;

     // construct a noncentral element of <Q> 
     e := Degree (GF (q));
     L1gens := [s^(h^i) : i in [0..e-1]] cat [s1];
     L1 := sub <Generic (G) | L1gens>;
     wL1 := [ws^(wh^i) : i in [0..e-1]] cat [ws1];
     type := <"A", 1, q>;
//the following shouldnt be necessary
/*
     myflag:= t eq type;
     if not myflag then
         return false;
     end if;
*/
     // find the smallest section of L1
     FoundSection2, LL1, sectionsnum, sections := SmallestFaithful(L1, type : CheckType := false);
vprint su3: "FoundSection2 =", FoundSection2;
     if not FoundSection2 then
         LL1 := L1;
         MB1:= map< Generic(L1) -> Generic(L1) | g :-> g>;
         f,phi1,tau1,gamma1,delta1 := RecogniseSL2(L1 ,q) ;
         if not f then
             return false;
         end if;
     else 
         if Type (LL1) eq GrpMat and IsAbsolutelyIrreducible(LL1) then 
             f, L1tilde := IsOverSmallerField(LL1, k);
         else
             f := false;
         end if;
         if f then
             reducedimage1 := map<Generic(LL1) -> Generic(L1tilde) | 
                                  x :-> SmallerFieldImage(LL1, x)>;
             subL1tilde := sub<Generic(L1tilde) | 
                    [(LL1.i @ reducedimage1) : i in [1..Ngens(LL1)]]>;
             L1tilde := subL1tilde;
         else
             L1tilde := LL1;
             reducedimage1 := map<Generic(LL1) -> Generic(L1tilde) | x:-> x>;
         end if;
         if Type (G) eq GrpMat then 
             vprint su3: "Call RecogniseSL2 on group of dimension", 
                 Dimension(L1tilde), "over", BaseRing(L1tilde);
         else
             vprint su3: "Call RecogniseSL2"; 
         end if;
         flag1tilde, phi1tilde, tau1tilde, gamma1tilde, delta1tilde := 
                               RecogniseSL2 (L1tilde, q);
         if not flag1tilde then return false; end if;
         MB1 := map<Generic(L1) -> Generic(L1tilde) | 
                         g:->((MatrixBlocks(L1, g)[sectionsnum]) @ reducedimage1)>;
         phi1 := MB1*phi1tilde;
         tau1 := map<Generic(SL(2, q)) -> Generic(L1) | 
                     x:-> Evaluate(((x @ tau1tilde) @ gamma1tilde), L1gens)>;
         gamma1 := MB1*gamma1tilde;
     end if;
     h1 := SL2NormalisingToralElement (L1, phi1, tau1, s, s1);
     wh1 := h1 @ gamma1;
     wh1 := Evaluate (wh1, wL1);
     u := (h, h1);
     wu := (wh, wh1);
     v := u^z;

	
     ///////////////////////////////////
     // define the isomorphism on <L> //
     ///////////////////////////////////
     F := BaseRing (Codomain(phiL));
     rho, rho_inv := SL2ToSU3 (F);     
     L_Images := [(L.i @ phiL) @ rho : i in [1..Ngens (L)]];
     H := Generic (Parent (L_Images[1]));
     E := BaseRing (H);
     // modify <h> so that it induces on <Q> / <S>
     // the standard field generator for <F>

     mu := PrimitiveElement (F);
     hh := H![mu, 0, 0, 0, 1, 0, 0, 0, 1/mu];
     h := (hh @ rho_inv) @ tauL;
     wh := h @ gammaL;   // a word in <wL>
     wh := Evaluate (wh, wL);   // a word in defining gens
     // construct another useful element of <L>

     // changed by PAB on 11/10/2010 after correspondence with E.A. O'Brien
     // want to make generating set canonical and match up with
     // input and output of other recognition functions
     //lsl2 := SL(2, F)![0, 1, -1, 0];
     //ll := lsl2 @ rho;

     xi := 1 / Frobenius (PrimitiveElement (E), e);
     if (q mod 2 eq 0) then
         alpha := E!1;
     else
         alpha := xi^((q+1) div 2);
     end if;
     ll := GL (3, E)![0, 0, alpha, 0, 1, 0, 1/Frobenius (alpha, e), 0, 0];
     lsl2 := ll @ rho_inv;
     ttLGO := GL (3, E)![1, 0, 0, 0, 1, 0, 1/Frobenius (alpha, e), 0, 1];
     tLGOsl2 := ttLGO @ rho_inv;
     l := lsl2 @ tauL;
     tLGO := tLGOsl2 @ tauL;
     wl := l @ gammaL;          // a word in <wL>
     wl := Evaluate (wl, wL);   // a word in defining gens   
     wtLGO := tLGO @ gammaL;
     wtLGO := Evaluate (wtLGO, wL);

     ///////////////////////////////////
     // extend the isomorphism to <z> //
     ///////////////////////////////////
     vprint su3: "==1";
     s := (u, v);
     ss := (s @ phiL) @ rho;
     zeta := ss[3][1];
     s1 := (u, v^z);
     s2 := (v, v^z);
     ss1 := (s1 @ phiL) @ rho;
     ss2 := (s2 @ phiL) @ rho;
     zeta1 := ss1[3][1];
     zeta2 := ss2[3][1];
     a2 := zeta1 / zeta;
     a1 := -zeta2 / zeta;
     assert ((a1 in F) and (a2 in F));
     pol := Polynomial ([F!(-a1), F!(-a2), 1]);
     roots := Roots (pol, E);
     beta := roots[1][1];
     P<X> := PolynomialRing(E);
     flag := exists(vect){vect : vect in Roots(X^3 - beta) | 
                                 Order(vect[1]) eq Order(z)};
     if not flag then 
	 // "G is PSU";
         flag:= exists(vect){vect: vect in Roots(X^3 -beta) | 
                                   Order(vect[1]) eq Order(z)*3};
     end if;
     if (not flag) then
         //"(iii)";
         "SU3: fail 0";
         return false;
     end if;
     nu := vect[1];
     zz := H![nu, 0, 0, 0, 1/nu^2, 0, 0, 0, nu];

     ///////////////////////////////////
     // extend the isomorphism to <Q> //
     ///////////////////////////////////

     alpha1 := zeta / (beta^q - beta);
     alpha := ElementHavingPrescribedNorm (alpha1, F, E, q);
     gamma := ElementHavingPrescribedTrace (E, -alpha^(q+1));
     delta := ElementHavingPrescribedTrace (E, 0);
     pows := Eltseq (F!a1) cat Eltseq (F!a2);
     pows := [Integers ()!t : t in pows];
     Qlist := [u^(h^i) : i in [0..e-1]] cat 
                  [u^(z * h^i) : i in [0..e-1]];    
     u0 := &*[Qlist[i]^pows[i] : i in [1..2*e]];
     // <u0> and <u>^(<z>^2) should be equal mod <S>
     s0 := v^z * (u0^-1);
     ss0 := (s0 @ phiL) @ rho;
     gamma0 := ss0[3][1];
     j := 1;
     F_scalar := F!1;
     jgamma := F_scalar * delta + gamma;
     uu := RootElementOfSU3 (E, alpha, jgamma);
     QQlist := [uu^(hh^i) : i in [0..e-1]] cat
                   [uu^(zz * hh^i) : i in [0..e-1]];
     uu0 := &*[QQlist[i]^pows[i] : i in [1..2*e]];
     tt0 := uu^(zz^2) * (uu0^-1);
     tt0tilde := tt0[3, 1];
     intelt := &+[(pows[i] + pows[i+e])*mu^(2*(i-1)) : i in [1..e]];
     myt := (gamma0 - tt0tilde)*(1 - intelt)^-1;
     mytransvection := GL(3, q^2)![1, 0, 0, 0, 1, 0, myt, 0, 1];
     uu := mytransvection*uu;
     QQlist := [uu^(hh^i) : i in [0..e-1]] cat
             [uu^(zz * hh^i) : i in [0..e-1]];
     uu0 := &*[QQlist[i]^pows[i] : i in [1..2*e]];
     tt0 := uu^(zz^2) * (uu0^-1);

     vprint su3: "==2";
     // when the former condition holds <uu> is a suitable image for <u>

     /////////////////////////////////
     // assemble the data structure //
     /////////////////////////////////

     // first construct an element of order q^2 - 1 
     delta := - ll[1][3];
     rho := xi * delta;
     alpha := ElementHavingPrescribedNorm (-(rho + rho^q), F, E, q);
     uu1 := RootElementOfSU3 (E, alpha / rho, 1 / rho^q);
     uu2 := RootElementOfSU3 (E, alpha / delta, - rho / delta^2);
     uu3 := RootElementOfSU3 (E, alpha / rho^q, 1 / rho^q);
     hh := uu1 * (ll^-1 * uu2 * ll) * uu3 * ll;
     wu1 := NRSU3_QSLP_Generic (uu, zz, uu1);
     u1 := Evaluate (wu1, [u, z]);
     wu2 := NRSU3_QSLP_Generic (uu, zz, uu2);
     u2 := Evaluate (wu2, [u, z]);
     wu3 := NRSU3_QSLP_Generic (uu, zz, uu3);
     u3 := Evaluate (wu3, [u, z]);
     h := u1 * (l^-1 * u2 * l) * u3 * l;
     if (Order (h) mod m ne 0) then
        // recall that <m> = (3, <q>+1)
        //"(iv)";
	// "fail00";
        return false;
     end if;
     wu1 := Evaluate (wu1, [wu, wz]);
     wu2 := Evaluate (wu2, [wu, wz]);  // words in <G.j>
     wu3 := Evaluate (wu3, [wu, wz]);
     wh := wu1 * (wl^-1 * wu2 * wl) * wu3 * wl;
     vprint su3: "==3";
     // replace <u> with <u0> so that <uu0> has the form r(1, g)
     // changed by PAB on 11/10/2010: see above
     //gamma := ElementHavingPrescribedTrace (F, E, -1);
     if (q mod 2 eq 0) then
         gamma := (xi + Frobenius (xi, e))^-1 * xi;
     else
         gamma := E!(-1/2);
     end if;
     //uu0 := RootElementOfSU3 (E, E!1, gamma);
     uu0 := RootElementOfSU3 (E, -E!1, gamma);
     wu0 := NRSU3_QSLP_Generic (uu, zz, uu0);
     u0 := Evaluate (wu0, [u, z]);
     wu0 := Evaluate (wu0, [wu, wz]);
     
     // conduct basic check on canonical generators
     p := Characteristic (GF (q));

     if (p mod 2 eq 1) and (Order (u0) ne p) then 
        //"(v)";
        // "fail1";
        return false; 
     end if;
     if (p eq 2) and (Order (u0) ne 4) then 
        //"(vi)";
        // "fail2";
        return false; 
     end if;
     if ((u0, u0^h), u0) ne Identity (G) then 
        //"(vii)";
        //"fail3";
        return false; 
     end if;
     if ((u0^l, u0^(l*h)), u0^l) ne Identity (G) then 
        //"(viii)";
        //"fail4";
        return false; 
     end if;

     // order the transvection group
     T := [Identity (G)];
     if not (Type(G) eq GrpMat and Irreducible) then 
         vprint su3: "Ordering transvection list";
         // EOB - another nasty enumeration? no, here q is small 
         T cat:= [(u0, u0^h)^(h^i) : i in [0..q-2]];
     end if;

     // set up LGO words
     // if these are evaluated in G, then the obvious map to
     // the Leedham-Green & O'Brien standard generators extends
     // (modulo scalars) to an isomorphism
     W := Parent (wl);

     LGOWords := [wl, Identity (W), wtLGO, wh^(q+1), Identity (W), wu0, wh];
  
     rf := recformat <Generators, Words, Images, LGOWords, 
                      LGOGenerators, TransvectionGroup, Qgens, QQgens>;
                          
     data := rec <rf | Generators := [u0, h, l], 
                       Words := [wu0, wh, wl], 
                       Images := [uu0, hh, ll], 
                       LGOWords := LGOWords, 
		       TransvectionGroup := T, 
                       Qgens := Qlist, 
		       QQgens := QQlist
                 >;

     G`SU3DataStructure := data;
     vprint su3: "End of IsBlackBoxSU3 function";
return true;
end function;
//////////////////////////////////////////////////////////////////////

/////////////////// CANONICAL GENERATORS /////////////////

/*
   For convenience here are the matrices corresponding to 
   the canonical generators that we are using for SU(3, q).

       [1  0  0]       [1/r^q  0   0]       [  0   0   a]  
   u = [1  1  0]   h = [0   r^q/r  0]   l = [  0   1   0]
       [g -1  1]       [0      0   r]       [1/a^q 0   0]

   <r> is the preferred Magma generator of the 
       multiplicative group of GF(q^2).

   <g> is an element of GF(q^2) satisfing g + g^q + 1 = 0
       defined as in [L-GO]

   <a> is an element satisfying a + a^q = 0 defined as in [L-GO]

   Notice that these matrices all preserve an alternating
   form having matrix

   [0 0 1]           
   [0 1 0]  
   [1 0 0]

   Thus they are expressed relative to the same 
   basis as the group stored in Magma.
*/

////////////////////////////////////////////////////////////


/*
   Input:
     (1) <Images> of the canonical generators (see above)
     (2) An element <r> of the form
            [1   0  0]
            [a   1  0]
            [b -a^q 0]
         namely an element of the (matrix) group Q.
   Output: a word in <Images> that evaluates to <r>
*/

NRSU3_QSLP := function (Images, r)

     assert #Images eq 3;
     W := SLPGroup (3);
     E := BaseRing (Parent (r));
     e := Degree (E);
     assert e mod 2 eq 0;
     f := e div 2;
     F := GF (Characteristic (E)^f);
     q := Characteristic (E)^f;
     rho := Images[2][1][1];
     mu := F!(rho^(q+1));
//     nu := rho^(2-q);
// PAB: 11/09/2010:
     nu := rho^(2*q - 1);

     // first deal with <Q> / <T>
     alpha := r[3][2];
     coords := MyCoordinates ([1, nu], F, alpha);
     assert #coords eq 2;
     v := Identity (GL (3, E));
     wv := Identity (W);
     for i in [1, 2] do
         a := coords[i];   // an element of <F>
         if (a ne 0) then
            j := Log (mu, a);
            if (i eq 1) then
               v := v * (Images[1])^((Images[2])^(j*(q+1)));
               wv := wv * (W.1)^((W.2)^(j*(q+1)));
            else
               v := v * (Images[1])^((Images[2])^(1+j*(q+1)));
               wv := wv * (W.1)^((W.2)^(1+j*(q+1)));
            end if;
	 end if;
     end for;

     // now deal with <T>
     t := r * v^-1;
     assert t[2][1] eq 0;
     delta := t[3][1];
     if (delta ne 0) then
         a := F!(delta / (nu - nu^q));
         j := Log (mu, a);
         assert t eq (Images[1], (Images[1])^Images[2])^((Images[2])^j);
	 wt := (W.1, (W.1)^(W.2))^((W.2)^j);
     else
         wt := Identity (W);
     end if;
     return wt * wv;
end function;
///////////////////////////////////////////////////////////////////

/*
   Black box analogue of the preceding routine.
   
   Input:
     (1) Canonical <Generators>
     (2) Transvection group <T> listed as follows:
         [1, [u, u^h], [u, u^h]^h, ...]
     (3) an element <r> of Q
     
   Output: An SLP that evaluates from <Generators> to <r>
*/
BBSU3_QSLP := function (Generators, T, r)
     assert #Generators eq 3;
     W := SLPGroup (3);
     // first deal with <Q> / <T>
     assert exists (j1){ i : i in [1..#T] | 
                             T[i] eq (Generators[1], r) };
     assert exists (j2){ i : i in [1..#T] | 
                            T[i] eq (r, (Generators[1])^(Generators[2]))};
     posns := [j2, j1];
     q := #T;
     v := Identity (Generic (Parent (r)));
     wv := Identity (W);
     for i in [1, 2] do
         j := posns[i];
         if (j ne 1) then 
            if (i eq 1) then
               v := v * (Generators[1])^((Generators[2])^((j-2)*(q+1)));
               wv := wv * (W.1)^((W.2)^((j-2)*(q+1)));
            else
               v := v * (Generators[1])^((Generators[2])^(1+(j-2)*(q+1)));
               wv := wv * (W.1)^((W.2)^(1+(j-2)*(q+1)));
            end if;
         end if;
     end for;
       
     // now deal with <T>
     t := r * v^-1;
     assert exists (j){i : i in [1..#T] | T[i] eq t};
     if (j ne 1) then
         wt := (W.1, (W.1)^(W.2))^((W.2)^(j-2));
     else 
         wt := Identity (W);
     end if;
       
return wv * wt;
end function;
//////////////////////////////////////////////////////////////////

/*
   Input: A transvection <x> belonging to a transvection group
          <X> opposite <T>.
          
   Output: An element of Q conjugating <T> to <S>
*/
NRSU3_ConjugatingElementOfQ := function (x)
     E := BaseRing (Parent (x));
assert Degree (E) mod 2 eq 0;
     q := Characteristic (E)^(Degree (E) div 2);
     MA := MatrixAlgebra (E, 3);
     center := Image (MA!x - Identity (MA));
assert Dimension (center) eq 1;
     v := center.1;
assert v[3] ne 0;
return RootElementOfSU3 (E, -(v[2]/v[3])^q, v[1]/v[3])^-1;
end function;
////////////////////////////////////////////////////////////

/*
   Input:
     (1) <G> our black box SU(3, q)
     (2) <TransvectionGroup> = <T>
     (3) <s> an element from a transvection group <S>
     (4) <h1> an element of order q-1 normalising <S> and <T>
     (5) <mu> the field generator corresponding to <h1>
     (6) <x> a transvection opposite <t>
     (7) degree of the field extension
   Output:
     An element <u> of <Q> such that <X>^<u> = <S>, 
     where <X> is the transvection group containing <x>
*/
BBSU3_ConjugatingElementOfQ := function (G, T, s, h1, mu, x, e)

     t := T[2];
     q := #T;
     p := Characteristic (Parent (mu));
     Lgens := [T[i] : i in [2..e+1]] cat [x];
     L := sub <Generic (G) | Lgens>;
     if (p eq 2) then
         i := 0;
         repeat
            i +:= 1;
            flag, phi, tau, gamma, delta := RecogniseSL2 (L, #T);
         until (flag) or (i eq 5);
         if (not flag) then
            return false, _;
         end if;
         h := SL2NormalisingToralElement (L, phi, tau, t, x);
         // EOB -- enumeration over field
         assert exists (j){i : i in [1..(q-1)] | t^(h^i) eq t^h1};
         h := h^j;
         k := Log (mu^2, 1/(1 - mu^2));
         u := (h^-1 * h1)^(h^k);
     else 

         procL := RandomProcess (L);
         repeat 
            l := Random (procL);
         until Order (l) mod 2 eq 0;
         h := l^(Order (l) div 2);
         u := (h * h1^((q-1) div 2))^((p+1) div 2);
     end if;
        // <u> conjugates <X> into <L1>
     z := x^u;
     // EOB -- another nasty enumeration 
     flag := exists (tt){y : y in T | (z^y, s) eq Identity (G)};
     // should replace this with a more efficient method
     if (not flag) then
         return false, _;
     end if;

return true, u * tt;
end function;

////////////////////////////////////////////////////////////////

/*
   Input:
     (1) A black box group <G> constructively recognised as SU(3, q).
     (2) An element <x> of SU(3, q) or of <G>
     (3) <flag> either "Natural" or "BlackBox" indicating which 
           
   Output: 
      A word in the canonical generators that evaluate to <x>
*/

SU3SLP := function (G, x, flag)

     rho := G`SU3DataStructure`Images[2][1][1];
     E := Parent (rho);
     e := Degree (E);
assert e mod 2 eq 0;
     f := e div 2;
     q := Characteristic (E)^f;
    
     if (flag eq "Natural") then
         CanGens := G`SU3DataStructure`Images;
         H := sub <GL (3, E) | CanGens>;
     else 
         H := G;
         CanGens := G`SU3DataStructure`Generators;
         T := G`SU3DataStructure`TransvectionGroup;
     end if;

     W := SLPGroup (#CanGens);
     u := CanGens[1];
     h := CanGens[2];
     h1 := h^(q+1);
     l := CanGens[3];
     t := (u, u^h);
     s := t^l;
    
     y := x;
     
     if not IsIdentity ((t^y, t)) then
        // modify <y> so that it normalises <T>
        if (flag eq "Natural") then
           u := NRSU3_ConjugatingElementOfQ (t^y);
           wu := NRSU3_QSLP (CanGens, u^-1);
        else
           flagu, u := BBSU3_ConjugatingElementOfQ (G, T, s, h1, rho^(q+1), t^y, f);
           if (not flagu) then
               return false, _;
           end if;
           wu := BBSU3_QSLP (CanGens, T, u^-1);
        end if; 
        wu := Evaluate (wu, [W.i : i in [1..#CanGens]]);
        y := y * u * l^-1;
     else
        wu := (W.3)^-1;
     end if;
        
     if not IsIdentity ((s^y, s)) then  
        // modify <y> so that it normalises <S>
        if (flag eq "Natural") then
           v := NRSU3_ConjugatingElementOfQ (s^y);
           wv := NRSU3_QSLP (CanGens, v^-1);
        else
           flagv, v := BBSU3_ConjugatingElementOfQ (G, T, s, h1, rho^(q+1), s^y, f); 
           if (not flagv) then return false, _; end if;
           wv := BBSU3_QSLP (CanGens, T, v^-1);
        end if;
        wv := Evaluate (wv, [W.i : i in [1..#CanGens]]);
        y := y * v;
     else
        wv := Identity (W);
     end if;

     // <y> is now a power of <h>
     if (flag eq "Natural") then
         power := Log (rho, y[1][1]);
     else
         if (q eq 2) then
	    assert exists (power){i : i in [1..3] | h^i eq y};
         else
            /* modified on 03/04/2011 by PAB to remove reliance on <Torus> */
	    u := CanGens[1];
            h := CanGens[2];
            uh := u^h;
            uy := u^y;
            wuh := BBSU3_QSLP (CanGens, T, uh);
            uuh := Evaluate (wuh, G`SU3DataStructure`Images);
            wuy := BBSU3_QSLP (CanGens, T, uy);
            uuy := Evaluate (wuy, G`SU3DataStructure`Images);
            power := Log (-uuh[2][1], -uuy[2][1]);	       

            d := Gcd (q^2 - 1, 2 - q);
            n := (q^2 - 1) div d;
            for i in [1..d] do
               if (h^((i-1) * n + power) eq y) then
	          power := ((i-1) * n + power) mod (q^2 - 1);
               end if;
	    end for;

            flag := h^power eq y;
            if not flag then return false, _; end if;
         end if;
     end if;

     w := (W.2)^power;
     
     // compose to obtain a word evaluating to <x>
     w := w * wv * (W.3) * wu;

return true, w;
end function;

////////////////////////////////////////////////////////////////

/*
   Some tweaking needed to turn this into a membership test.

   Input:
     (1) Constructively recognised SU(3, q) black box group <G>
     (2) An element <x> of <G> (should really allow supergroup)
   Output:
     An element of the word group of <G> that evluates to <x>.
     If <SU3Image> is set to <true> then it also returns the
     image of <x> in the natural copy of SU(3, q)
*/
BlackBoxElementToSLP := function (G, x : SU3Image := false);
     flag, w := SU3SLP (G, x, "BlackBox");
     if (not flag) then
         // "(aaa)";
         return false, _, _;
     end if;
     if (SU3Image) then
         xx := Evaluate (w, G`SU3DataStructure`Images);
         return true, w, xx;
     else
         return true, w, _;
     end if;
end function;
//////////////////////////////////////////////////////////////

/*
   Input:
     (1) Constructively recognised SU(3, q) black box group <G>
     (2) An element <x> of SU(3, q)
   Output:
     The preimage of <x> in <G>
*/
SU3ElementToBlackBoxElement := function (G, x)
     flag, w := SU3SLP (G, x, "Natural");
     assert flag;
     xx := Evaluate (w, G`SU3DataStructure`Generators);
return xx;
end function;
/////////////////////////////////////////////////////////////

/* additional elements to generate SU */

SUAdditionalElements := function (F: EvenCase := true)
   if EvenCase then d := 4; else d := 3; end if;
   M := MatrixAlgebra (F, d);
   gamma := PrimitiveElement (F);
   q := Isqrt (#F);
   I := Identity (M);
   if EvenCase then  
      I[1][3] := 1;
      I[4][2] := -1;
      J := DiagonalMatrix (F, [gamma, gamma^-q, gamma^-1, gamma^q]);
   else
      if IsEven (q) then
         phi := (Trace (gamma, GF(q)))^-1 * gamma;
      else
         phi := -1/2;
      end if;
      I := M![1, phi, 1, 0, 1, 0, 0, -1, 1];
      J := DiagonalMatrix (F, [gamma, gamma^(-q), gamma^(q - 1)]);
   end if;
   I := GL(d, F)!I;
   J := GL(d, F)!J;
   return I, J;
end function;

/* 
   EOB function: 
   g is element of G which is isomorphic to SU(d, q);
   solve for g as SLP in defining generators of G;
   X = the copy of the standard generators of SU(3, q) in G;
   X is obtained by evaluating words in the defining generators of G;
   first express g as an SLP in X, then evaluate the SLP in words 
   to obtain an SLP for g in the defining generators of G
*/

ElementToSLP := function (G, words, X, d, q, g)
   flag, w := ClassicalRewrite (G, X, "SU", d, q, g);
   assert flag;
   w := Evaluate (w, words);
   return w;
end function;

/*
   The following function is the generic (black box) constructive
   recognition function for central quotients of SU(3, q).
   The input is:
      (1) A black box group G
      (2) A prime power q 
   The output is:
      (1) A flag indicating whether or not G is as advertised
      (2) A map G -> SU(3, q)
      (3) Its inverse SU(3, q) -> G
      (4) A map G -> W(G) the word group on G
      (5) Its inverse W(G) -> G
*/

intrinsic RecogniseSU3 (G::Grp, q::RngIntElt) ->
                     BoolElt, Map, Map, Map, Map
{if G is isomorphic, possibly modulo scalars, to (P)SU(3, q), 
 construct homomorphisms between G and (P)SU(3, q);
 return homomorphism from G to (P)SU(3, q), homomorphism
 from (P)SU(3, q) to G, the map from G to its word group and 
 the map from the word group to G.
}
     // "**** March 2014 revised SU3 code"; 
     require IsPrimePower (q): "Field size is not correct";
     if q eq 2 then error "Group is soluble, not handled"; end if;

     if assigned (G`RecognitionMaps) then
         maps := G`RecognitionMaps;
         return true, maps[1], maps[2], maps[3], maps[4];
     end if;

     //limit parameter
     limit1 := 5; //How many times do we run IsBlackBox?

     // if (q in {3, 4, 5, 8, 11, 17}) then
     // EOB -- revised Jan 2015 
     if (q in {3, 5, 8, 11}) then
          return SporadicSU3 (G, q);
     end if;

     // G natural copy? if so, use special machinery
     Natural := Type (G) eq GrpMat and Degree (G) eq 3 and #BaseRing(G) eq q^2 and
                RecogniseClassical (G: Case := "unitary") cmpeq true;

     if Natural then 
         f, phi, tau, gamma, delta := RecogniseSU3White(G, q);
         G`RecognitionMaps := <phi, tau, gamma, delta> ;
         return f, phi, tau, gamma, delta;
     end if;

     Myflag := Type(G) eq GrpMat and IsIrreducible(G); 

     i := 0;
     repeat
         i +:= 1;
         isit := IsBlackBoxSU3 (G, q: Irreducible := Myflag);
     until (i eq limit1) or (isit);
     if (not isit) then
          return false, _, _, _, _;
     end if;
       
     /* Added 12/08/2010 after correspondence with D. Holt and J. Cannon
        At this stage a set of generators is stored, purportedly
        for G, but certainly for a subgroup of G isomorphic
        (mod scalars) to (P)SU(3, q). We must check that the 
        generators for G are in this subgroup.
     */

     // set up maps
     generic := Generic (G);
     W := WordGroup (G);

     LGOWords := G`SU3DataStructure`LGOWords;
     E := Evaluate (LGOWords, [G.i: i in [1..Ngens (G)]]);
     G`SU3DataStructure`LGOGenerators := E;
     
     if Type (G) eq GrpMat and Myflag then 
        // Set up maps using CT rewriting code
        SS := ClassicalStandardGenerators ("SU", 3, q);
        CB := GL(3, q^2)![1, 0, 0, 0, 0, 1, 0, 1, 0];
        S := SS^(CB^-1);
        flag := forall{i : i in [1..Ngens (G)] |
	       ClassicalRewrite (G, E, "SU", 3, q, G.i) eq true};

        if (not flag) then
	    return false, _, _, _, _;
        end if;

        phi := hom<generic -> GL(3, q^2) | x :-> Evaluate (w where 
                   _, w := ClassicalRewrite (G, E, "SU", 3, q, x), S)>;

        tau := hom<GL(3, q^2) -> generic | x :-> Evaluate (w where 
           _, w := ClassicalRewrite (SU(3, q), S, "SU", 3, q, x), E)>;

        gamma := hom<generic -> W | x :-> 
                 ElementToSLP (G, LGOWords, E, 3, q, x)>;

     else
        flag := forall{i : i in [1..Ngens (G)] | SU3SLP (G, G.i, "BlackBox")};
        if (not flag) then
            return false, _, _, _, _;
        end if;
 
        // "Set up maps using Peter's code";
        phi := hom<generic -> GL(3, q^2) | x :-> y where 
               _, _, y := BlackBoxElementToSLP (G, x : SU3Image := true)>;
     
        tau := hom<GL(3, q^2) -> generic | x :->
                  SU3ElementToBlackBoxElement (G, x)>;
                   
        gamma := hom<generic -> W | x :->
                    Evaluate (w, G`SU3DataStructure`Words) where
                    _, w := BlackBoxElementToSLP (G, x)>;
     end if;

     delta := hom<W -> generic | x :->
                  Evaluate (x, [G.i : i in [1..Ngens (G)]])>;

     G`RecognitionMaps := <phi, tau, gamma, delta>;
return true, phi, tau, gamma, delta;                
end intrinsic;

verify := function (X, Y)
     W := SLPGroup (#X);
     for i in [1..5] do
         w := Random (W);
         if Order (Evaluate (w, X)) ne Order (Evaluate (w, Y)) then
            return false;
         end if;
     end for;
return true;
end function;

intrinsic SU3ElementToWord(G :: Grp, g :: GrpElt) -> BoolElt, GrpSLPElt
{ if g is element of G which has been constructively recognised to have 
  central quotient isomorphic to PSU(3, q), then return true and element 
  of word group of G which evaluates to g, else false.
}
    data := G`SU3DataStructure;
    field := BaseRing (Universe (data`Images));
    q := Isqrt (#field);
    if q in {2, 3, 4, 5, 8, 11, 17} then 
       flag := g in G;
       if g in G then
          gamma := G`RecognitionMaps[3];
          w := gamma (g);
          return true, w;
       else
          return false, _;
       end if;
    end if;

    flag, w := BlackBoxElementToSLP(G, g);
    if flag then
       return true, Evaluate(w, G`SU3DataStructure`Words);
    else
       return false, _;
    end if;
end intrinsic;
