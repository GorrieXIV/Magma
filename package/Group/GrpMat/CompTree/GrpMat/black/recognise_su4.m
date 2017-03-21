freeze;
declare verbose su4, 1;

import "white-prelims.m": IsMersenne, Isppdhash, 
                          ElementHavingPrescribedNorm, 
                          ElementHavingPrescribedTrace;

import "recognise_su3.m": RootElementOfSU3, 
                          SmallestFaithful, 
                          MatrixBlocks;
import "bbprelims.m": HyperbolicTransition, 
                      BruteForceHomomorphism, 
    		      PreservesSesquilinearForm, 
                      PGL2ActionOnTransvectionGroups, 
		      MyInsertBlock, 
		      MyCoefficients, 
		      MyEltseq, 
                      IsHermitianForm;

import "bbsporadics.m": SporadicSU4;

import "su4_white.m": RecogniseSU4White;

import "../../recog/magma/centre.m" : EstimateCentre;

/////////////////////////////////////////////////////////////////////
//                                                                 //
// This file contains the generic constructive recognition         //
// functions for central quotients of SU(4, q). The                 //
// sporadic cases of q in {2, 3, 4, 5, 7} are handled separately.  // 
/////////////////////////////////////////////////////////////////////

SU4_GOOD_ELEMENT := function(G, proc, q, limit)
    f, p, k := IsPrimePower(q);
    if not f then
        return false, _, _;
    end if;
    i := 1;
    repeat
        t, w := Random(proc);
        ot := Order(t);
        cond := false;
        cond2 := false;
        cond3 := false;
        i +:= 1;
        if IsMersenne(p) and (k eq 1) and ((ot mod 8) ne 0) then 
            continue; 
        end if;
        o2 := (2*(q^2-q +1));
        a := t^o2;
        gcd := Gcd(o2, ot);
        oa := (o2*ot) div gcd;
        cond := Isppdhash(oa, p, 2*k);
        cond2 := Isppdhash(ot, p, 2*k);
        cond3 := Isppdhash(ot, p, 6*k);
    until (cond2 and cond3 and cond) or i eq limit;
    if (cond2 and cond3 and cond) then
        wa := w^o2;
        return true, a, wa;
    else
        return false, _, _;
    end if;
end function;

// Peter's original 
SU4_GOOD_ELEMENT_ORIGINAL := function (G, proc, q, limit)
    count := 0;
    o1 := q^3 + 1;
    good := [o1];
    if (q + 1) mod 2 eq 0 then
        Append (~good, o1 div 2);
    end if;
    if (q + 1) mod 4 eq 0 then
	Append (~good, o1 div 4);
    end if;
    o2 := q^2 - q + 1;
    found := false;
    while ((count lt limit) and (not found)) do
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

// Return a naturally embedded SL(2, q) subgroup of G.
SU4_CONSTRUCT_L := function (G, proc, a, wa, q, limit) 
    
    trials := 0;
    found := false;
    _, p, k := IsPrimePower(q);
    while ((not found) and (trials le limit)) do
	trials +:= 1;
        g, w := Random (proc);
        b := a^g;
        wb := wa^w;
        A := sub < Generic (G) | [a, a^g]>;
        L, wL := DerivedGroupMonteCarlo (A);
        vprint su4: "use LieType (SU4 - construct L)"; 
        f, type := LieType(L,p);
        if not f then continue; end if;
        if type ne <"A",1,q> then continue; end if;
        FoundSection, LL, sectionsnum, sections := SmallestFaithful(L, <"A", 1, q>);
        if not FoundSection then 
	    LL:= L;
            found , phiL, tauL, gammaL, deltaL := RecogniseSL2(L ,q );
            MB:= map< Generic(L) -> Generic(L) | g :-> g >;

        else
            if Type (LL) eq GrpMat and Dimension(LL) eq 2 then
                flag := RecogniseClassical(LL : Case := "unitary");
                if not flag then 
                    flag := RecogniseClassical(LL : Case := "linear");
                end if; 
                result := <"A", 1, q>;
            else
        	vprint su4: "Use LieType";
                flag, result := LieType (L, p);
            end if;
            if not flag then 
               continue; 
            end if;
            if result eq <"A", 1, q> then
                if Type (LL) eq GrpMat then 
                   f, Ltilde := IsOverSmallerField(LL, k);
                else
                    f := false;
                end if;
                if f then 
                    reducedimage := map < Generic(LL) -> Generic(Ltilde) | 
                                      x:-> SmallerFieldImage(LL, x)>;
                    subLtilde := sub< Generic(Ltilde) | 
                          [(LL.i @ reducedimage) : i in [1..Ngens(LL)]]>;
                    Ltilde := subLtilde;
                    vprint su4: "Found 2-dimensional representation of SL2 over GF(", q, ")";
           	else 
       	            Ltilde := LL;
                    reducedimage := map< Generic(LL) -> Generic(Ltilde) | x :-> x>;
                    if Type (G) eq GrpMat then 
                       vprint su4: "Found SL2 of dimension:", 
                       Dimension (Ltilde), "defined over", BaseRing(Ltilde);
                    else 
                       vprint su4: "Found SL2";
                    end if;
                end if;
                flagtilde, phiLtilde, tauLtilde, gammaLtilde, deltaLtilde 
                                   := RecogniseSL2 (Ltilde, q);
                if (flagtilde) then 
                    found := true; 
                end if;
            end if;
        end if;
    end while;
    if (not found) then
        // "Failed to construct suitable L";
        return false, _, _;
    end if;
    if FoundSection then  
        Lgens := [L.i : i in [1..Ngens(L)]];
        MB := map<Generic(L) -> Generic(Ltilde) |
                g:-> ((MatrixBlocks(L, g)[sectionsnum]) @ reducedimage)>; 
        phiL := MB*phiLtilde;
        tauL := map<Generic(Domain(tauLtilde)) -> Generic(L) | 
                  x:->Evaluate(((x @ tauLtilde) @ gammaLtilde), Lgens)>;
        gammaL := MB*gammaLtilde;
        W := WordGroup(L);
        deltaL := hom<W -> Generic(L) | w :-> Evaluate(w, Lgens)>;
    end if;
    // modify <wL> to give words in <G.i>
    wL := [Evaluate (w, [wa, wb]) : w in wL];

    // put together the constructions that we wish to return
    mu := PrimitiveElement (GF (q));
    S := SL(2, q)![1, 0, 1, 1];
    T := SL(2, q)![1, 1, 0, 1];
    H := SL(2, q)![mu, 0, 0, 1/mu];
    s := S @ tauL;
    t := T @ tauL;
    h := H @ tauL;
    ws := s @ gammaL;
    wt := t @ gammaL;   // words in <L.i>
    wh := h @ gammaL;
    ws := Evaluate (ws, wL);
    wt := Evaluate (wt, wL);   // words in <G.i>
    wh := Evaluate (wh, wL);
    L := sub <Generic (G) | [s, t, h]>;
    wL := [ws, wt, wh];
    return true, L, wL;   
end function;

// Return a naturally embedded SU(3, q)-subgroup of G containing L.

SU4_CONSTRUCT_NATURAL_SU3 := function (G, proc, L, wL, q, limit)
    _, p, k := IsPrimePower(q);
    s := L.1;
    ws := wL[1];
    count := 0;
    flag := false;
    repeat
        count +:= 1;
        g, w := Random (proc);
        u := s^g;
        wu := ws^w;
        J := sub<Generic (G) | [L.i : i in [1..Ngens (L)]] cat [u]>;
        f,t := LieType(J, p);
        if not f then continue; end if;
        type := <"2A", 2, q>;
        if type ne t then continue; end if;
        FoundSection, Jtilde, sectionsnum, sections := SmallestFaithful(J, type);
        if not FoundSection then 
      	    vprint su4: "did not find good section";
	    Jtilde := J;
            myflag:=true;
            zxc:= Cputime();
            flag, phi, tau, gamma, delta:= RecogniseSU3(Jtilde, q);
            su3time := Cputime(zxc);
            vprint su4: "Time taken to recognise su3:", su3time;	
        else 
	    vprint su4 : "found good section";
            myflag := Type (Jtilde) eq GrpPerm or 
                 (Type (Jtilde) eq GrpMat and IsAbsolutelyIrreducible(Jtilde));
            if not myflag then
                Jtilde, f := AbsoluteRepresentation(Jtilde);
            else
                f := hom<Generic(Jtilde) -> Generic(Jtilde) | x :-> x>;
            end if;
	    zxc := Cputime();
            flag, phitilde, tautilde, gammatilde, deltatilde 
	           := RecogniseSU3 (Jtilde, q);
            su3time := Cputime(zxc);
            vprint su4: "Time taken to recognise su3:", su3time;
        end if;
    until ((flag) or (count ge limit));
    if (not flag) then
       return false, _, _, _, _, _, _, _, _, _, _;
    end if;
    if FoundSection then
        Jgens := [J.i : i in [1..Ngens(J)]];
        MB := hom<Generic(J) -> Generic(Jtilde) | 
                 g :-> (MatrixBlocks(J, g)[sectionsnum]@ f)>;
        phi := MB*phitilde;
        tau := hom<Generic(Domain(tautilde)) -> Generic(J) | 
                 x :-> Evaluate(((x @ tautilde) @ gammatilde), Jgens)>;
        gamma := MB*gammatilde;
        W := WordGroup(J);
        delta := hom<W -> Generic(J) | w :-> Evaluate(w, Jgens)>;
    else
        W := WordGroup(J);
        phitilde := phi;
        gammatilde := gamma;
        tautilde:= tau;
        deltatilde := delta;
    end if;
    wJ := wL cat [wu];
    return flag, J, wJ, phi, tau, gamma, delta, 
           phitilde, tautilde, gammatilde, deltatilde;
end function;

/* Given opposite (non-commuting) transvections <S> and <T>
   in SU(3, <E>) find a change-of-basis matrix <C> such that
                  [1 0 0]                     [1 0 y]
   <C><S><C>^-1 = [0 1 0] and  <C><T><C>^-1 = [0 1 0]
                  [x 0 1]                     [0 0 1]
   where <x> and <y> are (unspecified) trace-zero elements of <E>
*/
   
SU3_CHANGE_OF_BASIS_MATRIX := function (S, T)
     E := BaseRing (Parent (S));
     l := Degree (E);
     p := Characteristic(E);
     ll := l div 2;
     q := p^ll;
     assert l mod 2 eq 0;
     k := l div 2;
     F := GF (Characteristic (E)^k);
     MA := MatrixAlgebra (E, 3);
     form := MA![0, 0, 1, 0, 1, 0, 1, 0, 0];
     V := VectorSpace (E, 3);
     XS := MA!S - Identity (MA);
     XT := MA!T - Identity (MA);
     SS := sub <V | Image (XS)>;
     TT := sub <V | Image (XT)>;
     if Dimension (SS) * Dimension (TT) ne 1 then
        "Problem with SU3-isomorphism(s)";
        return Identity (GL (3, E));
     end if;
     e := SS.1; f := TT.1; 
     e := e / InnerProduct (e * form, FrobeniusImage (f, k));
     U := Nullspace (XS) meet Nullspace (XT);
     assert Dimension (U) eq 1;
     u := U.1;
     a := InnerProduct (u * form, FrobeniusImage (u, k));
     b := ElementHavingPrescribedNorm (a, F , E, q);
     assert (b^(q+1)) eq a;
     u := u / b;
     bas := [V!e , V!u , V!f];
return GU (3, E)!Matrix (bas);
end function;

/* Input:
     (1) <Qgens> 
     (2) An element <r> of the form
            [1   c  a  b]
            [0   1  0  0]
            [0 -b^q 0  0]
            [0 -a^q 0  0]
         namely an element of the (matrix) group <Q>
   Output: a word in <Qgens> that evaluates to <r>
*/

NRSU4_QSLP := function (Qgens, r)  

     assert #Qgens mod 5 eq 0;
     e := #Qgens div 5;

     k := BaseRing (Parent (r));

     u := VectorSpace (k, 2)![r[1][3], r[1][4]];
     Q := [VectorSpace (k, 2)![Qgens[i][1][3], Qgens[i][1][4]]:
	    	          i in [e+1..#Qgens]];
     coeffs := MyCoefficients (Q, u);
     r0 := &*[Qgens[e+i]^coeffs[i]: i in [1..#coeffs]];
     t0 := r * r0^-1;

     c0 := t0[1][2];
     c := Qgens[1][1][2];
     q := Characteristic (k)^e;
     k0 := GF (q);
     B := [k0!(Qgens[i][1][2]/c) : i in [1..e]];
     d := k0!(c0/c);
     Tcoeffs := MyEltseq (B, d);
assert t0 eq &*[Qgens[i]^Tcoeffs[i]: i in [1..e]];

     pows := Tcoeffs cat coeffs;
     X := SLPGroup (5*e);

return &*[(X.i)^pows[i]: i in [1..5*e]];
end function;

su2_to_sl2 := function (alpha)
     K := Parent (alpha);
     e := Degree (K);
     assert (e mod 2 eq 0);
     f := e div 2;
     assert alpha + Frobenius (alpha, f) eq 0;
     su2 := SU(2, K);
     k := GF (Characteristic (K), f);
     sl2 := SL(2, k);
     image := function (x, d)
         y := MatrixAlgebra (BaseRing (Parent (x)), Degree (Parent (x)))!x;
         y[1][2] := y[1][2]* d;
         y[2][1] := y[2][1]/ d;
         return y;
     end function;
     return hom <su2 -> sl2 | x :-> sl2!image (x, alpha)>;
end function;

/* EOB function:
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
//  [Br]P. A. Brooksbank, Fast constructive recognition of black box 
//  unitary groups, LMS J. Comput. Math. 6 (2003), 1 -- 36. (Section 6.2)
//
// This is the main engine for the intrinsics to follow
////////////////////////////////////////////////////////////////////////////

IsBlackBoxSU4 := function (G, q)
     // limit parameters
     limit1 := 10; //construct L limit
     limit2 := 12; //construct SU3 limit
     _, p, k := IsPrimePower(q);
     proc := RandomProcessWithWords (G);

     //////////////////////////////////////////////////// 
     // find a naturally embedded SL(2, q) subgroup <L> //
     //              ---- See [Br], Section 6.2.1 ---- //
     ////////////////////////////////////////////////////
     
     limit := 16 * Ceiling (Log (2, q));
     if q eq 8 then
         flag, a, wa := SU4_GOOD_ELEMENT_ORIGINAL(G, proc, q, limit);
     else
         flag, a, wa := SU4_GOOD_ELEMENT (G, proc, q, limit);
     end if;
     if (not flag) then return false, _; end if;
     zxc := Cputime();
     flag, L, wL := SU4_CONSTRUCT_L (G, proc, a, wa, q, limit1);
     vprint su4: "Time taken for CONSTRUCT_L:", Cputime(zxc);
     if (not flag) then return false, _; end if;
       
     ///////////////////////////////////////////// 
     // find two SU(3, q) subgroups containg <L> //
     //   ---- See [Br], Section 6.2.2 ----     //
     /////////////////////////////////////////////
     
     flag, J1, wJ1, phi1, tau1, gamma1, delta1, 
     phi1tilde, tau1tilde, gamma1tilde, delta1tilde := 
             SU4_CONSTRUCT_NATURAL_SU3 (G, proc, L, wL, q, limit2);
     if (not flag) then return false, _; end if;
       
     flag, J2, wJ2, phi2, tau2, gamma2, delta2, 
     phi2tilde, tau2tilde, gamma2tilde, delta2tilde := 
             SU4_CONSTRUCT_NATURAL_SU3 (G, proc, L, wL, q, limit2);
     if (not flag) then return false, _; end if;

     /////////////////////////////////////////////
     // the basic idea is to embed SU(3, <E>) in //
     // SU(4, <E>) using <phi1> and then to      //
     // modify <phi2> so that the the two maps  //
     // define consistent embeddings.           //
     /////////////////////////////////////////////
     F := GF (q);
     k := Degree (F);
     p := Characteristic (F);
     E := ext <F | 2>;
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
     iota1 := hom <GL(3, E) -> GL (4, E) | 
                          x :-> MyInsertBlock (x, 4, [1, 2, 4])>;
     iota2 := hom <GL(3, E) -> GL (4, E) | 
                          x :-> MyInsertBlock (x, 4, [1, 3, 4])>;
     psi1 := hom <Generic (J1) -> GL (4, E) | 
                          x :-> (C1 * (x @ phi1) * C1^-1) @ iota1>;
     
     r := PrimitiveElement (E);
     hhh := SU(3, E)![r, 0, 0, 0, r^(q-1), 0, 0, 0, 1/r^q];  
     y1 := ElementHavingPrescribedTrace (E, -1);
     yr := ElementHavingPrescribedTrace(E, -r^(q+1));
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

     z1 := h1^(q-1); z2 := h2^(q-1);
     // <zi> is a (???generator????) for the centralizer in <Ji> of <L>
     A0 := sub <Generic (G) | [z1 , z2]>;
     L0, wL0 := DerivedGroupMonteCarlo (A0);
     type0 := <"A" , 1, q>;
     f,mytype := LieType(L0 , p);
     if not f or (mytype ne type0) then 
         return false, _;
     end if;
     FoundSection, LL0, sectionsnum0, sections0 := SmallestFaithful(L0, type0);
     if FoundSection then
         if Type (LL0) eq GrpMat then 
            f, L0tilde := IsOverSmallerField(LL0, k);     
         else 
            f := false; 
         end if;
         if f then
             reducedimage0 := map<Generic(LL0) -> Generic(L0tilde) | 
                                  x:-> SmallerFieldImage(LL0, x)>;
             subL0tilde := sub<Generic(L0tilde) | 
                       [(LL0.i @ reducedimage0) : i in [1..Ngens(LL0)]]>;
             vprint su4: "Found 2-dimensional rep of SL2 over GF(", q, ")";
         else
             L0tilde := LL0;
             reducedimage0 := map<Generic(LL0) -> Generic(L0tilde) | x :-> x>;
             if Type (G) eq GrpMat then 
                vprint su4: "Found SL2 of dimension:", Dimension(L0tilde), 
                            "defined over ", BaseRing(L0tilde);
             else 
                vprint su4: "Found SL2";
             end if; 
         end if;

         flag, phi0tilde, tau0tilde, gamma0tilde, delta0tilde 
                            := RecogniseSL2 (L0tilde, q);
         if (not flag) then
             return false, _;
         end if;
         L0gens := [L0.i : i in [1..Ngens(L0)]];
         MB0 := map<Generic(L0) -> Generic(L0tilde) | g:-> 
		       ((MatrixBlocks(L0, g )[sectionsnum0]) @ reducedimage0)>;
         phi0 := MB0*phi0tilde;
         tau0 := map<Generic(SL(2, q))-> Generic(L0) | 
                     x:-> Evaluate(((x @ tau0tilde) @ gamma0tilde ) , L0gens)>;
         gamma0 := MB0*gamma0tilde;
     else
         flag, phi0, tau0, gamma0, delta0 := RecogniseSL2(L0, q);
         if not flag then
             return false, _;
         end if;
     end if;

     //////////////////////////////////////////////////
     // Compute the action of <z1> and <z2> on <L0>: //
     // see Procedure 6.9, Steps 3 and 4.            //
     //////////////////////////////////////////////////
     zxc := Cputime();
     flag, zz1, _ := PGL2ActionOnTransvectionGroups 
                         (L0, phi0, tau0, z1 : PSLAction := false);
     // EOB addition 
     if not flag then return false, _; end if;

     flag, zz2, _ := PGL2ActionOnTransvectionGroups 
                         (L0, phi0, tau0, z2 : PSLAction := false);
     // EOB addition 
     if not flag then return false, _; end if;

     zxc := Cputime(zxc);
     vprint su4: "Two calls to PGLAction takes time:", zxc;
     zz1 := GL (2, E)!zz1;
     zz2 := GL (2, E)!zz2;
     // find an Hermitian form preserved by <zz1> and <zz2>
     M := MatrixAlgebra(E, 2)![0, 1, -1, 0];
     N := ElementHavingPrescribedTrace(E, 0);
     N := N*M;
     assert IsHermitianForm(N);
     assert zz1*(GL(2, q^2)!N)*(Transpose(FrobeniusImage(zz1, k))) eq (GL(2, q^2)!N);
     assert zz2*(GL(2, q^2)!N)*(Transpose(FrobeniusImage(zz2, k))) eq (GL(2, q^2)!N);

     // compute the eigenvectors of <zzi>
     evals1 := Eigenvalues (zz1);
     evals2 := Eigenvalues (zz2);
     evecs1 := [Eigenspace (zz1, x[1]).1 : x in evals1];
     evecs2 := [Eigenspace (zz2, x[1]).1 : x in evals2];
     
     //////////////////////////////////////////////////////
     // Compute <z> in <L0> conjugating <Q2> / <S> to a  //
     // vector of <Q> / <S> perpendicular to <Q1> / <S>: //
     //               see Procedure 6.9, Steps 5 and 6.  //
     //////////////////////////////////////////////////////
     B1 := [];
     for v in evecs1 do
         lambda := InnerProduct (v * N, FrobeniusImage (v, k));
         gamma := ElementHavingPrescribedNorm (lambda, F, E , q);
         Append (~B1, v / gamma);
     end for;
     B2 := [];
     for v in evecs2 do
         lambda := InnerProduct (v * N, FrobeniusImage (v, k));
         gamma := ElementHavingPrescribedNorm (lambda, F , E , q );
         Append (~B2, v / gamma);
     end for;
     Z1 := GL(2, E)!Matrix (B1);
     Z2 := GL(2, E)!Matrix (B2);
     Z1 := GL(2, E)!Matrix ([B1[1]/ Determinant (Z2^-1 * Z1) , B1[2]]);
     zz := SL(2, F)!(Z2^-1 * Z1);
     z := zz @ tau0;
     if not ((u1, u2^z) eq Identity (G) and (w1, u2^z) eq Identity (G) ) then
         Z1 := GL(2, E)!Matrix ([B1[2], B1[1]]);
         Z1 := GL(2, E)!Matrix ([B1[2]/ Determinant (Z2^-1 * Z1) , B1[1]]);
         zz := SL(2, F)!(Z2^-1 * Z1);
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
     wz := Evaluate (wz, [wh1^(q-1) , wh2^(q-1)]);
     // "check wz word 2:", Evaluate (wz, [G.i : i in [1..Ngens (G)]]) eq z;

     ////////////////////////////////////////////////////
     // Compute the field automorphism needed to       // 
     // correct the second isomorphism <J2> -> SU(3, q).// 
     // This now differs slightly from Procedure 6.11. //
     ////////////////////////////////////////////////////
     
     K2 := sub <Generic (G) | [(J2.i)^z : i in [1..Ngens (J2)]]>;
     psi2 := hom <Generic (K2) -> GL (4, E) | x :-> 
                       (C2 * ((z * x * z^-1) @ phi2) * C2^-1) @ iota2>;
     h := h2^z;
     w := u1^h;
     ww := w @ psi1;
assert exists (e){j : j in [0..2*k-1]| r^(p^j) eq ww[2][1]};

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
     xi := ElementHavingPrescribedNorm (mu, F, E , q);
     D2 := GL (4, E)![1/xi, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, xi^q];
                         
     // modify <psi2>
     psi2 := hom <Generic (K2) -> GL (4, E) | 
                         x :-> D2 * FrobeniusImage (x @ psi2, e) * D2^-1>;
       
     // added by PAB on 11/07/2010:           
     ////////////////////////////////////////
     // Final transition to Eamonn's basis //
     ////////////////////////////////////////
     P := HyperbolicTransition (VectorSpace (E, 2));
     D3 := Identity (GL (4, E));
     InsertBlock (~D3, P, 2, 2);
     perm := SymmetricGroup (4)![1, 4, 2, 3];
     D3 := GL (4, E)!PermutationMatrix (E, perm) * D3;
     psi1 := hom <Generic (J1) -> GL (4, E) | 
                         x :-> D3 * (x @ psi1) * D3^-1>;
     psi2 := hom <Generic (K2) -> GL (4, E) | 
                         x :-> D3 * (x @ psi2) * D3^-1>;
     // end addition
                         
     /////////////////////////////////////
     // Create images of new generators //
     /////////////////////////////////////
     // added by PAB on 11/23/2010:

     // construct Eamonn's element <s>
     if (q mod 2 eq 1) then
         alpha := (E.1)^((q+1) div 2);
     else 
         alpha := E!1;
     end if;
     sss := GL(3, E)![0, 0, alpha, 0, 1, 0, 1/Frobenius (alpha, k), 0, 0];
     zxc := Cputime();
     s := (C1^-1 * sss * C1) @ tau1;
     evaltime := Cputime(zxc);

     ws := s @ gamma1;
     ws := Evaluate (ws, wJ1);
     // "check s word:", s eq Evaluate (ws, [G.i : i in [1..Ngens (G)]]);
     ss := s @ psi1;

     // construct Eamonn's element <t>
     ttt := GL(3, E)![1, 0, alpha, 0, 1, 0, 0, 0, 1];
     zxc := Cputime();
     t := (C1^-1 * ttt * C1) @ tau1;
     evaltime +:= Cputime(zxc);

     wt := t @ gamma1;
     wt := Evaluate (wt, wJ1);
     tt := t @ psi1;

     // construct Eamonn's element <delta>
     omega := E.1^(q+1);
     ddd := GL(3, E)![omega, 0, 0, 0, 1, 0, 0, 0, 1/omega];
     zxc := Cputime();
     d := (C1^-1 * ddd * C1) @ tau1;
     evaltime +:= Cputime(zxc);
     vprint su4: "Evaluation time since found SL2:", evaltime;
     wd := d @ gamma1;
     wd := Evaluate (wd, wJ1);
     dd := d @ psi1;
     
     // bring back my <h1> and make generators for <T>
     hh1 := h1 @ psi1;
     Tgens := [t^(h1^(-i)) : i in [1..k]];
     Tmats := [tt^(hh1^(-i)) : i in [1..k]];
     Twords := [wt ^(wh1^(-i)) : i in [1..k]];
     // "check Twords", 
     // forall {i : i in [1..#Twords]|
     // Evaluate (Twords[i], [G.j : j in [1..Ngens (G)]]) eq Tgens[i]};
     zxc := Cputime();
     // construct generators for Q(<f1>))

     RootElements := [];
     l := ElementHavingPrescribedTrace (E, -1);
     uuu := RootElementOfSU3 (E, E!1, l);
     for i in [1..2*k]do
	Append (~RootElements, uuu^(hhh^(i-1)));
     end for;

     Qe1mats1 := [(D3*(RootElements[i]@ iota1) * D3^-1) : i in [1..2*k]];
     Qe1words1 := [((C1^-1 * RootElements[i]*C1) @ tau1tilde) @ gamma1tilde 
                                             : i in [1..2*k]];
     Qe1words1 := [Evaluate (Qe1words1[i], wJ1) : i in [1..2*k]];

     // "check Qe1words1", 
     // forall { i : i in [1..#Qe1words1]|
     //      Evaluate (Qe1words1[i], [G.j : j in [1..Ngens (G)]]) eq Qe1gens1[i]};
     Qe1words2 := [((C2^-1 * RootElements[i]* C2) @ tau2tilde) @ gamma2tilde 
                         : i in [1..2*k]];
     Qe1words2 := [Evaluate (Qe1words2[i], wJ2) : i in [1..2*k]];
     Qe1words2 := [Qe1words2[i]^wz : i in [1..2*k]];

     // "check Qe1words2", 
     // forall { i : i in [1..#Qe1words2]|
     // Evaluate (Qe1words2[i], [G.j : j in [1..Ngens (G)]]) eq Qe1gens2[i]};
     Qe1mats2 := [D3*D2*(FrobeniusImage((RootElements[i]@ iota2), e))
                                   *D2^-1*D3 ^-1 : i in [1..2*k]];

     Qe1words := Qe1words1 cat Qe1words2;
     Qe1mats := Qe1mats1 cat Qe1mats2;
     Qf1words := [Qe1words[i]^ws : i in [1..4*k]];
     Qf1mats := [ss^-1*Qe1mats[i]*ss : i in [1..4*k]];
     Qmats := Tmats cat Qf1mats;
     Qwords := Twords cat Qf1words;
     Qtime := Cputime(zxc);
     vprint su4: "Time to construct Qgens:", Qtime;

     // "check Qwords:", forall { i : i in [1..#Qwords]|
     // Evaluate (Qwords[i], [G.j : j in [1..Ngens (G)]]) eq Qgens[i]};
     // construct Eamonn's element <x>
     xx := GL(4, E)![1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 1];
     wx := NRSU4_QSLP (Qmats, xx);
     // Evaluate (wx, Qmats) eq xx;

     wx := Evaluate (wx, Qwords);
     Ggens := [G.i : i in [1..Ngens(G)]];
     zxc := Cputime();
     x := Evaluate(wx, Ggens);

     evaltime +:= Cputime(zxc);
     vprint su4: "A Evaluation time since found SL2", evaltime;
     // "check x word:", Evaluate (wx, [G.i : i in [1..Ngens (G)]]) eq x;

     // need two more elements to construct Eamonn's <v>
     xx1 := GL(4, E)![1, 0, 0, 0, 0, 1, 0, 1, -1, 0, 1, 0, 0, 0, 0, 1];
     xx1s := xx1^ss;
     wx1s := NRSU4_QSLP (Qmats, xx1s);
     // Evaluate (wx1s, Qmats)^(ss^-1) eq xx1;

     wx1s := Evaluate (wx1s, Qwords);
     zxc := Cputime();
     x1s := Evaluate(wx1s, Ggens);
     evaltime +:= Cputime(zxc);

     x1 := x1s^(s^-1);
     wx1 := wx1s^(ws^-1);
     // "check x1 word:", Evaluate (wx1, [G.i : i in [1..Ngens (G)]]) eq x1; 
     if (q mod 2 eq 1) then
         vv0 := hh1^((q^2-1) div 2);
         v0 := h1^((q^2-1) div 2);
         wv0 := wh1^((q^2-1) div 2);
     else
         vv0 := Identity (GL(4, E));
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
     Sgens := [Tgens[i]^s : i in [1..#Tgens]];
     Swords := [Twords[i]^ws : i in [1..#Twords]];
     Smats := [Tmats[i]^ss : i in [1..#Tmats]];
     L2gens := [Tgens[i]^v : i in [1..#Tgens]]cat
               [Sgens[i]^v : i in [1..#Tgens]];
     wL2 := [Twords[i]^wv : i in [1..#Twords]]cat
            [Swords[i]^wv : i in [1..#Swords]];
     L2mats := [Tmats[i]^vv : i in [1..#Tmats]]cat
               [Smats[i]^vv : i in [1..#Tmats]];
     su2mats := [ExtractBlock (L2mats[i], 3, 3, 2, 2) :
                     i in [1..#L2mats]];
     sumap := su2_to_sl2 (alpha);
     sl2mats := [su2mats[i]@ sumap : i in [1..#su2mats]];
     sl2 := sub <GL(2, q) | sl2mats>;
     isit, a, b, c := RecogniseSL2 (sl2);
     // "isit?", isit;
     // <c> is a map to the word group on <sl2mats>
     yy := GL(4, E)![E.1, 0, 0, 0, 0, 1/E.1^q, 0, 0, 0, 0, 1/E.1, 0, 0, 0, 0, E.1^q];
     jj := yy * hh1^-1;
     jjj := ExtractBlock (jj, 3, 3, 2, 2);
     error if (Determinant(jjj) ne 1), "Determinant of jjj is not 1";
     wj := (jjj @ sumap) @ c;
     // "good?", Evaluate (wj, L2mats) eq jj;
     zxc := Cputime();
     j := Evaluate (wj, L2gens);
     evaltime +:= Cputime(zxc);
     wj := Evaluate (wj, wL2);
     // "check j:", Evaluate (wj, [G.i : i in [1..Ngens (G)]]) eq j;
     y := j * h1;
     wy := wj * wh1;
     // "check y:", Evaluate (wy, [G.i : i in [1..Ngens (G)]]) eq y; 
     vprint su4: "B Evaluation time since found SL2:", evaltime;     
     vprint su4: "End of IsBlackBoxSU4";

     /////////////////////////////////
     // assemble the data structure //
     /////////////////////////////////
     // EOB list of generators 
     Generators := [s, u, t, d, v, x, y];
     Images := [ss, uu, tt, dd, vv, xx, yy];
     Words := [ws, wu, wt, wd, wv, wx, wy];

     rf := recformat <Generators, Images, Words>;
     data := rec <rf | Generators := Generators, Images := Images, Words := Words>;
     G`SU4DataStructure := data;
return true;
end function;

/* IsBlackBoxSU4 returns true or false according to whether of not the 
   input is a central quotient of SU(4, q). If it is then a data structure 
   SU4DataStructure is attached to <G> containing the following fields:

   (1) Generators -- new generators for <G> that are the preimages
       of Eamonn's standard generators for SU(4, q);
   (2) Images -- Eamonn's standard generators; and
   (3) Words -- SLPs that evaluate from the user-defined generators
       to the new generators.
*/

////////////////////////////////////////////////////////////////
// This function sets up an isomorphism by constructing a new //
// generating set for <G> and identifying suitable images in  //
// SU(4, q). The output matrices in SU(4, q) are not written    //
// relative to a basis that Magma would regard as standard.   //
// Due to the natural construction of the generators, they    //
// written relative to a basis <e>, <v1>, <v2>, <f>, where    //
// <e> and <f> are a hyperrbolic pair, and <vi> satisfies     //
// (<vi>, <vi>) = 1, (<v1>, <v2>) = (<vi>, <e>) = (<vi>, <f>) = 0 //
////////////////////////////////////////////////////////////////

intrinsic RecogniseSU4 (G::Grp, q::RngIntElt) -> BoolElt, Map, Map, Map, Map
{given a central quotient G of SU(4, q), return a homomorphism from G to 
 (P)SU(4, q), a homomorphism from (P)SU(4, q) to G, the map from G to its 
 word group and the map from the word group to G.
}
// "**** March 2014 revised SU4 code";

     require IsPrimePower (q): "Field size is not correct";

     if assigned (G`RecognitionMaps) then
         maps := G`RecognitionMaps;
         return true, maps[1], maps[2], maps[3], maps[4];
     end if;

     //limit parameters
     limit1 := 10; //how many times do we run IsBlackBoxSU4?

     if (q in {2, 3, 4, 5, 7}) then
        return SporadicSU4 (G, q);
     end if;

     // G natural copy? if so, use special machinery 
     Natural := Type (G) eq GrpMat and Degree (G) eq 4 and #BaseRing(G) eq q^2 and 
                RecogniseClassical (G: Case := "unitary") cmpeq true;

     if not (q in {8, 11}) and Natural eq true then 
        f, phi, tau, gamma, delta := RecogniseSU4White (G, q);
        if not f then return false, _, _, _, _; end if;
        G`RecognitionMaps := <phi, tau, gamma, delta>;
        return true, phi, tau, gamma, delta;
     end if;

     i := 1;
     flag := false;
     while (i lt limit1) and (not flag) do 
        i +:= 1;
        flag := IsBlackBoxSU4 (G, q);
     end while;
     if (not flag) then
        return false, _, _, _, _;
     end if;

     generic := Generic (G);
     W := WordGroup (G);

     // Set up maps using rewriting machinery
     LGOWords := G`SU4DataStructure`Words;

     E := G`SU4DataStructure`Generators;
     SS := ClassicalStandardGenerators ("SU", 4, q);
     CB := GL(4, q^2)![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0];
     S := SS^(CB^-1);

     phi := hom<generic -> GL(4, q^2) | x :-> Evaluate (w where
                _, w := ClassicalRewrite (G, E, "SU", 4, q, x), S)>;

     tau := hom<GL(4, q^2) -> generic | x :-> Evaluate (w where
                _, w := ClassicalRewrite (SU(4, q), S, "SU", 4, q, x), E)>;

     gamma := hom<generic -> W | x :-> 
                  w where _, w := ElementToSLP (G, LGOWords, E, 4, q, x)>;

     delta := hom<W -> generic | x :->
                  Evaluate (x, [G.i : i in [1..Ngens (G)]])>;

     // find a change-of-basis matrix to convert to Magma form
     H := sub <GL(4, q^2) | G`SU4DataStructure`Images>;
     M := MatrixAlgebra (GF (q^2), 4)![0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0];
     assert forall {i : i in [1..Ngens (H)]| 
                        PreservesSesquilinearForm (M, H.i) };    
     C := TransformForm (M, "unitary");
     Images := [C^-1 * G`SU4DataStructure`Images[i]* C:
                i in [1..#G`SU4DataStructure`Images]];
     Gens := G`SU4DataStructure`Generators;       
     assert #Gens eq #Images;

     /* Added 12/08/2010 after correspondence with D. Holt and J. Cannon
        At this stage a set of generators is stored, purportedly
        for G, but certainly for a subgroup of G isomorphic
        (mod scalars) to (P)SU(4, q). We must check that the 
        generators for G are in this subgroup.
     */
     zxc := Cputime();

     flag := forall{i : i in [1..Ngens (G)]| 
                  ClassicalRewrite (G, E, "SU", 4, q, G.i) eq true};
     vprint su4: "Classical rewrite took time", Cputime(zxc);
     if (not flag) then
         return false, _, _, _, _;
     end if;
       
    G`RecognitionMaps := <phi, tau, gamma, delta>;
    return true, phi, tau, gamma, delta;
end intrinsic;

intrinsic SU4ElementToWord(G :: Grp, g :: GrpElt) -> BoolElt, GrpSLPElt
{ if g is element of G which has been constructively recognised to have
  central quotient isomorphic to PSU(4, q), then return true and element
  of word group of G which evaluates to g, else false.
}
    data := G`SU4DataStructure; 
    field := BaseRing (Universe (data`Images));
    q := Isqrt (#field);
    words := G`SU4DataStructure`Words;
    E := data`Generators;
    flag, w := ElementToSLP (G, words, E, 4, q, g);
    if flag then return flag, w; else return false, _; end if;
end intrinsic;
