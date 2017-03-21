freeze;

import "bbprelims.m": MyEltseq, SL2NormalisingToralElement,
                    IsSL2xSL2, FactorizeSL2xSL2, 
                    FactorizeSL2xSL2Alt, PreservesBilinearForm;
import "bbsporadics.m": SporadicSp4;

///////////////////////////////////////////////////////
//                                                   //
// Constructive recognition functions for Sp(4,2^e). //
//                                                   //
///////////////////////////////////////////////////////


/*
   This function is the springboard for the constructive
   recognition of black box Sp(4,even).

   Input:
     (1) A black box group <G>
     (2) A random process for <G> (with words)
     (3) A 2-power <q>
     (4) An integer <limit>
   Output:
     (1) A <flag> indicating success or failure.
     (2) A subgroup <K> of <G> isomorphic to SL(2,q) x SL(2,q)
     (3) A list of <words> expressing the generators of <K>
         in terms of the generators of <G>
*/
Sp4_CONSTRUCT_SL2xSL2 := function (G, proc, q, limit)

     count := 0;
     ord := q^2 - 1;
     found := false;
     while (count lt limit) and (not found) do
         count +:= 1;
         g, w := Random (proc);
         o := Order (g);
         if (o eq ord) then
            found := true;
         end if;
     end while;
     if (not found) then
       return false, _, _;
     end if;

     a := g^(q-1);
     wa := w^(q-1);
     found := false;
     count := 0;
     while (count lt limit) and (not found) do
         count +:= 1;
         g, w := Random (proc);
         K := sub < Generic (G) | [a, a^g] >;
         found := IsSL2xSL2 (K, q);
     end while;
     if (not found) then
         return false, _, _;
     end if;

return true, K, [wa, wa^w];
end function;
///////////////////////////////////////////////////////////////


/*
   The following function is the generic (black box) constructive
   recognition function Sp(4,2^e).
   The input is:
      (1) A black box group G
      (2) e > 1 an integer
   The output is:
      (1) a flag indicating success or failure
      (2) A record with the following fields:
        (a) LData = a record storing necessary data concerning a
                  constructively recognised SL(2,q) subgroup of <G>

        (d) Generators = list of new generators for <G>
        (e) Words = corresponding list of SLPs from given gens
        (f) Images = list of generators for SU(3,q) such that
                            Generators -> Images 
                      defines an isomorphism
*/

/////////////////////////////////////////////////////////////////////////
//  [Sp] P. A. Brooksbank, Fast constructive recognition of black box  // 
//  symplectic groups, J. Algebra 320 (2008), 885 -- 909. (Section 4)  //
/////////////////////////////////////////////////////////////////////////

IsBlackBoxSp4Even := function (G, e)

     q := 2^e;
     F := GF (q);
     mu := PrimitiveElement (F);
     proc := RandomProcessWithWords (G);

     /////////////////////////////////////////////
     // First find a subgroup <K> isomorphic to //
     // SL(2,q) x SL(2,q) and a corresponding   //
     // factorisation: See Section 4.1.         //
     /////////////////////////////////////////////

     limit := 50 * e; 
     flag, K, wK := Sp4_CONSTRUCT_SL2xSL2 (G, proc, q, limit);
     if (not flag) then
         return false;
     end if;

     limit := 10;
     i := 0;
     flag := false;
     repeat
         i +:= 1;
         flag0, L1, wL1, L2, wL2 := FactorizeSL2xSL2Alt (K, q);
         if (flag0) then
            flag1, phi1, tau1, gamma1, delta1 := RecogniseSL2 (L1, q);
            if (flag1) then
               flag2, phi2, tau2, gamma2, delta2 := RecogniseSL2 (L2, q);
               if (flag2) then
                  flag := true;
               end if;
            end if;
         end if;
     until flag or (i eq limit);  
     if (not flag) then
          return false; 
     end if;
       
     wL1 := [ Evaluate (x, wK) : x in wL1 ];
     wL2 := [ Evaluate (x, wK) : x in wL2 ];


     //////////////////////////////////////////////////////////
     // construct short root element in <Q>, the unipotent   //
     // radical of the normalizer in <G> of a transvection   //
     // group <S1>: See Section 4.2.                         //
     //////////////////////////////////////////////////////////
     sM := GL (2, F)![1,0,1,1]; 
     tM := GL (2, F)![1,1,0,1];
     hM := GL (2, F)![ mu , 0 , 0 , 1/mu ]; 
     s1 := sM @ tau1;   // a transvection in L
     t1 := tM @ tau1;   // a transvection in L
     h1 := hM @ tau1;   // a normalizing toral element
     wt1 := t1 @ gamma1;  // a word in <wL1>
     wt1 := Evaluate (wt1, wL1);   // a word in defining gens   
     ws1 := s1 @ gamma1;  // a word in <wL1>
     ws1 := Evaluate (ws1, wL1);   // a word in defining gens
     wh1 := h1 @ gamma1;   // a word in <wL>
     wh1 := Evaluate (wh1, wL1);   // a word in defining gens

        // --- find a conjugate of <s1> not in <L1> --- //
     repeat
         g, w := Random (proc);
         t := t1^g;
         wt := wt1^w;
         inL1, _ := SL2ElementToWord (L1, t);
     until (not inL1) and (t, t1) ne Identity (G);
        // --- construct a noncentral element of <Q> --- //   
     Lgens := [ t1^(h1^i) : i in [0..e-1] ] cat [ t ];
     L := sub < Generic (G) | Lgens >;
     wL := [ wt1^(wh1^i) : i in [0..e-1] ] cat [ wt ];
     flag, phiL, tauL, gammaL, deltaL := RecogniseSL2 (L, q);
     if (not flag) then
         return false;
     end if;
     h := SL2NormalisingToralElement (L, phiL, tauL, t1, t);
     wh := h @ gammaL;
     wh := Evaluate (wh, wL);
     u0 := (h, h1);
     wu0 := (wh, wh1);

     /////////////////////////////////////////////////////
     // assemble the data structure: See Section 4.3.2. //
     /////////////////////////////////////////////////////

     // first elements of <L2> and their images ... Eq (10)
     lM := GL (2, F)![0,1,-1,0];  
     l2 := lM @ tau2;
     wl2 := Evaluate (l2 @ gamma2, wL2);
     s2 := sM @ tau2;
     ws2 := Evaluate (s2 @ gamma2, wL2);
     h2 := hM @ tau2;
     wh2 := Evaluate (h2 @ gamma2, wL2);
     I4 := Identity (GL (4, F));
     ll2 := GL (4, F)!InsertBlock (I4, lM, 3, 3);
     ss2 := GL (4, F)!InsertBlock (I4, sM, 3, 3);
     hh2 := GL (4, F)!InsertBlock (I4, hM, 3, 3);

     // next generators for <Q> as <F>-space and their images ... Eq (13)
     u := ((u0, s2), h2);
     wu := ((wu0, ws2), wh2);
     if (u eq Identity (G)) then
         u := (u0, h2);
         wu := (wu0, wh2);
     end if;
     v := u^l2;
     wv := wu^wl2;
     uu := GL (4, F)![1,0,1,0,0,1,0,0,0,0,1,0,0,-1,0,1];
     vv := GL (4, F)![1,0,0,1,0,1,0,0,0,1,1,0,0,0,0,1];
     
     // find the field generator induced by <h1> ... Eq (16)
     U := [ Identity (G) ] cat [ u^(h2^i) : i in [0..q-2] ];
          // this is the short root group containing <u>
          // this root group is also normalised by <h1>
     assert exists (j){ i : i in [3..q] | u^h1 eq U[i] };
     assert Gcd (j-2, q-1) eq 1;
     rho := mu^(2-j);
     hh1 := GL (4, F)!InsertBlock (I4, GL (2, F)!
                            [rho,0,0,1/rho], 1, 1);

     // redefine <t1> and find a suitable image ... Eq (14)
     t1 := u * (s2, v);
     tt1 := uu * (ss2, vv);
     assert tt1[1][2] eq 1;
     wt1 := wu * (ws2, wv);

     // find a suitable image for <s1>
     T1 := [ Identity (G) ] cat [ t1^(h1^i) : i in [0..q-2] ];
     x := t1^s1;
     assert exists (k){ i : i in [2..q] | 
                            (x, s1^T1[i]) eq Identity (G) };
     lambda := (mu^(j-2))^(2*(2-k));
     ss1 := GL (4, F)![1,0,0,0,lambda,1,0,0,0,0,1,0,0,0,0,1];

     // finally construct <l1> and its image
     pows := MyEltseq ([ (rho^2)^i : i in [0..e-1] ], 1/lambda);
     xx := &*[ (ss1^pows[i])^(hh1^(i-1)) : i in [1..e] ];
     assert xx[2][1] eq 1;
     wx := &*[ (ws1^pows[i])^(wh1^(i-1)) : i in [1..e] ];
     x := &*[ (s1^pows[i])^(h1^(i-1)) : i in [1..e] ];
     ll1 := xx * tt1^-1 * xx;
     wl1 := wx * wt1^-1 * wx;
     l1 := x * t1^-1 * x;

     rf := recformat < L2data, TransvectionGroup, ShortRootGroup, 
                       Generators, Words, Images >;

     ///////////////////////////////////////////////////////
     // we shall also need the ability to write elements  //
     // of <L2> as words in <s2>, <h2>, <l2>; this should //
     // ultimately be replaced with a direct procedure    //
     ///////////////////////////////////////////////////////
     X := sub < Generic (G) | [ s2 , h2 , l2 ] >;
     flag, phiX, tauX, gammaX, deltaX := RecogniseSL2 (X, q);

     rf2 := recformat < Group, Forward, Backward, WordMap, 
                        CanonicalWordMap, Words >;

     L2data := rec < rf2 | Group := L2,
                           Forward := phi2,
                           Backward := tau2,
                           WordMap := gamma2,
                           CanonicalWordMap := gammaX,
                           Words := wL2 
                   >;

     Images := [ tt1 , uu , vv , hh1 , ll1 , ss2 , hh2 , ll2 ];
     Generators := [ t1 , u , v , h1 , l1 , s2 , h2 , l2 ];
     Words := [ wt1 , wu , wv , wh1 , wl1 , ws2 , wh2 , wl2 ];

     flag := forall { i : i in [1..#Generators] |
                       Evaluate (Words[i], 
           [ G.j : j in [1..Ngens (G)] ]) eq Generators[i] };

     if (not flag) then
         return false;
     end if;
  
     data := rec < rf | L2data := L2data,
                        TransvectionGroup := T1,
                        ShortRootGroup := U,
                        Generators := Generators,
                        Words := Words,
                        Images := Images 
                 >;

     G`Sp4DataStructure := data;

return true;
end function;


/////////////////// CANONICAL GENERATORS /////////////////

/*
   For convenience here are the matrices corresponding to 
   the canonical generators that we are using for Sp(4,even).
   Analogous generators should be used also for Sp(4,odd)
   since the SLP functions are encoded independently of
   characteristic.

        [ 1 1 0 0 ]       [ 1 0 1 0 ]       [ 1 0 0 1 ]
   t1 = [ 0 1 0 0 ]   u = [ 0 1 0 0 ]   v = [ 0 1 0 0 ]
        [ 0 0 1 0 ]       [ 0 0 1 0 ]       [ 0 1 1 0 ]
        [ 0 0 0 1 ]       [ 0 1 0 1 ]       [ 0 0 0 1 ]

        [ r  0  0 0 ]        [ 0 1 0 0 ] 
   h1 = [ 0 1/r 0 0 ]   l1 = [ 1 0 0 0 ]
        [ 0  0  1 0 ]        [ 0 0 1 0 ]
        [ 0  0  0 1 ]        [ 0 0 0 1 ]

        [ 1 0 0 0 ]        [ 1 0 0  0  ]        [ 1 0 0 0 ]
   s2 = [ 0 1 0 0 ]   h2 = [ 0 1 0  0  ]   l2 = [ 0 1 0 0 ]
        [ 0 0 1 0 ]        [ 0 0 m  0  ]        [ 0 0 0 1 ]
        [ 0 0 1 1 ]        [ 0 0 0 1/m ]        [ 0 0 1 0 ]

   here <r> is an arbitrary generator of the multiplicative
   group of the field, whereas <m> is the preferred Magma
   generator of this group.

   Notice that these matrices all preserve an alternating
   form having matrix

   [ 0 1 0 0 ]           
   [ 1 0 0 0 ]  
   [ 0 0 0 1 ]
   [ 0 0 1 0 ]

   which is slightly different from the standard group
   stored by Magma but is more in keeping with the
   basis preferred by Leedham-Green and O'Brien.
*/

////////////////////////////////////////////////////////////


/*
   Input:
     (1) <Images> of the canonical generators (see above)
     (2) An element <r> of the form
            [ 1 x y z ]
            [ 0 1 0 0 ]
            [ 0 z 1 0 ]
            [ 0 y 0 1 ]
         namely an element of the (matrix) group Q.
   Output: a word in <Images> that evaluates to <r>

   Remark: This procedure is independent of characteristic
           so long as we use a suitable analgoue of the 
           canonical generating set.

   Afterthought: Don't need SLPs over GF(p) at all! It suffices
                 just to compute powers of the toral elements.
                 This is easily fixed if the lengths of SLPs 
                 are becoming prohibitively long.
*/
Sp4NRQSLP := function (Images, r)

     assert #Images eq 8;
     W := SLPGroup (8);
     E := BaseRing (Parent (r));
     e := Degree (E);
     rho := Images[4][1][1];
     mu := Images[7][3][3];

     upows := Eltseq (r[1][3]);
     upows := [ Integers ()!(upows[i]) : i in [1..#upows] ];
     vpows := MyEltseq ( [ (mu^-1)^i : i in [0..e-1] ], r[1][4]);
     ru := &*[ (Images[2]^upows[i])^((Images[7])^(i-1)) : 
                     i in [1..#upows] ];
     wru := &*[ ((W.2)^upows[i])^((W.7)^(i-1)) : i in [1..#upows] ];
     rv := &*[ (Images[3]^vpows[i])^((Images[7])^(i-1)) : 
                     i in [1..#vpows] ];
     wrv := &*[ ((W.3)^vpows[i])^((W.7)^(i-1)) : i in [1..#vpows] ];
     t := r * (ru * rv)^-1;
     tpows := MyEltseq ([ (rho^(-2))^i : i in [0..e-1] ], t[1][2]);
//assert t eq &*[ (Images[1]^tpows[i])^((Images[4])^(i-1)) : 
//                                               i in [1..#tpows] ];
     wt := &*[ ((W.1)^tpows[i])^((W.4)^(i-1)) : 
                                   i in [1..#tpows] ];

return wt * wru * wrv;
end function;
////////////////////////////////////////////////////////////////////


/*
   Input:
     (1) <Generators> the canonical ones described above
     (2) <Images> of these generators
     (3) <TransvectionGroup> listed according to the action of <h1>
     (4) <ShortRootGroup> list according to the action of <h2>
     (5) <r> an element of the black box group Q
   Output: a word in <Generators> that evaluates to <r>

   Remark: This procedure is independent of characteristic
           so long as we use a suitable analgoue of the 
           canonical generating set. Well ... one needs to
           be careful about how one lists <TransvectionGroup>

   Afterthought: Don't need SLPs over GF(p) at all! It suffices
                 just to compute powers of the toral elements. 
                 This is easily fixed if the lengths of SLPs 
                 are becoming prohibitively long.
*/
Sp4BBQSLP := function (Generators, Images, T, U, r)
 
assert #Generators eq 8;
     mu := Images[7][3][3];
     rho := Images[4][1][1];
     E := Parent (mu);
     e := Degree (E);
     W := SLPGroup (8);  

     r1 := ( (Generators[6], r), Generators[7] );
     assert exists (j){ i : i in [1..#U] | r1 eq U[i] };
     if (j eq 1) then
         rv := U[1];
         wrv := Identity (W);
     else
         beta := mu^(j-2) / (mu - 1);
         vpows := MyEltseq ([ (mu^-1)^i : i in [0..e-1] ], beta);
         rv := &*[ ((Generators[3])^(vpows[i]))^((Generators[7])^(i-1)) : 
                                              i in [1..#vpows] ];
         wrv := &*[ ((W.3)^(vpows[i]))^((W.7)^(i-1)) : i in [1..#vpows] ];
     end if;

     r2 := ( ( (Generators[6])^(Generators[8]), r ), 
             Generators[7] )^(Generators[8]);
     assert exists (j){ i : i in [1..#U] | r2 eq U[i] };
     if (j eq 1) then
         ru := U[1];
         wru := Identity (W);
     else
         alpha := mu^(j-2) / (1 - 1/mu);
         upows := MyEltseq ([ mu^i : i in [0..e-1] ], alpha);
         ru := &*[ ((Generators[2])^(upows[i]))^((Generators[7])^(i-1)) : 
                                              i in [1..#upows] ];
         wru := &*[ ((W.2)^(upows[i]))^((W.7)^(i-1)) : i in [1..#upows] ];
     end if;

     t := r * (ru * rv)^-1;
     assert exists (j){ i : i in [1..#T] | t eq T[i] };
     if (j eq 1) then
         wt := Identity (W);
     else
         gamma := (rho^-2)^(j-2);
         tpows := MyEltseq ([ (rho^-2)^i : i in [0..e-1] ], gamma);
         wt := &*[ ((W.1)^(tpows[i]))^((W.4)^(i-1)) : i in [1..#tpows] ];
     end if;

     w := wt * wru * wrv;

return w;
end function;
///////////////////////////////////////////////////////////////////////////

/*
   Input:
     (1) <G> our black box Sp(4,even)
     (2) <TransvectionGroup> according to <h1>
     (3) <s> an element from a transvection group <S>
     (4) <h1> an element of order q-1 normalising <S> and <T>
     (5) <mu> the field generator corresponding to <h1>
     (6) <x> a transvection opposite <t>
     (7) degree of the field extension
   Output:
     An element <u> of <Q> such that <X>^<u> = <S>,
     where <X> is the transvection group containing <x>

   Follows [Sp] Section 5.5.2: Effective transitivity of Q

   Note: odd characteristic is similar but easier.
*/
BBSpEvenConjugatingElementOfQ := function (G, T, s, h1, mu, x, e)
     t := T[2];
     if (t, x) eq Identity (G) then
         return false, _;
     end if;
     Lgens := [ T[i] : i in [2..e+1] ] cat [ x ];
     L := sub < Generic (G) | Lgens >;
     flag, phi, tau, gamma, delta := RecogniseSL2 (L, #T);
     if (not flag) then 
         return false, _;
     end if;
     h := SL2NormalisingToralElement (L, phi, tau, t, x);
     flag := exists (j){i : i in [3..#T] | T[i] eq t^h};
     if (not flag) then
         return false, _;
     end if;
        // the scalar <h> induces the same scalar as <h1>^(j-2)
     l := Integers ()!((Integers (#T-1)!(j-2))^-1);
     h := h^l;
        // now both <h> and <h1> induce <mu>^-2 on <T>
     flag := t^h eq T[3];
     if (not flag) then
         return false, _;
     end if;
     j := Log (mu^-2, 1/(mu^-2 - 1));
     u := (h1^-1 * h)^(h1^j);
        // <u> conjugates <X> into <L1>
     z := x ^ u;
     flag := exists (tt){ y : y in T | (z^y, s) eq Identity (G) };
        // should replace this with a more efficient method
     if (not flag) then
         return false, _;
     end if;
     w := u * tt;
return true, w;
end function;
/////////////////////////////////////////////////////////////////////


/*
   Analogue for the natural representation. Can easily be extended
   to arbitrary dimension. Stick to d = 4 here since the preferred
   basis may change as we move to higher dimensions.

   Input:
     <x> a transvection that is opposite our standard <t>

   Output:
     An element of <Q> conjugating <X> to <S>
*/

NRSp4ConjugatingElementOfQ := function (x)
     E := BaseRing (Parent (x));
     MA := MatrixAlgebra (E, 4);
     center := Image (MA!x - Identity (MA));
assert Dimension (center) eq 1;
     v := center.1;
assert v[1] ne 0;
     z := [ v[2]/v[1] , v[3]/v[1] , v[4],v[1] ];
     u := GL (4, E)![1,z[1],z[2],z[3],0,1,0,0,0,-z[3],1,0,0,z[2],0,1];
return u^-1;
end function;
/////////////////////////////////////////////////////////////////


/*
   Input:
     (1) A black box group <G> constructively recognised as Sp(4,q).
     (2) An element <x> of Sp(4,q) or of <G>
     (3) <flag> either "Natural" or "BlackBox" indicating which 
           
   Output: 
      A word in the canonical generators that evaluate to <x>
*/

Sp4SLP := function (G, x, flag)

     rho := G`Sp4DataStructure`Images[4][1][1];
     mu := G`Sp4DataStructure`Images[7][3][3];
     E := Parent (rho);
     e := Degree (E);
    
     if (flag eq "Natural") then
         CanGens := G`Sp4DataStructure`Images;
         H := sub < GL (4, E) | CanGens >;
     else 
         H := G;
         CanGens := G`Sp4DataStructure`Generators;
         T := G`Sp4DataStructure`TransvectionGroup;
         U := G`Sp4DataStructure`ShortRootGroup;
     end if;

     W := SLPGroup (#CanGens);
     t := CanGens[1]; 
     h1 := CanGens[4];
     l1 := CanGens[5];
     s := t ^ l1;
     L2data := G`Sp4DataStructure`L2data;

     y := x;

     // tweek <y> so that <t>^<y> is opposite <t>
     if (t, t^y) eq Identity (H) then
         if (t^l1, t^y) ne Identity (H) then
            y := y * l1^-1;
            wc := W.5;
         else
            isit := exists (j){ i : i in [2,3] |
                  (t, t^(y * (CanGens[i]^-1) ^ l1)) 
                        ne Identity (H) };
            if (not isit) then
               return false, _;
            end if;
            y := y * (CanGens[j]^-1) ^ l1;
            wc := W.j ^ W.5;
         end if;
     else
         wc := Identity (W);
     end if;

     // modify <y> so that it normalises <T>
     if (flag eq "Natural") then
         u := NRSp4ConjugatingElementOfQ (t^y);
         wu := Sp4NRQSLP (CanGens, u^-1);
     else
         isit, u := BBSpEvenConjugatingElementOfQ (G, T, s, h1, rho, t^y, e);
         if (not isit) then
             return false, _;
         end if;
         wu := Sp4BBQSLP (CanGens, G`Sp4DataStructure`Images, T, U, u^-1);
     end if; 
     wu := Evaluate (wu, [W.i : i in [1..#CanGens]]);

     y := y * u * l1^-1;

     // next modify <y> so that it normalises <S>
     if (flag eq "Natural") then
         v := NRSp4ConjugatingElementOfQ (s^y);
         wv := Sp4NRQSLP (CanGens, v^-1);
     else
         isit, v := BBSpEvenConjugatingElementOfQ (G, T, s, h1, rho, s^y, e); 
         if (not isit) then
             return false, _;
         end if;
         wv := Sp4BBQSLP (CanGens, G`Sp4DataStructure`Images, T, U, v^-1);
     end if;
     wv := Evaluate (wv, [W.i : i in [1..#CanGens]]);

     y := y * v;

     // from here we depart from the previous function
     // find the scalar induced on <T> by <y>
     if (flag eq "Natural") then
         xi := y[1][1];
         j := Log (rho, xi) mod Order (rho);
     else
         assert (t eq T[2]);
         isit := exists (j){ i : i in [2..#T] | t^y eq T[i] };
         if (not isit) then
             return false, _;
         end if;
         j -:= 2;
     end if;
     wh := (W.4)^j;

     y := y * h1^(-j);
 
     // now (since we are in characteristic 2) <y> is in <L2>
     if (flag eq "Natural") then
         // find the preimage in the black box group
         yyy := ExtractBlock (y, 3, 3, 2, 2);
         yy := yyy @ (L2data`Backward);
     else
         yy := y;
     end if;
     w := yy @ (L2data`CanonicalWordMap);   // word in [<s2>,<h2>,<l2>]
     w := W!(Evaluate (w, [W.i : i in [6,7,8]]));   // word in can gens

     // compose to obtain a word evaluating to <x>
     w := w * wh * wv * (W.5) * wu * wc;

return true, w;
end function;
//////////////////////////////////////////////////////////////////


/*
   Input:
     (1) Constructively recognised Sp(4,even) black box group <G>
     (2) An element <x> of <G> (should really allow supergroup)
   Output:
     An element of the word group of <G> that evaluates to <x>.
     If <Sp4Image> is set to <true> then it also returns the
     image of <x> in the natural copy of Sp(4,even)
*/
BlackBoxElementToSLP := function (G, x : Sp4Image := false);
     flag, w := Sp4SLP (G, x, "BlackBox");
     if (Sp4Image) then
         xx := Evaluate (w, G`Sp4DataStructure`Images);
         return w, xx;
     else
         return w, _;
     end if;
end function;
//////////////////////////////////////////////////////////////


/*
   Input:
     (1) Constructively recognised Sp(4,even) black box group <G>
     (2) An element <x> of Sp(4,even)
   Output:
     The preimage of <x> in <G>
*/
Sp4ElementToBlackBoxElement := function (G, x)
     flag, w := Sp4SLP (G, x, "Natural");
     xx := Evaluate (w, G`Sp4DataStructure`Generators);
return xx;
end function;
/////////////////////////////////////////////////////////////


/*
   The main recognition function for Sp(4,even).
   Input:
     (1) A black box group <G> thought to be isomorphic
         to Sp(4,q), where q is a power of 2.
     (2) A 2-power <q>
   Output:
     (1) <flag> indicating whether or not <G> is as claimed.
     (2) <phi> a map <G> -> Sp(4,q)
     (3) <tau> the inverse of <phi>
     (4) <gamma> a map <G> -> <W> the word group on <G>
     (5) <delta> the imverse of <gamma>
*/

intrinsic RecogniseSp4Even (G::Grp, q::RngIntElt) -> 
                             BoolElt, Map, Map, Map, Map
     { 
      if G is isomorphic to (P)Sp(4, 2^e),
      construct homomorphisms between G and Sp(4, 2^e);
      return homomorphism from G to Sp(4, 2^e), homomorphism
      from Sp(4, 2^e) to G, the map from G to
      its word group and the map from the word group to G.
     }

     if assigned (G`RecognitionMaps) then
         maps := G`RecognitionMaps;
         return true, maps[1], maps[2], maps[3], maps[4];
     end if;

     if (q eq 2) then
         return SporadicSp4 (G, q);
     end if;
  
     fac := Factorisation (q);
assert (#fac eq 1 and fac[1][1] eq 2);
     e := fac[1][2];

     // run the main constructive identification function    
     isit := IsBlackBoxSp4Even (G, e);
     if (not isit) then
         return false, _, _, _, _;
     end if;
       
     /*
        Added 12/08/2010 after correspondence with D. Holt and J. Cannon
        
        At this stage a set of generators is stored, purportedly
        for G, but certainly for a subgroup of G isomorphic
        (mod scalars) to (P)SU(3,q). We must check that the 
        generators for G are in this subgroup.
     */
     flag := forall { i : i in [1..Ngens (G)] |
                        Sp4SLP (G, G.i, "BlackBox") };
     if (not flag) then
         "(zzz)";
         return false, _, _, _, _;
     end if;
       

     // find change-of-basis matrix to convert form into Magma form  
     H := sub < GL (4, q) | G`Sp4DataStructure`Images >;
     M := MatrixAlgebra (GF (q), 4)![0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,0];
assert forall { i : i in [1..Ngens (H)] | 
                      PreservesBilinearForm (M, H.i) };    
     C := TransformForm (M, "symplectic");

     // set up maps
     
     generic := Generic (G);
     W := WordGroup (G);

     phi := hom < generic -> GL (4, q) | x :-> C^-1 * y * C where _, y :=
                   BlackBoxElementToSLP (G, x : Sp4Image := true) >;

     tau := hom < GL (4, q) -> generic | x :->
                   Sp4ElementToBlackBoxElement (G, C * x * C^-1) >;

     gamma := hom < generic -> W | x :-> 
                     Evaluate (w, G`Sp4DataStructure`Words) where
                     w := BlackBoxElementToSLP (G, x) >;

     delta := hom < W -> generic | x :->
                     Evaluate (x, [ G.i : i in [1..Ngens (G)] ]) >;

     G`RecognitionMaps := < phi , tau , gamma , delta >;
             
return true, phi, tau, gamma, delta;
end intrinsic;
    
