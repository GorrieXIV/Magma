freeze;

import "base.m": 
MyExteriorPower, MySymmetricPower, 
MyRecogniseSL4, MySL4q3,
MyRecogniseSL2_3, MyRecogniseSp2, MyRecogniseSp4,
MyRecogniseSU2, MyRecogniseSU4, MyRecogniseSU3;
import "omega8.m": MyRecogniseOmega8P;
import "base.m": IsNewInvolution;
import "rest-omega.m": SolveOmega6InOmega8;
import "SX63.m": MySolveSX63;
import "split.m": SmallestSection, SmallestFaithful, MatrixBlocks;
import "../../../../recog/magma/centre.m":EstimateCentre;
import "../../../classical.m": ClassicalConstructiveRecognitionNatural;
import "SX63.m": MyO78q3;
import "../even/baseCases.m": SXESolveSL4black, SXESolveSL5black;
import "../../../../GrpMat/black/recognise-section.m": RecogniseSection;
 
Factorise_qeq3 := function (G: VerifySL2 := true)
   if #G eq 576 and IdentifyGroup (G) ne <576, 5128> then 
      return false, _, _, _,_,_,_,_,_,_; 
   end if;

   q := 3;
   S := Subgroups (G);
   // EOB -- change to factorise SL2 x SL2 -- any consequences? 
   //   if #G eq 288 then o := 24; m := 2; else o := 12; m := 1; end if;
   if #G eq 288 then o := 24; m := 2; 
   elif #G eq 144 then o := 12; m := 1; 
   else o := 24; m := 1; end if;
   T := [(S[i]`subgroup) : i in [1..#S] | #S[i]`subgroup eq o];
   T := [x : x in T | IdentifyGroup (x) eq <o, 3>];

   if #T eq 0 then return false, _, _, _,_,_,_,_,_,_; end if;

   found := false;
   for i in [1..#T] do
      for j in [i + 1..#T] do 
         if #(T[i] meet T[j]) eq m then found := true; a := i; b := j; break i; end if;
      end for;
   end for; 

   if not found then return false, _, _, _,_,_,_,_,_,_; end if;

   W, phi := WordGroup (G);
   phi := InverseWordMap (G);
   
   U := T[a]; V := T[b];
   wU := [U.i @ phi: i in [1..Ngens (U)]];
   wV := [V.i @ phi: i in [1..Ngens (V)]];
   found, alpha, beta := RecogniseSL2 (U, q: Verify := false);
   found, delta, gamma := RecogniseSL2 (V, q: Verify := false);

   if VerifySL2 then 
      return true, U, wU, alpha, beta, V, wV, delta, gamma;
   else 
      return true, U, wU, V, wV;
   end if;
end function;

// remove redundant or trivial elements from Words
FixGens := function (G, Words)
   P := Generic (G);
   Gens := Evaluate (Words, UserGenerators (G));
   NewGens := [];
   NewWords := [];
   for i in [1..#Gens] do
      if not (Gens[i] in NewGens or Gens[i] eq Id (G)) then
         Append (~NewGens, Gens[i]);
         Append (~NewWords, Words[i]);
      end if;
   end for;
   NewG := sub<P | NewGens>;
   return NewG, NewWords;
end function;

/* Factorise the input group as a direct product of two SL(2,q)s.
   The input is:
     (1) A black box group H that is probably
         isomorphic to SL(2,q) x SL(2,q)
     (2) A prime power q
   The output is:
     (1) A flag
     (2) An SL(2,q)-subgroup L1 of H 
     (3) words expressing L1.i in terms of H.j
     (4) An SL(2,q)-subgroup L2 of H
     (5) words expressing L2.i in terms of H.j
   such that H = L1 x L2
*/

FactorizeSL2xSL2 := function (H, q: Omega4Test := false, VerifySL2 := true)

   procH := RandomProcessWithWords (H);
 
   p := Factorisation (q)[1][1];    
   if q eq 5 then 
       pows := [3,4,5,6,10];
       limit := 500;
   else
       pows := [2*p, q-1, q+1];
       limit := 50 * Floor (Log (2, q));
   end if;
 
   if q eq 3 then
     return Factorise_qeq3 (H: VerifySL2 := VerifySL2);
   else 
      // first search for elements that exhibit the desired factors  
      elts := [];
      words := [];
      count := 0;
      while (#elts lt 8) and (count lt limit) do
       count +:= 1;
       h, w := Random (procH);
       o := Order (h);
       for n in pows do
 	    if (o mod n eq 0) then
             a := h^n;
             wa := w^n;
             if (not a eq Identity (H)) and 
                (not forall {i : i in [1..Ngens (H)] | 
                             (H.i, a) eq Identity (H)}) then
                Append (~elts, a);
                Append (~words, wa);
             end if;
          end if;
       end for;
      end while;
   end if;

   if #elts eq 0 then return false, _, _, _,_,_,_,_,_,_; end if;
 
   // find the two factors
   gens1 := [elts[1]];
   wL1 := [words[1]];
   gens2 := [];
   wL2 := [];
   for i in [2..#elts] do
       flag1 := forall{j : j in [1..#gens1] | 
                           (gens1[j], elts[i]) eq Identity (H)};
       flag2 := forall{j : j in [1..#gens2] | 
                           (gens2[j], elts[i]) eq Identity (H)};
       if elts[i] eq elts[i]^0 or elts[i] in gens1 or elts[i] in gens2 
          then continue; 
       end if;
       if (flag1) then
          if (not flag2) or (#gens2 eq 0) then
             Append (~gens2, elts[i]);
             Append (~wL2, words[i]);
          end if;
       elif (flag2) then
 	    if (not flag1) then
 	       Append (~gens1, elts[i]);
             Append (~wL1, words[i]);
          end if;
       else     
  	    return false, _, _, _,_,_,_,_,_,_;
       end if;
   end for;
 
   if (#gens1 lt 2) or (#gens2 lt 2) then
       return false, _, _, _,_,_,_,_,_,_;
   end if;
 
   L1 := sub <Generic (H) | gens1>;
   L2 := sub <Generic (H) | gens2>;

   if not (IsProbablyPerfect (L1) and IsProbablyPerfect (L2)) then 
// "About to go home ...";
// "FAC L1", CompositionFactors (L1);
// "FAC L2", CompositionFactors (L2);
      return false, _, _, _,_,_,_,_,_,_;
   end if;
   
   if not VerifySL2 and q ne 9 then 
      return true, L1, wL1, L2, wL2;
   end if;
 
   found := false;
   if Type (L1) eq GrpPerm then 
      flag, type := LieType (L1, p);
      if flag and type cmpeq <"A", 1, q> then
         found, alpha, beta := RecogniseSL2 (L1, q);
      end if;
   else 
      Verify := q eq 9; 
      S_L1 := Omega4Test select SmallestSection (L1) else L1;
      flag, type := LieType (S_L1, p);
      if flag and type cmpeq <"A", 1, q> then
         found, alpha, beta := RecogniseSL2 (S_L1, q: Verify := Verify);
      end if;
   end if;
   if found eq false then 
       return false, _, _, _,_,_,_,_,_,_;
   end if;
 
   found := false;
   if Type (L2) eq GrpPerm then 
      flag, type := LieType (L2, p);
      if flag and type cmpeq <"A", 1, q> then
         found, delta, gamma := RecogniseSL2 (L2, q);
      end if;
   else 
      S_L2 := Omega4Test select SmallestSection (L2) else L2;
      // S_L2 := SmallestSection (L2);
      flag, type := LieType (S_L2, p);
      if flag and type cmpeq <"A", 1, q> then
         found, delta, gamma := RecogniseSL2 (S_L2, q: Verify := Verify);
      end if;
   end if;

   if found eq false then 
       return false, _, _, _,_,_,_,_,_,_;
   end if;

   if not VerifySL2 then 
      return true, L1, wL1, L2, wL2;
   end if;
 
   return true, L1, wL1, alpha, beta, L2, wL2, delta, gamma;
end function;

// ensure delta and delta', standard generators for Omega^+(4, F), are conjugate
// E is the list of standard generators, W corresponding SLPs
MakeConjugate := function (E, W, F)
   p := Characteristic (F);
   e := Degree (F);
   ev := Eigenvalues (E[3]);
   for i in [0..e - 1] do
       power := p^i;
       x := E[6]^(power);
       if Eigenvalues (x) eq ev then
          E[6] := E[6]^power;
          W[6] := W[6]^power;
          return E, W;
       end if;
   end for;
   error "Did not fix Omega+4 generators";
end function;

// constructively recognise H isomorphic to Omega+(4, F) 
// by decomposing G, a section of H, into SL(2, q) factors
// sometimes we need only standard generators, no maps  
MyRecogniseOmegaPlus4 := function (H, F: StandardOnly := true, Limit := 25)

   G := H;

   if #F eq 3 then
      o := #G;
      if #G ne 144 and #G ne 288 then return false, false; end if;
   end if;

   LargeToSmall := function (G, E, q, g, CB, index: type := "Omega+")
      blocks := MatrixBlocks (G, g);
      g := blocks[index];
      f, w := ClassicalRewrite (G, E, type, 4, q, g);
      X := ClassicalStandardGenerators (type, 4, q);
      return Evaluate (w, X)^(CB);
   end function;

   SmallToLarge := function (E, g, CB: type := "Omega+")
      P := Parent (g);
      q := #BaseRing (P);
      X := ClassicalStandardGenerators (type, 4, q);
      f, w := ClassicalRewrite (sub<Universe (X) | X>, X, type, 4, q, g^(CB^-1));
      return Evaluate (w, E);
   end function;

   LargeToWordGroup := function (G, E, W, q, g, index: type := "Omega+")
      blocks := MatrixBlocks (G, g);
      g := blocks[index];
      f, w := ClassicalRewrite (G, E, type, 4, q, g);
      return Evaluate (w, W);
   end function;

   p := Characteristic (F);
   q := #F;

   original_H := H;
   f, G, pos, S := SmallestFaithful (H, <"Omega+", 4, #F>);
   gens := UserGenerators (G);
   index := [Position (gens, G.i):  i in [1..Ngens (G)]];
   original_gens := [H.i: i in index];
   
   // get generating sets for two copies of SL2q in G
   NmrTries := 0;
   repeat 
      flag, Ng, WNg, NgtoSL2, SL2toG, Nh, WNh, NhtoSL2, SL2toH := 
         FactorizeSL2xSL2 (G, #F);
      NmrTries +:= 1;
   until flag or NmrTries gt Limit;
   if NmrTries gt Limit then 
      error "MyRecogniseOmegaPlus4: Failed to construct two SL2"; 
   end if;
   NewO4Words := WNg cat WNh;

   // map SL2 generators in G to SL(2, q)
   SL2gGens := [NgtoSL2 (t): t in UserGenerators (Ng)];
   SL2hGens := [NhtoSL2 (t): t in UserGenerators (Nh)];

   K := OmegaPlus (4, q);

   repeat 
      flag, K1, _, _, SL2toK1, K2, _, _, SL2toK2 := FactorizeSL2xSL2 (K, #F);
   until flag;

   // map SL2g into K1 < K and SL2h into K2 < K
   SL2gGensInK := [SL2toK1 (t): t in SL2gGens];
   SL2hGensInK := [SL2toK2 (t): t in SL2hGens];

   // generators of H are now in 1-1 correspondance with new generators of G
   gens := SL2gGensInK cat SL2hGensInK;
   H := sub<GL(4, q) | gens>;
   i := 1;
   repeat
      flag, E, W := ClassicalConstructiveRecognitionNatural (H);
      i +:= 1;
   until flag or i eq Limit;
   if not flag then error "MyRecogniseOmegaPlus4: Failure"; end if;

   // make sure W and NewO4Words are on same word group 
   if Ngens (H) ne #gens then 
      pos := [Index (gens, H.i): i in [1..Ngens (H)]];
      assert not (0 in pos);
      WW := SLPGroup (#gens);
      phi := hom<Universe (W)-> WW | [WW.i : i in pos]>;
      W := phi (W);
   end if;

   W := Evaluate (W, NewO4Words);
   E := Evaluate (W, [G.i: i in [1..Ngens (G)]]);

   // ensure that entries in the two diagonal standard generators 
   // are powers of the same primitive element: namely  
   // delta = diag (w, w^-1, w^-1, w) and delta' = diag (w, w^-1, w, w^-1)
   if Type (G) eq GrpMat then 
      E, W := MakeConjugate (E, W, F);
   end if;

   // ADDITION TO TAKE SECTION 
   H := original_H;
   small_E := E;
   if Degree (G) lt Degree (H) then
      E := Evaluate (W, original_gens);
   end if;

   G := H;

   if StandardOnly then return E, W; end if;

   WG, delta := WordGroup (G);
   W := Evaluate (W, [WG.i: i in [1..Ngens (WG)]]);

   S := ClassicalStandardGenerators ("Omega+", 4, q);
   S := sub<Universe (S) | S>;
   CB := TransformForm (S);
   K := OmegaPlus (4, q);
   phi := hom <Generic (H) -> K | x :-> LargeToSmall (G, small_E, q, x, CB, pos:
               type := "Omega+")>;
   tau := hom <Generic (K) -> H | x :-> SmallToLarge (E, x, CB: 
               type := "Omega+")>;
   gamma := hom<Generic (H) -> WG | x :-> LargeToWordGroup (G, small_E, W, q, x, pos:
               type := "Omega+")>;
   delta := hom<WG -> H | x :-> Evaluate (x, [G.i: i in [1..Ngens (G)]])>;
   return true, phi, tau, gamma, delta, E, W;
end function;

// constructively recognise G isomorphic to Omega-(4, F) 
// sometimes we need only standard generators, no maps  
MyRecogniseOmegaMinus4 := function (G, F: StandardOnly := true)

   LargeToSmall := function (G, E, q, g, CB : type := "Omega+")
      f, w := ClassicalRewrite (G, E, type, 4, q, g);
      X := ClassicalStandardGenerators (type, 4, q);
      return Evaluate (w, X)^(CB);
   end function;

   SmallToLarge := function (E, g, CB: type := "Omega+")
      P := Parent (g);
      q := #BaseRing (P);
      X := ClassicalStandardGenerators (type, 4, q);
      f, w := ClassicalRewrite (sub<Universe (X) | X>, X, type, 4, q, g^(CB^-1));
      return Evaluate (w, E);
   end function;

   LargeToWordGroup := function (G, E, W, q, g: type := "Omega+")
      f, w := ClassicalRewrite (G, E, type, 4, q, g);
      return Evaluate (w, W);
   end function;

   q := #F;
   Input_G := G;
   if Type (G) eq GrpMat and IsIrreducible (G) then 
      G := AbsoluteRepresentation (G);
      flag, phi := RecogniseSL2 (G, q^2: Verify := false);
      H := sub<GL(2, q^2) | [Function (phi) (G.i): i in [1..Ngens (G)]]>;
   else 
      // EOB Jan 2015: MyCCR should always return maps to desired copy 
      flag, phi := ClassicalConstructiveRecognition (G, "SL", 2, q^2);
      
      H := sub<GL(2, q^2) | [Function (phi) (G.i): i in [1..Ngens (G)]]>;
/* 
      T := CompositionTree (G);
      f, maps := CompositionTreeSeries (G);
      phi := maps[1];
      D := Codomain (phi);
      if Degree (D) ne 2 then 
         tau := D`MapToSL2; 
         gamma := hom<Generic (G) -> SL(2, q^2) | x :-> tau (phi(x))>;
         H := sub<GL(2, q^2) | [tau ((Function (phi) (G.i))): i in [1..Ngens (G)]]>;
      else 
         H := sub<GL(2, q^2) | [Function (phi) (G.i): i in [1..Ngens (G)]]>;
      end if;
*/
   end if;
   
   m := Ngens (H);

   Gens := [];
   for i in [1..m] do
      t1 := (H.i)[1][1]^q;
      t2 := (H.i)[1][2]^q;
      t3 := (H.i)[2][1]^q;
      t4 := (H.i)[2][2]^q;
      Gens[i] := GL(2, q^2)![t1, t2, t3, t4];
   end for;
   K := sub<GL(2, q^2) | Gens>;
   Gens := [TensorProduct (H.i, K.i): i in [1..m]];
   GG := sub<GL(4, q^2) | Gens>;
   FF := GF(q^2);
   gamma := PrimitiveElement (FF);
   if IsEven (q) then
      cb := GL(4, GF(q^2))![1,0,0,0, 0,gamma,1,0, 0,gamma^q,1,0, 0,0,0,1];
      cb := Transpose(cb);
      cb2 := GL(4, GF(q^2))![1,0,0,0, 0,0,0,1, 0,0,1,0, 0,1,0,0];
   else 
      alpha := gamma^((q + 1) div 2);
      cb := GL(4, q^2)![1,0,0,0, 0,alpha,1,0, 0,-alpha,1,0, 0,0,0,1];
      cb := cb^-1;
      cb2 := GL(4, q^2)![1,0,0,0, 0,0,0,1, 0,0,1,0, 0,1,0,0];
   end if;
   O4 := (GG^cb^-1)^cb2^-1;
   Gens := [GL(4, q)!UserGenerators (O4)[i]: i in [1..m]];
   O4 := sub<GL(4, q) | Gens>;
   f, E, W := ClassicalConstructiveRecognitionNatural (O4);

   E := Evaluate (W, [Input_G.i: i in [1..Ngens (Input_G)]]);

   WG, delta := WordGroup (Input_G);
   W := Evaluate (W, [WG.i: i in [1..Ngens (WG)]]);

   if StandardOnly then return E, W; end if;

   S := ClassicalStandardGenerators ("Omega-", 4, q);
   S := sub<Universe (S) | S >;
   CB := TransformForm (S);
   K := OmegaMinus (4, q);
   phi := hom<Generic (G) -> K | x :-> LargeToSmall (G, E, q, x, CB:
             type := "Omega-")>;
   tau := hom<Generic (K) -> G | x :-> SmallToLarge (E, x, CB: 
             type := "Omega-")>;
   gamma := hom<Generic (G) -> WG | x :-> LargeToWordGroup (G, E, W, q, x:
               type := "Omega-")>;
   delta := hom<WG -> G | x :-> Evaluate (x, [G.i: i in [1..Ngens (G)]])>;
   return true, phi, tau, gamma, delta, E, W;
end function;

// compute standard Omega(3, F) generators in G
MyRecogniseOmega3 := function (G, F: Limit := 5)
   NmrTries := 0;
   repeat
      NmrTries +:= 1;
      flag, a, b, c, d := RecogniseSL2 (G, #F: Verify := false);
   until flag or NmrTries gt Limit;
   if NmrTries gt Limit then error "MyRecogniseOmega3: Failure"; end if;

   Gens := [a (G.i): i in [1..Ngens (G)]];
   H := sub<GL(2, F) | Gens>;
   H := MySymmetricPower (H, 2);
   f, E, W := ClassicalConstructiveRecognitionNatural (H);
   E := Evaluate (W, UserGenerators (G));
   return E, W;
end function;

// recognise Omega(5, F) 
MyRecogniseOmega5 := function (G, F: Final := false, O8Subgroup := false, 
                                     O6 := 0, Limit := 20)
   // assert O8Subgroup eq false;

   // p := Characteristic (F);
   q := #F;

   NmrTries := 0;
   repeat
      NmrTries +:= 1;
      // flag, a, b := RecogniseSpOdd (G, 4, q);
      flag, a, b := ClassicalConstructiveRecognition (G, "Sp", 4, q);
   until flag or NmrTries gt Limit;
   if NmrTries gt Limit then error "MyRecogniseOmega3: Failure"; end if;
   
   // a: G -> Sp(4,q), b: Sp(4,q) -> G
   Gens := [a(G.i): i in [1..Ngens (G)]];
   id := [i: i in [1..#Gens] | Gens[i] eq Gens[i]^0];
   Index := [1..Ngens (G)];
   for i in [1..#id] do Exclude (~Index, id[i]); end for;
   
   H := sub<GL(4, F) | Gens>;
   K := MyExteriorPower (H, 2);
   S := Sections (K);
   T := [t: t in S | Degree (t) eq 5];
   H := T[1];
   if O8Subgroup then
      E, W := SolveOmega6InOmega8 (H, F, "B", O6);
      GoodGens := [G.i: i in Index];
      GoodWords := [WordGroup (G).i: i in Index];
   else
      f, E, W := ClassicalConstructiveRecognitionNatural (H); 
      CB := ClassicalChangeOfBasis (H);
      if Final eq false then 
         plus4gens := ClassicalStandardGenerators ("Omega+", 4, q);
         O4gens := [];
         O4words := [];
         for i in [1..6] do
            O4gens[i] := Generic(H)!(InsertBlock (Id(H), plus4gens[i], 1, 1));
            flag, w := ClassicalRewrite (H, E, "Omega", 5, q, O4gens[i]^CB);
            if not flag then error "MyRecogniseOmega5: Failed rewrite"; end if;
            w := Evaluate (w, W);
            Append (~O4words, w);
         end for;
         W := W cat O4words;
      end if;
      GoodGens := [G.i: i in Index];
      GoodWords := [WordGroup (G).i: i in Index];
   end if;

   E := Evaluate (W, GoodGens);
   W := Evaluate (W, GoodWords);

   return E, W;
end function;

// recognise Omega+^(6, F) 
MyRecogniseOmegaPlus6 := function (G, F: O8Subgroup := false, O6 := 0, 
   StandardOnly := false)

   if Type(F) eq RngIntElt then F := GF(F); end if;
   p := Characteristic (F);
   q := #F;
   type := "D";
   // UG := UserGenerators (G); 
   UG := [G.i: i in [1..Ngens (G)]];

   // construct corresponding SL4 Gens
   if Type (G) eq GrpMat and RecogniseClassical (G) eq true and ClassicalType (G) eq "orthogonalplus" then 
      f, H := RecogniseSmallDegree (G, "SL", 4, q);
      ug := [h where _, h := SmallDegreePreimage (G, UG[i]): i in [1..#UG]];
   else
      if IsOdd(p) then 
         if (Type (G) eq GrpMat and IsIrreducible (G)) or Type (G) eq GrpPerm then 
            E, W := MyRecogniseSL4 (G, F);
         else 
            f, a1, b1, c1, d1, E, W := RecogniseSection (G, "SL", 4, q: MapsOnly := false);
         end if;
      else
         // G`type := "O+";
         // G`natParams := <"O+", 6, q, 2>;
         //_, _, _, _, _, E, W := SXESolveSL4black (G);
         _, _, _, _, _, E, W := ClassicalConstructiveRecognition(G,"SL",4,q);
      end if;
      e := ClassicalStandardGenerators ("SL", 4, #F);

      ug := [];
      for i in [1..#UG] do
         flag, uw := ClassicalRewrite (G, E, "SL", 4, #F, UG[i]);
         if not flag then error "MyRecogniseOmegaPlus6: Failed rewrite"; end if;
         ug[i] := Evaluate (uw, e);
      end for;
   end if;

   // H is image of G as SL(4, q)
   H := sub<GL(4, F) | ug>;
   
   // H := MyExteriorPower (H, 2);
   
   // H -> Omega+(6,q) in natural repn
   MA := MatrixAlgebra (GF(q), 4);
   uh := [ExteriorPower (MA!ug[i], 2): i in [1..#ug]];
   H := sub<GL(6, F) | uh>;
   index := [Position (uh, H.i): i in [1..Ngens (H)]];
  
   WG := WordGroup (G);
   words := [WG.i: i in index];

   if O8Subgroup then
      E, W := SolveOmega6InOmega8 (H, F, type, O6);
   else
      f, E, W := ClassicalConstructiveRecognitionNatural (H);
      W := Evaluate (W, words);
      E := Evaluate (W, UserGenerators (G));
   end if;

   if StandardOnly then return E, W; end if;

   LargeToSmall := function (G, E, q, g, CB : type := "Omega+")
      f, w := ClassicalRewrite (G, E, type, 6, q, g);
      X := ClassicalStandardGenerators (type, 6, q);
      return Evaluate (w, X)^(CB);
   end function;

   SmallToLarge := function (E, g, CB: type := "Omega+")
      P := Parent (g);
      q := #BaseRing (P);
      X := ClassicalStandardGenerators (type, 6, q);
      f, w := ClassicalRewrite (sub<Universe (X) | X>, X, type, 6, q, g^(CB^-1));
      return Evaluate (w, E);
   end function;

   LargeToWordGroup := function (G, E, W, q, g: type := "Omega+")
      f, w := ClassicalRewrite (G, E, type, 6, q, g);
      return Evaluate (w, W);
   end function;

   WG, delta := WordGroup (G);
   W := Evaluate (W, [WG.i: i in [1..Ngens (WG)]]);

   S := ClassicalStandardGenerators ("Omega+", 6, q);
   S := sub<Universe (S) | S>;
   CB := TransformForm (S);
   K := OmegaPlus (6, q);
   phi := hom <Generic (G) -> K | x :-> LargeToSmall (G, E, q, x, CB:
               type := "Omega+")>;
   tau := hom <Generic (K) -> G | x :-> SmallToLarge (E, x, CB:
               type := "Omega+")>;
   gamma := hom<Generic (G) -> WG | x :-> LargeToWordGroup (G, E, W, q, x:
               type := "Omega+")>;
   delta := hom<WG -> G | x :-> Evaluate (x, [G.i: i in [1..Ngens (G)]])>;
   return true, phi, tau, gamma, delta, E, W;

end function;

// Homomorphism from SU4 to O^-6 is via ext square
SU4ToOmegaMinus6 := function (G)
   E := ExteriorSquare (G);
   isit, K := IsOverSmallerField (E);
   if not isit then return false, _; end if;
   C := TransformForm (K);
   if Type (C) eq BoolElt then return false, _; end if;
   H := K^C;
   return true, H;
end function;

// Homomorphism from SU4 to O^-6 is via ext square
SU4ToOmegaMinus6 := function (E)
   isit, K := IsOverSmallerField (E);
   if not isit then return false, _; end if;
   C := TransformForm (K);
   if Type (C) eq BoolElt then return false, _; end if;
   H := K^C;
   return true, H;
end function;

// recognise Omega-^(6, F) 
MyRecogniseOmegaMinus6 := function (G, F: Final := false, O8Subgroup := false, 
                                 Limit := 5, O6 := 0, StandardOnly := false)

   if Type(F) eq RngIntElt then	F := GF(F); end if;
   p := Characteristic(F);
   q := #F;
   type := "2D";
   FF := GF(q^2);
   N := Degree (G);
 
   NmrTries := 0;
   repeat
      NmrTries +:= 1;
      // flag, a, b, c, d := RecogniseSU4 (G, q);
      if (Type (G) eq GrpMat and IsIrreducible (G)) or Type (G) eq GrpPerm then 
         flag, a, b, c, d := RecogniseSU4 (G, q);
      else 
         flag, a, b, c, d := RecogniseSection (G, "SU", 4, q);
      end if;
   until flag or NmrTries gt Limit;
   if NmrTries gt Limit then error "MyRecogniseOmegaMinus6: Failure"; end if;

   ug := [a (G.i): i in [1..Ngens (G)]];
   MA := MatrixAlgebra (FF, 4);
   uh := [ExteriorSquare (MA!u): u in ug];
   H := sub<GL(6, FF) | uh>;
   index := [Position (uh, H.i): i in [1..Ngens (H)]];
   WG := WordGroup (G);
   words := [WG.i: i in index];

   flag, GG := SU4ToOmegaMinus6 (H);
   if flag eq false then error "MyRecogniseOmegaMinus6: Failure"; end if; 
   assert Ngens (GG) eq Ngens (H);

   // H := sub<GL(4, FF) | ug>;
   // H := sub<GL(4, FF) | [a (G.i): i in [1..Ngens (G)]]>;
   // flag, GG := SU4ToOmegaMinus6 (H);

   if not O8Subgroup then
      NmrTries := 0;
      repeat 
         f, E, W := ClassicalConstructiveRecognitionNatural (GG);
         NmrTries +:= 1;
      until f or NmrTries gt Limit;
      if (not assigned W) then GG:Magma;
          error "MyRecogniseOmegaMinus6: Failure"; 
      end if; 
      E := Evaluate (W, UserGenerators (GG));
      if Final eq false then 
         CB := ClassicalChangeOfBasis (GG);
         O6PlusWords := [];
         O6PlusGens := ClassicalStandardGenerators ("Omega+", 6, q);
         for i in [1..6] do
            flag, w := ClassicalRewrite (GG, E, "Omega-", 6, q, O6PlusGens[i]^CB);
            if not flag then error "MyRecogniseOmegaMinus6: Failed rewrite"; end if;
            w := Evaluate (w, W);
            Append (~O6PlusWords, w);
         end for;
         O6PlusGens := Evaluate (O6PlusWords, UserGenerators (G));
         E := Evaluate (W, UserGenerators (G));
         E := E cat O6PlusGens;
         W := W cat O6PlusWords;
      else 
         W := Evaluate (W, words);
         E := Evaluate (W, UserGenerators (G));
      end if;
   else
      E, W := SolveOmega6InOmega8 (GG, F, type, O6);
   end if;

   if StandardOnly then return E, W; end if;

   LargeToSmall := function (G, E, q, g, CB : type := "Omega-")
      f, w := ClassicalRewrite (G, E, type, 6, q, g);
      X := ClassicalStandardGenerators (type, 4, q);
      return Evaluate (w, X)^(CB);
   end function;

   SmallToLarge := function (E, g, CB: type := "Omega-")
      P := Parent (g);
      q := #BaseRing (P);
      X := ClassicalStandardGenerators (type, 6, q);
      f, w := ClassicalRewrite (sub<Universe (X) | X>, X, type, 6, q, g^(CB^-1));
      return Evaluate (w, E);
   end function;

   LargeToWordGroup := function (G, E, W, q, g: type := "Omega-")
      f, w := ClassicalRewrite (G, E, type, 6, q, g);
      return Evaluate (w, W);
   end function;

   WG, delta := WordGroup (G);
   W := Evaluate (W, [WG.i: i in [1..Ngens (WG)]]);

   S := ClassicalStandardGenerators ("Omega-", 6, q);
   S := sub<Universe (S) | S>;
   CB := TransformForm (S);
   K := OmegaMinus (6, q);
   phi := hom <Generic (G) -> K | x :-> LargeToSmall (G, E, q, x, CB:
               type := "Omega-")>;
   tau := hom <Generic (K) -> G | x :-> SmallToLarge (E, x, CB:
               type := "Omega-")>;
   gamma := hom<Generic (G) -> WG | x :-> LargeToWordGroup (G, E, W, q, x:
               type := "Omega-")>;
   delta := hom<WG -> G | x :-> Evaluate (x, [G.i: i in [1..Ngens (G)]])>;
   return true, phi, tau, gamma, delta, E, W;

end function;

IsOmegaPlus4 := function (G, F: Limit := 10)

   //if q is small then check a few random elt order (and compare with known exponent)
   //this is a quick negative check
 
   q := #F;
   exp := [[ 2, 6 ],[ 3, 12 ],[ 5, 60 ],[ 7, 168 ], [ 11, 660 ],[ 13, 1092 ],[ 17, 2448 ],
          [ 19, 3420 ], [ 23, 6072 ],
          [ 29, 12180 ],[ 31, 14880 ],[ 37, 25308 ],[ 41, 34440 ],[ 43, 39732 ],[ 47, 51888 ],
          [ 53, 74412 ], [ 59, 102660 ],
          [ 61, 113460 ], [ 67, 150348 ], [ 71, 178920 ],[ 73, 194472 ], [ 79, 246480 ], 
          [ 83, 285852 ], [ 89, 352440 ],
          [ 97, 456288 ], [ 4, 30 ], [ 9, 120 ], [ 25, 1560 ], [ 49, 8400 ], [ 121, 80520 ], 
          [ 169, 185640 ], [ 289, 709920 ],
          [ 361, 1238040 ], [ 8, 126 ], [ 27, 1092 ], [ 125, 39060 ], [ 343, 411768 ], [ 81, 9840 ],
          [ 243, 88572 ],
          [ 729, 797160 ], [ 625, 976560 ], [ 16, 510 ], [ 32, 2046 ], [ 64, 8190 ], [ 128, 32766 ], 
          [ 256, 131070 ], [ 512, 524286 ], [ 1024, 2097150 ]  ];

   if #F le 10 then nre := 20; elif #F le 30 then nre := 10; else nre := 5; end if;
   if exists(i){ i : i in [1..#exp] | exp[i][1] eq q} then
      ro := Lcm([Order(Random(G)) : i in [1..nre]]);
      if ro gt exp[i][2] then return false; end if;
   end if; 

   //"passed exp test; although group has order ",#G;
   //"exp is",Exponent(G);
   //"and o+4 has exponent",Exponent(OmegaPlus(4,4));

   if q eq 3 then 
      if Type (G) eq GrpMat then 
         f := RandomSchreierBounded (G, 288);
      else 
         RandomSchreier (G); f := true;
      end if;
      if f and #G eq 288 then return IdentifyGroup (G) eq <288, 860>; end if;
      return false;
   end if;

   if not IsProbablyPerfect (G) then return false; end if;

   small := [];
   small := [4,5,7,8,9]; 
   small := [4,5];
   if #F in small then 
      limit := [3600, 7200, 56448, 254016, 259200];
      pos := Position (small, #F);
      if Type (G) eq GrpMat then 
         // EOB -- if bound is precisely order then test may fail 
         f := RandomSchreierBounded (G, limit[pos] + 1000);
      else
         RandomSchreier (G); f := true;
      end if;
      if f and #G eq limit[pos] then return IsIsomorphic(G, OmegaPlus(4,q)); end if;
      return false;
   end if;

   // discussion with Alastair Litterick: 
   // applies only to irreducible faithful repns of Omega^+(4, q)  
   // if there are even number of even-dimensional factors for 
   // restriction to one of the commuting SL2s, then we have
   // representations of SL(2, q) 

   if Type (G) eq GrpMat and IsIrreducible (G) then 
      NmrTries := 0;
      repeat
         flag, Ng, WNg, NgtoSL2, SL2toG, Nh, WNh, NhtoSL2, SL2toH := 
            FactorizeSL2xSL2 (G, #F);
         NmrTries +:= 1;
      until flag or NmrTries gt Limit;
      if flag then  
         S := Sections (Ng);
         nmr := #[s: s in S | IsEven (Degree (s))]; 
         return nmr gt 0 and IsEven (nmr);
      end if;
   end if;

   NmrTries := 0;
   repeat
      flag, Ng, WNg, NgtoSL2, SL2toG, Nh, WNh, NhtoSL2, SL2toH := FactorizeSL2xSL2 (G, #F: Omega4Test := true);
      NmrTries +:= 1;
   until flag or NmrTries gt Limit;
   if flag then  
      Zg := EstimateCentre (Ng, 2);
      Zh := EstimateCentre (Nh, 2);
      if #Zg gt 1 and #Zh gt 1 then return Zg eq Zh; end if;
      return #Zg eq 1 and #Zh eq 1;
   else 
      vprint ClassicalRecognition: "IsOmegaPlus4: Failed to construct commuting SL2s";
   end if;

   return false;
end function;

/* G is isomorphic to a classical group of degree <= 8; 
   find the images in G of the standard generators for this group; 
   Final: if input group to ClassicalSolve has type "B", then 
   ensure that we return the 5 standard generators */ 

MyClassicalBaseCases := function (G, F, n, type: Final := false)

    vprint ClassicalRecognition: "Input to MyClassicalBaseCases: type, n, q are ", type, n, #F;
   // special handling of SL(2, q); last condition to avoid Omega^-(4, q) 

/* 
   if Type (G) eq GrpMat and (n eq 2 and type in {"A"} and 
      not IsAbsolutelyIrreducible (G) and #F gt 9 )
      // and Isqrt (#F) ne #BaseRing (G)) 
      then  
      f,_,_,_,_, E, W := ClassicalConstructiveRecognition (G, "SL", n, #F);
      return E, W;
   end if;
*/

   if type in {"D", "2D"} and n in {8} and #F eq 3 then
      vprint ClassicalRecognition: "Special code Omega+-8 and q = 3";
      E, W := MyO78q3 (G, type);
      return E, W;
   end if;

   q := type eq "2A" select Isqrt (#F) else #F;

   if type eq "A" then
      if #F eq 3 and n in {5,6} then  
         E, W := MySolveSX63 (G, n, "A");
      elif #F eq 3 and n in {4} then  
         E, W := MySL4q3 (G);
      elif n eq 4 then
         if IsEven (q) then 
            E, W := SXESolveSL4black (G, F);
         else
            if Type (G) eq GrpMat and IsIrreducible (G) eq false then 
              f, a1, b1, c1, d1, E, W := RecogniseSection (G, "SL", 4, q: MapsOnly := false);
            else 
              f := false; 
            end if;
            if not f then 
               E, W := MyRecogniseSL4 (G, F);
            end if;
         end if;
      elif n eq 5 and IsEven (q) then 
         E, W := SXESolveSL5black (G, F);
      elif n in {2, 3} then 
         E, W := MyRecogniseSL2_3 (G, F, n);
         if Type (E) ne SeqEnum then return false, _, _; end if;
      end if;
      return E, W;
   end if;

   if type eq "C" then
      if n eq 2 then
         E, W := MyRecogniseSp2 (G, F);
      elif n eq 4 then 
         if Type (G) eq GrpMat and IsIrreducible (G) eq false then 
            f, a1, b1, c1, d1, E, W := RecogniseSection (G, "Sp", 4, q: MapsOnly := false);
         else 
            f := false; 
         end if;
         if not f then 
            f, E, W := Internal_RecogniseSp4 (G, #F);
         end if;
         if f cmpeq false then return false, _; end if;
         // E, W := MyRecogniseSp4 (G, F);
      elif n eq 6 and #F eq 3 then 
         E, W := MySolveSX63 (G, n, "C");
         f := Type (E) ne BoolElt; 
      elif n eq 6 and IsEven (q) then 
         if Type (G) eq GrpMat and IsIrreducible (G) eq false then 
            f, a1, b1, c1, d1, E, W := RecogniseSection (G, "Sp", 6, q: MapsOnly := false);
         else 
            f := false; 
         end if;
         if not f then 
            f, E, W := Internal_RecogniseSp6 (G, #F);
         end if;
         if f cmpeq false then return false, _; end if;
      end if;
      return E, W;
   end if;

   if type eq "2A" then
      if n eq 2 then
         E, W := MyRecogniseSU2 (G, F);
      elif n eq 3 then
         E, W := MyRecogniseSU3 (G, F);
      elif n eq 4 then
         E, W := MyRecogniseSU4 (G, F);
      elif n in {5, 6} and #F eq 9 then 
         E, W := MySolveSX63 (G, n, "2A");
      elif n in {5, 7} and IsEven (q) then 
         if Type (G) eq GrpMat and IsIrreducible (G) eq false then 
            f, a1, b1, c1, d1, E, W := RecogniseSection (G, "SU", n, q: MapsOnly := false);
         else 
            f := false;
         end if;
         if not f then 
            recFct := n eq 5 select Internal_RecogniseSU5 else Internal_RecogniseSU7;
            f, E, W := recFct (G, q);
         end if;
         if f cmpeq false then return false, _; end if;
      end if;
      return E, W;
   end if;

   if type eq "D" then
      if n eq 4 then
         E, W := MyRecogniseOmegaPlus4 (G, F);
      elif n eq 6 then
         E, W := MyRecogniseOmegaPlus6 (G, F: StandardOnly := true);
      elif n eq 8 then
         // E, W := MyRecogniseOmega8P (G, F, "D");
         f, E, W := Internal_RecogniseOmegaPlus8 (G, #F);
         if f cmpeq false then return false, _; end if;
      end if;
      return E, W;
   end if;

   if type eq "2D" then
      if n eq 4 then
         E, W := MyRecogniseOmegaMinus4 (G, F);
      elif n eq 6 then
        E, W := MyRecogniseOmegaMinus6 (G, F: Final := Final, StandardOnly := true);
     elif n eq 8 then
        // E, W := MyRecogniseOmega8P (G, F, "2D");
        f, E, W := Internal_RecogniseOmegaMinus8 (G, #F);
        if f cmpeq false then return false, _; end if;
     elif n eq 10 and IsEven (q) then
        f, E, W := Internal_RecogniseOmegaMinus10 (G, #F);
        if f cmpeq false then return false, _; end if;
     end if;
     return E, W;
   end if;

   if type eq "B" then
      if n eq 3 then
         E, W := MyRecogniseOmega3 (G, F);
         return E, W;
      elif n eq 5 then
         E, W := MyRecogniseOmega5 (G, F: Final := Final);
         return E, W;
      elif n eq 7 then
         if #F mod 4 eq 3 and not Final then 
            E, W := MyRecogniseOmega8P (G, F, "B");
         else 
            ZG := EstimateCentre (G, 2);
            if #ZG ne 1 then 
               vprint ClassicalRecognition: "Group has non-trivial centre, not Omega"; 
               return false, _;
            end if;
            NmrTries := 0; Limit := 1;
            repeat 
               f, E, W := Internal_RecogniseOmega7 (G, #F);
               NmrTries +:= 1;
            until f or NmrTries gt Limit;
            if f cmpeq false then return false, _; end if;
         end if;
         if Final and #E gt 5 then
            E := [E[i]: i in [1..4]] cat [E[8]];
            W := [W[i]: i in [1..4]] cat [W[8]];
         end if;
         return E, W;
      end if;
   end if;

   error "ClassicalBaseCases: Type incorrect"; 
end function;
