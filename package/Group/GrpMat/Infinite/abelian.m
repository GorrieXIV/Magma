freeze;

import "finn/decomp.m": PrimitiveElementAbelianCR; 
import "present.m": ConstructPresentation;
import "cr.m": MatrixBlocks;
import "general.m": MyCongruenceSubgroup;
import "hirsch.m": IsValidInput;

FPToSLP := function (F)
  S := SLPGroup (Ngens (F));
  gamma := hom<F -> S | [S.i : i in [1..Ngens (S)]]>;
  Rels := Relations (F);
  Rels := [gamma (LHS (r) * RHS (r)^-1): r in Rels];
  return Rels, gamma;
end function;

// G is irreducible abelian matrix group
// return false, P an isomorphic copy as polycyclic group, 
// map phi from G to P, and images of generators of G in P

IrredAbelianGroup := function (G) 
   K := BaseRing (G);
   nu, m := PrimitiveElementAbelianCR (G);
   assert IsIrreducible (m);
   d := Degree (G);
   C := [nu^i: i in [0..d - 1]];
   MA := KMatrixSpace (K, Degree (G), Degree (G));
   ma := [MA!c: c in C];
   V := KMatrixSpaceWithBasis(ma);
   U := UserGenerators (G);
   B := [Coordinates (V, MA!u): u in U];

   // FF := ext <K | m>;
   FF := ext <K | m : DoLinearExtension>;
   // if FF cmpeq Rationals () then FF := RationalsAsNumberField (); end if;
   E := [FF!b: b in B]; 
   F := AbsoluteField (FF);

   // attempt to avoid use of IsIsomorphic 
   TT, eta := sub < F | FF.1>;

   // my original 
   // flag, eta := IsIsomorphic (FF, F);

   E := ChangeUniverse (E, F);
   A, phi := MultiplicativeGroup (E);

   P, delta := GPCGroup (A);
   vprint Infinite: "Multiplicative group is ", P;

   images := [(E[i] @@ phi) @ delta: i in [1..#E]];

   coeffs := [Eltseq (FF!(P.i @@ delta @ phi)): i in [1..Ngens (P)]];
   mats := [GL(d, K) ! &+[coeffs[i][j] * ma[j]: j in [1..#ma]]: i in [1..#coeffs]];

   W := SLPGroup (#E);
   // this is NOT a hom, but it allows us to write elements in terms 
   // of a generating set other than magma's choice of PC generators 
   gamma := hom<P -> W | [<images[i], W.i>: i in [1..#images]]: Check := false>;

   words := [gamma (A.i @ delta): i in [1..Ngens (A)]];

   G`AbelianBasis := <V, words, phi * eta, A, mats, FF>;

   P`UserGenerators := images;
   return false, P, phi * eta^-1, words;
end function;

// identify matrix g with element of field, the codomain of delta 

MatrixToFieldElement := function (G, delta, g)
   V := G`AbelianBasis[1];
   K := BaseRing (G);
   MA := KMatrixSpace (K, Degree (G), Degree (G));
   g := MA!g;
   if not (g in V) then return false, _; end if;
   B := Coordinates (V, g);

   if Type (Rep (B)) eq SeqEnum then B := &cat (B); end if;

   FF := G`AbelianBasis[6];
   F := Codomain (delta);
   return true, F!(FF!B);
end function;

// membership test in irreducible abelian matrix group 

IrredIsIn := function (G, g)
   AB := G`AbelianBasis;
 
   delta := AB[3];
   flag, e := MatrixToFieldElement (G, delta, g);
   if not flag then return false, _; end if;

   A := AB[4];
   F := Codomain (delta);
   value := ShowDL (A, F!e);
   if value cmpeq false then 
      return false, _; 
   else 
      w := Eltseq (value);
      W := WordGroup (A);
      w := &*[W.i^w[i]: i in [1..#w]];
      return true, w;
   end if;
end function;

// w word in isomorphic polycyclic copy of G
// return equivalent word in UserGenerators of G

WordInInputGenerators := function (G, w)
   P := Parent (w);
   gens := UserGenerators (P);
   F := SLPGroup (#gens);
   // this is NOT a hom, but it allows us to write elements in terms 
   // of a generating set other than magma's choice of PC generators 
   tau := hom<P -> F | [<gens[i], F.i>: i in [1..#gens]]: Check := false>;
   w := tau (w);
   W := G`SLPGroup;
   word := Evaluate (w, [W.i: i in [1..Ngens (W)]]);
   return word;
end function;

// compute image of x, an element of G, in its isomorphic polycyclic copy 

ImageOfMatrix := function (G, x)

   AB := G`AbelianBasis;
   S := AB[1]; D := AB[2]; ranks := AB[3]; P := AB[4];

   if IsTrivial (G) then return true, P.0; end if;
   
   blocksizes := [Degree (S[i]): i in [1..#S]];
   blocks := MatrixBlocks (x, G`ChangeOfBasis, blocksizes);
   W := [* *];
   len := 0;
   for i in [1..#blocks] do 
      if IsTrivial (S[i]) then continue; end if;
      len +:= 1;
      flag, w := IrredIsIn (S[i], blocks[i]);
      if not flag then return false, _; end if;
      W[len] := w;
   end for;

   w := Identity (D);
   offset := 0;
   for i in [1..#W] do
      n := ranks[i]; 
      w *:= Evaluate (W[i], [D.j : j in [offset + 1..offset + n]]);
      offset +:= n;
   end for;
   return true, P!w;
end function;

// G completely reducible abelian matrix group 
// return isomorphic polycyclic copy P and maps between G and P 

MyRecogniseAbelian := function (G)
   if IsTrivial (G) then 
      P := CyclicGroup (GrpGPC, 1);
      G`SLPGroup := SLPGroup (#UserGenerators (G));
      G`AbelianBasis := <[], P, [], P>;
      phi := map<Generic (G) -> P | x :-> P.0>;
      tau := map<P -> G`SLPGroup | x :-> G`SLPGroup.0>;
      return P, phi, tau;
   end if;

   S := Sections (G);
   Q := [* *]; images := [* *]; 
   len := 0;
   for i in [1..#S] do
      if IsTrivial (S[i]) then continue; end if;
      // assert IsAbelian (S[i]);
      len +:= 1;
      flag, Q[len] := IrredAbelianGroup (S[i]);
      images[len] := UserGenerators (Q[len]);
   end for;

   D := Q[1]; 
   Im := images;
   for i in [2..#Q] do 
      D, phi := DirectProduct (D, Q[i]); 
      for j in [1..i - 1] do 
         Im[j] := [phi[1](e): e in Im[j]];
      end for;
      Im[i] := [phi[2](e): e in Im[i]];
   end for;
   images := [x : x in Im];
   gens := [&*[images[i][j]: i in [1..#images]]: j in [1..#images[1]]];

   ranks := [NPCgens (q): q in Q];
   P := sub<D | gens>;
   P`UserGenerators := gens;

   G`SLPGroup := SLPGroup (#UserGenerators (G));
   // words := [WordInInputGenerators (G, P.i) : i in [1..Ngens (P)]];
   G`AbelianBasis := <S, D, ranks, P>;
   phi := map<Generic (G) -> P | x :-> w where _, w := ImageOfMatrix (G, x)>;
   tau := map<P -> G`SLPGroup | x :-> WordInInputGenerators (G, x)>;
   return P, phi, tau;
end function;

intrinsic RecogniseAbelian (G:: GrpMat) -> GrpGPC, Map, Map
{G is completely reducible abelian matrix group defined over number field; 
 return isomorphic polycyclic copy P, a map from G to P, and map from P to G}
   require IsValidInput (G):
      "Input must be defined over rationals or number field";
   require IsAbelian (G): "Input must be abelian";
   require IsCompletelyReducible (G): "Input must be completely reducible";
   P, phi, tau := MyRecogniseAbelian (G);
   delta := map<P -> Generic (G) | x :-> Evaluate (tau (x), UserGenerators (G))>;
   return P, phi, delta;
end intrinsic;

// G completely reducible abelian group recognised
// is x in G? if so, return true and word in UserGenerators (G), else false

IsElementOf := function (G, x)
   if IsIdentity (x) then return true, G`SLPGroup.0; end if;
   f, w := ImageOfMatrix (G, x);
   if f eq false then return false, _; end if;
   return true, WordInInputGenerators (G, w);
end function;

// construct presentation on input generators for G
// phi and tau are maps to and from polycyclic isomorphic copy of G 

PresentationOnInputGenerators := function (G, phi, tau)
   if IsTrivial (G) then return []; end if;

   P := Domain (tau);
   F, delta := FPGroup (P);
   assert forall{i: i in [1..Ngens (P)] | delta (F.i) eq P.i};
   Rels, gamma := FPToSLP (F);
   A := [Function (tau) (P.i): i in [1..NPCgens (P)]];

   // write relations on nice generators in terms of input gens 
   Rels := #A eq 0 select [] else Evaluate (Rels, A);

   U := UserGenerators (G);
   assert Set (Evaluate (Rels, U)) subset {Id (G)};

   W := Codomain (tau);

   // write input gens in terms of nice gens and rewrite
   // again to express them in terms of input gens only 
   B := [(phi (u)) @@ delta @ gamma: u in U];
   C := Evaluate (B, A);

   U := Universe (C);
   eta := hom <U -> W | [W.i: i in [1..Ngens (W)]]>;
   T := [W.i^-1 * eta (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;

   W := G`SLPGroup;
   Rels := Evaluate (Rels, [W.i : i in [1..Ngens (W)]]);
   return Rels;
end function;

// G is abelian-by-finite group 
// if it is AF, then we know its abelian congruence subgroup
// construct presentation for G on its user generators 
// return F, R, P where F is SLP group, R = relations as SLPs in F,
// P is isomorphic copy of the abelian congruence subgroup

PresentationForAFGroup := function (G)
   if IsTrivial (G) then 
      return SLPGroup (0), [], CyclicGroup (GrpGPC, 1); 
   end if;

   // G may be finite 
   if IsFinite (G) then
      U := UserGenerators (G);
      f, H, phi:= IsomorphicCopy (G);
      images := [phi (u): u in U];
      gens, rels := ConstructPresentation (G, H, images);
      return Universe (rels), rels,  CyclicGroup (GrpGPC, 1); 
   end if;

   // or G may be infinite abelian 
   if IsAbelian (G) then 
      P, phi, tau := MyRecogniseAbelian (G);
      Rels := PresentationOnInputGenerators (G, phi, tau);
      return Universe (Rels), Rels, P;
   end if;

   // G is infinite abelian-by-finite 
   K := MyCongruenceSubgroup (G);
   P, phi, tau := MyRecogniseAbelian (K);

   /* defining generators of kernel K expressed as words in 
      generators of G */
   words := K`UserWords[2];
   F := Universe (words);
   id := Identity (F);

   /* conjugates of kernel generators expressed as words in 
      generators of K */
   conjugates := [];
   F := Universe (words);
   UG := UserGenerators (G);
   UG := [G.i: i in [1..Ngens (G)]];
   UK := UserGenerators (K);
   for i in [1..#UG] do 
      for j in [1..#UK] do 
         z := UK[j]^UG[i];
         flag, w := IsElementOf (K, z);
         w := Evaluate (w, words);
         reln := words[j]^F.i = w; 
         if LHS (reln) ne RHS (reln) then 
            Append (~conjugates, LHS(reln) * RHS (reln)^-1); 
         end if;
     end for;
   end for;

   /* relations of K */
   RelsK := PresentationOnInputGenerators (K, phi, tau);
   RelsK := Evaluate (RelsK, words);
   // "Number of relations of K is ", #RelsK;

   /* finally relators of I lifted to G, evaluated in K and 
      solved there */

   I, phi, images := CongruenceImage (G);
   Q, R := ConstructPresentation (G, I, images);
   R := Evaluate (R, [F.i: i in [1..Ngens (F)]]);
   E := Evaluate (R, [G.i: i in [1..Ngens (G)]]);

   imagerels := [];
   for i in [1..#E] do 
      // "now process relator ", i;
      flag, w := IsElementOf (K, E[i]);
      if flag eq false then error "Kernel is not normal"; end if;
      w := Evaluate (w, words);
      reln := R[i] = w; 
      if LHS (reln) ne RHS (reln) then 
         Append (~imagerels, LHS(reln) * RHS (reln)^-1); 
      end if;
   end for;

   Rels := conjugates cat RelsK cat imagerels; 

   // rewrite presentation for G on its user generators 
   U := UserGenerators (G);
   S := SLPGroup (#U);
   pos := [Position (U, G.i): i in [1..Ngens (G)]];
   Rels := Evaluate (Rels, [S.i: i in pos]);
   Rels := [x : x in Set (Rels)];

   // user generators for G contain coincidences and possibly also trivial 
   other := [];
   images := [phi (u): u in UserGenerators (G)];
   U := UserGenerators (G);
   for i in [1..#images - 1] do
      if IsIdentity (U[i]) then Append (~other, S.i); end if;
      for j in [i + 1..#images] do
         if images[i] eq images[j] then Append (~other, S.i * S.j^-1); end if;
      end for;
   end for;
   Rels cat:= other;

   return S, Rels, P;
end function;
