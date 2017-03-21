freeze;

import "finite.m": ConstructCT;

/* convert fp-group F to SLPGroup of same rank */

FPToSLP := function (F)
  S := SLPGroup (Ngens (F));
  gamma := hom<F -> S | [S.i : i in [1..Ngens (S)]]>;
  Rels := Relations (F);
  Rels := [gamma (LHS (r) * RHS (r)^-1): r in Rels];
  return Rels, gamma;
end function;

/* construct presentation for soluble group H on input generators 
   from pc-presentation for soluble radical */

SolublePresentation := function (H)
   S, P, tau := LMGSolubleRadical (H);

   soluble := LMGIsSoluble (H);
   if not soluble then error "Input group must be soluble"; end if;

   F, delta := FPGroup (P);
   assert forall{i: i in [1..Ngens (P)] | delta (F.i) eq P.i}; 
   Rels, gamma := FPToSLP (F);
   eta := CompositionTreeNiceToUser (H);
   A := [eta (w) where _, w := CompositionTreeElementToWord (H, P.i @@ tau): 
                            i in [1..NPCgens (P)]];

   // write relations on nice generators in terms of input gens 
   Rels := #A eq 0 select [] else Evaluate (Rels, A);
   assert Set (Evaluate (Rels, [H.i : i in [1..Ngens (H)]])) eq {Id (H)};

   W := Universe (Rels);
   
   // write input gens in terms of nice gens and rewrite
   // again to express them in terms of input gens only 
   B := [(tau (H.i)) @@ delta @ gamma: i in [1..Ngens (H)]];
   C := Evaluate (B, A);
   
   U := Universe (C);
   tau := hom <U -> W | [W.i: i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

/* construct presentation for group H on input generators from 
   presentation on strong generators */

StrongGeneratorsPresentation := function (H)

   BSGS (H);
   F, delta := FPGroupStrong (H);
   Rels, gamma := FPToSLP (F);
   W, eta := WordGroup (H);
   S := StrongGenerators (H);
   A := [s @@ eta: s in S];

   // write relations on strong generators in terms of input gens 
   Rels := #A eq 0 select [] else Evaluate (Rels, A);
   assert Set (Evaluate (Rels, [H.i : i in [1..Ngens (H)]])) eq {Id (H)};

   W := Universe (Rels);
   
   // write input gens in terms of strong gens and rewrite
   // again to express them in terms of input gens only 
   R := SLPGroup (#S);
   B := [(F! Eltseq (WordInStrongGenerators (H, H.i))) @ gamma: 
         i in [1..Ngens (H)]];
   C := Evaluate (B, A);
   
   U := Universe (C);
   tau := hom <U -> W | [W.i: i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

/* construct presentation for H on input generators using composition tree */

CompositionTreePresentation := function (H)

   repeat 
      f, Rels := CompositionTreeVerify (H);
      if not f then
         CleanCompositionTree (H);
         T := CompositionTree (H);
      end if;
      f, Rels := CompositionTreeVerify (H);
   until f;

   assert f;
   _, A := CompositionTreeNiceToUser (H);
   // "# and relator lengths on nice generators", #Rels, [#x: x in Rels];

   // write relations on nice generators in terms of input gens 
   Rels := #A eq 0 select [] else Evaluate (Rels, A);
   assert Set (Evaluate (Rels, [H.i : i in [1..Ngens (H)]])) eq {Id (H)};

   W := Universe (Rels);
   
   // write input gens in terms of nice gens and rewrite
   // again to express them in terms of input gens only 
   B := [x where _, x := CompositionTreeElementToWord (H, H.i): 
           i in [1..Ngens (H)]];
   C := Evaluate (B, A);
   
   U := Universe (C);
   tau := hom <U -> W | [W.i: i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

/* rewrite given presentation Rels for H on its generators to 
   be one on the list <images>; generators of H are subset of images; 
   a generator of G maps to a generator of H, or the identity of H, 
   or images of two generators of G may coincide */
   
RewriteOnImages := function (G, H, images, Rels)
// assert #images eq Ngens (G);
   W := Universe (Rels);
// if Ngens (W) eq Ngens (G) then return Rels; end if;
// if Ngens (W) eq #UserGenerators (G) then return Rels; end if;

   // preimages in G of generators of H 
   I := [Position (images, H.i): i in [1..Ngens (H)]];
   assert not (0 in I);

   U := SLPGroup (#images);

   tau := hom <W -> U | [U.i: i in I]>;
   Rels := Evaluate (Rels, [U.i: i in I]);

   for i in [1..#images] do
      if not (i in I) then 
         assert exists (j) {j: j in [0..Ngens (H)] | H.j eq images[i]};
         Append (~Rels, U.i * U.j^-1);
      end if;
   end for;
   return Rels;
end function;

/* H is congruence image of G; 
   images are images of generators of G in H;
   construct presentation for H on <images>, which contains
   generators of H as subset; 

   Presentation: one of "CT", "PC", "FP"
   CT: presentation for H computed using CompositionTree;
   PC: if H is soluble, presentation from PC-presentation computed
       for soluble radical;
   FP: if #H < Small then return result of FPGroup, if #H < OrderLimit, 
       then return result of FPGroupStrong

   Small: if #G < Small, then compute presentation using FPGroup;
   OrderLimit: if Small < #G < OrderLimit, then compute presentation
               using FPGroupStrong 
     
   Short: if we compute presentation  of length < Short, then return it

   default: choose shortest in length from CT and FP
*/

ConstructPresentation := function (G, H, images: Presentation := "CT", 
   OrderLimit := 10^15, Small := 10^6, Short := 30)

   if not Presentation in {"CT", "PC", "FP"} then
      Presentation := "CT";
   end if;

   o := ConstructCT (H);

   gens := [G.i: i in [1..Ngens (G)]];

   f := func<x, y | #x - #y>;

   if Presentation eq "PC" then
      if LMGIsSoluble (H) then 
         P, PCRels := SolublePresentation (H);
         pclen := &+[#x: x in PCRels];
         vprint Infinite: "Soluble presentation: # of relations and lengths ", 
            #PCRels, pclen, [#x: x in PCRels];
         PCRels := RewriteOnImages (G, H, images, PCRels);
         Sort (~PCRels, f);
         return gens, PCRels;
      else
         Presentation := "CT";
      end if;
   end if;

   if IsTrivial (H) eq false and Presentation eq "CT" then 
      W, CTRels := CompositionTreePresentation (H); 
      Length := &+[#x: x in CTRels];
      vprint Infinite: "CompositionTree: Number of relations and lengths ", 
      #CTRels, Length, [#x: x in CTRels];
   else
      Length := 10^10;
   end if;

   // can we use magma to compute fp-group directly?
   // if so, always accept this presentation 
   if IsTrivial (H) or 
      // (Length gt Short and (Presentation eq "FP" or o lt Small)) then
      ((Presentation eq "FP" or o lt Small)) then
      vprint Infinite: "Use Magma to construct new presentation ... ";
      RandomSchreier (H);
      F, tau := FPGroup (H);
      assert forall{i: i in [1..Ngens (H)] | tau (F.i) eq H.i}; 
      FPRels := FPToSLP (F);
      new := &+[#x : x in FPRels];
      // if new lt Length then 
         vprint Infinite: "Use FPGroup: Number of relations and lengths to evaluate", 
              #FPRels, new, [#x : x in FPRels];
         FPRels := RewriteOnImages (G, H, images, FPRels);
         Sort (~FPRels, f);
         return gens, FPRels;
      // end if;
   end if;

   // bound for RandomSchreierBounded 
   OrbitLimit := 10^11;
   if IsTrivial (H) or (Length gt Short and o lt OrderLimit) then 
      complete := RandomSchreierBounded (H, OrbitLimit);
      vprint Infinite: "Completed RS?", complete;
      if complete then 
         W, StrongRels := StrongGeneratorsPresentation (H);
         new := &+[#x : x in StrongRels];
         // if new lt Length then 
            vprint Infinite: "Use StrongGeneratorsPresentation: Number of relations and lengths to evaluate", 
              #StrongRels, new, [#x : x in StrongRels];
            StrongRels := RewriteOnImages (G, H, images, StrongRels);
            Sort (~StrongRels, f);
            return gens, StrongRels;
         // end if;
      end if;
   end if;

   Sort (~CTRels, f);
   CTRels := RewriteOnImages (G, H, images, CTRels);
   return gens, CTRels;
end function;
