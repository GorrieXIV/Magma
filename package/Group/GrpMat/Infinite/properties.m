freeze;

import "congruence.m": IsValidInput;

/* presentation for G */

MyPresentation := function (G : Verify := false)
   flag, H, tau := IsomorphicCopy (G: Verify := Verify);
   CT := CompositionTree (H);
   Data := G`Congruence;
   if assigned Data`Relations then 
      Rels := Data`Relations; 
   else 
      f, Rels := CompositionTreeVerify (H);
      assert f;
   end if;
   return Rels;
end function;

/* is x in G? */

MyIsIn := function (G, x: Verify := false)
   if (Degree (G) ne Nrows (x)) or (BaseRing (G) cmpne BaseRing (Parent (x))) then
      return false; 
   end if;

   gens := [Generic (G) | G.i: i in [1..Ngens (G)]];
   if x in gens or IsIdentity (x) then return true; end if;

   P := sub<Generic (G) | gens, x>;
   if not IsFinite (P) then return false; end if;

   flag, IP, tau := IsomorphicCopy (P: Verify := Verify); 
   
   H := sub<Generic (G) | [tau (g): g in gens]>;
   return LMGIsIn (H, tau (x));
end function;

/* is H subgroup of G? */

MyIsSubgroup := function (G, H: Verify := false)
   if (Degree (G) ne Degree (H)) or (BaseRing (G) cmpne BaseRing (H)) then
      return false; 
   end if;
   if forall{h: h in Generators (H) | h in Generators (G)} or IsTrivial (H)
      then return true; 
   end if;
   if exists{h: h in Generators (H) | not HasFiniteOrder (h)} then
      return false;
   end if;

   P := sub<Generic (G) | G, H>;
   if IsFinite (P) eq false then return false; end if;

   flag, IP, tau := IsomorphicCopy (P: Verify := Verify);
   I := sub<Generic (IP) | [tau (G.i): i in [1..Ngens (G)]]>;
   return forall{i : i in [1..Ngens (H)] | LMGIsIn (I, tau (H.i))};
end function;

/* is H equal to K? */

MyIsEqual := function (H, K: Verify := false)
   if (Degree (H) ne Degree (K)) or (BaseRing (H) cmpne BaseRing (K)) then
      return false; 
   end if;
   if (IsTrivial (H) and not IsTrivial (K)) or 
      (not IsTrivial (H) and IsTrivial (K)) then 
      return false; 
   end if;
   gensH := [Generic (H) | H.i: i in [1..Ngens (H)]];
   gensK := [Generic (K) | K.i: i in [1..Ngens (K)]];
   if forall{h : h in gensH | h in gensK} and 
      forall{k : k in gensK | k in gensH} then 
      return true; 
   end if;
   return MyIsSubgroup (H, K: Verify := Verify) and MyIsSubgroup (K, H);
end function;

/* Is K a normal subgroup of G? */

MyIsNormal := function (G, K: Verify := false)
   if not MyIsSubgroup (G, K) then return false; end if;
   // if IsTrivial (K) or MyIsEqual (G, K) then return true; end if;
   if IsTrivial (K) then return true; end if;
   flag, H, tau := IsomorphicCopy (G: Verify := Verify);
   CT := CompositionTree (H);
   L := sub<Generic (H) | [tau (K.i): i in [1..Ngens (K)]]>;
   return LMGIsNormal (H, L);
end function;

/* N is a subgroup of H, an isomorphic copy of G;
   construct preimage of N in G */

MyLift := function (G, H, N)
   CT := CompositionTree (H);
   phi, W := CompositionTreeNiceToUser (H);

   tau := G`Congruence`Map;
   images := [tau (G.i): i in [1..Ngens (G)]];
   I := [Position (images, H.i): i in [1..Ngens (H)]];
   assert not (0 in I);
   gens := [G.i : i in I];

   /* evaluate preimages in G of "nice generators" of H */ 
   gens := Evaluate (W, gens);

   /* words in nice generators of H for generators of N */
   words := [w where _, w := CompositionTreeElementToWord (H, N.i): 
                             i in [1..Ngens (N)]];

   /* evaluate preimage in G */
   return sub<Generic (G) | Evaluate (words, gens)>;
end function;

/* normal closure of K in G */

MyNormalClosure := function (G, K: Verify := false)
   if not MyIsSubgroup (G, K) then error "K is not a subgroup of G"; end if;
   flag, H, tau := IsomorphicCopy (G: Verify := Verify);
   L := sub<Generic (H) | [tau (K.i): i in [1..Ngens (K)]]>;
   N := LMGNormalClosure (H, L);
   return MyLift (G, H, N);
end function;

/* index of K in G */

MyIndex := function (G, K: Verify := false)
   if not MyIsSubgroup (G, K) then error "K is not a subgroup of G"; end if;
   flag, H, tau := IsomorphicCopy (G: Verify := Verify);
   L := sub<Generic (H) | [tau (K.i): i in [1..Ngens (K)]]>;
   return LMGIndex (H, L);
end function;

/* derived group of G */

MyDerivedGroup := function (G: Verify := false)
   flag, H := IsomorphicCopy (G: Verify := Verify);
   DH := LMGDerivedGroup (H);
   D := MyLift (G, H, DH);
   D`Order := DH`Order;
   return D;
end function;

/* unipotent radical of G */
MyUnipotentRadical := function (G: Verify := false)
   flag, H := IsomorphicCopy (G: Verify := Verify);
   RH := LMGUnipotentRadical (H);
   R := MyLift (G, H, RH);
   R`Order := LMGOrder (RH);
   return R;
end function;

/* solvalable radical of G */

MySolvableRadical := function (G: Verify := false)
   flag, H := IsomorphicCopy (G: Verify := Verify);
   SH := LMGSolvableRadical (H);
   S := MyLift (G, H, SH);
   S`Order := LMGOrder (SH);
   return S;
end function;

/* Fitting subgroup of G */

MyFittingSubgroup := function (G: Verify := false)
   flag, H := IsomorphicCopy (G: Verify := Verify);
   FH := LMGFittingSubgroup (H);
   F := MyLift (G, H, FH);
   // F`Order := FH`Order;
   F`Order := LMGOrder (FH);
   return F;
end function;

/* centre of G */

MyCentre := function (G: Verify := false)
   flag, H := IsomorphicCopy (G: Verify := Verify);
   ZH := LMGCentre (H);
   Z := MyLift (G, H, ZH);
   Z`Order := LMGOrder (ZH);
   return Z;
end function;

/* Sylow p-subgroup of G */

MySylow := function (G, p: Verify := false)
   flag, H := IsomorphicCopy (G: Verify := Verify);
   SH := LMGSylow (H, p);
   S := MyLift (G, H, LMGSylow (H, p));
   S`Order := LMGOrder (SH);
   return S;
end function;
