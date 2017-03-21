freeze;

import "base.m": IsNewInvolution, IsElementInDerivedGroup;

import "split.m": MyDerivedCentraliser, Step1, MySplitOCentraliser, 
IsOmegaPlus4Centraliser, SplitOPlus8, SubgroupsCommute, 
AreRepresentationsIdentical, SmallestSection, SmallerGeneratingSet,
SmallestFaithful, MyDerivedGroupMC;

import "../../../../recog/magma/centre.m": EstimateCentre;

import "base-omega.m": IsOmegaPlus4, FixGens, MyRecogniseOmegaPlus6, 
MyRecogniseOmegaMinus6, MyRecogniseOmega5;

import "SX63.m": MyO78q3, MyRecogniseOmega73; 

// crude test to decide if G is soluble
IsProbablySoluble := function (G)
    if IsTrivial (G) then return true; end if;
    if IsProbablyPerfect (G) then return false; end if;
    W := WordGroup (G);
    D := G;
    repeat
        // D := DerivedGroupMonteCarlo (D);
        D, W := MyDerivedGroupMC (D, W);
        id := IsTrivial (D);
        if id then return true; end if;
    until IsProbablyPerfect (D);
    return false;
end function;

// G is isomorphic to Omega^+-(8, F) or Omega(7, F)
// construct commuting X := Omega(n - 4, F) and Y := Omega^+(4, F) as subgroups
// and another W := Omega^+(4,F) where
// <X, W> = Omega(5, F) or Omega(6, F) and <W,Y> = Omega^+(6, F)
// now use these to write down standard gens in G

MyRecogniseOmega8P := function (G, F, type: Nmr := 100, Limit := 100, Final := false)
   vprint ClassicalRecognition: "Start Omega7/8 construction";

   // if type in {"B", "D", "2D"} and #F eq 3 then 
   if type in {"D", "2D"} and #F eq 3 then 
      return MyO78q3 (G, type); 
   end if;

   if type eq "B" and #F eq 3 then
      return MyRecogniseOmega73 (G);
   end if;

   p := Characteristic (F);
   q := #F;
   flag := false;
   case type:
      when "D": n := 8; desired := <"A", 3, q>; stringK := "orthogonalplus";
      when "2D": n := 8; desired := <"2A", 3, q>; stringK := "orthogonalminus";
      when "B": n := 7; desired := <"C", 2, q>; stringK := "orthogonalcircle";
      else error "Incorrect type";
   end case;
   stringL := "orthogonalplus"; desiredL := <"A", 3, q>;

   // construct two commuting Omega subgroups, X and Y  
   vprint ClassicalRecognition: "*** First X and Y";
   // if n = 7, ensure that X is PSL(2, q) = Omega (3, q), not SL(2, q)
   NmrTrials := 0;
   repeat 
      NmrTrials +:= 1;
      found, X, Y, WX, WY, G1, G2, typeX, typeY, f, rem, g, C, Cwords := 
          Step1 (G, type, n, q);
   until (found and (n eq 8 or (n eq 7 and #EstimateCentre (X, 2) eq 1))) or NmrTrials gt Limit div 10;
   if NmrTrials gt Limit div 10 then error "MyRecogniseOmega8P: Failed to split this group"; end if;
   vprint ClassicalRecognition: "Now construct W ";

   // Find third Omega subgroup of G which generates desired subgroups 
   // with each of X and Y
   found := false;
   Invs := [Generic(G) | g];

   vprint ClassicalRecognition: "Choose an involution in C whose centraliser contains 2 Omega factors" ;
   nmrg2 := 0; good := false;
   repeat
      vprint ClassicalRecognition: "Search for involution with soluble centraliser ", nmrg2;
      repeat 
         flag, g2, w2 := RandomElementOfOrder (C, 2); 
         found := flag and g2 ne g and not IsCentral (G, g2)
                  and IsNewInvolution (C, Invs, g2)
                  and AreInvolutionsConjugate (G, g, g2);
      until found; 
      // found := flag and IsNewInvolution (C, Invs, g2); 
      if found then 
         Invs[#Invs + 1] := g2; 
         if not IsElementInDerivedGroup (C, g2: NmrTries := 200) then 
            CentC := CentraliserOfInvolution (C, g2);
            good := IsProbablySoluble (CentC); 
         end if;
      end if;
      nmrg2 +:= 1;
   until good or nmrg2 gt Nmr; 
   if not good then error "No soluble cent inv found"; end if;
   
   // if IsElementInDerivedGroup (C, g2) then "RECURSE CALL"; return $$ (G, F, type);  end if;

   w2 := Evaluate (w2, Cwords);
   D2, D2words := MyDerivedCentraliser (G, g2, w2);
 
   trial := 0; good := false;
   repeat 
      trial +:= 1;
      vprint ClassicalRecognition: "\n\n trial is ", trial;
      if type eq "2D" or type eq "B" then 
         // has D2 direct factor O+4? if so, split to obtain two factors
         vprint ClassicalRecognition: "B or 2D split";
         found, Z, W, Zwords, Wwords := MySplitOCentraliser (D2, type, n, q, n - 4: Limit := 3);
      elif type eq "D" and IsOmegaPlus4Centraliser (D2, q) then 
         found, W, Wwords := SplitOPlus8 (G, F, D2, D2words: OneOnly := true);
      else 
         found := false;
      end if;

      // W should not commute with X and Y; 
      // also <X, W> should be "desired" Omega and <W, Y> should be Omega^+6
      found := found and (not SubgroupsCommute (X, W) and not SubgroupsCommute (Y, W));
      vprint ClassicalRecognition: "Subgroups X, W and Y, W don't commute?", found;

      if found then  
         K := sub<Generic (G) | UserGenerators (X) cat UserGenerators (W)>;
         found := AreRepresentationsIdentical (K, n); 
         // "K reps identical ", found;
         if found then 
            S := SmallestSection (K);
            if ((IsEven (n) and Degree (S) eq n - 2) 
               or (IsOdd (n) and Degree (S) eq n - 3)) 
               and RecogniseClassical (S) then 
               found := ClassicalType (S) eq stringK; 
               if found then 
                  vprint ClassicalRecognition: "Natural K found", found;
               end if;
            else 
               // if LieCharacteristic (S) cmpeq p then
               found, result := LieType (S, p);
               if found then 
                  vprint ClassicalRecognition: "LieType result from K is ", result; 
               end if;
               found := found and result eq desired;
            end if;
            if found then
               L := sub<Generic(G) | UserGenerators (W) cat UserGenerators (Y)>;
               found := AreRepresentationsIdentical (L, n);
               // "L reps identical ", found;
               if found then 
                  S := SmallestSection (L);
                  if Degree (S) eq n - 2 and RecogniseClassical (S) then 
                     good := ClassicalType (S) eq stringL;
                     if good then 
                        vprint ClassicalRecognition: "Natural L found", ClassicalType (S); 
                     end if;
                  else 
                     // if LieCharacteristic (S) cmpeq p then
                     found, result := LieType (S, p);
                     if found then 
                        vprint ClassicalRecognition: "Result from L is ", result; 
                     end if;
                     good := found and result eq desiredL;
                     // end if;
                  end if;
               end if;
            end if;
         end if;
      end if;
   until good or trial gt Limit;

   if not good then error "RecogniseO8P failed"; end if;
   vprint ClassicalRecognition: "Now found all subgroups after", trial;

   W, Wwords := SmallerGeneratingSet (W, Wwords, desired);
   Wwords := Evaluate (Wwords, D2words);

   K := sub<Generic(G) | UserGenerators (X) cat UserGenerators (W)>;
   WK := WX cat Wwords; 
   assert Ngens (K) eq #WK;
   L := sub<Generic(G) | UserGenerators (W) cat UserGenerators (Y)>;
   WL := Wwords cat WY; 

   K, WK := FixGens (G, WK);
   assert Ngens (K) eq #WK;
   L, WL := FixGens (G, WL);

   // construct standard gens for K and L; L is always + type
   if Type (K) eq GrpMat then
      flag, KK := SmallestFaithful (K, desired); 
      if not flag then
         error "OmegaP8: SmallestFaithful failed";
      end if;
   else
      KK := K;
   end if;

   vprint ClassicalRecognition: "Deal with K"; 
   if type eq "D" then
      vprint ClassicalRecognition: "Recognise Omega+6";
      E1, W1 := MyRecogniseOmegaPlus6 (KK, F: StandardOnly := true,
                   O8Subgroup := true, O6 := Ngens (X));
   elif type eq "2D" then
      vprint ClassicalRecognition: "Recognise Omega-6";
      E1, W1 := MyRecogniseOmegaMinus6 (KK, F: StandardOnly := true, 
                  O8Subgroup := true, O6 := Ngens (X));
   elif type eq "B" then 
      vprint ClassicalRecognition: "Recognise Omega5";
      E1, W1 := MyRecogniseOmega5 (KK, F: 
                   O8Subgroup := true, O6 := Ngens (X));
   end if;
   W1 := Evaluate (W1, WK);
   vprint ClassicalRecognition: "Evaluate elements back in G";
   E1 := Evaluate (W1, UserGenerators (G));

   if Type (L) eq GrpMat then
      flag, LL := SmallestFaithful (L, <"A", 3, #F>);
      if not flag then
         error "MyRecogniseOmega8P: SmallestFaithful failed";
      end if;
   else
      LL := L;
   end if;

   vprint ClassicalRecognition: "Now deal with L"; 
   E2, W2 := MyRecogniseOmegaPlus6 (LL, F: StandardOnly := true,
                O8Subgroup := true, O6 := Ngens (W));
   W2 := Evaluate (W2, WL);
   E2 := Evaluate (W2, UserGenerators (G));

   if type eq "D" then
      c1 := E1[8]; wc1 := W1[8];
      c2 := E2[4]^E2[8]; wc2 := W2[4]^W2[8];
       c :=  c2 * c1;
      wc := wc2 * wc1;
      E := [E1[i]: i in [1..7]] cat [c];
      W := [W1[i]: i in [1..7]] cat [wc];
   elif type eq "2D" then
      E := [E1[i]: i in [1..3]] cat [E2[4]^E2[8]^-2, E2[8]] cat [E2[i]^E2[8]^-2: i in [1..6]];
      W := [W1[i]: i in [1..3]] cat [W2[4]^W2[8]^-2, W2[8]] cat [W2[i]^W2[8]^-2: i in [1..6]];
   elif type eq "B" then
      E := [E1[i]: i in [1..3]] cat [E2[8]] cat [E2[i]^E2[8]^-2: i in [1..6]];
      W := [W1[i]: i in [1..3]] cat [W2[8]] cat [W2[i]^W2[8]^-2: i in [1..6]];
   end if;
   return E, W;
end function;
