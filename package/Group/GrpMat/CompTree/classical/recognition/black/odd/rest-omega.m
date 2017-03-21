freeze;

import "split.m": SubgroupsCommute, RankToDegree, MakeSmaller, MyDerivedCentraliser,
GlueCentraliser, SmallestFaithful;

import "base-omega.m": FixGens, MyRecogniseOmegaPlus6, MyRecogniseOmegaMinus6, 
MyRecogniseOmega5;

import "base.m": IsNewInvolution;

// construct SL(2, q) < G as normal closure of an element of order 3
ConstructSL2qSubgroup := function (G, F: Limit := 100)
   Nmr := 0; Ntries := 5;
   q := #F; 

   p := Characteristic (F);
   found := false;
   repeat
      repeat
         flag, g, wg := RandomElementOfOrder (G, 3);
      until flag;
      Xg := sub<Generic (G) | g>;
      WXg := [wg];
      Ng, WNg:= NormalClosureMonteCarlo (G, Xg: slpsH := WXg, SubgroupChainLength := 8);
      flag := q gt 3 select IsProbablyPerfect (Ng) else true;
      if flag then
         if q gt 3 then flag, type := LieType (Ng, p : Perfect := true); end if;
         if (q eq 3) or (flag and type eq <"A", 1, q>) then
            if q eq 3 then
               RandomSchreier (Ng);
               flag:= #Ng in [12, 24];
               if flag then
                  tries := 0;
                  repeat
                     found, alpha, beta := RecogniseSL2 (Ng, q: Verify := false);
                     tries +:=1;
                  until found or tries ge Ntries;
               else
                  found := false;
               end if;
            else
               found, alpha, beta := RecogniseSL2 (Ng, q: Verify := false);
            end if;
         else
            found := false;
         end if;
      end if;
      Nmr +:= 1;
   until found or Nmr gt Limit;

   if Nmr gt Limit then
      error "ConstructSL2qSubgroup: Failure"; 
   end if;
   return Ng, WNg, alpha, beta;
end function;

// construct 2 commuting SL(2, q) subgroups in G = Omega+(4, F)
ConstructSL2qSubgroupsInO4 := function (G, F)

   Ng, WNg, NgtoSL2, SL2toNg := ConstructSL2qSubgroup (G, F);
   repeat
      Nh, WNh, NhtoSL2, SL2toH := ConstructSL2qSubgroup (G, F);
   until SubgroupsCommute (Ng, Nh);
    
   return Ng, WNg, NgtoSL2, SL2toNg, Nh, WNh, NhtoSL2, SL2toH;
end function;
forward ElementsOfCentraliser;
// forward SolveOmega6InOmega8;

CheckMatrixGroupCentraliser := function (D, Range, type, n, F)
   Degrees := [];
   p := Characteristic (F);
   S := Sections (D);
   for i in [1..#S] do
      if Degree (S[i]) eq 1 then continue; end if;
      flag, value := LieType (S[i], p);
      if flag then 
      degree := RankToDegree (value);
      Append (~Degrees, degree);
      if not (degree in Range) and not (n - degree in Range) then
         return false; 
      end if;
      end if;
   end for;
   return true;

/* 
   if type in ["D", "2D", "B"] then
      good := exists (t){t: t in Degrees | n - t eq 4};
      if not good then
         good := exists (t){[x, y]: x in Degrees, y in Degrees | x + y eq n};
      end if;
   else
      good := exists (t){[x, y]: x in Degrees, y in Degrees | x + y eq n};
   end if;
   return good;
*/
end function;

// construct the complement of Subgrp in D
ConstructComplement := function (G, F, D, Dwords, Subgrp: 
      NmrTries := 10, NmrGenerators := 20, Limit := 100)

   count := 0;
   if #F eq 3 then
      NmrGenerators := 7;
   else
      NmrGenerators := 20;
   end if;
   ComplementGenerators := [Generic(D) |];
   ComplementWords := [];
   repeat
      elts, words := ElementsOfCentraliser (D, NmrTries);
      for i in [1..#elts] do
         if SubgroupsCommute (Subgrp, sub<Generic(D) | elts[i]>) then
            if not elts[i] in ComplementGenerators then
               Append (~ComplementGenerators, elts[i]);
               Append (~ComplementWords, words[i]);
            end if;
         end if;
      end for;
      count +:=1;
   until #ComplementGenerators ge NmrGenerators or count eq Limit;

   if count eq Limit then
      error "Failed to construct enough generators for Complement";
   end if;

   Complement := sub<Generic(D) | ComplementGenerators>;
   NC, NCwords := NormalClosureMonteCarlo (D, Complement: 
                  slpsH := ComplementWords, SubgroupChainLength := 16);
   return NC, NCwords;
end function;


// D is derived group of centraliser and so is direct product; 
// using powering, attempt to construct element of a direct factor 
ElementsOfCentraliser := function (D, NmrTries)
   P := RandomProcessWithWords (D);
   centelts := [];
   centwords := [];
   
   repeat
      repeat
         g, wg := Random (P);
         ng := Order (g);
      until (ng gt 2) and (IsOdd (ng));

      fac := Factorisation (ng);
      primes := [fac[i][1]: i in [1..#fac]];
      powers := [fac[i][2]: i in [1..#fac]];

      if #fac eq 1 then
         Append (~centelts, g);
         Append (~centwords, wg);
      else
         for j in [1..#fac] do
            m := ng div (primes[j]^powers[j]);
            Append (~centelts, g^m);
            Append (~centwords, wg^m);
         end for;
      end if;
   until #centelts ge NmrTries;
   
   E := Set (centelts);
   Exclude (~E, Rep (E)^0);
   pos := [Position (centelts, e): e in E];
   E := [centelts[i]:  i in pos];
   Words := [centwords[i] : i in pos];
   return E, Words;
end function;

// Construct SL(2, q) subgroups via normal closures and complements
GenerateSL2s := function (G, F, D, Dwords: type := "D", Limit := 10)

   q := #F;
   X, WX := ConstructSL2qSubgroup (D, F);
   WX := Evaluate (WX, Dwords);
   NmrTries := 0;
   repeat
      NmrTries +:= 1;
      R, Rwords := ConstructComplement (G, F, D, Dwords, X);
      Rwords := Evaluate (Rwords, Dwords);
      // know enough of complement in centraliser to find other SL(2, 3)?
      // 288 * 3456 is size of desired centraliser div 3 
      if type eq "D" then ell := 3456; else ell := 288; end if;
      if q eq 3 then
         RandomSchreier (R);
         flag := #R ge ell;
      else
         flag := true;
       end if;
   until flag or NmrTries gt Limit;
   if NmrTries gt Limit then error "GenerateSL2s: Failure"; end if;

   Y, WY := ConstructSL2qSubgroup (R, F);
   WY := Evaluate (WY, Rwords);
   NmrTries := 0;
   repeat
      NmrTries +:= 1;
      RR, RRwords := ConstructComplement (G, F, R, Rwords, Y); 
      RRwords := Evaluate (RRwords, Rwords);
      if type eq "D" then ell := 288; else ell := 24; end if;
      if q eq 3 then
         RandomSchreier (RR);
         flag := #RR ge ell;
      else
         flag := true;
      end if;
   until flag or NmrTries gt Limit;
   if NmrTries gt Limit then error "GenerateSL2s: Failure 2"; end if;

   Z, WZ := ConstructSL2qSubgroup (RR, F);
   WZ := Evaluate (WZ, RRwords);

   if type eq "B" then
      X, WX := MakeSmaller (X, WX);
      Y, WY := MakeSmaller (Y, WY);
      Z, WZ := MakeSmaller (Z, WZ);
      return X, WX, Y, WY, Z, WZ;
   end if;

   RRR, RRRwords := ConstructComplement (G, F, RR, RRwords, Z); 
   RRRwords := Evaluate (RRRwords, RRwords);
   W := RRR; WW := RRRwords;
   X, WX := MakeSmaller (X, WX);
   Y, WY := MakeSmaller (Y, WY);
   Z, WZ := MakeSmaller (Z, WZ);
   W, WW := MakeSmaller (W, WW);

   return X, WX, Y, WY, Z, WZ, W, WW;
end function;

//Split involution centraliser as O(3,q) x O+(4,q)
SplitOmega7Centraliser := function (G, F, D, Dwords: Limit := 3)

   X, WX, Y, WY, Z, WZ := GenerateSL2s (G, F, D, Dwords: type := "B");
   SL2s := [X, Y, Z]; WSL2s := [WX, WY, WZ];
   i := 1;
   Index := [1, 2, 3];
   foundO3 := false;
   q := #F;

   NmrTries := 0;
   repeat
      NmrTries +:= 1;
      G1 := SL2s[i];
      flag, a, b, c, d := RecogniseSL2 (G1, q);
      // O(3,q) is isomorphic to PSL(2,q), so need to 
      // distinguish it from the SL(2,q) factors of O+(4,q)
      foundO3 := b(-Id(SL(2, q))) eq Id (D); 
      i +:=1;
   until foundO3 or NmrTries gt Limit;
   if NmrTries gt Limit then error "SplitOmega7Centraliser: Failure"; end if;

   i -:= 1;
   Omega3 := SL2s[i]; WOmega3 := WSL2s[i];
   Index := [t: t in Index | t ne i];
   SL1 := SL2s[Index[1]]; WSL1 := WSL2s[Index[1]];
   SL2 := SL2s[Index[2]]; WSL2 := WSL2s[Index[2]];
   
   Omega3, WOmega3 := FixGens (G, WOmega3);
   SL1, WSL1 := FixGens (G, WSL1);
   SL2, WSL2 := FixGens (G, WSL2);
   Omega4 := sub<Generic(G) | SL1, SL2>;
   WOmega4 := WSL1 cat WSL2;
   
   return true, Omega3, WOmega3, Omega4, WOmega4;
end function;

// D is an involution centraliser in O+8; check if D > O+6
CheckOmega8Centraliser := function (D, F, type)

   p := Characteristic(F);
   q := #F;
   good := true;
   S := Sections (D);

   i := 1;
   repeat
      flag, sdegree := LieType (S[i], p);
      if type eq "D" then
         if not flag then sdegree := <"N", 0, 0>; end if;
         if flag and not (sdegree eq <"A", 1, #F>) then
            good := false;
         end if;
      elif type eq "2D" then
         if flag and not (sdegree eq <"A", 1, q^2>) then
            good := false;
         else
            good := true;
         end if;
      elif type eq "B" then
         if flag and not (sdegree eq <"A", 1, q>) then
            good := false;
         else
            good := true;
         end if;
      end if;
      i +:= 1;
   until i gt #S or good eq false;
   
   return good;
end function;

// Split involution centraliser as O+(4,q) x O+(4,q)
SplitOmegaPlus8Centraliser := function (G, F, D, Dwords: 
   SecondInvolution := false, Glueing := false, u := Id(D), v := Id(D))

   p := Characteristic(F);
   q := #F;

   // Construct SL(2, q) subgroups via normal closures and complements
   // "Generate sl2s";
   X, WX, Y, WY, Z, WZ, W, WW := GenerateSL2s (G, F, D, Dwords);

   if SecondInvolution then
      return true, X, WX, Y, WY, W, WW, Z, WZ;
   end if;

   SL2s := [X, Y, W, Z];
   WSL2s :=[WX, WY, WW, WZ];
   G1 := SL2s[1];
	
   if not Glueing then
      // find which SL(2, q)s generate Omega+(4, q)
      if Type (G1) eq GrpMat then 
         Z1 := LMGCentre (G1);
      else 
         RandomSchreier (G1);
         Z1 := Centre (G1);
      end if;
      i := 2;
      repeat
         G2 := SL2s[i];
         if Type (G2) eq GrpMat then 
            Z2 := LMGCentre (G2);
         else 
            RandomSchreier (G2);
            Z2 := Centre (G2);
         end if;
         flag := Z1.1 eq Z2.1;
         i +:= 1; 
      until flag or i eq 5;
      if not flag then return false, _, _, _, _; end if;
	
      WH1 := WSL2s[1] cat WSL2s[i-1];
      Index := [t: t in [2,3,4] | t ne (i - 1)];
      G3 := SL2s[Index[1]];
      G4 := SL2s[Index[2]];

      H2 := sub<Generic(D) | G3, G4>;
      WH2 := WSL2s[Index[1]] cat WSL2s[Index[2]];

      H1, WH1 := FixGens (G, WH1);
      H2, WH2 := FixGens (G, WH2);
      
      return true, H1, WH1, H2, WH2, G1, G2, G3, G4;
   else
      // if q = 1 mod 4 and glueing then we need to construct
      // the Omega+(4, q) containing the glue element
      // the above method will not work if G is POmega+
      U := sub<Generic(D) | u>;
      V := sub<Generic(D) | v>;
      Index := [1, 2, 3, 4];
      Pairs := [[x, y]: x in Index, y in Index | x lt y];
      AllPairs := [[x, y]: x in Pairs, y in Pairs | IsEmpty(Set (x) meet Set (y))];
      i := 1;
      repeat
         H1 := sub<Generic(D) | SL2s[AllPairs[i][1][1]], SL2s[AllPairs[i][1][2]]>;
         H2 := sub<Generic(D) | SL2s[AllPairs[i][2][1]], SL2s[AllPairs[i][2][2]]>;
         i +:= 1;
         flag1 := SubgroupsCommute (H1, U); 
         flag2 := SubgroupsCommute (H2, U);
      until {flag1, flag2} eq {true, false};
      i -:= 1;
      if flag1 eq false then
         A := H1;
         WA := WSL2s[AllPairs[i][1][1]] cat WSL2s[AllPairs[i][1][2]]; 
      else
         A := H2;
         WA := WSL2s[AllPairs[i][2][1]] cat WSL2s[AllPairs[i][2][2]];
      end if;
      return true, A, WA;
   end if;
end function;

// construct centraliser of an Omega+(8,q) involution and 
// check if it contains Omega+(4,q)
ConstructOmega8Centraliser := function (G, F, type, g, wg)
   q := #F;

   assert Ngens (Parent (wg)) eq Ngens (G);

   D, Dwords, C, Cwords := MyDerivedCentraliser (G, g, wg);
   if Type (G) eq GrpMat then
      if type eq "D" then
         flag := CheckOmega8Centraliser(D, F, type);
      else
         if type eq "2D" then 
            n := 8; Range := [4];
         else
            n := 7; Range := [3];
         end if;
         flag := CheckMatrixGroupCentraliser (D, Range, type, n, F);
      end if;
   else
      CompFacs := CompositionFactors (D);
      if type eq "D" then
         flag := (q eq 5 and CompFacs[1] eq <17,5,0>) or 
                 (q gt 5 and CompFacs[1] eq <1,1,q>); 
      elif type eq "2D" then
         flag := (q eq 3 and CompFacs[1] eq <17,6,0>) or
                 (q eq 7 and CompFacs[1] eq <1,1,49>);
      elif type eq "B" then 
         flag := (q eq 3 and CompFacs[1] eq <19,0,3>) or
                 (q eq 7 and CompFacs[1] eq <1,1,7>);
      end if;
   end if;
   return flag, C, Cwords, D, Dwords;
end function;

// X and Y are Omega+4 subgroups
// find which SL2s subgroups generate Omega+6 with X and which with Y
GenerateOmegaPlus6 := function (F, X, WX, Y, WY, SL2s, WSL2s)

   p := Characteristic(F);
   q := #F;
   G1 := SL2s[1];
   i := 2;
   Index := [2, 3, 4];
   repeat
      G2 := SL2s[i];
      Z := sub<Generic(X) | G1, G2>;
      WZ := WSL2s[1] cat WSL2s[i];
      K := sub<Generic(X) | X, Z>;
      WK := WX cat WZ;
      flag, result := LieType (K, p);
      
      if flag and result[1] in ["2A", "B", "C"] then
         flag := false;
         i := 5;
      else
         i +:= 1; 
         if flag then flag := result eq <"A", 3, q>; end if;
      end if;
   until flag or i eq 5;
   
   if not flag then
      return false, _, _, _, _, _, _;
   end if;
   L := sub<Generic(X) | Z, Y>;
   WL := WZ cat WY;
   return true, Z, WZ, K, WK, L, WL;
end function;
 
// Solve Omega 7 or Omega 8 
MyRecogniseOmega7_8 := function (G, F, type: NmrInvolutions := 12, NmrTries := 500)

   p := Characteristic(F);
   q := #F;
   n := type in ["D", "2D"] select 8 else 7;

   FirstInvolutions := [];
   repeat //until flag
      // find an involution whose centraliser contains two copies of Omega+(4,q), 
      // Omega+(4,q) and Omega-(4,q), or Omega+(4,q) and Omega(3,q)
      repeat // until foundXY
         FirstInvolutions := [];
         repeat // until good 
            repeat
               f, g, wg := RandomElementOfOrder (G, 2);
            until not (IsCentral (G, g));
            assert Ngens (Parent (wg)) eq Ngens (G);
            good, C, Cwords, D, Dwords := 
                ConstructOmega8Centraliser (G, F, type, g, wg);
            if q eq 3 then
               RandomSchreier (D);
               if type eq "D" then
                  good := #D in [82944, 41472];
               elif type eq "2D" then
                  good := #D eq 103680;
               else
                  good := #C eq 13824;
               end if;
            end if;
         until good;
         Append (~FirstInvolutions, g);

         if type eq "D" then
            foundXY, X, WX, Y, WY, H1, H2, H3, H4 := 
               SplitOmegaPlus8Centraliser (G, F, D, Dwords);
         elif type eq "B" then
            if q eq 3 then
               foundXY, X, WX, Y, WY := SplitOmega7Centraliser (G, F, C, Cwords);
            else
               foundXY, X, WX, Y, WY := SplitOmega7Centraliser (G, F, D, Dwords);
            end if;
         else
"TYPE ", type, n, q;
            repeat 
              foundXY, X, Y, WX, WY := GlueCentraliser (D, Dwords, type, n, q);
            until foundXY;
/* 
            repeat
               foundXY, X, WX, x, Y, WY, y := 
               SplitClassicalCentraliser (G, F, n, type, C, Cwords, D, Dwords);
            until foundXY;
*/
         end if;
      until foundXY;

      // find 3rd involution and Omega+(4,q) subgroup Z to generate SL(4,q)
      InvolutionsTried := [Generic(G) | g];
      Words := [wg];
      repeat 
         repeat 
            count := 1;
            if (q eq 3) or (Type (G) eq GrpPerm and q ge 3) then
               // EOB perhaps use LMG later 
               if 1 eq 0 and Type (C) eq GrpMat then 
                  o := LMGOrder (C);
                  Cl := LMGClasses (C); 
               else 
                  RandomSchreier (C); if q eq 3 then Verify (C); end if;
     	          Cl := Classes (C);
               end if;
               Cl2 := [t : t in Cl | t[1] eq 2];
               k := Cl2[#Cl2, 3];

               // EOB - strange way to find word for conjugate of k 
               repeat
                  flag, g2, w2 := RandomElementOfOrder (C, 2);
               until AreInvolutionsConjugate (C, g2, k);
               w2 := Evaluate (w2, Cwords);

               good, C2, C2words, D2, D2words := 
	          ConstructOmega8Centraliser (G, F, type, g2, w2);
               if q eq 3 then
                  i := 1;
                  repeat
                     D2, D2words := MyDerivedCentraliser (G, C2, C2words, F);
                     RandomSchreier (D2);
                     if type eq "D" then
                        good := #D2 in [82944, 41472]; 
                     elif type eq "2D" then
                        good := #D2 eq 103680;
                     else 
                        good := #C2 eq 13824;
                     end if;
                     i +:= 1;
                  until good or i eq 100;
               end if;
            elif (Type(G) eq GrpMat) then
               repeat
                  f, g2, w2 := RandomElementOfOrder (C, 2);
                  count +:= 1;
               until IsNewInvolution (C, InvolutionsTried, g2) or count eq NmrTries;
               if not (count eq NmrTries) then
                  Append (~InvolutionsTried, g2);
                  w2 := Evaluate (w2, Cwords);
                  Append (~Words, w2);
                  good, C2, C2words, D2, D2words := 
                    ConstructOmega8Centraliser (G, F, type, g2, w2);
               else
                  good := false;
               end if;
            end if;
         until good or count eq NmrTries;

 
         if not (count eq NmrTries) then
            if type eq "D" then
	       foundZW, G1, WG1, G2, WG2, G3, WG3, G4, WG4 := 
                  SplitOmegaPlus8Centraliser (G, F, D2, D2words: SecondInvolution := true);
               SL2s := [G1, G2, G3, G4];
               WSL2s := [WG1, WG2, WG3, WG4];
               flag, Z, WZ, K, WK, L, WL := GenerateOmegaPlus6 (F, X, WX, Y, WY, SL2s, WSL2s);
	       if flag then Z, WZ := FixGens (G, WZ); end if;
            else 
               if type eq "B" then
                  if q eq 3 then
                     foundZW, W, WW, Z, WZ := SplitOmega7Centraliser (G, F, C2, C2words);
                  else
                     foundZW, W, WW, Z, WZ := SplitOmega7Centraliser (G, F, D2, D2words);
                  end if;
                  if foundZW then Z, WZ := FixGens (G, WZ); end if;
               elif type eq "2D" then
                  attempts := 0;
/* 
                  repeat
                     foundZW, W, WW, w, Z, WZ, z := 
                     SplitClassicalCentraliser (G, F, n, type, C2, C2words, D2, D2words);
                     attempts +:=1;
                  until foundZW or attempts eq 10;
*/
               end if;
               if foundZW then
                  K := sub<Generic(G) | X, Z>;
                  L := sub<Generic(G) | Z, Y>;
               else
                  K := sub<Generic (G) | Id(G)>;
                  L := sub<Generic (G) | Id(G)>;
               end if;
               flagK, resultK := LieType (K, p);
               result1 := type eq "2D" select <"2A", 3, q> else <"C", 2, q>;
               if flagK then 
                  flagL, resultL := LieType (L, p);
               else 
                  flagL := false; 
               end if;
               if not flagK then resultK := <"N", 0, 0>; end if;
               if not flagL then resultL := <"N", 0, 0>; end if;
               flag := (flagK and flagL) and (resultK eq result1) and (resultL eq <"A", 3, q>);
               if flag then
                  WK := WX cat WZ;
                  WL := WZ cat WY;
               end if;
               if (flagK and flagL) and (resultK eq resultL) then
                  count := NmrTries;
               end if;
            end if;
         else
            flag := false;
         end if;
      until flag or #InvolutionsTried ge NmrInvolutions or count eq NmrTries;
   until flag;


   K, WK := FixGens (G, WK);
   L, WL := FixGens (G, WL);
   // construct standard gens for K and L; L is always + type
   Kdim := type eq "B" select 5 else 6;

   if Type (K) eq GrpMat then 
      // flag, KK := SmallestFaithful (K, F, Kdim, type);
      flag, KK := SmallestFaithful (K, <type, 3, #F>);
      if not flag then
         error "AAA Omega7_8: SmallestFaithful failed";
      end if;
   else 
      KK := K;
   end if;

   if type eq "D" then
      E1, W1 := MyRecogniseOmegaPlus6 (KK, F: StandardOnly := true,
                   O8Subgroup := true, O6 := Ngens (X));
   elif type eq "2D" then
      E1, W1 := MyRecogniseOmegaMinus6 (KK, F: StandardOnly := true, 
                    O8Subgroup := true, O6 := Ngens (X));
   else 
      E1, W1 := MyRecogniseOmega5 (KK, F: O8Subgroup := true, O6 := Ngens (X));
   end if;
   W1 := Evaluate (W1, WK);
   E1 := Evaluate (W1, UserGenerators (G));
   
   if Type (L) eq GrpMat then 
      // flag, LL := SmallestFaithful (L, F, 6, "D");
      flag, LL := SmallestFaithful (L, <"D", 3, #F>);
      if not flag then
         error "BBB Omega7_8: SmallestFaithful failed";
      end if;
   else 
      LL := L;
   end if;

   E2, W2 := MyRecogniseOmegaPlus6 (LL, F: StandardOnly := true,
                O8Subgroup := true, O6 := Ngens (Z));
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
   return E, W, X, WX, Y, WY, Z, WZ, E1, E2;
end function;

// Solve Omega6 < Omega8 wrt a certain basis
ComputeStandardOrthogonalForm := function (H, Dim, F, type, cb, Hform)

   q := #F;
   form := [* *];
   CBs := [* *];
   index := 1;
   CB := Identity(H);
   if type eq "D" then
      orthogonaltype := ["orthogonalplus", "orthogonalplus", "orthogonalplus"];
      blocksizes := [2, 2, 2];
   elif type eq "2D" then
      orthogonaltype := ["orthogonalplus", "orthogonalplus", "orthogonalminus"];
      blocksizes := [2, 2, 2];
   else
      orthogonaltype :=  ["orthogonalplus", "orthogonalplus", "orth"];
      blocksizes := [2, 2, 1];
   end if;
   if type eq "B" then t := 2; else t := 3; end if;

   for i in [1..t] do
      form[i] := ExtractBlock (Hform, index, index, blocksizes[i], blocksizes[i]);
      CBs[i] := TransformForm (form[i], orthogonaltype[i]);
      InsertBlock (~CB, CBs[i], index, index);
      index +:= 2;
   end for;
   CB := GL(Dim,q)!(CB^-1);
   
   return CB;
end function;

// H is generated by 2 subgroups X and Z
// If H is +type, we want X acting on the 1st four basis vectors
// Otherwise X should act on the final 3/4 generators
SolveOmega6InOmega8 := function (H, F, type, O6)

   p := Characteristic(F);
   q := #F;
   xgens := [H.i: i in [1..O6]];
   zgens := [H.i: i in [O6 + 1..Ngens (H)]];
   
   if type eq "B" then
      Dim := 5; xdim := 3;
   else
      Dim := 6; xdim := 4;
   end if;
   zdim := 4;
   
   x := sub<Generic(H) | xgens>;
   z := sub<Generic(H) | zgens>;

   V := VectorSpace (F, Dim);
   M := GModule (x);
   SS := IndecomposableSummands (M);
   index := [i: i in [1..#SS] | Dimension(SS[i]) eq xdim];
   S := SS[index];
   cindex := [i: i in [1..#SS] | not (i in index)];
   c1S := SS[cindex[1]];
   c2S := SS[cindex[2]];

   a, phi := sub<M | S>;
   A := phi (Basis (a));
   
   b, phi := sub<M | c1S, c2S>;
   B := phi (Basis (b));

   N := GModule (z);
   TT := IndecomposableSummands (N);
   index := [i: i in [1..#TT] | Dimension(TT[i]) eq 4];
   T := TT[index];
   cindex := [i: i in [1..#TT] | not(i in index)];
   c1T := TT[cindex[1]];
   c2T := type ne "B" select TT[cindex[2]] else c1T;

   c, phi := sub<N | T>;
   C := phi (Basis (c));
   if type ne "B" then
      d, phi := sub<N | c1T, c2T>;
   else
      d, phi := sub<N | c1T>;
   end if;
  
   D := phi (Basis (d));

   xbasis := []; zbasis := [];
   for i in [1..xdim] do
      xbasis[i] := [A[i][j]: j in [1..Dim]];
   end for;

   for i in [1..zdim] do
      zbasis[i] := [C[i][j]: j in [1..Dim]];
   end for;

   cxbasis := []; czbasis := [];
   if type ne "B" then
      for i in [1..2] do
         cxbasis[i] := [B[i][j]: j in [1..Dim]];
         czbasis[i] := [D[i][j]: j in [1..Dim]];
      end for;
   else
      for i in [1..2] do
         cxbasis[i] := [B[i][j]: j in [1..Dim]];
      end for;
      czbasis[1] := [D[1][j]: j in [1..Dim]];
   end if;
  
   Vx := sub<V | [xbasis[i]: i in [1..xdim]]>;
   Vz := sub<V | [zbasis[i]: i in [1..zdim]]>;
   cVx := sub<V | [cxbasis[i]: i in [1..2]]>;
   t := type eq "B" select 1 else 2; 
   cVz := sub<V | [czbasis[i]: i in [1..t]]>;
   
   VxcVz := Vx meet cVz;
   VzcVx := Vz meet cVx;
   Vxz := Vx meet Vz;
   cVx := Complement(Vx, Vxz);
   cVz := Complement(Vz, Vxz);
   
   v1 := Eltseq (Basis (VxcVz)[1]);
   v2 := type ne "B" select Eltseq (Basis (VxcVz)[2]) else [];
   v3 := Eltseq (Basis (Vxz)[1]);
   v4 := Eltseq (Basis (Vxz)[2]);
   v5 := Eltseq (Basis (VzcVx)[1]);
   v6 := Eltseq (Basis (VzcVx)[2]);
   
   if type eq "D" then
      cb := GL(6, F)!(v1 cat v2 cat v3 cat v4 cat v5 cat v6);
   elif type eq "2D" then
      cb := GL(6, F)!(v6 cat v5 cat v4 cat v3 cat v2 cat v1);
   else
      cb := GL(5, F)!(v6 cat v5 cat v4 cat v3 cat v1);
   end if;

   // we now have bases for subgroups preserved by x and by z
   // now do further base change to preserve the correct orthogonal form
   
   flag, otype, Hform := OrthogonalForm (H^cb^-1);
   CB := ComputeStandardOrthogonalForm (H, Dim, F, type, cb, Hform);

   K := (H^cb^-1)^(CB^-1);
   flag, otype, form := OrthogonalForm (K); 

   if type eq "2D" then
      omega := PrimitiveElement (F);
      kform := ExtractBlock (form, 5, 5, 2, 2);
      stform := GL(2, q)![-2, 0, 0, 2 * omega];
"HERE 2";
      cb := TransformForm (stform, "orthogonalminus");
      cb := GL(6, q)!(InsertBlock (Id(K), cb, 5, 5));
      K := K^cb^-1;
   end if;

   if type eq "B" then
      l := form[5][5];
      s := F!(-2^-1);
      x2 := s * l^-1;
      flag, t := IsSquare (x2);
      if flag then
         v1 := [t * v1[i]: i in [1..5]];
         cb := GL(5, F)!(v6 cat v5 cat v4 cat v3 cat v1);
         K := (H^cb^-1)^CB^-1;
      else
         changeform := GL(5, q)!DiagonalMatrix (F, [x2, x2, x2, x2, x2]);
         form := changeform * form;
         KCB := ComputeStandardOrthogonalForm (K, Dim, F, type, Id(K), form);
         K := K^KCB^-1;
      end if;
   end if;

   if type eq "D" then
      index1 := 1;
      index2 := 3;
   else
      index1 := 3;
      index2 := 1;
   end if;

   t := type eq "B" select 3 else 4; 

   // Lift out smaller matrices corresponding to irreducible reps of x and z
   // Compute standard generators for the smaller representations
   // Also compute extra generators of plus type if H is not of plus type

   G1Gens := [GL(xdim, q) |];
   G2Gens := [GL(4, q) |];

   for i in [1..O6] do
      G1Gens[i] := ExtractBlock (K.i, index1, index1, t, t);
   end for;

   for i in [O6 + 1 .. Ngens (K)] do
      G2Gens[#G2Gens + 1] := ExtractBlock (K.i, index2, index2, 4, 4);
   end for;

   G1 := sub<GL(xdim, q) | G1Gens>;
   T := CompositionTree (G1);
   tau := CompositionTreeNiceToUser (G1);
   if type eq "D" then
      O4gens := ClassicalStandardGenerators ("Omega+", xdim, q);
   elif type eq "2D" then
      O4gens := ClassicalStandardGenerators ("Omega-", xdim, q);
   else
      O4gens := ClassicalStandardGenerators ("Omega", xdim, q);
   end if;

   O4words := [];
   for i in [1..#O4gens] do
      flag, O4words[i] := CompositionTreeElementToWord (G1, O4gens[i]);
   end for;
   Omega6words := [tau (O4words[i]): i in [1..#O4words]];
   Omega6gens := Evaluate (Omega6words, [H.i: i in [1..O6]]);

   O4gens := ClassicalStandardGenerators ("Omega+", 4, q);
   G2 := sub<GL(4,q) | G2Gens>;
   T := CompositionTree (G2); 
   tau := CompositionTreeNiceToUser (G2);
   flag, wx := CompositionTreeElementToWord (G2, O4gens[4]);
   wx := tau(wx);
   x := Evaluate (wx, [H.i: i in [O6 + 1..Ngens (H)]]);
   wx := Evaluate (wx, [WordGroup (H).i: i in [O6 + 1..Ngens (H)]]);
   Omega6Words := [Evaluate (Omega6words[i], WordGroup (H)): i in [1..#Omega6words]];
   if type eq "D" then
      z := x * Omega6gens[4];
      wz := wx * Omega6Words[4];
      Omega6gens[8] := z;
      Omega6Words[8] := wz;
      return Omega6gens, Omega6Words;
   elif type eq "2D" then
      return Omega6gens cat [x, x], Omega6Words cat [wx, wx];
   else
      return Omega6gens cat [x], Omega6Words cat [wx];
   end if;
end function;
