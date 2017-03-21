freeze;

import "split.m": Step1, SmallestFaithful, SubgroupsCommute, CommutingElement, MakeSmaller, SmallestSection, KillFactor; 
import "glue.m": ConstructInvolution, SX4ForGlue;
import "main.m": SetupStandardGenerators;
import "base-omega.m":  FixGens, IsOmegaPlus4, MyRecogniseOmega5, MyRecogniseOmegaPlus6; 
import "../../../../recog/magma/node.m": ERROR_RECOGNITION;

import "O7-8.m": PO8p3AtlasToLGOGens, O8p3AtlasToLGOGens, O8m3AtlasToLGOGens, 
            O73AtlasToLGOGens; 

ConstructSL23 := function (G, First: NmrTrials := 10)
   P := RandomProcessWithWords (G);
   trial := 0;
   repeat
      fx, x, wx := CommutingElement (G, P, First);
      fy, y, wy := CommutingElement (G, P, First);
      found := fx and fy and Order ((x, y)) eq 4;
      if found then 
         H := sub<Generic (G) | x, y>;
         if Type (H) eq GrpMat then 
            flag := RandomSchreierBounded (H, 48);
         else
            RandomSchreier (H);
            flag := true;
         end if;
         found := flag and #H in {12,24,48} and 
                  IdentifyGroup (H) in {<24, 3>, <48, 29>, <12,3>};
       end if;
      trial +:= 1;
   until found or trial gt NmrTrials;
   if found then
      return true, H, [wx, wy];
   else
      return false, _, _;
   end if;
end function;

// G is SX(6, 3); construct centraliser of involution C = SX(4, 3) x SL(2, 3)
// construct both factors 
MySplitSX63 := function (G, n, type)

   found := false;
   if n eq 6 then 
      if type eq "2A" then order := 156764160; 
      elif type eq "A" then order := 291133440; 
      else order := 622080; 
      end if;
   else 
      order := type eq "2A" select 580608 else 2 * 134784;
   end if;

   repeat 
      repeat
         flag, g, wg := RandomElementOfOrder (G, 2);
      until flag and IsCentral (G, g) eq false;
      nmr := 0;
      repeat 
         C, Cwords := CentraliserOfInvolution (G, g, wg);
         RandomSchreier (C);
         if n eq 6 then found := #C mod order eq 0 and #C div order le 8; 
         else found := #C eq order; end if;
         nmr +:= 1;
      until found or nmr gt 3;
   until found;
   
   found := false;
   repeat 
      f, Y, WordsY := KillFactor (C, type, n, 3, [n - 2], sub<G|>:
                                  ConstructOnly := true);
   until f and IsProbablyPerfect (Y);

   WordsY := Evaluate (WordsY, Cwords);
   // assert Evaluate (WordsY, UserGenerators (G)) eq [Y.i: i in [1..Ngens (Y)]];
   repeat 
       f, X, WordsX := ConstructSL23 (C, Y);
   until f;
   WordsX := Evaluate (WordsX, Cwords);
   // assert Evaluate (WordsX, [G.i: i in [1..Ngens (G)]]) eq [X.i: i in [1..Ngens (X)]];

   // EOB -- can't do this, may lose centre 
   // S := SmallestSection (Y);
   return true, Y, X, WordsY, WordsX, Y, X;
end function;

// construct standard generators for SU(6,3) and Sp(6, 3) 
// FinalCall: input to ClassicalSolve is this group
// otherwise construct generators used in recursion 

MySolveSX63 := function (G, n, type: FinalCall := false)
   q := 3; 
   if type eq "2A" then F := GF (9); else F := GF (3); end if;

   IsMatrixGroup := Type (G) eq GrpMat;

   f := n eq 6 select 4 else 3;
   rem := 2;
   found, X, Y, WX, WY, G1, G2 := MySplitSX63 (G, n, type);

   if (type eq "2A") and (n eq 5) then
      temp := X; X := Y; Y := temp; 
      temp := WX; WX := WY; WY := temp;
      temp := G1; G1 := G2; G2 := temp;
      f := 2; rem := 3;
   end if;

   if type eq "C" then a_type := "Sp"; qq := 3; 
   elif type eq "A" then a_type := "SL";  qq := 3;
   else a_type := "SU"; qq := 9; end if; 

   flag, E1, W1 := Internal_ClassicalSolve (G1, a_type, f, q);
   flag, E2, W2 := Internal_ClassicalSolve (G2, a_type, rem, q);

   W1 := Evaluate (W1, WX);
   E1 := Evaluate (W1, UserGenerators (G));

   W2 := Evaluate (W2, WY);
   E2 := Evaluate (W2, UserGenerators (G));

   I, wI, Base1, WBase1, Base2, WBase2, u, wu, v, wv :=
     ConstructInvolution (E1, W1, E2, W2, f, F, type);

   if type eq "A" then k := f - 2; else k := (f div 2) - 1; end if;

   Base1 := [E1[1]^(E1[2]^k), E1[3]^(E1[2]^k), E1[4]^(E1[2]^k)];
   WBase1 := [W1[1]^(W1[2]^k), W1[3]^(W1[2]^k), W1[4]^(W1[2]^k)];
   Base2 := [E2[1], E2[3], E2[4]];
   WBase2 := [W2[1], W2[3], W2[4]];

   CI, CIwords := CentraliserOfInvolution (G, I, wI);

   found := false;
   repeat
      // f, Z, WZ := ConstructSX43 (CI);
      f, Z, WZ := KillFactor (CI, type, n, 3, [4], sub<G|>: ConstructOnly := true);
   until f and IsProbablyPerfect (Z);
   WZ := Evaluate (WZ, CIwords);
   // assert Evaluate (WZ, UserGenerators (G)) eq [Z.i: i in [1..Ngens (Z)]];

   Index := [];
   Base12 := Base1 cat Base2;
   Base12 := [Generic (Z)!x : x in Base12];
   WBase12 := WBase1 cat WBase2;
   for i in [1..Ngens (Z)] do
      if not (UserGenerators (Z)[i] in Base12) then
         Append (~Index, i);
      end if;
   end for;
   Z := sub<Generic (G) | [Z.i : i in Index] cat Base12>;
   WZ := [WZ[i] : i in Index] cat WBase12;

   glue, wglue := SX4ForGlue (Z, WZ, F, n, type, FinalCall,
                              IsMatrixGroup, false);

   glue := Evaluate (wglue, UserGenerators (Z));
   wglue := Evaluate (wglue, WZ);
   E, W := SetupStandardGenerators (E1, E2, W1, W2, glue,   
                                    wglue, n, f, q, type, FinalCall);
   return E, W;
end function;

// G is centraliser of involution in OmegaPlus (8, 3); 
// construct O^+(4, 3) as subgroup of G

ConstructOP43 := function (G, First, type: NmrTrials := 10)
   P := RandomProcessWithWords (G);
   trial := 0;
   found := false;
   F := GF (3); 
   repeat
      fx, x, wx := CommutingElement (G, P, First);
      fy, y, wy := CommutingElement (G, P, First);
      if fx and fy and x ne y and x ne Id (G) and y ne Id (G) then 
         H := sub<Generic (G) | x, y>;
         H, W := NormalClosureMonteCarlo (G, H : slpsH := [wx, wy]);
         found := IsOmegaPlus4 (H, F);
      end if;
      trial +:= 1;
    until found or trial gt NmrTrials;
    if trial gt NmrTrials then return false, _, _, _, _, _; end if;

    R := RandomProcessWithWords (H);
    gens := [Generic (G) | ]; words := [];
    repeat 
       g, w := Random (R);
       if not g in gens and g ne Id (H) then 
          Append (~gens, g);
          Append (~words, w);
       end if;
       K := sub<H | gens>;
    until K eq H;
    W := Evaluate (words, W);

    value := <"D", 2, 3>;
    if found then
       return true, K, W, _, value, 4;
    else
       return false, _, _, _, _, _;
    end if;
end function;

// G contains O+(4, 3) \times O+(4,3); construct both 
SplitO4O4P3 := function (G, type)
   repeat 
      f, H, WH, _, value  := ConstructOP43 (G, sub<G|>, type);
   until f;
   repeat 
      f, K, WK := ConstructOP43 (G, H, type);
   until f;
   return true, H, WH, K, WK;
end function;

// GG is Omega+-(8, 3) or Omega(7,3); find standard generators
MyO78q3 := function (GG, type)

   if type in {"D", "2D"} then 
      n := 8; 
      string := type eq "D" select "Omega+" else "Omega-"; 
   else 
      n := 7;  string := "Omega";
   end if;

   perfect := IsProbablyPerfect (GG); 
   if perfect then 
      G := GG;
   else 
      G, WG := DerivedGroupMonteCarlo (GG);
   end if;

   prior := [i : i in [19 .. 1 by -1]];
   for i in [16..18] do prior[i] := 0; end for;
   // EOB added LeafPriorities to avoid recursion
   // T := CompositionTree (G);
if type eq "2D" then 
    T := CompositionTree(G); 
   // if type eq "2D" then 
    // T := CompositionTree(G : Priorities := prior, LeafPriorities := [1,2,3,5,4]);
   else 
     T := CompositionTree(G : Priorities := prior);
    end if;

   // T := CompositionTree (G);
   // A,B,C, D := CompositionTreeSeries (G);
   _, toFactor, _, _, _, _, goldToW := CompositionTreeSeries(G);
   phi := goldToW[#goldToW];
   // phi := D[#D];
   S := Domain (phi);
   if Type (S) ne GrpMat then 
      error "Failure in domain of map for O78q3";
   end if;

   E := ClassicalStandardGenerators (string, n, 3);
   P := sub<GL(n, 3) | E>;
   tr := TransformForm (P);
   tr2 := TransformForm (S);
   tr := tr * tr2^-1;
   W := [Function (phi) (e^tr): e in E];
   N := CompositionTreeNiceGroup (G);
   tau := CompositionTreeNiceToUser (G);
   WN := Domain (tau);
   W := Evaluate (W, [WN.i: i in [1..Ngens (WN)]]);

   S := Evaluate (W, [N.i: i in [1..Ngens (N)]]);
   W := [tau (w): w in W];

   if not perfect then 
      W := Evaluate (W, WG);
   end if;

   return S, W;
end function;

// G is Omega+-(8, 3) or Omega(7,3); find standard generators
MyO78q3 := function (G, type)

   if type in {"D", "2D"} then 
      n := 8; 
      string := type eq "D" select "Omega+" else "Omega-"; 
   else 
      n := 7;  string := "Omega";
   end if;

   try 
      if string eq "Omega+" then
         f, A, AW := StandardGenerators (G, "O8p3");
         if f then
            return PO8p3AtlasToLGOGens (G, A, AW);
         else 
            f, A, AW := StandardGenerators (G, "2O8p3");
            if f then 
               return O8p3AtlasToLGOGens (G, A, AW);
            end if;
         end if;
      elif string eq "Omega-" then 
         f, A, AW := StandardGenerators (G, "O8m3");
         if f then return O8m3AtlasToLGOGens (G, A, AW); end if;
      elif string eq "Omega" then 
         f, A, AW := StandardGenerators (G, "O73");
         if f then return O73AtlasToLGOGens (G, A, AW); end if;
      end if;
      assert f;
   catch err
      error ERROR_RECOGNITION;
   end try;
   return false, _;
end function;

// G has direct factor O+4(3); split to obtain two factors
MySplitO73Centraliser := function (G, type, n, q, dim: Limit := 100)
   F := GF (q); p := Characteristic (F);
   found := false;

   NmrTries := 0;
   repeat 
      f, C, WC := ConstructOP43 (G, sub<G|>, "D"); NmrTries +:= 1;
   until f or NmrTries gt Limit;
   if not f then return false, _, _, _, _; end if;

   First := C;
   P := RandomProcessWithWords (G);
   NmrTries := 0;
   repeat
      NmrTries +:= 1;
      fx, x, wx := CommutingElement (G, P, First);
      fy, y, wy := CommutingElement (G, P, First);
      found := fx and fy; 
      if found then
         A := sub<Generic (G) | x, y>;
         RandomSchreier (A);
         found := #A eq 12 and IdentifyGroup (A) eq <12,3>;
      end if;
   until found or NmrTries gt Limit;
   if not found then return false, _, _, _, _; end if;

   WA := [wx, wy];

   value := <"B", 1, 3>;

   return true, A, C, WA, WC, value, <"D", 2, q>, n - 4, 4;
end function;

MyRecogniseOmega73 := function (G)
   type := "B"; n := 7; q := 3;
   desired := <"C", 2, q>;
   F := GF (q);

   // construct two commuting Omega subgroups, X and Y
   vprint ClassicalRecognition: "*** First X and Y";
   foundsubgrps, X, Y, WX, WY, G1, G2, typeX, typeY, f, rem, g, C, Cwords :=
          Step1 (G, type, n, q);
nmr := 0;
   found := false;
   repeat 
      nmr +:= 1;
      repeat 
         repeat
            flag, g2, w2 := RandomElementOfOrder (C, 2);
         until flag and g ne g2 and not IsCentral (G, g2) 
            and AreInvolutionsConjugate (G, g, g2);
         w2 := Evaluate (w2, Cwords);
         C2, C2words := CentraliserOfInvolution (G, g2, w2);
         f, Z, W, _, Wwords := MySplitO73Centraliser (C2, "B", 7, 3, 3);
      until SubgroupsCommute (X, W) eq false and SubgroupsCommute (Y, W) eq false;
      K := sub<Generic (G) | X, W>; // LMGCompositionFactors (K);
      f, resultK := LieType (K, 3);
      if f and resultK eq <"C", 2, 3> then 
         L := sub<Generic (G) | W, Y>; // LMGCompositionFactors (L);
         found, resultL := LieType (L, 3);
      end if;
   until found and resultL eq <"A", 3, 3>;

   Wwords := Evaluate (Wwords, C2words);

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
         error "Omega73: SmallestFaithful failed";
      end if;
   else
      KK := K;
   end if;

   E1, W1 := MyRecogniseOmega5 (K, F: O8Subgroup := true, O6 := Ngens (X));
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

   E := [E1[i]: i in [1..3]] cat [E2[8]] cat [E2[i]^E2[8]^-2: i in [1..6]];
   W := [W1[i]: i in [1..3]] cat [W2[8]] cat [W2[i]^W2[8]^-2: i in [1..6]];

   return E, W;
end function;
