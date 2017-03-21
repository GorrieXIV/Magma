freeze;

import "split.m": MyDerivedCentraliser, KillFactor, SubgroupsCommute, 
SmallerGeneratingSet, AreRepresentationsIdentical, SmallestSection, Step1,
MatrixBlocks, SmallestFaithful, MyFixProjections; 

// import "../../sp/odd/sp.m": SpProcess;
// import "../../su/odd/su.m": SUProcess;
import "../../../../recog/magma/centre.m":EstimateCentre;
import "../../basics.m": RecognitionError;
import "../../../../recog/magma/node.m": ERROR_RECOGNITION;
import "../../../classical.m": ClassicalConstructiveRecognitionNatural, RecogniseSLWrapper;
import "sl43.m": SL43AtlasToLGOGens, L43AtlasToLGOGens;

MyExteriorPower := function (G, t)
   M := GModule (G);
   N := ExteriorPower (M, t);
   G := ActionGroup (N);
   return G;
end function;

MySymmetricPower := function (G, t)
   M := GModule (G);
   N := SymmetricPower (M, t);
   G := ActionGroup (N);
   return G;
end function;

// do the list of matrices E satisfy standard presentation
// determined by d, q and type?
TestPresentation := function (E, d, q, type)
   if type eq "A" then
      type := "SL";
   elif type eq "2A" then
      type := "SU";
   elif type eq "C" then
      type := "Sp";
   elif type eq "D" then
      type := "Omega+";
   elif type eq "2D" then
      type := "Omega-";
   else
      type := "Omega";
   end if;

   Q, R := ClassicalStandardPresentation (type, d, q);
   Z := Evaluate (R, E);
   return #Set (Z), Z;
end function;

// x1 and x2 are SL(2, q) as subgroups of SL(3, q). 
// Obtain a basis to show action of x1 and x2 on the underlying space 
GetCOB := function (x1, x2, F: first := true)

   V := VectorSpace (F, 3);
   M := GModule (x1);
   S := IndecomposableSummands (M);
   a, phi := sub<M | S[1]>;
   A := phi (Basis (a));

   b, phi := sub<M | S[2]>;
   B := phi (Basis (b));

   /* w1 and <w2, w3> are fixed by x1 */
   w1 := [A[1][1], A[1][2], A[1][3]];
   w2 := [B[1][1], B[1][2], B[1][3]];
   w3 := [B[2][1], B[2][2], B[2][3]];
   U2 := sub<V | w2, w3>;

   N := GModule (x2);
   T := IndecomposableSummands (N);
   c, phi := sub<N | T[1]>;
   C := phi (Basis (c));

   d, phi := sub<N | T[2]>;
   D := phi (Basis (d));

   /* v1 and <v2, v3> are fixed by x2 */
   v1 := [C[1][1], C[1][2], C[1][3]];
   v2 := [D[1][1], D[1][2], D[1][3]];
   v3 := [D[2][1], D[2][2], D[2][3]];

   U2 := sub<V | w2, w3>;
   W2 := sub<V | v2, v3>;
   x := Basis (U2 meet W2); 
   /* x is a basis for the 1dim space U2 meet W2 */
   x := [x[1][1], x[1][2], x[1][3]];

   w := first select v1 cat x cat w1 else w1 cat x cat v1;
   w := GL(3, F)!w;
   cob1 := w^-1;
   return cob1;
end function;

// is g in derived group of G?
IsElementInDerivedGroup := function (G, g: NmrTries := 100)
   K := sub<G | [(G.i, G.j): i in [1..Ngens (G)], j in [1..Ngens (G)]]>;
   O := {};
   for j in [1..NmrTries] do
      k := NormalSubgroupRandomElement (G, K);
      o := Order (g * k);
      Include (~O, o);
      if Gcd (O) eq 1 then return true; end if;
  end for;
  return false;
end function;

// is g conjugate to any of the supplied involutions? if so, return false 
IsNewInvolution := function (C, Involutions, g: NmrTries := 5)
   for t in Involutions do
      if AreInvolutionsConjugate (C, g, t) then return false; end if; 
   end for;
   return true;
end function;

// ext square repn of SL(4, 3)

/* 
SolveSL43Ext := function (G)
   d := 4; q := 3; F := GF(3);
   f, H := RecogniseSmallDegree (G);
   M := GModule (G);
   N := GModule (H);
   N := ExteriorPower (N, 2);
   flag, CB := IsIsomorphic (N, M);
   CB := GL(6,3)!CB;
   
   E := ClassicalStandardGenerators ("SL", d, 3);
   K := sub<GL(4, 3) | E>;
   N := GModule (K);
   N := ExteriorPower (N, 2);
   K := ActionGroup (N);
   E := [CB^-1 * K.i * CB^1: i in [1..#E]];

   prior := [i : i in [19 .. 1 by -1]];
   for i in [16..18] do prior[i] := 0; end for;
   // EOB added LeafPriorities to avoid recursion
   // T := CompositionTree (G);
   //   T := CompositionTree(G : Priorities := prior);
   T := CompositionTree(G : Priorities := prior, LeafPriorities := [1,2,3,4]);

   tau := CompositionTreeNiceToUser (G);
   W:=[w where _, w:=CompositionTreeElementToWord (G, e): e in E];
   W := [tau(w): w in W];
   // assert Evaluate (W, [G.i : i in [1..Ngens (G)]]) eq E;
   return E, W;
end function;
*/

// Solve SL(4, 3) 
MySL4q3 := function (G) 
/* 
   if Degree (G) eq 6 and IsIrreducible (G) then return SolveSL43Ext (G); end if;
   prior := [i : i in [19 .. 1 by -1]];
   for i in [16..18] do prior[i] := 0; end for;

   // EOB added LeafPriorities to avoid recursion
   // T := CompositionTree (G);
//    if Type (G) eq GrpPerm then 
//    T := CompositionTree(G : Priorities := prior, LeafPriorities := [1,5,4,3,2]);
//   else 
   T := CompositionTree(G : Priorities := prior);
//   end if;

//   T := CompositionTree (G: KnownLeaf := true);
// T := CompositionTree (G);

*/
  
  Z, _, flag := EstimateCentre (G, 4);
  
"FLAG ", #Z; 

G:Magma;
  if #Z gt 1 then 
     T := CompositionTree (G: KnownLeaf := true);
  else 
     T := CompositionTree (G);
  end if;
"#T is ", #T;
   _, toFactor, _, _, _, _, goldToW := CompositionTreeSeries (G);

   E := ClassicalStandardGenerators ("SL", 4, 3);

   phi := goldToW[#goldToW];
   S := Domain (phi);

   if Type (S) ne GrpMat or Degree (S) ne 4 then
      try 
         f, tau, gamma := RecogniseSLWrapper (S, 4, 3);
         assert f;
      catch err
         // error "Failure in domain of map for SL43";
         error ERROR_RECOGNITION;
      end try;
      E := [gamma(e): e in E];
   end if;

   W := [phi (e): e in E];
   N := CompositionTreeNiceGroup (G);
   tau := CompositionTreeNiceToUser (G);
   WN := Domain (tau);
   W := Evaluate (W, [WN.i: i in [1..Ngens (WN)]]);
   S := Evaluate (W, [N.i: i in [1..Ngens (N)]]);
   W := [tau (w): w in W];
   return S, W;
end function;

// Solve SL(4, 3) 
MySL4q3 := function (G: Limit := 2) 
   try 
         f, A, AW := StandardGenerators (G, "L43");
         if f then 
            return L43AtlasToLGOGens (G, A, AW);
         else 
            f, A, AW := StandardGenerators (G, "2L43");
            if f then 
               return SL43AtlasToLGOGens (G, A, AW);
             end if;
         end if;
         assert f;
   catch err
      error ERROR_RECOGNITION;
   end try;
   return false, _;
end function;

// Solve SL(d, q) using Kantor-Seress 

OrigMySolveSLRep := function (G, d, q) 
   prior := [i : i in [19 .. 1 by -1]];
   for i in [16..18] do prior[i] := 0; end for;
   Leaf := Type (G) eq GrpPerm;
   T := CompositionTree(G : KnownLeaf := true, Priorities := prior, LeafPriorities := [1,2,3,5,4]);
   _, toFactor, _, _, _, _, goldToW := CompositionTreeSeries (G);

   E := ClassicalStandardGenerators ("SL", d, q);

   phi := goldToW[#goldToW];
   S := Domain (phi);

"XYA";

   if Type (S) ne GrpMat or Degree (S) ne d then
      try 
         f, tau, gamma := RecogniseSLWrapper (S, d, q);
         assert f;
      catch err
         error ERROR_RECOGNITION;
      end try;
      E := [(gamma)(e): e in E];
   end if;

   W := [phi (e): e in E];
   N := CompositionTreeNiceGroup (G);
   tau := CompositionTreeNiceToUser (G);
   WN := Domain (tau);
   W := Evaluate (W, [WN.i: i in [1..Ngens (WN)]]);
   S := Evaluate (W, [N.i: i in [1..Ngens (N)]]);
   W := [tau (w): w in W];
   return S, W;
end function;

// Solve SL(d, q) using Kantor-Seress 
// Expect input defined over fields of size 2 and 3 
MySolveSLRep := function (G, d, q) 
   // "Enter Solve SLRep";
   flag, iso, inv := RecogniseSLWrapper (G, d, q);
   if not flag then return false, false; end if;
   H:=sub<GL(d, q) | [iso(G.i): i in [1..Ngens (G)]]>;
   f, e, w :=ClassicalConstructiveRecognition(H);
   E:=[inv (x): x in e];
   Q,R:=ClassicalStandardPresentation ("SL", d, q);
   // assert Evaluate (w, [G.i: i in [1..Ngens (G)]]) eq E;
   W := WordGroup (G);
   words := Evaluate (w, [W.i: i in [1..Ngens (G)]]);
   return E, words; 
end function;

// G is isomorphic to SL(4, F) 
MyRecogniseSL4 := function (G, F: Limit := 10)
   if #F eq 3 then return MySL4q3 (G); end if;

   type := "A";
   p := Characteristic(F);
   q := #F;
   flag := false;
   n := 4;
   foundsubgrps := false;

   // construct two commuting SL(2, q) 
   foundsubgrps, X, Y, WX, WY, G1, G2, typeX, typeY, f, rem, g, C, Cwords := 
      Step1 (G, "A", 4, q);

   // Find third SL(2, q) to generate SL(3, q) subgroups of G with X and Y
   found := false;
   NmrTries := 0;
   Invs := [Generic(G) | g];
   repeat 
      repeat 
         // "choose another inv in SL4 ";
         getg2 := 0;
         repeat
            flag, g2, w2 := RandomElementOfOrder (C, 2);
            getg2 +:= 1;
         until (flag and IsNewInvolution (C, Invs, g2) and 
                AreInvolutionsConjugate (G, g, g2) and
                not IsElementInDerivedGroup (C, g2)) or getg2 eq Limit;
         if getg2 gt Limit then 
            error "MyRecogniseSL4: Failed to find suitable involution"; 
         end if;
         Invs[#Invs + 1] := g2;
         w2 := Evaluate (w2, Cwords);
         D2, D2words := MyDerivedCentraliser (G, g2, w2);
         found, W, Wwords := KillFactor (D2, type, 4, q, [2], sub<D2 | >);
      until found;

      found := (not SubgroupsCommute (X, W) and not SubgroupsCommute (Y, W));
      if found then  
         W, Wwords := SmallerGeneratingSet (W, Wwords, <"A", 1, q>);
         Wwords := Evaluate (Wwords, D2words);
         // check if K and L each generate SL(3, q)
         K := sub<Generic(G) | UserGenerators (X) cat UserGenerators (W)>;
         found := AreRepresentationsIdentical (K, 4); 
         if found then 
            S := SmallestSection (K);
            if LieCharacteristic (S) cmpeq p then 
               found, result := LieType (S, p);
               found := found and result eq <"A", 2, q>; 
               if found then WK := WX cat Wwords; end if;
            else 
               found := false;
            end if;
            if found then 
               L := sub<Generic(G) | UserGenerators (Y) cat UserGenerators (W)>;
               found := AreRepresentationsIdentical (L, 4);
               if found then  
                  S := SmallestSection (L);
                  if LieCharacteristic (S) cmpeq p then 
                     found, result := LieType (S, p);
                     found := found and result eq <"A", 2, q>; 
                     if found then WL := WY cat Wwords; end if;
                  end if;
               end if;
            end if;
         end if;
      end if;
      NmrTries +:= 1;
   until found or NmrTries gt Limit;

   vprint ClassicalRecognition: "Number of trials to find 3 SL2s in SL4 is ", NmrTries;

   if NmrTries ge Limit then return $$ (G, F); end if;

   K, WK, K1, index, S := MyFixProjections (K, WK, <"A", 2, q>);

   K1 := K; index := 1;
   Ktries := 0; LimitSL3 := 5;
   repeat
      flag, a, b, c, d := RecogniseSL3 (K, F);
      // flag, a, b, c, d := RecogniseSL3 (K1, F);
      Ktries +:=1;
   until flag or Ktries eq LimitSL3;
   if Ktries ge LimitSL3 then return $$ (G, F); end if;

   // images := [MatrixBlocks (K, X.i)[index]: i in [1..Ngens(X)]];
   // x := [Function(a)(images[i]): i in [1..Ngens (X)]];

   images := [X.i: i in [1..Ngens(X)]];
   x := [Function(a)(images[i]): i in [1..Ngens (X)]];

   // images := [MatrixBlocks (K, W.i)[index]: i in [1..Ngens(W)]];
   // w := [Function(a)(images[i]): i in [1..Ngens (W)]];

   images := [W.i: i in [1..Ngens(W)]];
   w := [Function(a)(images[i]): i in [1..Ngens (W)]];

   /* Find a change-of-basis that exhibits elements of x in top left, 
      elements of w in bottom right of SL(3,F) */
   cob1 := GetCOB (x, w, F);
   e := ClassicalStandardGenerators ("SL", 3, #F);
   e := e^cob1^-1;
   e := [Function(b)(t): t in e];
   Words1 := [Function(c)(t): t in e];

   L, WL, L1, index, S := MyFixProjections (L, WL, <"A", 2, q>);
   L1 := L;  index := 1;

   Ltries := 0;
   repeat
      // flag, a, b, c, d := RecogniseSL3 (L1, F);
      flag, a, b, c, d := RecogniseSL3 (L, F);
      Ltries +:=1;
   until flag or Ltries ge LimitSL3;
   if Ltries ge LimitSL3 then return $$ (G, F); end if;

   images := [Y.i: i in [1..Ngens(Y)]];
   y := [Function(a)(images[i]): i in [1..Ngens (Y)]];

   images := [W.i: i in [1..Ngens(W)]];
   w := [Function(a)(images[i]): i in [1..Ngens (W)]];

   cob2 := GetCOB (y, w, F: first := false);
   g3 := GL(3, F)![1,0,0, 0,0,1, 0,-1,0];
   cy2 := g3^cob2^-1;
   cy2 := Function(b)(cy2); 
   Words2 := Function(c)(cy2);
   Words1 := Evaluate (Words1, WK);
   Words2 := Evaluate (Words2, WL);
   Words := [Words1[1], Words2 * Words1[2], Words1[3], Words1[4]];
   // E := Evaluate (Words, UserGenerators (G));
   E := Evaluate (Words, [G.i: i in [1..Ngens (G)]]);
   return E, Words;
end function;

// compute standard Sp(4, q) generators in G
SmallRecogniseSp4 := function (G, F: Limit := 10)
   q := #F;
   NmrTries := 0;
   try 
      repeat
         if IsEven (q) then 
            flag, a, b := RecogniseSp4Even (G, q);
         else 
            flag, a, b := RecogniseSpOdd (G, 4, q); 
         end if;
         NmrTries +:= 1;
      until flag or NmrTries gt Limit;
      assert flag;
   catch err
      error ERROR_RECOGNITION;
   end try;

   if NmrTries gt Limit then error "MyRecogniseSp4: Failure"; end if; 
    
   // a: G -> Sp(4, q), b: Sp(4, q) -> G
   Gens := [a (G.i): i in [1..Ngens (G)]];
   H := sub<GL(4, F) | Gens>;
   Index := [Position (Gens, H.i): i in [1..Ngens (H)]];
   repeat 
      f, E, W := ClassicalConstructiveRecognitionNatural (H);
   until f;
   GoodGens := [G.i: i in Index];
   GoodWords := [WordGroup (G).i: i in Index];
   E := Evaluate (W, GoodGens);
   W := Evaluate (W, GoodWords);
   return true, E, W;
end function;

// compute standard Sp(4, q) generators in G
MyRecogniseSp4 := function (G, F: Limit := 10)
   q := #F;
   NmrTries := 0;
   try 
      repeat
         if #F in {} then 
            flag, E, W := SmallRecogniseSp4 (G, F); 
         else 
            flag, E, W := Internal_RecogniseSp4 (G, q); 
         end if;
         if flag then return E, W; end if;
         NmrTries +:= 1;
      until flag or NmrTries gt Limit;
      assert flag;
   catch err
      error ERROR_RECOGNITION;
   end try;
end function;

/* 
   if NmrTries gt Limit then error "MyRecogniseSp4: Failure"; end if; 
    
   // a: G -> Sp(4, q), b: Sp(4, q) -> G
   Gens := [a (G.i): i in [1..Ngens (G)]];
   H := sub<GL(4, F) | Gens>;
   Index := [Position (Gens, H.i): i in [1..Ngens (H)]];
   repeat 
      f, E, W := ClassicalConstructiveRecognitionNatural (H);
   until f;
   GoodGens := [G.i: i in Index];
   GoodWords := [WordGroup (G).i: i in Index];
   E := Evaluate (W, GoodGens);
   W := Evaluate (W, GoodWords);
   return E, W;
*/

// for n = 2 or 3, compute standard SL(n, F) generators in G 
MyRecogniseSL2_3 := function (G, F, n: Limit := 10)
   try 
      if n eq 2 then 
         nmr := 0;
         repeat 
            nmr +:= 1;
            flag, a, b := RecogniseSL2 (G, #F: Verify := false); 
         until flag or nmr gt Limit;
      elif n eq 3 then  
         flag, a, b, c, d, E, W := RecogniseSL3 (G, #F);
      end if;
      // assert flag;
   catch err
      error ERROR_RECOGNITION;
   end try;

   if not flag then return false, false; end if;
   if assigned E and assigned W then return E, W; end if;

   // a: G -> SL(n,q), b: SL(n,q) -> G
   Gens := [a (G.i): i in [1..Ngens (G)]];
   H := sub<GL(n, F) | Gens>;
   Index := [Position (Gens, H.i): i in [1..Ngens (H)]];

   repeat 
      f, E, W := ClassicalConstructiveRecognitionNatural (H);
   until f;
   GoodGens := [G.i: i in Index];
   WG := WordGroup (G);
   GoodWords := [WG.i: i in Index];
   E := Evaluate (W, GoodGens);
   W := Evaluate (W, GoodWords);
   return E, W;
end function;

// compute standard Sp(2, F) generators in G 
MyRecogniseSp2 := function (G, F)
   try 
      if Degree (G) eq 2 then 
         flag, a, b, c := RecogniseSL2 (G, #F: Verify := false);
      else 
         flag, a, b, c := ClassicalConstructiveRecognition (G, "SL", 2, #F);
      end if;
      assert flag;
   catch err
      error ERROR_RECOGNITION;
   end try;

   Gens := [a (G.i): i in [1..Ngens (G)]];
   H := sub<GL(2, F) | Gens>;
   assert Ngens (H) eq Ngens (G);
   E, W := Internal_SolveSp (H);
   E := b (E);
   W := c (E); 
   return E, W;
end function;

// compute standard SU(2, F) generators in G 
MyRecogniseSU2 := function (G, F: Limit := 5)

   p := Characteristic(F);
   E := GF(p, Degree (F) div 2);
 
   try 
      if Degree (G) eq 2 then 
         flag, a, b, c := RecogniseSL2 (G, #E: Verify := false);
      else 
         flag, a, b, c := ClassicalConstructiveRecognition (G, "SL", 2, #E);
      end if;
      assert flag;
   catch err
      error ERROR_RECOGNITION;
   end try;

 //Hgens := [a (G.i): i in [1..Ngens (G)]];
 //H := sub<GL(2, F) | Hgens>;
 //assert Ngens (H) eq Ngens (G);
 
   Gens := [a (G.i): i in [1..Ngens (G)]];
   H    := sub<GL(2, F) | Gens>;
   Index := [Position (Gens, H.i): i in [1..Ngens (H)]];

   E, W := Internal_SolveSU (H);

   // we handle SU different than Sp: natural copy for SL and Sp is over GF(q) 
   // but SU is over GF(q^2)
   
   E := Evaluate (W, [G.i: i in [1..Ngens (G)]]);
   WG := WordGroup (G);
   GoodGens := [G.i: i in Index];
   GoodWords := [WG.i: i in Index];
   E := Evaluate (W, GoodGens);
   W := Evaluate (W, GoodWords);
   return E, W;
end function;

// compute standard SU(3, F) generators in G 
MyRecogniseSU3 := function (G, F: Limit := 1)
   p := Characteristic(F);
   E := GF(p, Degree (F) div 2);
   q := #E;
   n := 3;
   
   try 
      NmrTries := 0;
      repeat
         NmrTries +:= 1;
         flag, a, b := RecogniseSU3 (G, q); 
      until flag or NmrTries gt Limit;
      assert flag;
   catch err 
      error ERROR_RECOGNITION;
   end try;
   W := G`SU3DataStructure`LGOWords; 
   E := G`SU3DataStructure`LGOGenerators; 
   return E, W;
end function;

// compute standard SU(4, q) gens in G
MyRecogniseSU4 := function (G, F: Limit := 1)
   p := Characteristic (F);
   E := GF(p, Degree (F) div 2);
   q := #E;
   n := 4;

   NmrTries := 0;
   try 
      repeat
         NmrTries +:= 1;
         flag, a, b := RecogniseSU4 (G, q); 
      until flag or NmrTries gt Limit;
      assert flag;
   catch err 
      error ERROR_RECOGNITION;
   end try;

   E := G`SU4DataStructure`Generators; 
   W := G`SU4DataStructure`Words; 
   return E, W;
end function;
