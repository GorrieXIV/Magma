freeze;

import "../../../../recog/magma/centre.m": EstimateCentre;
import "base-omega.m": IsOmegaPlus4;
forward IsOmegaPlus4Centraliser;
forward AreRepresentationsIdentical; 
import "SX63.m": ConstructOP43, SplitO4O4P3, MySplitO73Centraliser;
 
// convert Chevalley type to corresponding one 
ConvertType := function (type, result, q)
    if type eq "2D" and result eq <"A", 1, q^2> then return <"2D", 2, q>;
   elif type eq "2D" and result eq <"2A", 2, q> then return <"2D", 3, q>;
   elif type eq "2D" and result eq <"A", 3, q> then return <"D", 3, q>;
   elif type eq "2D" and result eq <"2A", 3, q> then return <"2D", 3, q>;
   elif type eq "D" and result eq <"A", 3, q> then return <"D", 3, q>;
   elif type eq "D" and result eq <"A", 1, q> then return <"D", 1, q>;
   elif type eq "2A" and result eq <"A", 1, q> then return <"2A", 1, q>;
   elif type eq "B" and result eq <"A", 1, q> then return <"B", 1, q>;
   elif type eq "B" and result eq <"A", 3, q> then return <"D", 3, q>;
   elif type eq "B" and result eq <"C", 2, q> then return <"B", 2, q>;
   elif type eq "C" and result eq <"A", 1, q> then return <"C", 1, q>;
   else return result;
  end if;
end function;

//  Given Chevalley tuple return degree in natural repn 
RankToDegree := function (result)
   type := result[1]; rank := result[2];
   if type in ["A", "2A"] then
      n := rank + 1;
   elif type in ["C", "D", "2D"] then
      n := 2 * rank;
   elif type eq "B" then
      n := 2 * rank + 1;
   end if;
   return n;
end function;

// Given degree in natural repn, return Chevalley rank 
DegreeToRank := function (type, degree) 
   if type in ["A", "2A"] then
      rank := degree - 1;
   elif type in ["B", "C", "D", "2D"] then
      rank := degree div 2;
   end if;
   return rank;
end function;

TensorIndecomposables := function (G)
   if Type (G) eq GrpPerm then return [G]; end if;
   flag := IsTensor (G: Fast := true);
   L := [];
   if flag cmpeq true then
      S := TensorFactors (G);
      if IsTensor (S[1]: Fast := true) cmpeq true then
         L cat:= $$ (S[1]);
      else
         Append (~L, S[1]);
      end if;
      if IsTensor (S[2]: Fast := true) cmpeq true then
         L cat:= $$ (S[2]);
     else 
         Append (~L, S[2]);
      end if;
      return L;
   end if;
   return [G];
end function;

IsGoodCentraliser := function (G, type, n, q, Range)
   if Type (G) eq GrpPerm then return true; end if;

   if type eq "D" and n eq 8 then 
      return IsOmegaPlus4Centraliser (G, q); 
   end if;

   F := GF (q);
   p := Characteristic (F);
   case type:
      when "2D", "B": find_type := "D";
      else find_type := type;
   end case;

   types := {type, find_type};

   if Type (G) eq GrpMat then 
      S := Sections (G); 
      S := &cat[TensorIndecomposables (s): s in S];
      S := [s : s in S | Degree (s) gt 1];
      Dims := [Degree (x): x in S];
      ParallelSort (~Dims, ~S);
   else 
      S := [G]; 
   end if;
   
   i := 0;
   repeat 
      i +:= 1;
      if type eq "C" and Type (S[i]) eq GrpMat and 
         IsTensor (S[i]: Fast := true) cmpeq true then
         continue; 
      end if;
      if Degree (S[i]) le 4 and p le 7 and
         p cmpne LieCharacteristic (S[i]: Verify := false) then continue;
      end if;
      
      flag, result := LieType (S[i], p);
      if not flag then 
         vprint ClassicalRecognition: "Result of LieType is ", flag;
      else 
         vprint ClassicalRecognition: "Result of LieType is ", result;
      end if;

      if flag then
         value := ConvertType (type, result, q);
         if value[1] in types and value[3] eq q then 
            m := RankToDegree (value);
            if value[1] eq type and m gt Maximum (Range) then 
               return false;  
            end if;
            if type in {"2D"} and value[1] in {"D"} then
               return  m eq n - 6;
            elif type in {"B"} and value[1] in {"D"} then
               return (q mod 4 eq 3 and n mod 4 eq 3 and m eq n - 7) or 
                      (m eq n - 5);
            end if;
         elif type in {"D", "2D", "B"} and value[1] eq "A" and value[2] eq 1 
            and q mod value[3] eq 0 then
            continue; 
         else 
            return false; 
         end if;
      end if;
   until i ge #S;

   return true;
end function;

// D is derived group of centraliser of involution in Omega^+(8, q)
// could it be direct product of two Omega^+(4, q)?
IsOmegaPlus4Centraliser := function (D, q)
   F := GF (q);
   p := Characteristic (F);
   S := Type (D) eq GrpMat select Sections (D) else [D]; 
   for i in [1..#S] do 
      H := S[i];
      if Degree (H) eq 1 then continue; end if;
      // if IsProbablyPerfect (H) eq false then return false; end if;
      flag, value := LieType (H, p);
      if flag and value ne <"A", 1, q> then return false; end if;
   end for;
   order := #EstimateCentre (D, 8); 
   return order ge 2;
end function;

// choose smallest section of X having faithful action
SmallestFaithful := function (X, type)
   if Type (X) eq GrpPerm then return true, X, 1, [X]; end if;

   q := type[3];
   F := GF (q);
   p := Characteristic (F);
   S, cob := Sections (X); 
   cob := Generic (X) ! cob;
   Deg := [Degree (s): s in S];
   index := [i: i in [1..#Deg]];
   Sort (~Deg, ~perm);
   index := index^perm;
   for i in index do
      if Degree (S[i]) eq 1 then continue; end if;
      if Degree (S[i]) le 4 and p le 7 and 
         p cmpne LieCharacteristic (S[i]) then continue;
      end if;
      if type[1] eq "Omega+" and type[2] eq 4 then
         flag := IsOmegaPlus4 (S[i], GF(type[3]));
         if flag then return true, S[i], i, S, cob; end if;
      else 
         flag, result := LieType (S[i], p);
         if flag then 
            value := ConvertType (type[1], result, q);
            if value eq type then 
               return true, S[i], i, S, cob;   
            end if;
         end if;
      end if;
   end for;

   /* possible that no section is recognised to be faithful */
   return true, X, 1, [X];
end function;

// return action of matrix g on composition factors of G
MatrixBlocks := function (G, g)

   if Type (G) eq GrpPerm then return [g]; end if;
   CF := G`CompositionFactors;
   COB := G`ChangeOfBasis;
   F := BaseRing (G);
   d := Degree (G);
   e := [* *];
   I := COB * g * COB^-1;
   offset := 0;
   for i in [1..#CF] do
      k := Dimension (CF[i]);
      e[i] := GL (k, F) ! ExtractBlock (I, offset + 1, offset + 1, k, k);
      offset +:= k;
   end for;
   return e;
end function;

TensorDimensions := function (G)
   fac := TensorFactors (G);
   u := Degree (Rep (fac[1]));
   w := Degree (Rep (fac[2]));
   return u, w;
end function;

/* construct projection of h in G to section of G described by S;
   S may be composition factor or decomposed into tensor factor */

ProjectionOfElement := function (G, S, h)

   F := BaseRing (G);
   index := S[2];
   blocks := MatrixBlocks (G, h);
   image := blocks[index];
   if S[4] eq 0 then
      return blocks[index];
   elif S[4] ne 0 then
      istp := IsTensor (S[1]); 
      CB := TensorBasis (S[1]);
      dim1, dim2 := TensorDimensions (S[1]);
      image := image^CB;
      flag, factors := IsProportional (image, dim2);
      if not flag then error "not a tensor product"; end if;
      m := Nrows (factors[S[4]]);
      return GL(m, F)!factors[S[4]], CB;
   end if;
   return false;
end function;

// fast negative test to check if G is a single copy of a group
// of natural dimension at most n, or a direct product of two or more copies 
// must allow for case where one factor is PSX, the other is SX 
AreRepresentationsIdentical := function (G, n: Limit := 20)
   S := Type (G) eq GrpMat select Sections (G) else [G]; 
   if #S eq 1 then return true; end if;
   repeat
      Limit -:= 1;
      g := Random (G);
      B := MatrixBlocks (G, g);
      B := [* b : b in B | Degree (b) gt 1 *];
      O := {Order (b): b in B};
      // if not (Gcd (O) in O) then "A"; return false; end if;
      m := Minimum (O);
      if not IsCentral (G, g^m) then return false; end if;
      // if #{Order (b) : b in B} gt 1 then return false; end if;
   until Limit eq 0;
   return true;
end function;

// Z projects onto G2
// We remove generators of Z that map onto the identity of G2
// ensuring that the generators are in one-to-one correspondance
MyFixProjections := function (Z, WZ, type)
   Index := [];
   G2Gens := [];
   flag, G2, i, S := SmallestFaithful (Z, type);
   if Degree (G2) lt Degree (Z) then
      ZZ := <Z, i, S[i], 0>;
      ZGens := []; ZWords := [];
      for j in [1..Ngens (Z)] do
         zz := ProjectionOfElement (Z, ZZ, Z.j);
         if not (zz in G2Gens) and not (IsIdentity (zz)) then
            Append (~Index, j);
            Append (~G2Gens, zz);
         end if;
      end for;
      for i in Index do
         Append (~ZGens, UserGenerators (Z)[i]);
         Append (~ZWords, WZ[i]);
      end for;
      CF := Z`CompositionFactors;
      COB := Z`ChangeOfBasis;
      Z := sub<Generic (Z) | ZGens>;
      Z`CompositionFactors := CF;
      Z`ChangeOfBasis := COB;
      WZ := ZWords;
      return Z, WZ, G2, i, S;
   else
      return Z, WZ, Z, 1, S;
   end if;
end function;

// identify range for dimension in natural copy of centraliser 
SetRange := function (type, n, q)
   if type eq "D" then
      if n eq 8 then
         Range := [4];
      // elif n eq 16 and q mod 4 eq 3 then
         // Range := [4,12];
         // Range := [8];
      else 
         Range := [i: i in [n div 3 .. (2*n) div 3] | IsEven (i)];
         // Omega+4 and Omega+8 are expensive 
         if n eq 14 or n eq 20 then Exclude (~Range, 4); return Range; end if;
/* 
         if q mod 4 eq 3 then 
            if n eq 12 then return Range; end if;
            if #Range gt 1 and 4 in Range then Exclude (~Range, 4); end if;
            if #Range gt 1 and n - 4 in Range then Exclude (~Range, n - 4); end if;
            if #Range gt 1 and 8 in Range then Exclude (~Range, 8); end if;
            if #Range gt 1 and n - 8 in Range then Exclude (~Range, n - 8); end if;
         end if;
*/
      end if;
      return Range;
   end if;
      
   if type eq "2D" then 
      if n eq 8 then
         Range := [4];
      else 
         Range := [6];
      end if;
      return Range;
   end if;

   if type eq "B" then
      if n eq 7 then Range := [3]; return Range; end if;
      Range := n mod 4 eq 3 and q mod 4 eq 3 select [7] else [5];
      return Range;
   end if;

   // range for non-orthogonal groups
   if type eq "A" and n eq 4 then
      Range := q eq 3 select [4] else [2];
   elif n eq 5 then
      Range := [2, 3];
   elif n eq 7 then
      Range := [3, 4];
   elif n eq 8 then
      Range := [4];
   elif type in {"2A", "C"} and IsEven (n) then 
      Range := [i : i in [n div 3 .. (2*n) div 3] | IsEven (i)];
   else 
      Range := [n div 3 .. (2*n) div 3];
   end if;

   return Range;
end function;

// W words for generators of G in parent group P of G
// return smaller generating set for G with words
// for the new generating set in P
MakeSmaller := function (G, W : Limit := 10)
   P := RandomProcessWithWords (G);
   if Ngens (G) gt Limit then 
      Gens := []; Words := [];
      for i in [1..Limit] do 
         x, w := Random (P);
         if x ne x^0 and not (x in Gens) then 
            Append (~Gens, x);
            Append (~Words, w);
         end if;
      end for;
      H := sub<Generic (G) | Gens>;
      assert Ngens (H) eq #Words;
      W := Evaluate (Words, W);
      return H, W; 
   else 
      return G, W;
   end if;
end function;

// do G and K commute?
SubgroupsCommute := function (G, K)
   return forall{<g, k>: g in Generators (G), k in Generators (K) | g*k eq k*g};
end function;

// derived group of centraliser in G of w
MyDerivedCentraliser := function (G, g, w)
   C, Cwords := CentraliserOfInvolution (G, g, w);
   D, Dwords := DerivedGroupMonteCarlo (C: MaxGenerators := 25);
   Dwords := Evaluate (Dwords, Cwords);
   D, Dwords := MakeSmaller (D, Dwords: Limit := 10);
   return D, Dwords, C, Cwords;
end function;

// derived group of K
MyDerivedGroupMC := function (K, WK)
   K, Words := DerivedGroupMonteCarlo (K: MaxGenerators := 20);
   WK := Evaluate (Words, WK);
   K, WK := MakeSmaller (K, WK);
   return K, WK;
end function;

// choose non-trivial section
SmallestSection := function (G)
   if Type (G) eq GrpPerm then return G; end if;
   S := Sections (G);
   dim := [Degree (s): s in S];
   index := [i : i in [1..#dim] | dim[i] gt 1];
   if #index eq 0 then return G; end if;
   dims := [dim[i] : i in index];
   _, pos := Minimum (dims);
   H := S[index[pos]];
   vprint ClassicalRecognition: "Now chosen section of degree ", Degree (H);
   return H;
end function;

AnotherMakeSmaller := function (G, Words, type: Limit := 10)
   if Ngens (G) le 2 then return G, Words; end if;

   n := RankToDegree (type);
   q := type[3]; F := GF (q); p := Characteristic (F);
   E := [i: i in [1..Ngens (G)]];
   I := []; last := 0;
   for i in [1..Limit] do 
      r := Random (E);
      if (r in I) then continue; end if;
      H := sub<Generic (G) | [G.(E[i]) : i in I], G.E[r]>;
      if Ngens (H) eq 1 then Append (~I, r); continue i; end if;
      M := GModule (H);
      CF := CompositionFactors (M);
      if #CF eq last then continue i; end if;
      if Ngens (H) gt 1 and IsProbablyPerfect (H) and 
         AreRepresentationsIdentical (H, n) then 
         S := SmallestSection (H);
         flag := (Degree (S) gt 2) or 
            (Degree (S) eq 2 and LieCharacteristic (S: Verify := false) eq p);
         if flag then 
            flag, value := LieType (S, p: Perfect := true);
            vprint ClassicalRecognition: "Result of LieType call on section is", flag;
            Append (~I, r); 
            if flag and value eq type then  
               W := [Words[i]: i in I];
               assert Ngens (H) eq #W; 
               return H, W; 
            end if;
         end if;
         last := #CF;
         if #I eq #E then break i; end if;
      end if;
   end for;
   return G, Words; 
end function;

// G is a group of supplied <type>;
// SLPs for its generators are given in some parent group
// construct small generating set for G

SmallerGeneratingSet := function (G, Words, type: TRY := -1)
   if TRY eq 1 then 
      vprint ClassicalRecognition: "Use new SmallerGenSet";
      return AnotherMakeSmaller (G, Words, type);
   end if;

   if Ngens (G) le 5 then return G, Words; end if;
   P := RandomProcessWithWords (G); 
   F := GF (type[3]); 
   n := RankToDegree (type);
   p := Characteristic (F);
   E := []; W := [];
   repeat 
      e, w := Random (P);
      if not (e in E) and e ne Id (G) then 
         E[#E + 1] := e; W[#W + 1] := w;
         H := sub<Generic (G) | E >;
         if Ngens (H) gt 1 and IsProbablyPerfect (H) and 
            AreRepresentationsIdentical (H, n) then 
            vprint ClassicalRecognition: "A SmallestSection Call";
            S := SmallestSection (H);
            if type eq <"D", 2, #F> then 
               flag := IsOmegaPlus4 (S, F);
               vprint ClassicalRecognition: "Result of IsOmegaPlus4 call on section is", flag;
               if flag then value := type; end if;
            else 
               flag := n le 4 select LieCharacteristic (S: Verify := false) cmpeq p else true;
               if flag then 
                  flag, value := LieType (S, p: Perfect := true); 
                  if flag then 
                     value := ConvertType (type[1], value, type[3]);
                  end if;
               end if;
            end if;
            if flag and value eq type then 
               assert Ngens (H) eq #W; 
               W := Evaluate (W, Words);
               return H, W; 
            end if;
         end if;
      end if;
   until #E ge Ngens (G);
   return G, Words;
end function;

CommutingElement := function (G, P, First: NumberTrials := 100)
   trial := 0;
   repeat 
      trial +:= 1;
      g, wg := Random (P);
      o := Order (g);
      B := PrimeBasis (o);
      // Exclude (~B, 2);
      good := false;
      for p in B do 
         h := g^(o div p);
         good := not IsCentral (G, h) and IsCentral (First, h); 
         if good then pp := p; break p; end if;
      end for;
   until good or (trial gt NumberTrials);
   if good then return true, h, wg^(o div pp); 
    else return false, _, _; end if;
end function;

ConstructSL23 := function (G, First, type: NmrTrials := 10)
   P := RandomProcessWithWords (G);
   trial := 0;
   repeat 
      fx, x, wx := CommutingElement (G, P, First); 
      fy, y, wy := CommutingElement (G, P, First); 
      found := fx and fy and Order ((x, y)) eq 4;
      if found then H := sub<Generic (G) | x, y>; 
         found := Order (H) in {12,24,48}; 
       end if;
      trial +:= 1;
    until found or trial gt NmrTrials;
    result := <"A", 1, 3>;
    value := ConvertType (type, result, 3);
    h := RankToDegree (value);
    if found then 
       return true, H, [wx, wy], _, value, h; 
    else  
       return false, _, _, _, _, _; 
    end if;
end function;

/* given a direct product of two simple groups,  
   construct factor which commutes with First */

KillFactor := function (G, type, n, q, Range, First: 
   NumberTrials := 50, Exact := false, ConstructOnly := false)

   if q eq 3 and ([2] eq Range) then 
      return ConstructSL23 (G, First, type);
   end if;

   P := RandomProcessWithWords (G);
   trial := 0; 
   repeat 
      trial +:= 1;
      g, wg := Random (P);
      o := Order (g);
      B := PrimeBasis (o);
      Exclude (~B, 2);
      good := false;
      for p in B do 
         h := g^(o div p);
         good := not IsCentral (G, h) and IsCentral (First, h); 
         if good then pp := p; break p; end if;
      end for;
   until good or (trial gt NumberTrials);

   if (trial gt NumberTrials) then return false, _, _, _, _; end if;

   p := pp;
   wh := wg^(o div p);

   trial := 0; 
   repeat 
      trial +:= 1;
      k, wk := Random (P);
      m := (h, k);
   until (IsCentral (G, m) eq false) or (trial gt NumberTrials);

   if (trial gt NumberTrials) then return false, _, _, _, _; end if;

   wm := (wh, wk);
   H := sub<Generic (G) | m>;
   N, Nwords := NormalClosureMonteCarlo (G, H: slpsH := [wm], 
                   SubgroupChainLength := n); 
   if IsAbelian (N) then return false, _, _, _, _; end if;
   N, Nwords := MakeSmaller (N, Nwords);

   if ConstructOnly then return true, N, Nwords; end if;

   flag := AreRepresentationsIdentical (N, n);
   if flag then 
      vprint ClassicalRecognition: "C SmallestSection Call";
      S := SmallestSection (N);
      F := GF (q);
      p := Characteristic (F);
      if Degree (S) eq 2 and p eq 3 then 
         if IsProbablyPerfect (S) and p ne SL2Characteristic (S: Verify := false) then 
            return false, _, _, _, _; 
         end if;
      end if;
      // various SL2s in characteristics other than p are mis-identified 
      // also 3Alt(7) is incorrectly recognised by LieType in char 5 as U(3, 5) 
      if Degree (S) le 4 and p le 11 then 
         prime := LieCharacteristic (S: Verify := false);
         vprint ClassicalRecognition: "KillFactor: Degree and prime is ", Degree (S), prime;
         good := prime cmpeq p
           // SU(4, 2) vs PSp (4, 3)
           or (type eq "C" and Degree (S) eq 4 and q eq 3 and prime eq 2)
           // SL(2, 4) vs SL(2, 5)
           or (type in {"A", "C"} and Degree (S) eq 2 and q eq 5 and prime eq 2)
           // PSL(2, 7) vs SL(3, 2)
           or (type eq "C" and Degree (S) eq 3 and q eq 7 and prime eq 2);
      else 
         good := true;
      end if;
      if good then 
         flag, value := LieType (S, p); 
      else 
         flag := false; 
      end if;
   end if;
   if not flag then return false, _, _, _, _; end if;

   value := ConvertType (type, value, q);
   h := RankToDegree (value);

   // if type is "2D" or "B" then other factor is of type "D" 
   if not Exact then 
      if type eq "2D" and h in {4} and value[1] eq type then 
         found := true;
      elif type in {"2D", "B"} and value[1] eq "D" and n - h in Range then 
         found := true;
      else 
         found := (value[1] eq type and (h in Range or n - h in Range) 
             and value[3] eq q); 
      end if;
   else
      found := (value[1] eq type and h in Range) and value[3] eq q; 
   end if;

   return found, N, Nwords, value, h;
end function;

O4KillFactor := function (G, type, n, q: Limit := 20)
   F := GF (q); p := Characteristic (F);
   NmrTrials := 0;
   repeat 
      found, A, WA, value, h := KillFactor (G, type, n, q, [n - 4], sub<G|>: Exact := true); 
      NmrTrials +:= 1;
   until found or NmrTrials gt Limit; 
   if NmrTrials gt Limit then return false, _, _, _, _,_,_,_,_; end if;
   vprint ClassicalRecognition: "Nmrtrials to split first factor is ", NmrTrials;

   NmrTrials := 0;
   repeat 
       found, C, WC := KillFactor (G, "D", n, q, [4], A: ConstructOnly := true);
       if found then found := IsOmegaPlus4 (C, (GF(q))); end if;
       NmrTrials +:= 1;
   until found or NmrTrials gt Limit;
   if NmrTrials gt Limit then return false, _, _, _, _,_,_,_,_; end if;
   return true, A, C, WA, WC, value, <"D", 2, q>, n - 4, 4;
end function;

// G has direct factor O+4; split to obtain two factors 
MySplitOCentraliser := function (G, type, n, q, dim: Limit := 10)
   F := GF (q); p := Characteristic (F);
   found := false; 

   if n eq 7 and q eq 3 and type eq "B" then
      vprint ClassicalRecognition: "Call MySplitO73Centraliser"; 
      return MySplitO73Centraliser (G, type, n, q, 3);
   end if;

   NmrTrials := 0;
   repeat 
      found, A, WA, value, h := KillFactor (G, type, n, q, 
         [dim], sub<G|>: Exact := true); 
      NmrTrials +:= 1;
   until found or NmrTrials gt Limit; 
   vprint ClassicalRecognition: "N is ", NmrTrials;
   if NmrTrials gt Limit then return false, _, _, _, _, _, _, _, _; end if;

   if q eq 3 then 
      f, C, WC := ConstructOP43 (G, A, "D");
      if f eq false then return false, _, _, _, _, _, _, _, _; end if;
   else 
      NmrTrials := 0;
      repeat 
         NmrTrials +:= 1;
         f, C, WC := KillFactor (G, "D", n, q, [4], A: ConstructOnly := true);
      until (f and IsOmegaPlus4 (C, F)) or NmrTrials gt Limit;
      vprint ClassicalRecognition: "N2 is ", NmrTrials;
      if NmrTrials gt Limit then return false, _, _, _, _, _, _, _, _; end if;
   end if;

   return true, A, C, WA, WC, value, <"D", 2, q>, n - 4, 4;
end function;

// G is Omega^+(8, F) -- construct two commuting copies of Omega^+(4, F) as subgroups
SplitOPlus8 := function (G, F, D, Dwords: Limit := 50, OneOnly := false)
   q := #F;
   if q eq 3 then return SplitO4O4P3 (D, "D"); end if;

   NmrTrials := 0;
   repeat 
      NmrTrials +:= 1;
      f, A, WA := KillFactor (D, "D", 8, q, [4], sub<D|>: ConstructOnly:=true);
      good := (f and IsOmegaPlus4 (A, F) and #EstimateCentre (A, 4) eq 2);
  until good or NmrTrials gt Limit; 

   if NmrTrials gt Limit then 
      return false, _, _, _, _;
   end if;

   if OneOnly then 
      if good then return true, A, WA; else return false, _, _, _, _; end if;
   end if;

   NmrTrials := 0;
   repeat 
      NmrTrials +:= 1;
      f, C, WC := KillFactor (D, "D", 8, q, [4], A: ConstructOnly:=true);
      good := (f and IsOmegaPlus4 (C, F) and #EstimateCentre (C, 4) eq 2);
   until good or NmrTrials gt Limit; 

   if NmrTrials gt Limit then 
      return false, _, _, _, _;
   end if;

   assert SubgroupsCommute (A, C);
   return true, A, WA, C, WC;
end function;

// G is isomorphic to classical group of specified type, 
// in degree n over field of size q
// choose involution g in G and construct factors in its centraliser 
// until factors of derived centaliser have natural dimension in Range 

SplitCentraliser := function (G, type, n, q:  
   Check := true, Limit := 5, Range := [], Exact := false) 
   F := GF(q);
   p := Characteristic (F);
   if Range cmpeq [] then Range := SetRange (type, n, q); end if;
   vprint ClassicalRecognition: "Range for SplitCentraliser is ", Range;
   Nmr_Sampled := 0; 
   FACTOR := 4; 
   repeat 
      Nmr_Sampled +:= 1;
      nInv := 0;
      repeat 
         vprint ClassicalRecognition: "Choose next involution";
         nInv +:= 1;
         repeat 
            flag, g, wg := RandomElementOfOrder (G, 2); 
         until flag and IsCentral (G, g) eq false;
         if (type in {"A", "C", "2A", "D", "2D"} and IsEven (n)) 
            or (type in {"B"}) then 
            D, Dwords, C, Cwords := MyDerivedCentraliser (G, g, wg);
         else 
            C, Cwords := CentraliserOfInvolution (G, g, wg);
            D := C; Dwords := Cwords;
         end if;
         if Check eq true then 
            vprint ClassicalRecognition: "Test if good inv cent?", type, n, q, Range;
            good_inv := IsGoodCentraliser (D, type, n, q, Range);
            vprint ClassicalRecognition: "*** Check involution result?", good_inv;
         else 
            good_inv := true;
         end if;
      until good_inv or nInv gt Limit;
      if nInv gt Limit then return false, _, _,_,_,_,_,_,_,_,_,_; end if;
      vprint ClassicalRecognition: "Number of involutions chosen is ", nInv;

      special := (type eq "2D" and ((q mod 4 eq 1 and n in {8}) 
                                 or (q mod 4 eq 3 and n in {8, 10})))
         or (type eq "B" and n in {7,9}) 
         or (type eq "B" and q mod 4 eq 3 and n in {11});
      
      if special then 
         vprint ClassicalRecognition: "Split: In special O case";
         found, N, M, WN, WM := MySplitOCentraliser (D, type, n, q, n - 4: Limit := 20);
         if found then 
            if type eq "2D" then 
               typeN := <"2D", (n - 4) div 2, q>;
            elif type eq "B" then  
               typeN := <"B", (n - 4) div 2, q>;
            end if;
            typeM := <"D", 2, q>;
            rankN := n - 4; rankM := 4;
         end if;
      elif type eq "D" and n eq 8 then
         vprint ClassicalRecognition: "Split: In O+4 case";
         // if IsOmegaPlus4Centraliser (D, q) then 
            // "passed the test ...";
            // "now apply split for Omega8...";
            found, N, WN, M, WM := SplitOPlus8 (G, F, D, Dwords);
            if found then 
               typeN := <"D", 2, q>;
               typeM := <"D", 2, q>;
               rankN := 4; rankM := 4;
            end if;
         // else 
           //  found := false;
         // end if;
      elif type in {"D", "2D"} and (4 in Range or n - 4 in Range) then 
         vprint ClassicalRecognition: "Split: In O4 case";
         found, N, M, WN, WM, typeN, typeM, rankN, rankM := 
             MySplitOCentraliser (D, type, n, q, n - 4);
      else 
         vprint ClassicalRecognition: "Split: In general case";
         nmr := 0; m := Maximum (Range); max := Maximum (n, m);
         repeat 
            found, N, WN, typeN, rankN :=  KillFactor 
               (D, type, n, q, Range, sub<D | D.0>);
             nmr +:= 1; 
             // bad centraliser? 
             bad := assigned rankN and rankN gt max;
         until found or nmr gt Limit or bad;
         if found then 
            // if n - rankN eq 2 and q eq 3 then Range := [2]; end if;
            found, M, WM, typeM, rankM :=  KillFactor (D, type, n, q, Range, N:
                         Exact := Exact);
            found := found and rankN + rankM eq n;
         end if;
      end if;
   until found or Nmr_Sampled gt Limit; 
   if not found then return false, _, _,_,_,_,_,_,_,_,_,_; end if;

   WN := Evaluate (WN, Dwords); WM := Evaluate (WM, Dwords);  
   assert SubgroupsCommute (N, M);
   return found, N, M, WN, WM, typeN, typeM, rankN, rankM, g, C, Cwords;
end function;

// construct two classical subgroups of G whose dimensions lie in Range

Step1 := function (G, type, n, q : Check := true, Range := [], Exact := false) 
   F := GF(q);
   p := Characteristic (F);
   nmr := 0;  
   Factor := type in {"B", "2D"} select 10 else 4;
   P := RandomProcessWithWords (G);
   repeat 
      nmr +:= 1;
      found, X, Y, WX, WY, typeX, typeY, f, rem, g, C, Cwords := 
      SplitCentraliser (G, type, n, q : Check := Check, Range := Range, Exact := Exact);
   until found or nmr gt Factor;
   if not found then return false, _,_,_,_,_,_,_, _, _, _, _, _, _; end if;

   vprint ClassicalRecognition, 1 : "Result from call to Split is ", typeX, typeY, f, rem;

   X, WX := SmallerGeneratingSet (X, WX, typeX);
   Y, WY := SmallerGeneratingSet (Y, WY, typeY);

   if (type eq "2A" and IsOdd (n) and n ne 5 and IsEven (rem)) or
      (type eq "2A" and n eq 5 and f eq 3) or
      (type eq "2A" and IsEven (n) and f lt rem) or
      (type in ["A", "C", "D"]  and f lt rem) or
      (type eq "B" and IsEven (f)) or 
      (type eq "2D" and typeX[1] ne "2D") then 
      T := X; WT := WX; t := f; tt := typeX;
      X := Y; WX := WY; f := rem; typeX := typeY;
      Y := T; WY := WT; rem := t; typeY := tt;
   end if;

   // if MatrixGroup then construct smallest faithful representations
   if Type (G) eq GrpMat then 
      X, WX, G1 := MyFixProjections (X, WX, typeX);
      Y, WY, G2 := MyFixProjections (Y, WY, typeY);
   else
      G1 := X; G2 := Y;
   end if;

   return found, X, Y, WX, WY, G1, G2, typeX, typeY, f, rem, g, C, Cwords;
end function;

// D is centraliser of involution in SX(n, q) of supplied type
// it has an SX4 or SX8 factor which contains "glue" element
// construct this factor -- its type and natural copy degree 
// depends on supplied type 

GlueCentraliser := function (D, Dwords, type, n, q: Limit := 20)

   Range := type in { "B", "D", "2D"} and q mod 4 eq 3 select [8] else [4]; 
   // Range := type in { "B", "D", "2D"} select [8] else [4]; 
   
   if type eq "D" and n eq 8 then 
      found, N, WN, M, WM := SplitOPlus8 (D, GF(q), D, Dwords);
      WN := Evaluate (WN, Dwords); WM := Evaluate (WM, Dwords);  
      assert SubgroupsCommute (N, M);
      typeN := <"D", 2, q>;
      typeM := <"D", 2, q>;
      rankN := 4; rankM := 4;
      return found, N, M, WN, WM, typeN, typeM, rankN, rankM;
   elif type in {"B", "D", "2D"} and Range eq [4] then 
      ntries := 0; 
      repeat 
         found, N, M, WN, WM, typeN, typeM, rankN, rankM := 
            MySplitOCentraliser (D, type, n, q, n - 4);
         // distinguish Omega(3, q) from SL(2, q) 
         if n eq 7 and type eq "B" then 
            found := found and #EstimateCentre (N, 2) eq 1;
         end if;
         ntries +:= 1;
      until found or ntries gt Limit;
      if ntries gt Limit then return false,_,_,_,_,_,_,_,_; end if;
      WN := Evaluate (WN, Dwords); WM := Evaluate (WM, Dwords);  
      assert SubgroupsCommute (N, M);
      return found, N, M, WN, WM, typeN, typeM, rankN, rankM;
   end if;

   if n eq 5 then
      F := GF (q);
      p := Characteristic (F);
      flag := AreRepresentationsIdentical (D, 5);
      if flag then 
         flag, value := LieType (D, p);
         degree := RankToDegree (value);
         if degree in Range then 
            return true, D, D, Dwords, Dwords, value, value, degree, degree;
         else 
            return false,_,_,_,_,_,_,_,_;
         end if;
      end if;
   end if;

   case type: 
      when "2D", "B": find_type := "D";
      else find_type := type;
   end case;
     
   ntries := 0; 
   repeat 
      found, N, WN, typeN, rankN :=  KillFactor (D, find_type, n, q, 
                                     Range, sub<D | D.0>: Exact := true);
      ntries +:= 1;
   until found or ntries eq Limit;
   if ntries eq Limit then return false,_,_,_,_,_,_,_,_; end if;

   F := GF (q);
   p := Characteristic (F);

   WN := Evaluate (WN, Dwords); 
   return true, N, N, WN, WN, typeN, typeN, rankN, rankN;
end function;
