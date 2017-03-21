freeze;

import "general.m": JordanDecompositionForGroup, MyCongruenceSubgroup; 
import "congruence.m": IsValidInput;

MyDiagonalJoin := function (L)
    L := <x: x in L>;
    return DiagonalJoin (L);
end function;

MatrixBlocks := function (g, CB, blocks)
   F := BaseRing (Parent (g));
   I := CB * g * CB^-1;
   e := [* *];
   offset := 0;
   for i in [1..#blocks] do 
      k := blocks[i];
      e[i] := GL (k, F) ! ExtractBlock (I, offset + 1, offset + 1, k, k);
      offset +:= k;
   end for;
   return e;
   end function;

SetupBlocks := function (G, CB, blocks)
   F := BaseRing (G);

   U := UserGenerators (G);
   E := [MatrixBlocks (U[j], CB, blocks): j in [1..#U]];
   sections := [* *];
   for i in [1..#blocks] do
      k := blocks[i];
      gens := [E[j][i]: j in [1..#U]];
      sections[i] := sub <GL(k, F) | gens>;
      // sections[i]`UserGenerators := gens;
   end for;
   return sections;
end function;

CentralisedSpace := function (g)
   G := Parent (g);
   F := CoefficientRing (G);
   A := MatrixAlgebra (F, Degree (G));
   a := A!g;
   N := NullSpace (a - Identity (A));
   vprint Smash: "Nullspace has dimension ", Dimension (N);
   return N;
end function;

ConstructSubmodule := function (S, U)
    if Dimension (U) eq 0 then return U; end if;
    repeat
       i := 1; fixed := true;
       while (i le #S and fixed) do
          // "ConstructSubmodule generator i = ", i;
          product := U * S[i];
          I := U meet product;
          fixed := I eq U;
          if not fixed then
             U := I; if Dimension (U) eq 0 then return U; end if;
          end if;
          i +:= 1;
       end while;
    until fixed;

    return U;
end function;

// H is unipotent part of K 
ConstructFlag := function (G, H, blocksizes)
   if IsTrivial (H) then 
      return <Identity (Generic (H)), blocksizes cat [Degree (H)]>; 
   end if;

   U := &meet[CentralisedSpace (H.i): i in [1..Ngens (H)]];
   W := ConstructSubmodule ([G.i : i in [1..Ngens (G)]], U);
   Append (~blocksizes, Dimension (W));

   d := Degree (H);
   F := BaseRing (H);
   V := RSpace (F,d);
   eb := ExtendBasis ([V!b: b in Basis (W)], V);
   cb := GL(Degree (G), F) ! &cat[Eltseq (x): x in eb];

   a := Ngens (G); b := Ngens (H); 
   a := Set ([Generic (G) | G.i: i in [1..a]]); Exclude (~a, Identity (G)); 
   b := Set ([Generic (H) | H.i: i in [1..b]]); Exclude (~b, Identity (H)); 
   a := [x : x in a];
   common := [Position (a, x) : x in b | x in a];
   a := #a;
   b := #b;
   G := sub<Generic (G) | [G.i: i in [1..a]], [H.i: i in [1..b]]>;

   M := GModule (G);
   W := sub<M | W>;

   Q := quo <M | W>;
   A := [ActionGenerator (Q, i): i in [1..a]];
   B := [ActionGenerator (Q, i): i in [a + 1..Ngens (G)]] cat 
        [ActionGenerator (Q, i): i in common];
   Q := sub<GL(Dimension (Q), F) | A>;
   R := sub<GL(Dimension (Q), F) | B>;

   if IsTrivial (Q) eq false then
       COB := $$ (Q, R, blocksizes);
       cob := COB[1]; blocksizes := COB[2];
       // cob, blocksizes := $$ (Q, R, blocksizes);
       cob := DiagonalJoin (Identity (MatrixAlgebra (F, Dimension (W))), cob);
       cb := cob * cb;
   else 
       Append (~blocksizes, Dimension (Q));
   end if;
   return <cb, blocksizes>;
end function;

SFChangeOfBasis := function (G)
   if assigned G`SFChangeOfBasis then
      CB := G`SFChangeOfBasis[1];
      blocks := G`SFChangeOfBasis[2];
      return CB, blocks;
   end if;
   error "Not assigned SFChangeOfBasis";
end function;

CompletelyReducibleBasis := function (G)
   d := Degree (G); F := BaseRing (G);

   p := Characteristic (BaseRing (G));
   if p gt 0 then 
      I := CongruenceImage (G);
      if LMGOrder (I) mod p eq 0 then
         error "Cannot construct completely reducible part since image order is divisible by characteristic";
      end if;
   end if;

   f := IsSolubleByFinite (G: NeedChangeOfBasis := true);
   if not f then error "G is not soluble-by-finite"; end if;

   CB, blocks := SFChangeOfBasis (G);
   K := MyCongruenceSubgroup (G);

   S := SetupBlocks (G, CB, blocks);
   B := SetupBlocks (K, CB, blocks);

   U := [u where _, u := JordanDecompositionForGroup (b): b in B];
   L := [* ConstructFlag (S[i], U[i], []): i in [1..#U] *]; 
   blocksizes := &cat[L[i][2]: i in [1..#L]];
   L := [* L[i][1]: i in [1..#L] *];
   cb := L[1]; 
   for i in [2..#L] do 
      cb := DiagonalJoin (cb, L[i]);
   end for;
   cb := GL(d, F) ! cb;
   return cb * CB, blocksizes;
end function;

CompletelyReducibleImage := function (G, CB, blocksizes)
   U := UserGenerators (G);
   blocks := [MatrixBlocks (u, CB, blocksizes): u in U];
   gens := [Generic (G) | MyDiagonalJoin (blocks[i]): i in [1..#blocks]];
   I := sub<Generic (G) | gens>;
   I`UserGenerators := gens;
   I`SLPGroup := SLPGroup (#gens);
   return I;
end function;

intrinsic CompletelyReduciblePart (G:: GrpMat) -> GrpMat, GrpMatElt 
{ return completely reducible part of soluble-by-finite group 
defined over number field} 

   require IsValidInput (G):
      "Input defined over invalid field";

   require IsSolubleByFinite (G): "Argument must be soluble-by-finite";

   if IsCompletelyReducible (G) then return G, G.0; end if;

   CB, blocksizes := CompletelyReducibleBasis (G);
   I := CompletelyReducibleImage (G, CB, blocksizes);
   return I, CB;
end intrinsic;

