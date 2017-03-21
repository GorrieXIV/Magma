freeze;

import "ut.m": ConjugateToIntegers, PCPresentationUT;
import "general.m": IsKnownSF;
import "abelian.m": IrredAbelianGroup;
import "cr.m": CompletelyReducibleBasis, CompletelyReducibleImage;
import "abelian.m": PresentationForAFGroup;
import "ut.m": MatrixToWord;
 
// G is unipotent matrix group -- return its Hirsch number 

MyHirschNumberU := function (G)
   Z := Integers ();
   H, CB := ConjugateToIntegers (G);
   P, U := PCPresentationUT (Degree (G), Z);
   gens := [MatrixToWord (P, H.i, U): i in [1..Ngens (H)]];
   vprint Infinite: "Compute pc-presentation for subgroup of polycyclic group ...";
   S := sub<P | gens>;
   s := HirschNumber (S);
   return s, P, gens, S;
end function;

// Normal closure of H in G is unipotent matrix group -- 
// return Hirsch number of normal closure 

HirschNumberNormalU := function (G, H)
   if IsTrivial (H) then return 0; end if;
   vprint Infinite: "first call to MyHirschNumberU";
   h := MyHirschNumberU (H);
   vprint Infinite: "Now back from MyHirschNumberU";
   vprint Infinite: "Start value of h, # of gens is", h, Ngens (H);
   n := h;
   repeat 
      h := n;
      N := sub<Generic (G) | H, 
      &cat[[H.i^G.l, H.i^(G.l^-1)]: i in [1..Ngens (H)], l in [1..Ngens (G)]]>;
      vprint Infinite: "now recall MyHirschNumberU";
      n := MyHirschNumberU (N);
      vprint Infinite: "Back from recall to MyHirschNumberU";
      vprint Infinite: "new h, ngens is", n, Ngens (N);
      H := N;
   until n eq h;
   return h;
end function;

IsValidInput := function (G)
  K := BaseRing (G);
  return ISA (Type(K), FldRat) or ISA (Type(K), FldNum); 
end function;

intrinsic HirschNumber (G :: GrpMat) -> RngIntElt 
{Hirsch number of soluble-by-finite matrix group G defined over number field}

   require IsValidInput (G): 
      "Input must be defined over rationals or number field";

   if IsKnownSF (G) cmpeq false then 
      error "G is not soluble-by-finite so algorithm does not apply";
   end if;

   if assigned G`HirschNumber then
      return G`HirschNumber;
   end if; 
      
   if IsFinite (G) cmpeq true then 
      G`HirschNumber := 0;
      return 0; 
   end if;

   if IsAbelian (G) then 
      if IsIrreducible (GModule (G)) then 
         vprint Infinite: "Process irreducible abelian input "; 
         f, P := IrredAbelianGroup (G);
      elif IsCompletelyReducible (G) then 
         vprint Infinite: "Process completely reducible abelian input "; 
         P := RecogniseAbelian (G);
      end if;
      v := HirschNumber (P);
      G`HirschNumber := v;
      return v;
   end if;
      
   vprint Infinite: "Test if G is soluble-by-finite"; 
   f := IsSolubleByFinite (G: NeedChangeOfBasis := true);
   if not f then 
      vprint Infinite: "G is not soluble-by-finite so algorithm does not apply";
      return false; 
   end if;

   CB, blocksizes := CompletelyReducibleBasis (G);
   I := CompletelyReducibleImage (G, CB, blocksizes);

   if IsTrivial (I) then 
      assert IsUnipotent (G);
      v := MyHirschNumberU (G);
      G`HirschNumber := v;
      return v;
   end if;

   assert IsAbelianByFinite (I);
   F, R, P := PresentationForAFGroup (I);
   v1 := HirschNumber (P);
   K := Evaluate (R, [G.i: i in [1..Ngens (G)]]);
   K := sub<Generic (G) | K>;
   assert IsUnipotent (K);
   if IsTrivial (K) eq false then 
      v2 := HirschNumberNormalU (Expand (G), Expand (K));
   else 
      v2 := 0;
   end if;
   G`HirschNumber := v1 + v2; 
   return v1 + v2;
end intrinsic;

intrinsic HasFiniteIndex (G :: GrpMat, H :: GrpMat) -> BoolElt 
{does subgroup H have finite index in soluble-by-finite matrix group G
defined over number field}
   require IsValidInput (G): 
      "Input must be defined over rationals or number field";
   require IsSolubleByFinite (G): "First argument must be soluble-by-finite";
   g := HirschNumber (G);
   h := HirschNumber (H);
   return g eq h;
end intrinsic;

intrinsic HasFiniteRank (G :: GrpMat) -> BoolElt 
{return true if matrix group G defined over number field has finite (Pruefer and Hirsch) rank}
   return IsSolubleByFinite (G);
end intrinsic;

RankGL := function (n)
   if n lt 4 then return Floor ((n^2 + 2*n) / 2);
   else return Floor (n^2/4) + 1; end if;
end function;

intrinsic PrueferRankBound (G :: GrpMat) -> RngIntElt
{upper bound for Pruefer rank of matrix group defined over number field}
   require IsValidInput (G): 
      "Input must be defined over rationals or number field";
   h := HirschNumber (G);
   F := BaseRing (G);
   n := Degree (G);
   m := AbsoluteDegree (F);
   bound := RankGL (n * m);
   return h + bound;
end intrinsic;
