freeze;

import "general.m": IsKnownFinite, IsKnownSF, IsKnownCF, 
IsKnownNF, IsKnownAF, MatrixGenerators, AllCommute,
SetVirtualValues, SetValues, IsKnownCR, HasKnownCongruenceSubgroup,
JordanDecompositionForGroup, IsUpperTriangularGroup, IsDiagonalisable, 
MyIsTrivial;

import "random.m": NormalClosureRandom;
import "finite.m": ConstructCT;
import "congruence.m": IsValidInput, MyCongruenceImage;
import "present.m": ConstructPresentation;

/* construct (normal) generators for congruence subgroup;
   Virtual: congruence homomorphism suitable for Virtual testing;
   Selberg: construct Selberg congruence homomorphism;
   NormalClosure: construct normal closure of subgroup; 
   Monte: algorithm used to construct normal closure;

   Presentation: one of "CT", "FP", "PC" to dictate method of construction;
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation;

   if Reducible and char p > 0, then check if #I mod p ne 0;  
   if CF, then check if kernel normal generators commute with 
   generators of G; 
   if any test fails, then return false;
   these are used by IsCompletelyReducible in certain cases, 
   and always by IsCentralByFinite;

   otherwise return true, congruence subgroup, image, 
   and congruence homomorphism 
*/

CongruenceSubgroup := function (G: Monte := false, Selberg := true, 
   Reducible := false, CentralByFinite := false, 
   OrderLimit := 10^15, Presentation := "CT", Small := 10^6, Short := 10, 
   NormalClosure := false, Virtual := false)

   if not IsValidInput (G) then 
      error "CongruenceSubgroup: incorrect input";
   end if;

   if Virtual then Selberg := true; end if;

   H, tau, images := MyCongruenceImage (G: Selberg := Selberg, Virtual := Virtual);
   if IsTrivial (H) then 
      G`Congruence`Finite := false; 
      if CentralByFinite then flag := IsAbelian (G); else flag := true; end if;
      return flag, G, H, tau; 
   end if;

   o := ConstructCT (H);

   p := Characteristic (BaseRing (G));

   /* can we decide completely reducibility? */
   if (Reducible and (o mod p eq 0)) then return false, _, _, _; end if; 

   gens, Rels := ConstructPresentation (G, H, images: Small := Small,
      Presentation := Presentation, OrderLimit := OrderLimit, Short := Short);

   F := BaseRing (G); d := Degree (G);
   MA := MatrixAlgebra (F, d);

   /* if CentralByFinite, then evaluation of single relation 
      may be enough to decide relevant questions negatively */
   if CentralByFinite then 
      E := [MA | ]; 
      for i in [1..#Rels] do 
         vprint Infinite: "process relator ", i; 
         E[i] := Evaluate (Rels[i], gens); 
         if exists{g : g in Generators (G) | g * E[i] ne E[i] * g} then
            return false, _, H, tau; 
         end if;
      end for;
   else 
      vprint Infinite: "Now evaluating all relators ...";
      E := Evaluate (Rels, gens);
   end if;

   vprintf Infinite: "Now set up %o normal generators as subgroup\n", #E;

   //  N := sub<Generic (G) | E>;
   N := sub<MA | E>;
   N`UserWords := <gens, Rels>;
   N`UserGenerators := E;
   vprint Infinite: "Have now set up the normal generators for subgroup";

   if not NormalClosure then
      SetValues (G, H, N, Rels);
      return true, N, H, tau;
   end if;

   if NormalClosure and not IsTrivial (N) then 
      vprint Infinite: "Construct normal closure";
      if Monte then 
         N := NormalClosureMonteCarlo (G, N); 
      else 
         N := NormalClosureRandom (G, N); 
      end if;
   end if;

   return true, N, H, tau;
end function;

/* construct a basis for the F-enveloping algebra of <S> */

BasisEnvelopingAlgebra := function (H, T: Shadow := false)

   if #T eq 0 then return [], []; end if;

   if Shadow then 
      assert assigned H`Congruence`Map;
      tau := H`Congruence`Map;
      d := Degree (H);
      K := BaseRing (H);
      MB := MatrixAlgebra (K, d);
      S := [tau (t): t in T];
   else
     S := T;
     G := H;
   end if;

   G := Parent (Rep (S));
   F := BaseRing (G);
   n := Degree (G);
   MA := MatrixAlgebra (F, n);

   if exists{s : s in S | Determinant (s) eq 0} then
      A := [MA | S[1]];
   else
      A := [MA | S[1]^0];
      if Shadow then B := [MB | T[1]^0]; end if;
   end if;

   if IsField (F) then V := VectorSpace(F, n^2); else V := RSpace (F, n^2); end 
if;
   U := sub <V | [Vector (a): a in A]>;

   i := 0;
   while i lt #A do 
      i +:= 1;
      vprint Infinite: " i = ", i, " #S = ", #S;
      for j in [1..#S] do 
         u := A[i] * S[j];
	 Include (~U, Vector (u), ~new);
	 if not new then continue; end if;
         Append (~A, u);
         if Shadow then Append (~B, B[i] * T[j]); end if;
         if Dimension (U) mod 20 eq 0 then 
            vprint Infinite: "Dimension of enveloping algebra is now ...", Dimension (U);
         end if;
      end for;
   end while;

   vprint Infinite: "Dimension of enveloping algebra is ", Dimension (U);

   if Shadow then return B; else return A; end if;
end function;

/* basis for enveloping algebra of normal closure <K>^G where G = <S> */

BasisEnvelopingAlgebraClosure := function (G, K, S: Shadow := false)

   if #S eq 0 then return []; end if;

   vprint Infinite: "BasisEnvelopingAlgebraClosure: Compute inverses of defining matrices";
   S := MatrixGenerators (S);
   A := MatrixGenerators (K);

   F := BaseRing (K);
   n := Degree (K);
   if IsField (F) then V := VectorSpace (F, n^2); else V := RSpace (F, n^2); end if;

   vprint Infinite: "Set up subspace spanned by normal generators of K ...";
   U := sub <V | [Vector (x): x in A]>;

   vprint Infinite: "Test if conjugates of normal generators of K are new"; 
   i := 0;
   repeat 
      // "currently ", #A, #S;
      i +:= 1; j := 0; 
      repeat 
         j +:= 1;
         // "testing ... ", i, j;
         v := S[j] * A[i] * S[j]^-1;
         Include (~U, Vector (v), ~new);
         if new then A[#A+1] := v; end if;
      until j eq #S; 
   until i eq #A; 

   vprint Infinite: "Construct basis for enveloping algebra of normal closure of K"; 
   A := BasisEnvelopingAlgebra (G, A: Shadow := Shadow);

   return A;
end function;

// construct G-module in the null space of J for G = <S> 

ModuleViaNullSpace := function (S, J)
    U := Nullspace (J);
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

forward ExploreBasis;

/* 
MyExtendBasis := function (U, V)
   W := []; 
   d := Dimension (V);
   for i in [1..#Basis (V)] do
      T := sub<V | U, W>;
      if not (V.i in T) then Append (~W, V.i); end if;
      if Dimension (T) eq d then return W; end if;
   end for;
   
   m := 5;
   repeat
      coeffs := [Random (Z, m): i in [1..d]];
      v := &+[coeffs[i] * V.i: i in [1..#coeffs]];
      if not (v in T) then Append (~W, v); end if;
      if Dimension (T) eq d then return Basis (T); end if;
   until Dimension (T) eq d; 

   return false;

end function;
*/
   
/* U is submodule for G = <S>, K is congruence subgroup of G;
   rewrite matrices wrt new basis, exhibiting U;
   process the two block-diagonal images */

ProcessBlockDiagonals := function (K, S, U, B, CList, Blocks)
   n := Degree (K);
   F := BaseRing (K);

   /* is input defined over Z? if so, promote to Q */
   if Type (F) eq RngInt then 
      F := Rationals (); 
      K := ChangeRing (K, F);
      W := Universe (S);
      W := ChangeRing (W, F);
      S := [W | s : s in S];
      W := Universe (B);
      W := ChangeRing (W, F);
      B := [W | b : b in B];
      F := Integers ();
   end if;

   V := RSpace (F, n);
   // CB := ExtendBasis (U, V);
   CB := ExtendBasis ([V!b: b in Basis (U)], V);
   CB := [Eltseq (x): x in CB];

   CB := GL(n, F) ! CB;
   Append (~CList, <CB, Dimension (U)>);

   /* rewrite K wrt basis exhibiting submodule */
   K := sub<GL(n, F) | [CB * K.i * CB^-1: i in [1..Ngens (K)]]>;
   S := [CB * S[i] * CB^-1: i in [1..#S]];
   B := [CB * B[i] * CB^-1: i in [1..#B]];

   u := Dimension (U);
   /* process first block */
   K1 := sub<GL(u, F) | [ExtractBlock (K.i, 1, 1, u, u): 
                        i in [1..Ngens (K)]]>; 
   S1 := [ExtractBlock (S[i], 1, 1, u, u): i in [1..#S]];
   B1 := [ExtractBlock (B[i], 1, 1, u, u): i in [1..#B]];
   vprint Infinite: "Dimension of first block of K is", Degree (K1);

   orig := #CList;
   first, CList, Blocks := ExploreBasis (K1, S1, B1, CList, Blocks); 
   if orig ne #CList then 
      for ii in [orig + 1..#CList] do 
      C := CList[ii][1]; m := CList[ii][2];
      C := DiagonalJoin (C, Identity (MatrixAlgebra (F, n - u)));
      CList[ii] := <C, m>;
      end for;
   else    
      Append (~Blocks, Degree (K1));
   end if;

   vprint Infinite: "Result of first block call of degree ", Degree (K1), ":", first;
   if first eq false then return false, _, _; end if;
         
   /* process second block */
   K2 := sub<GL(n - u, F) | 
              [ExtractBlock (K.i, u+1, u+1, n-u, n-u): i in [1..Ngens (K)]]>; 
   vprint Infinite: "Dimension of second block of K is", Degree (K2);
   S2 := [ExtractBlock (S[i], u+1, u+1, n-u, n-u): i in [1..#S]];
   B2 := [ExtractBlock (B[i], u+1, u+1, n-u, n-u): i in [1..#B]];

   orig := #CList;
   second, CList, Blocks := ExploreBasis (K2, S2, B2, CList, Blocks);
   if orig ne #CList then 
      for ii in [orig + 1..#CList] do 
      C := CList[ii][1]; m := CList[ii][2];
      C := DiagonalJoin (Identity (MatrixAlgebra (F, u)), C);
      CList[ii] := <C, m>;
      end for;
   else 
      Append (~Blocks, Degree (K2));
   end if;
   vprint Infinite: "Result of second block call of degree ", Degree (K2), ":", second;
   if second eq false then return false, _, _; end if;

   assert first eq true and second eq true;
   return true, CList, Blocks;
end function;

/* K is congruence subgroup of G = <S>;
   Commute := true: test only if basis elements B commute;
   otherwise construct submodule and explore two block diagonal images */

ExploreBasis := function (K, S, B, CList, Blocks: Commute := false)

   vprint Infinite: "Test for commutativity of basis elements";
   vprint Infinite: "Construct submodule? ", not Commute;
   for i in [1..#B] do
      for j in [i + 1..#B] do
         h := B[i] * B[j] - B[j] * B[i];
         if not IsZero (h) then
            if Commute then return false; end if;
            vprint Infinite: "Construct nullspace ";
            U := ModuleViaNullSpace (S, h);
            vprint Infinite: "Submodule has dimension ", Dimension (U);
            if Dimension (U) eq 0 then return false, CList, Blocks; end if;
            // return ProcessBlockDiagonals (K, S, U, B);
            flag, CList, Blocks := ProcessBlockDiagonals (K, S, U, B, CList, Blocks);
            if flag then 
               return flag, CList, Blocks;
            else 
               return flag, _, _; 
            end if;
         end if;
      end for;
   end for;
   if #CList eq 0 then CList := [<Identity (K), Degree (K)>]; end if;
   return true, CList, Blocks;
end function;

IsMonomialGroup := function (G)
   return forall{g : g in Generators (G) | IsMonomial (g)};
end function;

intrinsic IsCompletelyReducible (G :: GrpMat : SolubleByFinite := false,
   OrderLimit := 10^15, Small := 10^6, Short := 30, Presentation := "CT", 
   Nilpotent := false, NilpotentByFinite := false, AbelianByFinite := false)
-> BoolElt 
{
   is G completely reducible? return true or false;
   one of the following properties is a requirement: 
   Nilpotent: G is nilpotent; 
   SolubleByFinite: G is soluble-by-finite; 
   NilpotentByFinite: G is nilpotent-by-finite;
   AbelianByFinite: G is abelian-by-finite;
   Presentation: one of "CT", "FP", "PC" to dictate method of construction;
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation
}
   flag := IsKnownCR (G);
   if flag cmpeq true or flag cmpeq false then return flag; end if;

   p := Characteristic (BaseRing (G));
   if p eq 0 and IsKnownFinite (G) then return true; end if;

   if IsMonomialGroup (G) then 
      SetVirtualValues (G, "CR", true); return true;
   end if;

   if Nilpotent then 
      S, U := JordanDecompositionForGroup (G);
      flag := IsTrivial (U);
      SetVirtualValues (G, "CR", flag); return flag;
   end if;

   if not IsValidInput (G) then error
      "IsCompletelyReducible: incorrect input";
   end if;

   /* we may be able to decide readily that G is soluble-by-finite */
   if IsKnownSF (G) cmpne false and 
      (IsAbelian (G) or IsUpperTriangularGroup (G) or IsMonomialGroup (G)) then
      SetVirtualValues (G, "SF", true); 
   end if;

   good := IsKnownSF (G) cmpeq true or IsKnownNF (G) cmpeq true or 
           IsKnownAF (G) cmpeq true or IsKnownFinite (G) or 
           (SolubleByFinite or NilpotentByFinite or AbelianByFinite);
   vprint Infinite: "Algorithm applicable? ", good;
   if not good then 
      error "Can decide only if G is known to be soluble-by-finite";
   end if;

   if assigned G`Congruence and assigned G`Congruence`Image and 
      assigned G`Congruence`Subgroup and G`Congruence`Virtual eq true then 
      Data := G`Congruence; I := Data`Image;
      if (p gt 0) and (CompositionTreeOrder (I) mod p eq 0) then 
         error "Cannot decide since image order is divisible by characteristic";
      end if;
      K := Data`Subgroup; 
   else
      flag, K, I, tau := CongruenceSubgroup (G: Virtual := true, 
         OrderLimit := OrderLimit, Presentation := Presentation, 
         Small := Small, Short := Short, Reducible := p gt 0);
      if not flag then 
         error "Cannot decide since image order is divisible by characteristic";
      end if;
      G`Congruence`Subgroup := K;
   end if;

   if p eq 0 and IsKnownFinite (G) then return true; end if;

   if p eq 0 and ((NilpotentByFinite or IsKnownNF (G) cmpeq true) 
              or ( AbelianByFinite   or IsKnownAF (G) cmpeq true)) then
      _, U := JordanDecompositionForGroup (K);
      flag := MyIsTrivial (U);
      SetVirtualValues (G, "CR", flag);
      return flag;
   end if;

   vprint Infinite: "Construct basis for closure of enveloping algebra";
   S := [G.i: i in [1..Ngens (G)]];
   B := BasisEnvelopingAlgebraClosure (G, K, S);

   flag := ExploreBasis (K, S, B, [* *], []: Commute := true);
   if not flag then 
      SetVirtualValues (G, "CR", flag); return false;
   end if;

   vprint Infinite: "Test if basis elements are diagonalisable";
   flag := forall{i : i in [1..#B] | IsDiagonalisable (B[i])};
   SetVirtualValues (G, "CR", flag);
   return flag;
end intrinsic;

/* return true if <K>^G is abelian, otherwise false */

IsAbelianClosure := function (G, K)
   if MyIsTrivial (K) then return true, []; end if;
   vprint Infinite: "Construct basis for closure of enveloping algebra";
   S := [G.i: i in [1..Ngens (G)]];
   B := BasisEnvelopingAlgebraClosure (G, K, S);
   return ExploreBasis (K, S, B, [* *], []: Commute := true), B; 
end function;

/* return true if <K>^G is unipotent, otherwise false */
    
IsUnipotentClosure := function (G, K)
   if MyIsTrivial (K) then return true, []; end if;
   MA := MatrixAlgebra (BaseRing (K), Degree (K));
   id := Identity (MA);
   gens := [MA | K.i: i in [1..Ngens (K)]];
   Kbar := sub<MA | [gens[i] - id: i in [1..#gens]]>;
   S := [G.i: i in [1..Ngens (G)]];
   B := BasisEnvelopingAlgebraClosure (G, Kbar, S: Shadow := false);
   if #B eq 0 then return true, B; end if;

   n := Degree (G);
   if #B gt n * (n - 1) / 2 then return false, B; end if;
   zero := Zero (Parent (B[1]));
   if exists{b : b in B | b^n ne zero} then return false, B; end if;
   
   gens := [MA | b + id: b in B];
   M := sub<Generic (G) | gens>;
   return IsUnipotent (M), B;
end function;

intrinsic IsNilpotentByFinite (G :: GrpMat : Presentation := "CT", 
   OrderLimit := 10^15, Small := 10^6, Short := 30) -> BoolElt
{ return true if G is nilpotent-by-finite, else false;
   Presentation: one of "CT", "FP", "PC" to dictate method of construction;
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation;
}
   if IsKnownFinite (G) then return true; end if;

   flag := IsKnownNF (G); 
   if flag cmpeq true or flag cmpeq false then return flag; end if;

   if IsAbelian (G) or IsUpperTriangularGroup (G) or IsMonomialGroup (G) then 
      SetVirtualValues (G, "NF", true); 
      return true; 
   end if;

   /* completely reducible? all 3 of SF, NF, AF are equivalent */
   if IsKnownCR (G) cmpeq true then
      if assigned G`Congruence`SolubleByFinite then 
         flag := G`Congruence`SolubleByFinite; 
         G`Congruence`NilpotentByFinite := flag;
         G`Congruence`AbelianByFinite := flag;
      end if;
   end if;

   K := BaseRing (G);
   if Characteristic (K) gt 0 then
      valid := false;
   elif ISA (Type (K), FldFun) then
      F := BaseRing (K);
      valid := Rank (F) eq 1;
   elif ISA (Type (K), FldFunRat) then
      valid := Rank (K) eq 1;
   else 
      valid := (ISA (Type (K), RngInt) or ISA (Type (K), FldRat) 
               or ISA (Type (K), FldNum));
   end if;
      
   if not valid then 
      error "IsNilpotentByFinite: coefficent field is not valid";
   end if;

   if assigned G`Congruence and assigned G`Congruence`Subgroup and 
      G`Congruence`Virtual eq true then 
      Data := G`Congruence; K := Data`Subgroup;
   else
      vprint Infinite: "Construct congruence subgroup";
      flag, K, I, tau := CongruenceSubgroup (G: Virtual := true,
         OrderLimit := OrderLimit, Presentation := Presentation, 
         Small := Small, Short := Short);
   end if;

   if IsKnownFinite (G) then 
      SetVirtualValues (G, "NF", true); return true; 
   end if;

   vprint Infinite: "Computing Jordan decomposition ...";
   S, U := JordanDecompositionForGroup (K);

   vprint Infinite: "Now check closure is abelian ...";
   flag, SB := IsAbelianClosure (G, S); 
   if not flag then SetVirtualValues (G, "NF", false); return false; end if;

   vprint Infinite: "Now check closure is unipotent ...";
   flag, SU := IsUnipotentClosure (G, U); 
   if not flag then SetVirtualValues (G, "NF", false); return false; end if;
   
   flag := forall{<i,j> : i in [1..#SB], j in [1..#SU] | 
                          SB[i] * SU[j] - SU[j] * SB[i] eq 0};

   /* completely reducible? all 3 of SF, NF, AF are equivalent */
   if IsKnownCR (G) cmpeq true then
      G`Congruence`SolubleByFinite := flag;
      G`Congruence`NilpotentByFinite := flag;
      G`Congruence`AbelianByFinite := flag;
   else 
      SetVirtualValues (G, "NF", flag); 
   end if;

   return flag;
end intrinsic;

intrinsic IsAbelianByFinite (G:: GrpMat : Presentation := "CT", 
   OrderLimit := 10^15, Small := 10^6, Short := 30) -> BoolElt
{  return true if G is abelian-by-finite, else false; 
   Presentation: one of "CT", "FP", "PC" to dictate method of construction;
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation;
}
   if IsKnownFinite (G) then return true; end if;

   flag := IsKnownAF (G); 
   if flag cmpeq true or flag cmpeq false then return flag; end if;

   if IsAbelian (G) or IsMonomialGroup (G) then 
      SetVirtualValues (G, "AF", true); return true; 
   end if;

   /* completely reducible? all 3 of SF, NF, AF are equivalent */
   if IsKnownCR (G) cmpeq true then
      if assigned G`Congruence`SolubleByFinite then 
         flag := G`Congruence`SolubleByFinite; 
         G`Congruence`NilpotentByFinite := flag;
         G`Congruence`AbelianByFinite := flag;
      elif assigned G`Congruence`NilpotentByFinite then 
         flag := G`Congruence`NilpotentByFinite; 
         G`Congruence`SolubleByFinite := flag;
         G`Congruence`AbelianByFinite := flag;
      end if;
      return flag;
   end if;

   K := BaseRing (G);
   if Characteristic (K) gt 0 then
      valid := false;
   elif ISA (Type (K), FldFun) then
      F := BaseRing (K);
      valid := Rank (F) eq 1;
   elif ISA (Type (K), FldFunRat) then
      valid := Rank (K) eq 1;
   else 
      valid := (ISA (Type (K), RngInt) or ISA (Type (K), FldRat) 
               or ISA (Type (K), FldNum));
   end if;
      
   if not valid then 
      error "IsAbelianByFinite: coefficent field is not valid";
   end if;

   if assigned G`Congruence and assigned G`Congruence`Subgroup and 
      G`Congruence`Virtual eq true then 
      Data := G`Congruence; K := Data`Subgroup;
   else
      vprint Infinite: "Construct congruence subgroup";
      flag, K, I, tau := CongruenceSubgroup (G: Virtual := true,
         OrderLimit := OrderLimit, Presentation := Presentation, 
         Small := Small, Short := Short);
      G`Congruence`Subgroup := K;
   end if;

   if IsKnownFinite (G) then return true; end if;
   
   flag := IsAbelianClosure (G, K); 
   
   /* completely reducible? all 3 of SF, NF, AF are equivalent */
   if IsKnownCR (G) cmpeq true then
      G`Congruence`SolubleByFinite := flag;
      G`Congruence`NilpotentByFinite := flag;
      G`Congruence`AbelianByFinite := flag;
   else 
      SetVirtualValues (G, "AF", flag);
   end if;

   return flag;
end intrinsic;

intrinsic IsCentralByFinite (G:: GrpMat: CompletelyReducible := false, 
   Presentation := "CT", OrderLimit := 10^15, Small := 10^6, Short := 30) 
-> BoolElt
{ is G central-by-finite? return true or false;
   CompletelyReducible: G is completely reducible;
   Presentation: one of "CT", "FP", "PC" to dictate method of construction;
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation
}
   if IsKnownFinite (G) then return true; end if;

   flag := IsKnownCF (G); 
   if flag cmpeq true or flag cmpeq false then return flag; end if;

   if IsAbelian (G) then 
      SetVirtualValues (G, "CF", true); return true; 
   end if;

   if not IsValidInput (G) then 
      error "IsCentralByFinite: incorrect input";
   end if;

   p := Characteristic (BaseRing (G));

   /* fast test for completely reducible */
   if IsMonomialGroup (G) then SetVirtualValues (G, "CR", true); end if;

   /* can test under the following hypotheses */
   valid := p eq 0 or (p gt 0 and (CompletelyReducible or IsKnownCR (G) cmpeq true)); 
   if not valid then 
      error "Algorithm in char > 0 applies only to completely reducible groups"; 
   end if;

   if HasKnownCongruenceSubgroup (G) and 
      ((p gt 0 and G`Congruence`Virtual) or 
       (p eq 0 and (G`Congruence`Virtual or G`Congruence`Selberg))) then 
      Data := G`Congruence; K := Data`Subgroup;
      flag := AllCommute (G, K);
   else 
      vprint Infinite: "Construct congruence subgroup";
      flag, K, I, tau := CongruenceSubgroup (G: Selberg := true, 
         OrderLimit := OrderLimit, Presentation := Presentation, 
         Small := Small, Short := Short,
         Virtual := p gt 0, CentralByFinite := true);
   end if;
   SetVirtualValues (G, "CF", flag);
   return flag;
end intrinsic;
