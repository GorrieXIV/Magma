freeze;

import "d2/abelian.m":AbelianList, SingerCycleList;
import "d2/monomial.m":Degree2MonomialList;
import "d2/primitive.m":Degree2PrimitiveList;
import "d2/insoluble.m":Degree2InsolubleList;
import "d3/monomial.m":MonomialList;
import "d3/primitive.m":PrimitiveList;

/* all integer sequences whose i-th entry is in the 
   range [1..M[i] by 1] for i in [1..#M] */

BackTrack := function (M)
 
   if Set (M) eq {1} then return [M]; end if;
 
   offset := 1;
   n := #M;
   m := [1: i in [1..#M]] cat [1];
   original := m;
   min := Minimum (m);
 
   IndexList := [i: i in [1..#M] | M[i] ge min];
   len := #IndexList;
   Append (~IndexList, n + 1);
 
   Solns := [];
   repeat
      index := 1;
      m[IndexList[index]] +:= offset;
      while (index le len and m[IndexList[index]] gt M[IndexList[index]]) do
         m[IndexList[index]] := original[IndexList[index]];
         index +:= 1;
         m[IndexList[index]] +:= offset;                                       
      end while;
      Append (~Solns, Prune (m));
   until (index gt len);
 
   return Solns;
 
end function;

intrinsic IrreducibleSubgroups (n :: RngIntElt, q :: RngIntElt) -> SeqEnum 
{Conjugacy classes of irreducible subgroups of GL(2, q), 
- complete for char >= 5} 

   if n ne 2 then 
       error n, "is not a currently supported dimension (2)"; 
   end if;
   if not IsPrimePower (q) then error q, "must be field size"; end if;
   p := Factorisation (q)[1][1];
   if p lt 5 then "WARNING: subgroup list is not complete"; end if;
   vprint Subgroups: "Set up abelian list ...";
   A := AbelianList (2, q);
   vprint Subgroups: "Set up monomial list ...";
   M := Degree2MonomialList (q);
   vprint Subgroups: "Set up Singer cycle list ...";
   C := SingerCycleList (2, q);
   vprint Subgroups: "Set up primitive list ...";
   P := Degree2PrimitiveList (q);
   vprint Subgroups: "Set up insoluble list ...";
   I := Degree2InsolubleList (q);
   T := A cat M cat C cat P cat I;
   vprint Subgroups: "Total number of subgroups is ", #T;
   // return T, A, M, C, P, I;
   return T;
end intrinsic;

/* soluble irreducible subgroups of GL(2, q) - complete for char p >= 5 */

intrinsic IrreducibleSolubleSubgroups (n:: RngIntElt, q :: RngIntElt) -> SeqEnum
{Conjugacy classes of soluble irreducible subgroups of GL (n, q) for n = 2, 3
- complete for char p >= 5} 

   if n notin {2, 3} then 
       error n, "is not a currently supported dimension (2, 3)"; 
   end if;
   if not IsPrimePower (q) then error q, "must be field size"; end if;
   p := Factorisation (q)[1][1];
   if p lt 5 then "WARNING: subgroup list is not complete"; end if;
   
   vprint Subgroups: "Set up abelian list ...";
   A := AbelianList (n, q);
   vprint Subgroups: "Set up monomial list ...";
   if n eq 2 then
       M := Degree2MonomialList (q);
   else
       M := MonomialList (q);
   end if;
   vprint Subgroups: "Set up Singer cycle list ...";
   C := SingerCycleList (n, q);
   vprint Subgroups: "Set up primitive list ...";
   if n eq 2 then
       P := Degree2PrimitiveList (q);
   else
       P := PrimitiveList (q);
   end if;
   T := A cat M cat C cat P;
   vprint Subgroups: "Total number of subgroups is ", #T;
   // return T, A, M, C, P;
   return T;
end intrinsic;

/*
intrinsic IrreducibleSolubleSubgroups (3, q :: RngIntElt) -> SeqEnum
{Conjugacy classes of soluble irreducible subgroups of GL(3, q) - 
 complete for char p >= 5} 
   if not IsPrimePower (q) then error q, "must be field size"; end if;
   p := Factorisation (q)[1][1];
   if p lt 5 then "WARNING: subgroup list is not complete"; end if;

   vprint Subgroups: "Set up abelian list ...";
   A := AbelianList (3, q);
   vprint Subgroups: "Set up monomial list ...";
   M := MonomialList (q);
   vprint Subgroups: "Set up Singer cycle list ...";
   C := SingerCycleList (3, q);
   vprint Subgroups: "Set up primitive list ...";
   P := PrimitiveList (q);
   T := A cat M cat C cat P;
   vprint Subgroups: "Total number of subgroups is ", #T;
   // return T, A, M, C, P;
   return T;

end intrinsic;
*/
