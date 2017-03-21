freeze;

//$Id:: derived.m 1112 2008-10-14 02:53:47Z jbaa004                          $:

import "basics.m" : InitialiseGroup;

/* construct normal closure gens^G */

MyNormalClosure := function (G, gens: NumberOfElements := 10)
   d := Degree (G);

   if Type (G) eq GrpMat then 
      F := BaseRing (G);
      L := GL (d, F);
   elif Type (G) eq GrpPerm then
      L := Sym (d);
   else
      L := G;
   end if;

   N := sub <L | gens>;
   E := [NormalSubgroupRandomElement (G, N): i in [1..2 * NumberOfElements]];
   N := sub <L | gens, E>;
   P := RandomProcess (N);
   gens := [Random (P): i in [1..NumberOfElements div 2]];
   return sub <L | gens>, P;
end function;

/* derived subgroup of G */

MyDerivedSubgroup := function (G: NumberOfElements := 10)

   gens := [G.i : i in [1..Ngens (G)]];
   gens := {(g, h): g in gens, h in gens};

   N, P := MyNormalClosure (G, gens: NumberOfElements:= NumberOfElements);
   return N, P;
end function;

/* normal generating set for derived group of G */

MyDerivedSubgroupWithWords := function (G: NumberOfElements := 10) 

   d := Degree (G);
   F := BaseRing (G);
   P := GL (d, F);
   gens := []; words := [];
   U := UserGenerators (G);
   S := G`SLPGroup;
   n := #U;
   Limit := Minimum (2 * n, n + 10);
   nmr := 0;
   repeat
      nmr +:= 1;
      x, w := RandomWord (G);
      for i in [1..#U] do 
         c := (P!U[i], x);
         if not (c in gens) and c ne Id (G) then 
            Append (~gens, c);
            Append (~words, (S.i, w));
         end if;
      end for;
   until nmr ge NumberOfElements or #gens ge Limit;

   D := sub <GL (d, F) | gens>;
   InitialiseGroup (D);
   D`UserGenerators := gens;
   D`UserWords := words;
   assert Ngens (D) eq #gens;
   return D;
end function;
