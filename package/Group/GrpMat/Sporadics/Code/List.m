freeze;

import "recformat.m": SporadicRF;

/* maximal subgroups of ParentName in list L */

ListMaximals := function (G, ParentName, L: UserGenerators := []) 
   if UserGenerators eq [] then UserGenerators := [G.1, G.2]; end if;
   X := []; 
   for i in [1..#L] do
      if assigned L[i]`parent and L[i]`parent eq ParentName and #L[i]`generators gt 0 then 
         F := Parent (L[i]`generators[1]);
         a := F.1; b := F.2;
         f := hom <F -> G | UserGenerators>;
         images := [f (w): w in L[i]`generators];
         S := rec <SporadicRF | name := L[i]`name, order := L[i]`order, 
         parent := L[i]`parent, index := L[i]`index, group := sub <G | images>>;
         Append (~X, S);
      end if;
   end for;
   return X;
end function;

/* set up all subgroups of G stored in L */
ListAll := function (G, GroupName, L)
   S := ListMaximals (G, GroupName, L);
   for i in [1..#S] do
      S cat:= $$ (S[i]`group, S[i]`name, L);
   end for;
   return S;
end function;
