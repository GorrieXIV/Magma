freeze;

/* maximal subgroups of ParentName in list L */

ListMaximals := function (G, ParentName, L: UserGenerators := []) 
   if UserGenerators eq [] then UserGenerators := [G.1, G.2]; end if;
   X := []; Names := []; Orders := []; Index := [];
   for i in [1..#L] do
      if assigned L[i]`Parent and L[i]`Parent eq ParentName and #L[i]`generators gt 0 then 
         F := Parent (L[i]`generators[1]);
         a := F.1; b := F.2;
         f := hom <F -> G | UserGenerators>;
         images := [f (w): w in L[i]`generators];
         X[#X + 1] := sub <G | images>;
         Names[#Names + 1] := L[i]`Name;
         Orders[#Orders + 1] := L[i]`Order;
         Index[#Index + 1] := L[i]`Index;
      end if;
   end for;
   return X, Names, Orders, Index;
end function;

/* set up all subgroups of G stored in L */
ListAll := function (G, GroupName, L)
   S, Names, Orders, Index := ListMaximals (G, GroupName, L);
   for i in [1..#S] do
      T, TNames, TOrders, TIndex := $$ (S[i], Names[i], L);
      S cat:= T; Names cat:= TNames; 
      Orders cat:= TOrders; Index cat:= TIndex;
   end for;
   return S, Names, Orders, Index; 
end function;

