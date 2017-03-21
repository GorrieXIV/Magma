freeze;

/* sporadic maximal subgroup data verification */

SetUpSubgroups := function (G, ParentName, L)
   X := []; Names := [* *]; Ranges := []; Orders := []; Index := [];
   for i in [1..#L] do
      if assigned L[i]`Parent and L[i]`Parent eq ParentName and #L[i]`generators gt 0 then 
         F := Parent (L[i]`generators[1]);
         a := F.1; b := F.2;
         f := hom <F -> G | [G.1, G.2]>;
         images := [f (w): w in L[i]`generators];
         X[#X + 1] := sub <G | images>;
         Names[#Names + 1] := L[i]`Name;
         index := L[i]`Index;
         Ranges[#Ranges + 1] := [index div 10 .. index * 10];
         Orders[#Orders + 1] := L[i]`Order;
         Index[#Index + 1] := L[i]`Index;
      end if;
   end for;
   return X, Names, Ranges, Orders, Index;
end function;

VerifyData := function (G, L)
    GroupName := L[1]`Name;
    GroupOrder := L[1]`Order;
    S, Names, _, Orders, Index := SetUpSubgroups (G, GroupName, L);
    if #S gt 0 then "Names ", Names; "Orders ", Orders; "Index ", Index; end if;
    for i in [1..#S] do
       NumSi := #S[i];
       orderproblem:=false; indexproblem:=false;
       if NumSi ne Orders[i] then
          orderproblem:=true;
          "actual order for ", Names[i], " is ", NumSi;
          "error in order data";
       end if;
       if not orderproblem and NumSi * Index[i] ne GroupOrder then 
          indexproblem:=true;
          "actual index for ", Names[i], " is ", GroupOrder div NumSi;
          "error in index data";
       end if;
       if not orderproblem and not indexproblem then
          Names[i], "order and index correct";
       end if;
    end for;
    return true;
end function;
