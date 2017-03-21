freeze;

/* is the orbit of U under action of G smaller than Limit? */

IsOrbitSmall := function (G, U: Limit := 10)

   O := {@ U @};
   k := 1; DIV := 1;
  
   /* construct the orbit and stabiliser */
   while k le #O do
      pt := O[k]; 
      for i in [1..Ngens (G)] do
         /* compute the image of a point */
         im := pt * G.i;
         Include (~O, im);
      end for;
      if #O gt Limit then return false, #O; end if;
      k +:= 1;
   end while;

   return true, #O;

end function;

/* return i-th entry of submodule lattice L as subspace */

LatticeSubmoduleToSubspace := function (G, L, i)
   d := Degree (G);
   F := BaseRing (G);
   V := VectorSpace (F, d);
   B := Morphism (L!i);
   Base := [V!B[i]: i in [1..Dimension(Domain(B))]];
   S := sub <V | Base>;
   return S, B;
end function;

/* return submodule S of M as subspace */

SubmoduleToSubspace := function (M, S)
   d := Dimension (M);
   F := BaseRing (M);
   V := VectorSpace (F, d);
   Base := [V!Eltseq (M!S.i): i in [1..Dimension(S)]];
   MA := RMatrixSpace (F, Dimension (S), d);
   return sub <V | Base>, MA!&cat ([Eltseq (x): x in Base]); 
end function;

/* return submodule S of M as matrix */

SubmoduleToMatrix := function (M, S)
   d := Dimension (M);
   F := BaseRing (M);
   V := VectorSpace (F, d);
   Base := &cat[Eltseq (V!Eltseq (M!S.i)): i in [1..Dimension(S)]];
   return RMatrixSpace (F, Dimension (S), d) ! Base;
end function;

/* set up those subgroups of G described in L having named parent */

SetupSubgroups := function (G, parent, L)
   X := []; Names := [* *]; Ranges := []; Orders := [];
   for i in [1..#L] do
      if assigned L[i]`parent and L[i]`parent eq parent then 
         F := Parent (L[i]`generators[1]);
         a := F.1; b := F.2;
         f := hom <F -> G | [G.1, G.2]>;
         images := [f (w): w in L[i]`generators];
         X[#X + 1] := sub <G | images>;
         Names[#Names + 1] := L[i]`name;
         index := L[i]`index;
         /* permissible range for random check */
         Ranges[#Ranges + 1] := [index div 10 .. index * 10];
         Orders[#Orders + 1] := L[i]`order;
      end if;
   end for;
   return X, Names, Ranges, Orders;
end function;

/* confirm data stored in L */

VerifyData := function (G, GroupName, L)
    S, Names, _, Orders := SetupSubgroups (G, GroupName, L);
    if #S gt 0 then "Names ", Names; "Orders ", Orders; end if;
    for i in [1..#S] do 
       if #S[i] ne Orders[i] then
          "Actual order for ", Names[i], " is ", #S[i];
          error "Error in stored data";
       else
          Names[i], "correct";
          flag := $$ (S[i], Names[i], L);
       end if;
    end for;
    return true;
end function;

/* G is (subgroup of) sporadic group having name Name;
   SR is subgroup chain record for sporadic group
      returned by SubgroupChains<Name>;
   level is depth of recursion, initially set to 1;
   points records base points; 
   flag is set to true if base points found */
  
procedure NextStep (G, SR, Name, level, ~points, ~flag)

   // "Group acting on level ", level, ": ", Name;

   LARGE := 100; large := 50; SMALL := 2;
   SmallLength := 10; MinHits := 15;

   Subs, Names, Ranges := SetupSubgroups (G, Name, SR);
   if #Subs eq 0 then flag := true; return; end if;

   F := BaseRing (G);
   d := Degree (G);
   V := VectorSpace (F, d);

   flag := false;

   ActionSubmodule := function (L, j) 
      return Module (L!j), Morphism (L!j);
   end function;

   for i in [1..#Subs] do
      vprint User1: "Consider maximal subgroup ", Names[i], " at level ", level;
      H := Subs[i];

      M := GModule (H);
      CS := CompositionSeries (M);
      vprint User1: "Composition length for maximal subgroup module is ", #CS;
      if #CS eq 1 then continue; end if;

      complete := false;
      smallest := d;
      if #CS lt SmallLength then 
         L, complete := SubmoduleLattice (M: Limit := 1500);
         dims := [Dimension (L!j) : j in [1..#L]];
         smallest := Minimum ([x : x in dims | x gt 0]);
         reps := SetToSequence (Set (dims));
         Sort (~reps);
         list := [[x : x in [1..#L] | dims[x] eq y]: y in (reps)];
         mult := [<reps[k], #list[k]> : k in [1..#list]];
//         vprint User1: "Lattice: Submodule dimensions / multiplicities are", mult;
         list := &cat (list);
         T := [LatticeSubmoduleToSubspace (G, L, j): j in [1..#L]];
      end if;

      if not complete then 
         CS := [sub<M|>] cat CS;
         dims := [Dimension (CS[j]) : j in [2..#CS]];
//         vprint User1: "Composition series: Submodule dimensions are", dims;
         if Minimum (dims) lt smallest then 
            T := [SubmoduleToSubspace (M, CS[j]): j in [1..#CS]];
            list := [1..#T];
            L := false;
         end if;
      end if;

      for j in [1..#T] do
         U := T[list[j]];
         if Dimension (U) eq 0 then continue; end if;
         vprint User1: "Consider submodule of dimension ", Dimension (U);
         if Degree (U) gt LARGE or Dimension (U) gt large then 
            small, lb := IsOrbitSmall (G, U);
            accept := not small;
            vprint User1: "Size of orbit is at least ", lb;
         else 
            lb, ub, len := EstimateOrbit (G, U: 
                                 NumberCoincidences := MinHits);
            vprint User1: "Estimate of size of orbit is ", lb, ub, len;
            accept := lb gt SMALL and len in Ranges[i];
         end if; 

         if accept then 
            vprint User1: "Accept this point";
            points[level] := U;
            for ell in [1..#list] do 
               if Type (L) eq SubModLat then 
                  SM, m := ActionSubmodule (L, list[ell]);
               else
                  SM := CS[ell];
                  m := SubmoduleToMatrix (M, CS[ell]);
               end if;
               if Dimension (SM) eq 0 then continue; end if;
               K := sub <GL(Dimension (SM), F) | 
                    [ActionGenerator (SM, h): h in [1..Ngens (H)]]>;
               if Ngens (K) ne Ngens (G) then continue; end if;

               vprint User1: "Test level", level + 1, 
                   "with action on module of dim ", Degree (K);
               $$ (K, SR, Names[i], level + 1, ~points, ~flag);
               vprint User1: "Flag from Recurse is ", flag;

               if flag then 
                  for k in [level + 1..#points] do 
                     bp := points[k];
                     if Degree (bp) lt Dimension (M) then 
                         bp := sub <V | [Eltseq (bp.ell * m): 
                                 ell in [1..Dimension (bp)]]>;
                         points[k] := bp;
                     end if;
                  end for;
                  return;
               end if;
            end for; /* ell */
            if flag eq false then break j; end if;
         end if;
      end for;
   end for;

end procedure;
