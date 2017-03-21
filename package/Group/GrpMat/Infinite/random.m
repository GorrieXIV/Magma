freeze;

SeedLength := 10; NumberMultiplications := 10;

/* preprocessing for seed */

procedure ScrambleElements (~gens, n)

   NmrGens := #gens;

   for i in [1..n] do
      s := Random ([1..NmrGens - 1]);
      t := Random ([1..NmrGens - 1]);
      if s ne t then 
         u := Random ([1,2]);
         if u eq 1 then 
            gens[s] := gens[s] * gens[t];
         else
            gens[s] := gens[t] * gens[s];
         end if;
      end if;
      gens[NmrGens] *:= gens[s];
   end for; 

end procedure; 

BasicCheck := function (G)

   if Type (G) eq ModGrp then 
      gens := GroupGenerators (G);
   elif Type (G) eq GrpMat or Type (G) eq GrpPerm then 
      gens := SetToSequence (Generators (G));
   else 
      error "Procedure accepts group or G-module only";
   end if;

   if Type (G) eq GrpMat or Type (G) eq GrpPerm then 
      P := Generic (G);
   elif Type (G) eq ModGrp then 
      d, p := BasicParameters (G);
      P := GL (d, p);
   else
      error "Unknown type handed to BasicCheck";
   end if;
  
   return [gens[i] : i in [1..#gens]];

   return gens;

end function;

/* initialise seed for generating random elements */
     
procedure InitialiseSeed (G, SeedLength, n)

   if assigned G`Seed then return; end if;

   gens := BasicCheck (G);

   NmrGens := #gens;
   if #gens ne 0 then 
      Length := Maximum (SeedLength, #gens + 1);
      Seed := [gens[i mod NmrGens + 1] : i in [1..Length]];
      ScrambleElements (~Seed, n);
   else 
      Seed := [Identity (G): i in [1..2]];
   end if;

   G`Seed := Seed;

end procedure; 

/* construct a random element */

MyRandomElement := function (G) 

   InitialiseSeed (G, SeedLength, NumberMultiplications);
   ScrambleElements (~G`Seed, 1);
   return G`Seed[#G`Seed];

end function; 

procedure NormalScrambleElements (~gens, n, G)

   NmrGens := #gens;

   for i in [1..n] do
      s := Random ([1..NmrGens - 1]);
      gens[s] := gens[s]^MyRandomElement (G);
      t := Random ([1..NmrGens - 1]);
      if s ne t then 
         u := Random ([1,2]);
         if u eq 1 then 
            gens[s] := gens[s] * gens[t];
         else
            gens[s] := gens[t] * gens[s];
         end if;
      end if;
      gens[NmrGens] *:= gens[s];
   end for; 

end procedure;

/* initialise seed for generating random elements of 
   normal subgroup N of G */

procedure InitialiseNormalSeed (G, N, SeedLength, n)

   if assigned N`NormalSeed then return; end if;

   gens := BasicCheck (N);
   gl := Generic(G);

   NmrGens := #gens;
   if #gens ne 0 then 
      Length := Maximum (SeedLength, #gens + 1);
      Seed := [gl ! gens[i mod NmrGens + 1] : i in [1..Length]];
      NormalScrambleElements (~Seed, n, G);
   else 
      Seed := [gl ! Identity (G): i in [1..2]];
   end if;

   N`NormalSeed := Seed;

end procedure; 

/* construct a random element of the normal closure of N */

MyNormalSubgroupRandomElement := function (G, N) 

   InitialiseNormalSeed (G, N, SeedLength, NumberMultiplications);
   NormalScrambleElements (~N`NormalSeed, 1, G);
   return N`NormalSeed[#N`NormalSeed];
end function;

/* construct normal closure gens^G */

NormalClosureRandom := function (G, gens: NumberOfElements := 10)
   L := Generic (G);
   if Type (gens) eq GrpMat then N := gens; else N := sub <L | gens>; end if;
  E := [MyNormalSubgroupRandomElement (G, N):
             i in [1..NumberOfElements]];
   N := sub <L | gens, E>;
  gens := [MyRandomElement (N): i in [1..NumberOfElements]];
   return sub <L | gens>;
end function;

