freeze;

SeedLength := 10; NumberMultiplications := 100;

/* preprocessing for seed */

procedure ParallelScrambleElements (~gens, ~Gens, n)
   NmrGens := #gens;

   for i in [1..n] do
      s := Random ([1..NmrGens]);
      t := Random ([1..NmrGens]);
      if s ne t then
         u := Random ([1,2]);
         if u eq 1 then
            gens[s] := gens[s] * gens[t];
            Gens[s] := Gens[s] * Gens[t];
         else
            gens[s] := gens[t] * gens[s];
            Gens[s] := Gens[t] * Gens[s];
         end if;
      end if;
     gens[NmrGens] *:= gens[s];
     Gens[NmrGens] *:= Gens[s];
   end for;
end procedure;

/* initialise seed for generating random elements */
procedure ParallelInitialiseSeed (G, A, SeedLength, n)
   if assigned G`Seed and assigned A`Seed then return; end if;

   if Type (G) eq ModGrp then
      gens := GroupGenerators (G);
      Gens := GroupGenerators (A);
   elif Type (G) eq GrpMat or Type (G) eq GrpPerm then
      gens := [G.i: i in [1..Ngens (G)]];
      Gens := [A.i: i in [1..Ngens (A)]];
      assert #gens eq #Gens;
   elif Type (G) eq SeqEnum and Type (A) eq SeqEnum then
      gens := G;
      Gens := A;
   else
      error "Procedure accepts group or G-module only";
   end if;

   NmrGens := #gens;
   if #gens ne 0 then
      Length := Maximum (SeedLength, #gens);
      seed := [gens[i mod NmrGens + 1] : i in [1..Length]];
      Seed := [Gens[i mod NmrGens + 1] : i in [1..Length]];
      ParallelScrambleElements (~seed, ~Seed, n);
   else
      Seed := [];
   end if;

   G`Seed := seed;
   A`Seed := Seed;
end procedure;

/* apply a sequence of operations to construct a random element in G
   and the corresponding element in A under the map G.i -> A.i */
ParallelRandomElement := function (G, A)
   ParallelInitialiseSeed (G, A, SeedLength, NumberMultiplications);
   seed := G`Seed; Seed := A`Seed;
   ParallelScrambleElements (~seed, ~Seed, 1);
   G`Seed := seed; A`Seed := Seed;
   return G`Seed[#(G`Seed)], A`Seed[#(A`Seed)];
end function;
