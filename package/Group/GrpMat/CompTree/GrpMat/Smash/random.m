freeze;
 
import "smash-spec.m": SeedLength, NumberMultiplications;    

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
  
   return [P!gens[i] : i in [1..#gens]];

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

RandomElement := function (G) 

   InitialiseSeed (G, SeedLength, NumberMultiplications);
   ScrambleElements (~G`Seed, 1);
   return G`Seed[#G`Seed];

end function; 

procedure NormalScrambleElements (~gens, n, G)

   NmrGens := #gens;

   for i in [1..n] do
      s := Random ([1..NmrGens - 1]);
      gens[s] := gens[s]^RandomElement (G);
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

intrinsic NormalSubgroupRandomElement (G :: GrpMat, N :: GrpMat) -> GrpMatElt 
{return random element of the normal closure of N in G}

   InitialiseNormalSeed (G, N, SeedLength, NumberMultiplications);
   NormalScrambleElements (~N`NormalSeed, 1, G);
   return N`NormalSeed[#N`NormalSeed];
end intrinsic;

intrinsic NormalSubgroupRandomElement (G :: GrpPerm, N :: GrpPerm) -> 
              GrpPermElt 
{return random element of the normal closure of N in G}

   InitialiseNormalSeed (G, N, SeedLength, NumberMultiplications);
   NormalScrambleElements (~N`NormalSeed, 1, G);
   return N`NormalSeed[#N`NormalSeed];
end intrinsic;

/* choose SampleSize non-trivial random elements */

ChooseRandomElements := function (G, SampleSize: NonScalar := false)
   
   Elts := []; 
   if Type (G) eq ModGrp then G := Group (G); end if;
   id := Identity (G);
   P := RandomProcess (G);
   repeat 
      // g := RandomElement (G);
      g := Random (G);
      if (NonScalar and  IsScalar (g) eq false) then
            Append (~Elts, g);
      elif (NonScalar eq false and g ne id) then 
         Append (~Elts, g);
      end if;
   until #Elts eq SampleSize;

   return Elts;

end function;

/* return the conjugate of a random element of the set S by
   a random element of the group G */

RandomConjugate := function (G, S)
   if #S eq 0 then error "Error in RandomConjugate S is empty"; end if;
   P := RandomProcess (G);
   g := Random (P);
   S := sub <Generic (G) | S>;
   PS := RandomProcess (S);
   h := Random (PS);
   return g^-1 * h * g;
end function;

/* used only by function listed below */

MyRandomConjugate := function (G, S)

   if #S eq 0 then error "Error in RandomConjugate S is empty"; end if;

   g := RandomElement (G);
   d, F := BasicParameters (G);
   S := sub <GL (d, F) | S>;
   h := Random (S);
   return g^-1 * h * g;

end function;

/* find a random conjugate  of a random element of S by a random
   element of G that doesn't fix the subspace W, and add it to S */

AddRandomTranslatingConjugate := procedure (G, ~S, W)

  RS := RowSpace (W);

  ct := 0;
  repeat
     g := MyRandomConjugate (G, S);
     ct +:= 1;
  until RowSpace (W * g) ne RS or ct eq 10;

  Append (~S, g);
end procedure;
