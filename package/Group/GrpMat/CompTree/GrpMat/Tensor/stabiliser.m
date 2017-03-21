freeze;

// import "../Smash/random.m": RandomElement;
import "../Smash/functions.m": SetMatrixSeed, MatrixSeed;
import "../Smash/misc.m": HashSet;

/* generate those elements whose indices are in List */

procedure GenerateElements (G, List, ~Good)

   local x;

   Good := [];
   P := RandomProcess (G);
   for i in [1..Maximum (List)] do
      x := Random (P);
      if i in List then Append (~Good, x); end if;
   end for;

end procedure;

/* generate elements of set stabiliser of collection of spaces;
   do this by generating NmrImages images of spaces under
   random elements of G */

StabiliserOfSet := function (G, Spaces, NmrImages)

   W := Rep (Spaces);

   if Dimension (W) eq 0 then return G; end if;

   Seed := MatrixSeed (G);
   s1, s2 := GetSeed ();

   Images := [];

   // M := NextPrime (4 * NmrImages div 3);
   /* we're getting too many coincidences */
   M := NextPrime (7 * NmrImages div 3);
   Collisions := [];

   P := RandomProcess (G);
   for i in [1..NmrImages] do
      g := Random (P);
      I := {W^g : W in Spaces};
      index := HashSet (I, M);
      if IsDefined (Collisions, index) eq false then 
         Collisions[index] := []; 
      end if;
      Append (~Collisions[index], i);
   end for;

   Stab := {};

   /* which random elements do we consider? */

   List := &cat [Collisions[i] : i in [1..#Collisions] |
                  IsDefined (Collisions, i) and #Collisions[i] gt 1 ];
   if #List ne 0 then 
      Sort (~List);

      /* get these elements */

// "HERE TWO ARGS ";
   
      SetSeed (s1, s2);
      // SetSeed (s1);
      SetMatrixSeed (G, Seed);
      GenerateElements (G, List, ~Good);
      vprintf Tensor: "We consider %o elements\n", #Good;

      /* now test them */
      for i in [1..#Collisions] do 
         if not IsDefined (Collisions, i) then continue; end if;
         L := Collisions [i];
         if #L eq 1 then continue; end if;

         EltNmr := Position (List, L[1]);
         x := Good[EltNmr];
         xinv := x^-1;
         Im := {W^x : W in Spaces};
         for j in [2..#L] do 
            EltNmr := Position (List, L[j]);
            y := Good[EltNmr];
            Images := {W^y : W in Spaces};
            if Im eq Images then 
               Include (~Stab, y * xinv);
            end if;
         end for;
      end for;
   end if;

   P := GL (Degree (G), BaseRing (G));

   return sub <P | Stab>;

end function;

/* O is either a single space or set of spaces; compute some 
   elements of its stabiliser in G; the Boolean returned 
   indicates whether the whole of G stabilises O */

SpaceStabiliser := function (G, O, Nmr, NmrTries)

   Spaces := Type (O) eq ModTupFld select {O} else O;

   /* which generators of G stabilise Spaces? */
   N := Ngens (G);
   fixed := [G.j : j in [1..N] | {W^G.j : W in Spaces} eq Spaces];
   if #fixed eq N then return G, true; end if;

   P := GL (Degree (G), BaseRing (G));
   H := sub <P | fixed>;

   /* we want to find at least this many elements in one try */
   MinNmrElements := 2;

   i := 1;
   repeat
      K := StabiliserOfSet (G, Spaces, NmrTries * i);
      H := sub <P | H, K>;
      i +:= 1;
   until Ngens (K) gt MinNmrElements or i gt Nmr;

   vprintf Tensor: "We found %o elements of the set stabiliser of the spaces\n", Ngens (H);

   return H, false;

end function;
