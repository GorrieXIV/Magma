freeze;

// import "../Smash/random.m": RandomElement;
import "../Smash/minblocks.m": MinBlocks;
import "../Smash/minblocks.m": IsBlockSystem;

/* given irreducible matrix group G and collection of subspaces of 
   associated vector space V, write V as direct sum of subspaces of V */

procedure DirectSumSpaces (G, ~Spaces, ~flag)

   S := Spaces[1];
   d := Dimension (S);
   k := Ceiling (Degree (S) / d);
   NmrTries := 100;
   flag := true;

   P := RandomProcess (G);
   while #Spaces lt k do

      n := #Spaces;
      SumSpaces := &+[Spaces[i] : i in [1..n]];

      bound := n * d;

      count := 0;
      repeat 
         count +:= 1;
         // g := RandomElement (G);
         g := Random (P);
         I := S^g;
         Sum := SumSpaces + I;
         D := Dimension (Sum);
      until D gt bound or count gt NmrTries;
 
      /* do we have a submodule for G? */
      if D le bound then
         for i in [1..Ngens (G)] do 
            I := S^G.i;
            Sum := SumSpaces + I;
            D := Dimension (Sum);
            if D gt bound then break i; end if;
         end for;
      end if;
 
      /* yes, so this subspace is not a flat */
      if D le bound then flag := false; return; end if;

      if (D ne (n + 1) * d) then
         Spaces := [SumSpaces meet I];
         $$ (G, ~Spaces, ~flag);
         return; 
      end if;

      Append (~Spaces, I);

   end while;
  
end procedure;

/* flag is set false if we fail to express the underlying vector 
   space as a direct sum of images of the contents of Spaces; 
   this may happen if G acts reducibly or G is imprimitive */

procedure ObtainDirectSumSpaces (G, ~Spaces, ~flag)

   DirectSumSpaces (G, ~Spaces, ~flag);

   /* have we found a submodule? */
   if flag eq false then return; end if;

   F := BaseRing (G);
   d := Degree (G);

   /* have we found a block? */
   b := sub <VectorSpace (F, d) | Spaces[1]>;
   x := MinBlocks (G, Basis (b));
   if IsBlockSystem (x) then flag := false; end if;

end procedure;
