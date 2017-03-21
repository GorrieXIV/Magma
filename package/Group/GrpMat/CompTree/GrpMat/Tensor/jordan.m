freeze;

/* return homogenuous components of Jordan form of g 
   and the associated factors of minimal polynomial */

JordanBlocks := function (g)

   J, T, factors := JordanForm (g);
   facs := [factors[i][1] : i in [1..#factors]];
   
   G := Parent (g);
   d := Degree (G);
   F := BaseRing (G);
   V := VectorSpace (F, d);

   Blocks := [[] : i in [1..#facs]];
   offset := 0;
   for i in [1..#facs] do
      fac := factors[i][1];
      pos := Position (facs, fac);
      deg := Degree (fac);
      y := [T[j] : j in [offset + 1 .. offset + deg]];
      Blocks[pos] cat:= y;
      offset +:= deg;
   end for; 

   Spaces := [sub < V | Blocks[i] > : i in [1..#Blocks] | #Blocks[i] ne 0 ];
   Degrees := [Degree (factors[i][1]) : i in [1..#Blocks] | #Blocks[i] ne 0 ];
   return Spaces, Degrees;

end function;
 
FindIntersections := function (S, T)
   return {S[i] meet T[j] : i in [1..#S], j in [1..#T] | 
           Dimension (S[i] meet T[j]) ne 0};

end function;

JordanBlocksSet := function (Elements)

   if #Elements eq 0 then return []; end if;

   Blocks := [JordanBlocks (g) : g in Elements];

   Original := Blocks[1];
   for i in [2..#Blocks] do 
      Original := FindIntersections (Original, Blocks[i]);
   end for;

   return SetToSequence (Original);

end function;
