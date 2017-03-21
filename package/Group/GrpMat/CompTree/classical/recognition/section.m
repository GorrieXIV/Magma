//$Id:: section.m 2060 2010-11-18 10:46:13Z eobr007                          $:

freeze;

/* extract from g rows & columns listed in index */

ExtractAction := function (g, index)
   E := [];
   F := BaseRing (Parent (g));
   if Type (index) eq SetEnum then 
      index := Sort (SetToSequence (index)); 
   end if;
   for i in index do 
      for j in index do
         // E cat:= (ExtractBlock (g, i, j, 1, 1));
         Append (~E, g[i][j]);
      end for;
   end for;
   return GL(#index, F) ! (E);
end function;

/* extract chosen composition factor */

ExtractFactor := function (G, index)
   U := UserGenerators (G);
   if Type (index) eq SetEnum then 
      index := Sort (SetToSequence (index)); 
   end if;
   X := [ExtractAction (U[i], index): i in [1..#U]];
   H := sub < GL(#index, BaseRing (G)) | X >;
   H`UserGenerators := X;
   if assigned G`UserGenerators then
      assert #H`UserGenerators eq #G`UserGenerators;
   end if;
   return H;
end function;

/* return action of matrix g on composition factors of G */

MatrixBlocks := function (G, g)

   CF := G`CompositionFactors;
   COB := G`ChangeOfBasis;
   F := BaseRing (G);
   d := Degree (G);
   e := [* *];
   I := COB * g * COB^-1;
   offset := 0;
   for i in [1..#CF] do 
      k := Dimension (CF[i]);
      e[i] := GL (k, F) ! ExtractBlock (I, offset + 1, offset + 1, k, k);
      offset +:= k;
   end for;
   return e;
end function;

