freeze;

    /*--- file contains useful miscellaneous functions ---*/


/* computes solutions to system Q.A + B.Q^t = 0 */
SolveSystem := function (A, B)
     n := Nrows (A);
     f := BaseRing (A);
     W := VectorSpace (f, n^2);
     mat := [];
     for i in [1..n] do
         for j in [1..n] do
            row := W!0;
            for k in [1..n] do
               row[(i-1)*n+k] := row[(i-1)*n+k] + A[k][j];
               row[(j-1)*n+k] := row[(j-1)*n+k] + B[i][k];
            end for;
            Append (~mat, row);
         end for;
     end for;
     mat := Matrix (mat);
     mat := Transpose (mat);
return Nullspace (mat);
end function;


/* return algebra induced by <alg> on invariant subspace <X> */
InducedAlgebra := function (alg, X)
    MA := MatrixAlgebra (BaseRing (alg), Dimension (X));
    gens := [ ];
    for i in [1..Ngens (alg)] do
       ims := [ ];
       for j in [1..Ngens (X)] do
          Append (~ims, Coordinates (X, X.j * alg.i));
       end for;
       Append (~gens, MA!Matrix (ims));
    end for; 
return sub < MA | gens >;
end function;


/* map on defining generators extends to iso <algA> -> <algB> */
AlgebraIsomorphism := function (algA, algB)
     MSA := KMatrixSpace (BaseRing (algA), Degree (algA), Degree (algA));
     MSB := KMatrixSpace (BaseRing (algB), Degree (algB), Degree (algB));
     spA := KMatrixSpaceWithBasis ([ MSA!(algA.i) : i in [1..Ngens (algA)] ]); 
     spB := KMatrixSpaceWithBasis ([ MSB!(algB.i) : i in [1..Ngens (algB)] ]); 
     mapAB := hom < algA -> algB | x :-> 
                   &+ [ c[i] * algB.i : i in [1..Ngens (algB)] ]
                   where c := Coordinates (spA, MSA!x) >;
     mapBA := hom < algB -> algA | x :-> 
                   &+ [ c[i] * algA.i : i in [1..Ngens (algA)] ]
                   where c := Coordinates (spB, MSB!x) >;              
return mapAB, mapBA;
end function;


/* analogue of "Eltseq" that allows one to specify basis */
EltseqWithBasis := function (K, k, bas, x)
     assert #bas eq (Degree (K) div Degree (k));
     W, g := VectorSpace (K, k);
     U := VectorSpaceWithBasis ([ bas[i] @ g : i in [1..#bas] ]);
return Coordinates (U, x @ g);
end function;


/* lifted from composition tree machinery */
__approximate_kernel := function (wdgrp, G, alpha, gamma, delta:
                     NumberRandom := 50, KernelRank := 25)
   P := Generic (G);
   proc := RandomProcess (wdgrp);
   kgens := [];
   for i in [1..NumberRandom] do
       wd := Random (proc);
       a := alpha (wd);
       d := delta (wd);
       c := gamma (a);
       e := delta (c);
       k := d * e^-1;
       Append (~kgens, k);
   end for;
   K := sub <P | kgens >;
   // "Rank of K is ", Ngens (K);
   return [NormalSubgroupRandomElement (G, K) : i in [1..KernelRank]];
end function;


/* 
   <G> = group
   <H> = homomorphic image of <G>
   <Hgens> = images of defining generators of <G>
   <K> = subgroup of H;  
   return preimage of <K> in <G>
*/
PreimageUsingWordGroup := function (G, H, Hgens, K:
                                    NumberRandom := 50, KernelRank := 10)
   P := Generic (G);

   B := SLPGroup (#Hgens);
   tau := InverseWordMap (H);
   index := [ Position (Hgens, H.i) : i in [1..Ngens (H)] ];
   S := Image (tau);
   eta := hom < S -> B | [ B.i : i in index ] >;
   gamma := tau * eta;
   delta := hom < B -> G | [ G.i : i in [1..Ngens (G)] ] >;
   alpha := hom < B -> H | Hgens >;
   ker := __approximate_kernel (B, G, alpha, gamma, delta:
                  NumberRandom := NumberRandom, KernelRank := KernelRank);
   KgensB := [gamma (K.i) : i in [1..Ngens (K)]];
   KgensG := [delta (KgensB[i]) : i in [1..#KgensB]];
   return sub < P | ker, KgensG >;
end function;


/* sets up record formats for the two main data structures we use */
__RF_SETUP := function (string)

     if (string eq "algebra") then

         return recformat < isSimple, 
                            isSemisimple, 
                            jacobsonRadical, 
                            taftComplement, 
			    transitionMatrix,
			    srDegrees,
                            srComponents,
                            alternatingRadical,
                            basicSimpleTypes, 
                            sharpGroupOrder, 
			    sharpGroupGenerators,
                            mapToCorrectField
                          >;

     elif (string eq "simple") then

         return recformat < simpleParameters, 
                              standardSimple, 
                         standardIsomorphism, 
			     standardInverse,
			          sharpGroup,
        		     sharpGroupOrder
                          >;

     elif (string eq "grpalg") then

         return recformat < isSimple, 
                            isSemisimple, 
                            jacobsonRadical,
                            taftComplement, 
                            simpleParameters
                          >;

     else

         return false;

     end if;

end function;

/* Determine positions of a basis for space spanned by given vectors */
IdentifyBasis := function (Q)
     U := Parent (Q[1]);
     flag := exists (i){ j : j in [1..#Q] | Q[j] ne U!0 };
     if not flag then
         return [];
     end if;
     positions := [i];
     remaining := [1..#Q];
     Remove (~remaining, i);
     extends := true;
     while extends do
         W := VectorSpaceWithBasis ([Q[c] : c in positions]);
         extends := exists (j){ i : i in [1..#remaining] | 
                                    not Q[remaining[i]] in W };
         if extends then
             Append (~positions, remaining[j]);
             Remove (~remaining, j);
         end if;
     end while;
return positions;
end function;


/*
   Has the functionality of the GAP function of the same name.
   Maybe this already exists in Magma but I could not find it.
*/
Collected := function (L)
     dist := Set (L);
return [ [ x , #{ i : i in [1..#L] | L[i] eq x } ] : x in dist ];
end function;




