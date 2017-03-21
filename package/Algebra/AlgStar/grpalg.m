freeze;

   /*--- File constructor group algebras as *-algebras ---*/

intrinsic GroupAlgebraAsStarAlgebra (R::Rng, G::Grp) -> AlgGrp

   { The group algebra R[G] equipped with its natural involution. }
   
     A := GroupAlgebra (R, G);
     star := StarOnGroupAlgebra (A);
                      
return A;

end intrinsic;


/*
  The following function constructs the right regular 
  representation of R[G] as an R-matrix of degree |G| 
  equipped with its natural involution. It also 
  constructs the natural inverse *-isomorphisms to
  and from the natural copy of R[G]
*/

GroupAlgebraAsMatrixStarAlgebra := function (A)
   
     assert Type (A) eq AlgGrp;

     BasA := Basis (A);
     
     n := #BasA;
     MA := MatrixAlgebra (BaseRing (A), n);
     gens := [ ];
     
     for i in [1..n] do
       
         g := BasA[i];
         X := MA!0;    
         for j in [1..n] do
            l := Position (BasA, BasA[j] * g);
            X[j][l] := 1;
         end for;
         Append (~gens, X);
         
     end for;
       
     MatA := sub < MA | gens >;
     
     /* define the natural involution on {MatA> */
     MS := RMatrixSpace (BaseRing (A), n, n);
     MS := RMatrixSpaceWithBasis ([ MS!gens[i] : i in [1..n] ]);
     igens := [ gens[i]^-1 : i in [1..n] ];  
     MatA`Star := hom < MatA -> MatA | 
                      x :-> &+ [ c[i] * igens[i] : i in [1..n] ]
                      where c := Coordinates (MS, MS!x) >;

     /* construct natural inverse *-isomorphisms <A> <-> <MatA> */
     MatAtoA := hom < MatA -> A | 
                        x :-> &+ [ c[i] * BasA[i] : i in [1..n] ]    
                        where c := Coordinates (MS, MS!x) >;
     AtoMatA := hom < A -> MatA |                 
                     a :-> &+ [ c[i] * gens[i] : i in [1..n] ]
                     where c := Coefficients (a) >;

return MatA, AtoMatA, MatAtoA;

end function;
