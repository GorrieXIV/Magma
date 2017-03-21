freeze;

     /*--- Carry out standard ring decompositions of algebras. ---*/ 

import "star.m": StarOnBasis; 

import "grpalg.m": GroupAlgebraAsMatrixStarAlgebra;

/*
  Functions for the standard Wedderburn decomposition of matrix 
  algebras were adapted from code provided by Willem de Graaf 
  designed for the more general setting of algebras defined via 
  structure constants. The resulting functions for matrix algebras
  are therefore unlikely to be optimal.

  Functions for Taft decompositions of algebras with involution
  were designed by Peter Brooksbank and James Wilson, and are 
  based closely on Taft's original paper. They use Wedderburn
  decompositions repeatedly.
*/ 
 

                /* ---- Wedderburn decompositions ---- */

/* Wedderburn worker function */

__refine_wedderburn_complement := function (X, J)

assert Dimension (J) eq Ngens (J);
     MA := Generic (J);
     F := BaseRing (MA);
     d := Degree (MA);
     MS := RMatrixSpace (F, d, d);
     
     /* find a basis of <J> relative to <J>^2 */
     JJ := J * J;
     l := Dimension (J) - Dimension (JJ);
     assert l gt 0;
     temp := sub < MS | Basis (JJ) >;
     Jbas := [ MS!x : x in Basis (J) ];
     bas := [];
     while #bas lt l do
         assert exists (i){ j : j in [1..#Jbas] | 
                                       not Jbas[j] in temp  };
         Append (~bas, Jbas[i]);
         temp := sub < MS | Basis (temp) cat [Jbas[i]] >;
         Remove (~Jbas, i);
     end while;
     Jbas := bas cat [MS!x : x in Basis (JJ)];
     MJ := RMatrixSpaceWithBasis (Jbas);

     /* next a nice basis of sp(<X>)<J> */
     bas := [MS!x : x in X] cat Jbas;
     MX := RMatrixSpaceWithBasis (bas);
     n := #X;
     
     /* store the necessary scalar arrays */
     beta := [ [ ] : i in [1..n] ];     // <n> x <n> with entries in F^n
     delta := [ [ ] : i in [1..n] ];    // <n> x <n> with entries in F^l
     for i in [1..n] do
         for j in [1..n] do
             c := Coordinates (MX, MX!(X[i] * X[j]));
             beta[i][j] := [ c[z] : z in [1..n] ];
             delta[i][j] := [ c[z] : z in [n+1..n+l] ];
         end for;
     end for;
   
     lambda := [ [ ] : i in [1..n] ];  
     mu := [ [ ] : i in [1..n] ];   //  both <n> x <l> with entries in F^l
     for i in [1..n] do
         for t in [1..l] do
             c := Coordinates (MJ, MJ!(Jbas[t] * X[i]));
             lambda[i][t] := [ c[z] : z in [1..l] ];
             c := Coordinates (MJ, MJ!(X[i] * Jbas[t]));
             mu[i][t] := [ c[z] : z in [1..l] ];
         end for;
     end for;

     /* write down the system of equations */
     mat := RMatrixSpace (F, n*l, n^2*l)!0;
     vec := VectorSpace (F, n^2*l)!0;
     for i in [1..n] do
         for j in [1..n] do
             for z in [1..l] do
                 col := (i-1)*n*l + (j-1)*l + z;
                 vec[col] := delta[i][j][z];
                 for s in [1..n] do
                    row := (s-1)*l + z;
                    mat[row][col] := mat[row][col] + beta[i][j][s];
                 end for;
                 for t in [1..l] do
                    row := (i-1)*l + t;
                    mat[row][col] := mat[row][col] - lambda[j][t][z];
                    row := (j-1)*l + t;
                    mat[row][col] := mat[row][col] - mu[i][t][z];
                 end for;
             end for;
         end for;
     end for;
       
     /* solve the system */
     isit, sol := IsConsistent (mat, vec);
     assert isit;
     
     /* modify <X> */
     Y := [];
     for i in [1..n] do
         c := [ sol[z] : z in [(i-1)*l+1..i*l] ];
         u := &+ [ c[z] * Jbas[z] : z in [1..l] ];
         Y[i] := X[i] + MA!u;
     end for;

return Y, sub < J | Basis (JJ) >;
end function;


/* a version of the function with the additional parameter "basis" */

myWedderburnDecomposition := function (A : basis := false) 

     if not basis then
         Abas := [ x : x in Basis (A) ];
     else
         Abas := [ A.i : i in [1..Ngens (A)] ];
     end if;

     k := BaseRing (A);
     d := Degree (A);
    
     // compute the Jacobson radical of <A>    
     J := JacobsonRadical (A);
     Jbas := [ x : x in Basis (J) ];     
       
     // first find a vector space complement to <J>
     MS := RMatrixSpace (k, d, d);
     AS := sub < MS | [ MS!(Abas[i]) : i in [1..#Abas] ] >;
     JS := sub < AS | [ AS!(Jbas[i]) : i in [1..#Jbas] ] >;
     XS := Complement (AS, JS);
     X := [ A!x : x in Basis (XS) ];
     B := sub < A | X >;
     
     // now refine the vector space complement to an algebra complement
     B := sub < A | X >;
     Y := X;
     K := J;
     while Dimension (K) gt 0 do
         Y, K := __refine_wedderburn_complement (Y, K);       
     end while;
       
     B, fB := sub < A | Y >;
       
return sub < J | Jbas >, B;
end function;


intrinsic WedderburnDecomposition (A::AlgMat) -> AlgMat , AlgMat

   { Return a ring decomposition A = J + S, 
     where J is the Jacobson radical of A and S is semisimple } 
   
     k := BaseRing (A);
     require IsField (k) : "Base ring of argument 1 not a field";
   
return myWedderburnDecomposition (A : basis := false);

end intrinsic;


intrinsic WedderburnDecomposition (A::AlgGrp) -> AlgGrpSub, AlgGrpSub

   { Return a ring decomposition A = J + S, 
     where J is the Jacobson radical of A and S is semisimple }

     MatA, phi, psi := GroupAlgebraAsMatrixStarAlgebra (A);

     MatJ, MatW := WedderburnDecomposition (MatA);

     J := sub < A | [ MatJ.i @ psi : i in [1..Ngens (MatJ)] ] >;
     W := sub < A | [ MatW.i @ psi : i in [1..Ngens (MatW)] ] >;

return J, W;

end intrinsic;


               /* ---- Wedderburn complements ---- */

               
/* a version of the function with the additional parameter "basis" */          
               
WedderburnComplement := function (A, J : basis := false) 

     if not basis then
         Abas := [ x : x in Basis (A) ];
     else
         Abas := [ A.i : i in [1..Ngens (A)] ];
     end if;

     k := BaseRing (A);
     d := Degree (A);

     /* first find a vector space complement to <J> */
     MS := RMatrixSpace (k, d, d);
     Jbas := [ x : x in Basis (J) ];
     AS := sub < MS | [ MS!(Abas[i]) : i in [1..#Abas] ] >;
     JS := sub < AS | [ AS!(Jbas[i]) : i in [1..#Jbas] ] >;
     XS := Complement (AS, JS);
     
     /* refine vector space complement to an algebra complement */
     MA := MatrixAlgebra (k, d);
     X := [ MA!(XS.i) : i in [1..Ngens (XS)] ];
     B := sub < MA | X >;
     Y := X;
     K := J;
     while Dimension (K) gt 0 do
         Y, K := __refine_wedderburn_complement (Y, K);       
     end while;
       
return sub < MA | Y >;
end function;



                 /* ---- Taft decompositions ---- */

__TD_pi_image := function (MS, pos, x)
     c := Coordinates (MS, MS!x);
return &+[ c[i] * MS.i : i in [1..pos] ];
end function;


intrinsic TaftDecomposition (A::AlgMat) -> AlgMat , AlgMat

   { Return a *-invariant Wedderburn decomposition of the *-ring A }

     require IsStarAlgebra (A) : 
            "argument does not have an assigned involution";

     /* see if <A> has already been recognised as a *-algebra */
     if assigned A`StarAlgebraInfo then
         if assigned A`StarAlgebraInfo`jacobsonRadical then
            if assigned A`StarAlgebraInfo`taftComplement then
               return A`StarAlgebraInfo`jacobsonRadical, 
                           A`StarAlgebraInfo`taftComplement;
            end if;
         end if;
     end if;

     k := BaseRing (A);
     require IsField (k) : "Base ring of argument 1 not a field";
     require Characteristic (k) ne 2 :
                       "Base ring of argument 1 has characteristic 2";
            
     star := A`Star;
    
     /* approximate with Wedderburn complements until *-invariant */

     MS := RMatrixSpace (k, Degree (A), Degree (A));
     count := 0;  
     closed := false;
     D := sub < Generic (A) | Basis (A) >;;
     
     while (not closed) and (count lt Degree (A)) do
       
         count +:= 1;
         J, B := myWedderburnDecomposition (D);
         if count eq 1 then   // store the value of <J>
             JA := J;
         end if;
         Dbas := [ B.i : i in [1..Ngens (B)] ] cat 
                 [ J.i : i in [1..Ngens (J)] ];
         t := Ngens (B);
         DS := RMatrixSpaceWithBasis ([ MS!x : x in Dbas ]);
         pi := hom < D -> B | x :-> B!__TD_pi_image (DS, t, x) >;
         rho := hom < B -> D | x :-> (x + (((x @ star) @ pi) @ star)) / 2 >;
         gens := [ B.i @ rho : i in [1..Ngens (B)] ];
         D := sub < D | gens >;
         bas := Basis (D);
         D := sub < D | bas >;

         /* sanity check: make sure that <D> is closed under <star> */
         assert forall { i : i in [1..Ngens (D)] | D.i @ star in D };
         
         GB := [ B.i @ star : i in [1..Ngens (B)] ];
         closed := GB subset B;
         
     end while;

     assert closed;
     Bstar := StarOnBasis (B, GB);
     B`Star := Bstar;

return JA, B;

end intrinsic;


intrinsic TaftDecomposition (A::AlgGrp) -> AlgGrpSub, AlgGrpSub

  { Return a *-invariant Wedderburn decomposition of the *-ring A }

     if not IsStarAlgebra (A) then
         /* equip <A> with its natural involution */
         star := StarOnGroupAlgebra (A);
     end if; 

     MatA, phi, psi := GroupAlgebraAsMatrixStarAlgebra (A);

     MatJ, MatT := TaftDecomposition (MatA);

     J := sub < A | [ MatJ.i @ psi : i in [1..Ngens (MatJ)] ] >;
     T := sub < A | [ MatT.i @ psi : i in [1..Ngens (MatT)] ] >;

return J, T;

end intrinsic;




                    /* ---- Taft complements ---- */

__TC_pi_image := function (MS, pos, x)
     c := Coordinates (MS, MS!x);
return &+[ c[i] * MS.i : i in [1..pos] ];
end function;


TaftComplement := function (A, J, W)

     k := BaseRing (A);
          
     if Dimension (J) eq 0 then
         phi := hom < W -> W | w :-> w >;
         B := Basis (W);
         return W, phi;
     end if;

     star := A`Star;

     if forall { i : i in [1..Ngens (W)] | (W.i) @ star in W } then
         phi := hom < W -> W | w :-> w >;
         B := Basis (W);
         return W, phi;
     end if;
    
     MS := RMatrixSpace (k, Degree (A), Degree (A));
     closed := false;
     D := A;
     K := J;
     T := W;
     phi := hom < W -> T | w :-> w >;
     
     while (not closed) do

         Dbas := [ T.i : i in [1..Ngens (T)] ] cat 
                 [ K.i : i in [1..Ngens (K)] ];
         DS := RMatrixSpaceWithBasis ([ MS!x : x in Dbas ]);
         pi_old := hom < D -> T | 
                         d :-> T!__TC_pi_image (DS, Ngens (T), d) >;
         rho := hom < T -> D | 
                      t :-> (t + (((t @ star) @ pi_old) @ star)) / 2 >;

         /* modify <D> */
         gens := [ (T.i) @ rho : i in [1..Ngens (T)] ];
         D := sub < Generic (A) | gens >;

         /* sanity check: make sure that <D> is closed under <star> */
         assert forall { i : i in [1..Ngens (D)] | (D.i) @ star in D };

         K := D meet K;
         Kbas := Basis (K);

         /* modify <T> */
         if #Kbas eq 0 then
	    T := D;
            closed := true;
         else
            K := sub < Generic (A) | Kbas >;
            T := WedderburnComplement (D, K);
            Tim := [ (T.i) @ star : i in [1..Ngens (T)] ];
            closed := Tim subset T;
         end if;
           
         /* update <phi> */
         Dbas := [ T.i : i in [1..Ngens (T)] ] cat 
                 [ K.i : i in [1..Ngens (K)] ];
         DS := RMatrixSpaceWithBasis ([ MS!x : x in Dbas ]);
         pi_new := hom < D -> T | x :-> T!__TC_pi_image (DS, Ngens (T), x) >;
         
         phi := hom < W -> T | w :-> ((w @ phi) @ rho) @ pi_new >; 
         
     end while;

     BW := Basis (W);
     T`Star := star;

return T, phi;
end function;


