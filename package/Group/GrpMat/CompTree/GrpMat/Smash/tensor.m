freeze;

import "functions.m": SetTensorProductFlag;
import "functions.m": SetTensorBasis;
import "functions.m": SetGenerators;
import "functions.m": SetTensorFactors;

forward KroneckerFactors;

/* Test to see if we have a tensor product of modules of 
   dimensions dim1 and dim2. If so, return true, else false */

TensorProductDecomposition := function (M, basis, dim1, dim2) 
 
   vprintf Smash: "\nTesting for a tensor product decomposition\n";

   d, F := BasicParameters (M);

   if dim1 * dim2 ne d then
     vprint Smash: "Product of dimensions is incompatible with tensor product";
     return false;
   end if;

   gl1 := GL (dim1, F);
   gl2 := GL (dim2, F);
   invbasis := basis^-1;
   matrices1 := [];
   matrices2 := [];
   matrices := GroupGenerators (M);

   A := MatrixAlgebra(F, d);

   for g in matrices do
     x := basis * (A!g) * invbasis;

     flag, factors := KroneckerFactors (x, dim1, dim2, F);
     if flag eq false then
       vprint Smash: "Failed to find tensor decomposition";
       return false;
     else
       Append (~matrices1, gl1!factors[1]);
       Append (~matrices2, gl2!factors[2]);
     end if;
   end for;
   vprintf Smash: "Module is a tensor product of modules of dimensions %o and %o\n", 
         dim1, dim2;

   SetTensorProductFlag (M, true);
   SetTensorBasis (M, basis);
   m1 := GModule (matrices1);
   SetGenerators (m1, matrices1);
   m2 := GModule (matrices2);
   SetGenerators (m2, matrices2);
   SetTensorFactors (M, [m1, m2]);

   return true;

end function;
       
/* x is an element of a matrix algebra over F of degree dim1*dim2.
   Decide if x is a Kronecker product of 2 matrices of dimensions
   dim1 and dim2 resp., over F. More precisely, we try to find A,  
   a dim1 x dim1 matrix, and B, a dim2 x dim2 matrix,  so that x 
   decomposes into dim1 x dim1 blocks,  with the (k, l)-th block 
   equal to A[k][l] * B, so x is the Kronecker product of A and B.
   If we can find such matrices, we return true, and the pair 
   <A, B>,  where A and B lie in the appropriate algebras over F,
   otherwise we return false. */

KroneckerFactors := function (x, dim1, dim2, F) 
 
   A1 := MatrixAlgebra (F, dim1);
   A2 := MatrixAlgebra (F, dim2);
   z := F!0;
   A := [];
   B := [];

   // first find a position where there's a non-zero entry
   i := 1; j := 1;
   while x[i][j] eq z do
     if j lt dim2 then
        j +:= 1;
     else
       if i lt dim1*dim2 then
         j := 1; i +:= 1;
       else
         vprint Smash: "Error - first column of blocks of matrix is zero";
         return false, _;
       end if;
     end if;
   end while;

   // so x[i][j] ne 0
   y := x[i][j];
   r := (i - 1) mod dim2 + 1; r0 := i - r;
   s := (j - 1) mod dim2 + 1; s0 := j - s;
   for i in [1..dim2] do
     t := (i - 1) * dim2;
     for j in [1..dim2] do
       B[t + j] := x[r0 + i][s0 + j];
     end for;
   end for;
   for k in [1..dim1] do
     t := (k - 1) * dim1;
     for l in [1..dim1] do
       A[t + l] := x[(k - 1) * dim2 + r][(l - 1) * dim2 + s]/y;  
     end for;
   end for;

   A := A1!A; B := A2!B;

   if x ne TensorProduct (A, B) then 
      return false, _; 
   else 
      return true, <A, B>; 
   end if;

end function;
