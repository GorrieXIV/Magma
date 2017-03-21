freeze;

function SymplecticCBM (G)
   F := BaseRing (G);
   d := Dimension (G);
   M := KMatrixSpace (F, d, d);
   b := Basis (M);
   G := SL (d, F);

   CB := ZeroMatrix (F, d, d);
   for i in [1..d div 2] do
      CB := CB + b[(i-1)*d + 2*i - 1];
   end for;
   for i in [1..d div 2] do
      CB := CB + b[(d div 2)*d + i*d - 2*i + 2];
   end for;
   return G!CB;
end function;

function UnitaryOddCBM (G)
   F := BaseRing (G);
   d := Dimension (G);
   M := KMatrixSpace (F, d, d);
   b := Basis (M);

   CB := ZeroMatrix (F, d, d);
   for i in [1..(d div 2) + 1] do
      CB := CB + b[(i-1)*d + 2*i - 1];
   end for;
   for i in [2..(d div 2) + 1] do
      CB := CB + b[(d div 2)*d + i*d - 2*i + 3];
   end for;

   return GL(d, F)!CB;
end function;

function UnitaryCBM (G)
   F := BaseRing (G);
   d := Dimension (G);
   M := KMatrixSpace (F, d, d);
   b := Basis (M);
   G := SL (d, F);

   CB := ZeroMatrix (F, d, d);
   for i in [1..(d div 2)] do
      CB := CB + b[(i-1)*d + 2*i - 1];
   end for;
   for i in [1..(d div 2)] do
      CB := CB + b[(d div 2)*d + i*d - 2*i + 2];
   end for;
   return G!CB;
end function;

OmegaCBM := function (G)
   F := BaseRing (G);
   w := PrimitiveElement (F);
   d := Dimension (G);
   M := MatrixAlgebra (F, d);
   sl := SL (d, F);

   /* goes from the form defined for G above to the form defined for GG below */
   CB := Zero (M);
   for i in [1..d div 2] do
      CB[i, 2*i - 1] := 1;
   end for;
   for i in [1..d div 2] do
      CB[(d div 2) + i, d - 2*i + 2] := 1;
   end for;
   CB := sl!CB;
   return CB;
end function;
