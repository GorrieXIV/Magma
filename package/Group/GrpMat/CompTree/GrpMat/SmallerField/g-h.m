freeze;

/* revised functions for Glasby-Howlett version of SmallerField; 
   these follow John's improvements; Eamonn O'Brien May 2006 */

function ZProduct (Alpha, Z, k)

   z := Z[1];
   ZAlpha := Z;
   for i := 1 to k-1 do
      ZAlpha := Alpha (ZAlpha);
      z *:= ZAlpha;
   end for;
   return z[1];

end function;

function FindX (Alpha, Z, Y, k)

   X := Y;
   count := 0;
   while count ne (k - 1) do
      X := Y + Z * Alpha (X);
      count +:= 1;
   end while;

   return X;

end function;

/* does G have a representation over a field of degree d? */

function GHLowerFieldTest (G, d)

   K := BaseRing (G);
   m := Degree (G);
   
   p := Characteristic (K);

   R := MatrixAlgebra (K, m);
   Alpha := func<A | FrobeniusImage(A, d)>;

   mod1 := GModule (G, [R ! G.i : i in [1..Ngens(G)]]);
   mod2 := GModule (G, [R ! Alpha (R!G.i) : i in [1..Ngens(G)]]);
   flag, Z := IsIsomorphic (mod1, mod2);
   if not flag then return false, _; end if;

   k := Degree (K) div d;
   lambda := ZProduct (Alpha, Z, k);
 
   F := GF (p, d);
   yes, mu := NormEquation(K, F ! lambda);
   if not yes then error "Error in solving norm equation", K, F, lambda; end if;

   // assert Norm (mu, F) eq lambda;

   Z := mu^(-1) * Z;

   CB := G`SmallerFieldChangeOfBasis; 
   P := Parent (CB);
   GLmK := GL (m, K);
   GLmF := GL (m, F);
   repeat 
      Y := Random (R);
      X := FindX (Alpha, Z, Y, k);
      if Determinant (X) ne 0 then
         assert Z eq X * Alpha (X)^-1;
         Xinv := X^-1;
         H := sub < GLmF | [Xinv * G.i * X : i in [1..Ngens(G)]]>; 
         H`SmallerField := F;
         H`SmallerFieldChangeOfBasis := CB * P ! X;     
         return true, H;
      end if;
   until 1 eq 0;

end function;
