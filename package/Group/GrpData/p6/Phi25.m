freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


/* Easterfield list for Phi25 */

EasterfieldPhi25 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1

   F := FreeGroup (6);

   Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];

   family := [
   (Alpha[2], Alpha[3]) = Id(F),
   (Alpha[2], Alpha[4]) = Id(F),
   (Alpha[3], Alpha[4]) = Id(F),
   (Alpha[2], Alpha[5]) = Id(F),
   (Alpha[3], Alpha[5]) = Id(F),
   (Alpha[4], Alpha[5]) = Alpha[1],
   (Alpha[2], Alpha[6]) = Alpha[1],
   (Alpha[3], Alpha[6]) = Alpha[2],
   (Alpha[4], Alpha[6]) = Alpha[3],
   (Alpha[5], Alpha[6]) = Id(F),
   Alpha[6]^p = Alpha[5]];

   Pres := [];
///////////////////////////////////////////////////////////////
//Note the nontrivial relations top right of Easterfield's PHd
///////////////////////////////////////////////////////////////

   // (1)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[2]*Alpha[1]^-1,
                  Alpha[6]^(p^2) = Id(F)
              ] >;
   Append (~Pres, Q);

   // (2)
   for y in [1..(p-1) div 2] do
     Q := quo < F | family, [
                    Alpha[4]^p = Alpha[2]*Alpha[1]^(y-1),
                    Alpha[6]^(p^2) = Id(F)
                ] >;
     Append (~Pres, Q);
   end for;

   // (3)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[2],
                  Alpha[6]^(p^2) = Alpha[1]
              ] >;
   Append (~Pres, Q);

   return [pQuotient(q,p,4):q in Pres];

end function;
