freeze;
 
/* Easterfield list for Phi14*/

import "misc.m": NonQuadraticResidue, EasterfieldPair;



EasterfieldPhi14 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1

   xx, yy := EasterfieldPair (p);
   xx := Z ! xx;
   yy := Z ! yy;

   F := FreeGroup (6);

   Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];

   family := [
   (Alpha[2], Alpha[3]) = Id(F),
   (Alpha[2], Alpha[4]) = Id(F),
   (Alpha[3], Alpha[4]) = Id(F),
   (Alpha[2], Alpha[5]) = Id(F),
   (Alpha[3], Alpha[5]) = Id(F),
   (Alpha[4], Alpha[5]) = Alpha[1],
   (Alpha[2], Alpha[6]) = Id(F),
   (Alpha[3], Alpha[6]) = Alpha[1],
   (Alpha[4], Alpha[6]) = Alpha[2],
   (Alpha[5], Alpha[6]) = Id(F),
   Alpha[2]^p = Alpha[1],
   Alpha[4]^p = Alpha[3],
   Alpha[6]^p = Alpha[5]];

   Pres := [];

   // (1)
   Q := quo < F | family, [
                  Alpha[3]^p = Id(F),
                  Alpha[5]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (2)
   Q := quo < F | family, [
                  Alpha[3]^p = Alpha[1],
                  Alpha[5]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (3)
   Q := quo < F | family, [
                  Alpha[3]^p = Alpha[2],
                  Alpha[5]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   return [pQuotient(q,p,4): q in Pres];

end function;
