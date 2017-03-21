freeze;
 
/* Easterfield list for Phi13;
   case (7) amended from Easterfield to produce p - 1 groups */

import "misc.m": NonQuadraticResidue, EasterfieldPair;



EasterfieldPhi13 := function (p)

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
   (Alpha[3], Alpha[5]) = Alpha[1],
   (Alpha[4], Alpha[5]) = Alpha[2],
   (Alpha[2], Alpha[6]) = Id(F),
   (Alpha[3], Alpha[6]) = Alpha[2],
   (Alpha[4], Alpha[6]) = Id(F),
   (Alpha[5], Alpha[6]) = Id(F)];

   Pres := [];

   // (1)
   Q := quo < F | family, [
                  Alpha[3]^p = Id(F),
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (2)
   Q := quo < F | family, [
                  Alpha[3]^p = Alpha[2],
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (3)
   Q := quo < F | family, [
                  Alpha[3]^p = Alpha[1],
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (4)
   Q := quo < F | family, [
                  Alpha[3]^p = Id(F),
                  Alpha[4]^p = Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (5)
   Q := quo < F | family, [
                  Alpha[3]^p = Id(F),
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (6)
   Q := quo < F | family, [
                  Alpha[3]^p = Alpha[1],
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Alpha[2],
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (7)
   for x in [1..p - 1] do 
      Q := quo < F | family, [
                  Alpha[3]^p = Alpha[1]^x,
                  Alpha[4]^p = Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
      Append (~Pres, Q);
   end for;

   // (8)
   for x in [1,la] do
     Q := quo < F | family, [
                    Alpha[3]^p = Alpha[2],
                    Alpha[4]^p = Alpha[1]^x,
                    Alpha[5]^p = Id(F),
                    Alpha[6]^p = Id(F)
                ] >;
     Append (~Pres, Q);
   end for;

   // (9)
   Q := quo < F | family, [
                  Alpha[3]^p = Alpha[1],
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);

   // (10)
   Q := quo < F | family, [
                  Alpha[3]^p = Alpha[2],
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (11)
   Q := quo < F | family, [
                  Alpha[3]^p = Id(F),
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);

   return [pQuotient(q,p,2):q in Pres];

end function;
