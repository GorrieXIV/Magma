freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


/* Easterfield list for Phi22*/

EasterfieldPhi22 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda

   F := FreeGroup (6);

   Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];

   family := [
   (Alpha[2], Alpha[3]) = Id(F),
   (Alpha[2], Alpha[4]) = Id(F),
   (Alpha[3], Alpha[4]) = Alpha[1],
   (Alpha[2], Alpha[5]) = Id(F),
   (Alpha[3], Alpha[5]) = Id(F),
   (Alpha[4], Alpha[5]) = Id(F),
   (Alpha[2], Alpha[6]) = Alpha[1],
   (Alpha[3], Alpha[6]) = Id(F),
   (Alpha[4], Alpha[6]) = Id(F),
   (Alpha[5], Alpha[6]) = Alpha[2]];

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
                  Alpha[3]^p = Id(F),
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (3)
   for x in [1,la] do
     Q := quo < F | family, [
                    Alpha[3]^p = Id(F),
                    Alpha[4]^p = Id(F),
                    Alpha[5]^p = Alpha[1]^x,
                    Alpha[6]^p = Id(F)
                ] >;
     Append (~Pres, Q);
   end for;

   // (4)
   Q := quo < F | family, [
                  Alpha[3]^p = Id(F),
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (5)
   for x in [1,la] do
     Q := quo < F | family, [
                    Alpha[3]^p = Id(F),
                    Alpha[4]^p = Alpha[1]^x,
                    Alpha[5]^p = Alpha[1]^x,
                    Alpha[6]^p = Id(F)
                ] >;
     Append (~Pres, Q);
   end for;

   return [pQuotient(q,p,3):q in Pres];

end function;
