freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


/* Easterfield list for Phi32 */

EasterfieldPhi32 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1

   F := FreeGroup (6);

   Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];

   family := [
   (Alpha[2], Alpha[3]) = Id(F),
   (Alpha[2], Alpha[4]) = Alpha[1],
   (Alpha[3], Alpha[4]) = Id(F),
   (Alpha[2], Alpha[5]) = Id(F),
   (Alpha[3], Alpha[5]) = Alpha[1]^-la,
   (Alpha[4], Alpha[5]) = Id(F),
   (Alpha[2], Alpha[6]) = Id(F),
   (Alpha[3], Alpha[6]) = Id(F),
   (Alpha[4], Alpha[6]) = Alpha[2],
   (Alpha[5], Alpha[6]) = Alpha[3]];

   Pres := [];

   // (1)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (2)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (3)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (4)
   for x in [1,la] do
    Q := quo < F | family, [
                   Alpha[4]^p = Alpha[1],
                   Alpha[5]^p = Id(F),
                   Alpha[6]^p = Alpha[1]^x
               ] >;
    Append (~Pres, Q);
   end for;

    return [pQuotient(q,p,3):q in Pres];

end function;
