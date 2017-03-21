freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;

/* Easterfield list for Phi41 */

EasterfieldPhi41 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1

   w := PrimitiveRoot(p);
   F := FreeGroup (6);

   Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];

   family := [
   (Alpha[2], Alpha[3]) = Id(F),
   (Alpha[2], Alpha[4]) = Id(F),
   (Alpha[3], Alpha[4]) = Id(F),
   (Alpha[2], Alpha[5]) = Alpha[1]^(-la),
   (Alpha[3], Alpha[5]) = Id(F),
   (Alpha[4], Alpha[5]) = Alpha[2],
   (Alpha[2], Alpha[6]) = Id(F),
   (Alpha[3], Alpha[6]) = Alpha[1],
   (Alpha[4], Alpha[6]) = Alpha[3],
   (Alpha[5], Alpha[6]) = Alpha[4]];

   Pres := [];

   // (1)
   Q := quo < F | family, [
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (2)
   Q := quo < F | family, [
                  Alpha[5]^p = Alpha[1],
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   if p mod 3 eq 1 then
    for x in [w,w^2] do
     Q := quo < F | family, [
                    Alpha[5]^p = Alpha[1]^(x mod p),
                    Alpha[6]^p = Id(F)
                ] >;
     Append (~Pres, Q);
    end for;
   end if;

   return [pQuotient(q,p,4):q in Pres];
end function;
