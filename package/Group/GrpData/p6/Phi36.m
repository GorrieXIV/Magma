freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


/* Easterfield list for Phi36 */

EasterfieldPhi36 := function (p)

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
   (Alpha[2], Alpha[5]) = Id(F),
   (Alpha[3], Alpha[5]) = Id(F),
   (Alpha[4], Alpha[5]) = Alpha[1],
   (Alpha[2], Alpha[6]) = Alpha[1],
   (Alpha[3], Alpha[6]) = Alpha[2],
   (Alpha[4], Alpha[6]) = Alpha[3],
   (Alpha[5], Alpha[6]) = Alpha[4]];

   Pres := [];

   if p eq 5 then
   // (1a)
   Q := quo < F | family, [
                  Alpha[5]^p = Alpha[1]^-1,
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (2a)
   Q := quo < F | family, [
                  Alpha[5]^p = Alpha[1]^-1,
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (3a)
   Q := quo < F | family, [
                  Alpha[5]^p = Alpha[1]^-1,
                  Alpha[6]^p = Alpha[1]^2
              ] >;
   Append (~Pres, Q);

   for x in [0..3] do
      // (4a)
      Q := quo < F | family, [
                  Alpha[5]^p = Alpha[1]^x,
                  Alpha[6]^p = Id(F)
              ] >;
      Append (~Pres, Q);
   end for;
   return [pQuotient(q,5,5):q in Pres];

   end if;

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
   if p mod 4 eq 1 then
    for x in [w,w^2,w^3] do
     Q := quo < F | family, [
                    Alpha[5]^p = Alpha[1]^(x mod p),
                    Alpha[6]^p = Id(F)
                ] >;
     Append (~Pres, Q);
    end for;
   else;
    Q := quo < F | family, [
                   Alpha[5]^p = Alpha[1]^la,
                   Alpha[6]^p = Id(F)
               ] >;
    Append (~Pres, Q);
   end if;

   // (3)
   Q := quo < F | family, [
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);
   if p mod 3 eq 1 then
    for x in [w,w^2,w^3,w^4,w^5] do
     Q := quo < F | family, [
                    Alpha[5]^p = Id(F),
                    Alpha[6]^p = Alpha[1]^(x mod p)
                ] >;
     Append (~Pres, Q);
    end for;
   else;
    Q := quo < F | family, [
                   Alpha[5]^p = Id(F),
                   Alpha[6]^p = Alpha[1]^la
               ] >;
    Append (~Pres, Q);
   end if;

   return [pQuotient(q,p,5):q in Pres];

end function;
