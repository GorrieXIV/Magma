freeze;
 
 /* Easterfield list for Phi 18*/

import "misc.m": NonQuadraticResidue, EasterfieldPair;



EasterfieldPhi18 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1

   xx, yy := EasterfieldPair (p);
   xx := Z ! xx;
   yy := Z ! yy;
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
   (Alpha[2], Alpha[6]) = Id(F),
   (Alpha[3], Alpha[6]) = Alpha[1],
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
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Id(F),
                     Alpha[6]^p = Alpha[2]^x
                 ] >;
      Append (~Pres, Q);
   end for;

   // (4)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[1]^x,
                     Alpha[6]^p = Id(F)
                 ] >;
      Append (~Pres, Q);
   end for;

   // (5)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Alpha[2],
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (6)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (7)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (8)
   for x in [1,la] do
      for y in [1..p-1] do
         Q := quo < F | family, [
                        Alpha[4]^p = Id(F),
                        Alpha[5]^p = Alpha[1]^x,
                        Alpha[6]^p = Alpha[2]^y
                    ] >;
         Append (~Pres, Q);
      end for;
   end for;

   // (9)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Alpha[2],
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);

   if (p mod 4) eq 1 then
     for x in [w,w^2,w^3] do
        Q := quo < F | family, [
                       Alpha[4]^p = Id(F),
                       Alpha[5]^p = Alpha[2]^(x mod p),
                       Alpha[6]^p = Alpha[1]
                   ] >;
        Append (~Pres, Q);
     end for;
   else
        Q := quo < F | family, [
                       Alpha[4]^p = Id(F),
                       Alpha[5]^p = Alpha[2]^la,
                       Alpha[6]^p = Alpha[1]
                   ] >;
        Append (~Pres, Q);
   end if;

   // (10)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Alpha[1],
                     Alpha[5]^p = Id(F),
                     Alpha[6]^p = Alpha[2]^x
                 ] >;
      Append (~Pres, Q);
   end for;

   // (11)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (12)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Alpha[2],
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   if (p mod 3) eq 1 then
     for x in [w,w^2] do
        Q := quo < F | family, [
                       Alpha[4]^p = Alpha[1],
                       Alpha[5]^p = Alpha[2]^(x mod p),
                       Alpha[6]^p = Id(F)
                   ] >;
        Append (~Pres, Q);
     end for;
   end if;

   // (13)
   for y in [1..p-1] do
      Q := quo < F | family, [
                     Alpha[4]^p = Alpha[2],
                     Alpha[5]^p = Alpha[1]^y,
                     Alpha[6]^p = Id(F)
                 ] >;
      Append (~Pres, Q);
   end for;

   return [pQuotient(q, p, 3):q in Pres];

end function;
