freeze;
 
/* Easterfield list for Phi 17*/

import "misc.m": NonQuadraticResidue, EasterfieldPair;



EasterfieldPhi17 := function (p)

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
   (Alpha[4], Alpha[5]) = Alpha[2],
   (Alpha[2], Alpha[6]) = Id(F),
   (Alpha[3], Alpha[6]) = Alpha[1],
   (Alpha[4], Alpha[6]) = Id(F),
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
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);

   // (4)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[1]*Alpha[2]
              ] >;
   Append (~Pres, Q);

   // (5)
   for x in [1,la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[1]^x,
                     Alpha[6]^p = Id(F)
                 ] >;
      Append (~Pres, Q);
   end for;

   // (6)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Alpha[2],
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (7)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[1]^x*Alpha[2],
                     Alpha[6]^p = Id(F)
                 ] >;
      Append (~Pres, Q);
   end for;

   // (8)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[1]^x,
                     Alpha[6]^p = Alpha[1]^x
                 ] >;
      Append (~Pres, Q);
   end for;

   // (9)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Alpha[2],
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);

   // (10)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[1]^x*Alpha[2],
                     Alpha[6]^p = Alpha[1]^x*Alpha[2]
                 ] >;
      Append (~Pres, Q);
   end for;

   // (11)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (12)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (13)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1]*Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (14)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[1]^x,
                     Alpha[6]^p = Alpha[2]
                 ] >;
      Append (~Pres, Q);
   end for;

   // (15)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[1]^x,
                     Alpha[6]^p = Alpha[1]*Alpha[2]
                 ] >;
      Append (~Pres, Q);
   end for;

   // (16)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Alpha[2],
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (17)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[2],
                     Alpha[6]^p = Alpha[1]^x*Alpha[2]
                 ] >;
      Append (~Pres, Q);
   end for;

   // (18)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[1]^x*Alpha[2],
                     Alpha[6]^p = Alpha[2]
                 ] >;
      Append (~Pres, Q);
   end for;

   // (19)
   for x in [1, la] do
    for y in [0..p-1] do
     if (x*y) mod p ne 1 then
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F),
                     Alpha[5]^p = Alpha[1]^x*Alpha[2],
                     Alpha[6]^p = Alpha[1]*Alpha[2]^y
                 ] >;
      Append (~Pres, Q);
     end if;
    end for;
   end for;

   // (20)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);

   // (21)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (22)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1]*Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (23)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Alpha[2],
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (24)
   for x in [1,la] do
     Q := quo < F | family, [
                    Alpha[4]^p = Alpha[2],
                    Alpha[5]^p = Alpha[1]^x,
                    Alpha[6]^p = Id(F)
                ] >;
     Append (~Pres, Q);
   end for;

   // (25)
   for x in [1,la] do
     Q := quo < F | family, [
                    Alpha[4]^p = Alpha[1]^x*Alpha[2],
                    Alpha[5]^p = Alpha[2],
                    Alpha[6]^p = Id(F)
                ] >;
     Append (~Pres, Q);
   end for;

   // (26)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Alpha[2],
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);
   if (p mod 3) eq 1 then
     for x in [w,w^2] do
        Q := quo < F | family, [
                     Alpha[4]^p = Alpha[1]^(x mod p),
                     Alpha[5]^p = Alpha[2],
                     Alpha[6]^p = Alpha[2]
                 ] >;
        Append (~Pres, Q);
     end for;
   end if;

   // (27)
   for x in [1..p-1] do
     Q := quo < F | family, [
                    Alpha[4]^p = Alpha[2],
                    Alpha[5]^p = Alpha[1]^x,
                    Alpha[6]^p = Alpha[1]^x
                ] >;
     Append (~Pres, Q);
   end for;

   // (28)
   for x in [1..p-1] do
     Q := quo < F | family, [
                    Alpha[4]^p = Alpha[1]*Alpha[2],
                    Alpha[5]^p = Alpha[1]^x,
                    Alpha[6]^p = Alpha[1]
                ] >;
     Append (~Pres, Q);
   end for;

   return [pQuotient(q,p,3): q in Pres];

end function;
