freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


EasterfieldPhi20 := function (p)

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
   (Alpha[3], Alpha[5]) = Alpha[1],
   (Alpha[4], Alpha[5]) = Id(F),
   (Alpha[2], Alpha[6]) = Id(F),
   (Alpha[3], Alpha[6]) = Alpha[2],
   (Alpha[4], Alpha[6]) = Alpha[1]^-1,
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
   for x in [1,la] do
    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Id(F),
                   Alpha[6]^p = Alpha[1]^x
               ] >;
   Append (~Pres, Q);
   end for;

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
                  Alpha[5]^p = Alpha[1],
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (5)
   for x in [1,la] do
    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Alpha[2]^x,
                   Alpha[6]^p = Id(F)
               ] >;
   Append (~Pres, Q);
   end for;

   // (6)
   for x in [1,la] do
    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Alpha[1]*Alpha[2]^x,
                   Alpha[6]^p = Id(F)
               ] >;
   Append (~Pres, Q);
   end for;

   // (7)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (8)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (9)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Alpha[1],
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);

   // (10)
   for x in [1,la] do
    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Alpha[1],
                   Alpha[6]^p = Alpha[2]*Alpha[1]^x
               ] >;
   Append (~Pres, Q);
   end for;

   // (11)
   for x in [2..p-1] do
    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Alpha[1],
                   Alpha[6]^p = Alpha[2]^x
               ] >;
   Append (~Pres, Q);
   end for;

   // (12)
   for x in [1,la] do
    for y in [1,la] do
     Q := quo < F | family, [
                    Alpha[4]^p = Id(F),
                    Alpha[5]^p = Alpha[2]^x,
                    Alpha[6]^p = Alpha[1]^y
                ] >;
   Append (~Pres, Q);
    end for;
   end for;

   // (13)
   for x in [1,la] do
    for y in [1..p-1] do
     Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Alpha[2]^x,
                   Alpha[6]^p = Alpha[2]*Alpha[1]^y
               ] >;
   Append (~Pres, Q);
    end for;
   end for;

   // (14)
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);

   // (15)
   if (p mod 4) eq 1 then
      for x in [1,w,w^2,w^3] do
         Q := quo < F | family, [
                        Alpha[4]^p = Alpha[2],
                        Alpha[5]^p = Id(F),
                        Alpha[6]^p = Alpha[1]^(x mod p)
                    ] >;
      Append (~Pres, Q);
      end for;
   else
      for x in [1,la] do
         Q := quo < F | family, [
                        Alpha[4]^p = Alpha[2],
                        Alpha[5]^p = Id(F),
                        Alpha[6]^p = Alpha[1]^x
                    ] >;
      Append (~Pres, Q);
      end for;
   end if;

   // (16)
   for x in [1..p-1] do
     Q := quo < F | family, [
                   Alpha[4]^p = Alpha[1],
                   Alpha[5]^p = Alpha[2]^x,
                   Alpha[6]^p = Id(F)
               ] >;
   Append (~Pres, Q);
   end for;

   // (17)
   if (p mod 3) eq 1 then
      for x in [1,w,w^2] do
         Q := quo < F | family, [
                       Alpha[4]^p = Alpha[2],
                       Alpha[5]^p = Alpha[1]^(x mod p),
                       Alpha[6]^p = Id(F)
                ] >;
         Append (~Pres, Q);
      end for;
   else
          Q := quo < F | family, [
                      Alpha[4]^p = Alpha[2],
                      Alpha[5]^p = Alpha[1],
                      Alpha[6]^p = Id(F)
                ] >;
         Append (~Pres, Q);
   end if;

   // (18)
   for x in [1..p-1] do
      Q := quo < F | family, [
                    Alpha[4]^p = (Alpha[2]^x)*Alpha[1],
                    Alpha[5]^p = Alpha[1],
                    Alpha[6]^p = Id(F)
                ] >;
   Append (~Pres, Q);
   end for;

   return [pQuotient (q, p, 3): q in Pres];

end function;
