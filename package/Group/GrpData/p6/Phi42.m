freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


/* function for case three: x is mu1 and y is mu2 */
PairPhi42 := function(i, p)
 for x in GF(p) do
  for y in GF(p) do
   if (x*x - y*y) eq i then
    return x,y;
   end if;
  end for;
 end for;
end function;

/* Easterfield list for Phi42*/
EasterfieldPhi42 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1

   F := FreeGroup (6);

   Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];

   family := [
   (Alpha[2], Alpha[3]) = Id(F),
   (Alpha[2], Alpha[4]) = Id(F),
   (Alpha[3], Alpha[4]) = Id(F),
   (Alpha[2], Alpha[5]) = Alpha[1]^-1,
   (Alpha[3], Alpha[5]) = Id(F),
   (Alpha[4], Alpha[5]) = Alpha[2],
   (Alpha[2], Alpha[6]) = Id(F),
   (Alpha[3], Alpha[6]) = Alpha[1],
   (Alpha[4], Alpha[6]) = Alpha[3],
   (Alpha[5], Alpha[6]) = Alpha[4]];

   Pres := [];

   // (1)
   Q := quo < F | family, [
                  Alpha[5]^p = Alpha[3]*Alpha[1]^-1,
                  Alpha[6]^p = Alpha[2]*Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (2)
   Q := quo < F | family, [
                  Alpha[5]^p = Alpha[3],
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);

   // (3)
   for i in [1..(p-1)] do
    x, y := PairPhi42 (i, p);
    x := Z ! x;
    y := Z ! y;
          Q := quo < F | family, [
                         Alpha[5]^p = Alpha[3]*Alpha[1]^(-x-1),
                         Alpha[6]^p = Alpha[2]*Alpha[1]^(-y+1)
                     ] >;
          Append (~Pres, Q);
   end for;

   return [pQuotient(q,p,4):q in Pres];
end function;
