freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


/*function for case two*/
Pair := function(i,p)
   Z := Integers ();
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1
  for x in GF (p) do
    for y in GF (p) do
      if (x^2 - lam*y^2) eq i then
        return x,y;
      end if;
    end for;
  end for;
end function;

/* Easterfield list for Phi43*/
EasterfieldPhi43 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1

   F := FreeGroup (6);

   Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];

   family := [
   (Alpha[2], Alpha[3]) = Id(F),
   (Alpha[2], Alpha[4]) = Id(F),
   (Alpha[3], Alpha[4]) = Id(F),
   (Alpha[2], Alpha[5]) = Alpha[1]^-lam,
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
                  Alpha[6]^p = Alpha[2]^la*Alpha[1]
              ] >;
   Append (~Pres, Q);

   // (2)
   for i in [1..(p-1)] do
    x,y := Pair(i,p);
    x := Z ! x;
    y := Z ! y;
          Q := quo < F | family, [
                         Alpha[5]^p = Alpha[3]*Alpha[1]^-(x+1),
                         Alpha[6]^p = Alpha[2]^la*Alpha[1]^(-y+1)
                     ] >;
          Append (~Pres, Q);
   end for;

   return [pQuotient(q,p,4):q in Pres];
end function;
