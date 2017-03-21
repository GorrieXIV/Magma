freeze;
 
/* Easterfield list for Phi15; 
   last presentation corrects Easterfield list 
     Alpha[6]^p = Alpha[2] */

import "misc.m": NonQuadraticResidue, EasterfieldPair;



EasterfieldPhi15 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1

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
   (Alpha[4], Alpha[6]) = Alpha[1]^la,
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
                  Alpha[3]^p = Alpha[1],
                  Alpha[4]^p = Id(F),
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (3)
   Q := quo < F | family, [
                  Alpha[3]^p = Alpha[1],
                  Alpha[4]^p = Alpha[2],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

   // (4)
   Q := quo < F | family, [
                  Alpha[3]^p = Alpha[1],
                  Alpha[4]^p = Alpha[2]^-1,
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Id(F)
              ] >;
   Append (~Pres, Q);

//return suitable pairs for case 5

NewPair := function(p,i)
  lam := 1/NonQuadraticResidue(p);
  for x in GF (p) do
    for y in GF (p) do
      if (x^2 - lam*y^2) eq i and x ne 0 and y ne 0 then
        return x,y;
      end if;
    end for;
  end for;
end function;

   // (5)
   for i in [2..p-1] do
     x,y := NewPair(p,i);
     x := Z ! x;
     y := Z ! y;
     Q := quo < F | family, [
          Alpha[3]^p = Alpha[1]^(1-x)*Alpha[2]^(-lam*y),
	  Alpha[4]^p = Alpha[1]^y*Alpha[2]^(1+x),
          Alpha[5]^p = Id(F),
          Alpha[6]^p = Id(F)
          ] >;
     Append (~Pres, Q);
   end for;

   // (6)
   Q := quo < F | family, [
                  Alpha[3]^p = Id(F),
                  Alpha[4]^p = Alpha[1],
                  Alpha[5]^p = Id(F),
                  Alpha[6]^p = Alpha[2]
              ] >;
   Append (~Pres, Q);

   return [pQuotient(q,p,3): q in Pres];

end function;
