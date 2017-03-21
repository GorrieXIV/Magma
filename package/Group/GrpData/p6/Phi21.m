freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


/* Easterfield list for Phi 21
   Easterfield uses \xi and \eta in two ways 
   - these are translated to x, xx and y, yy */

EasterfieldPhi21 := function (p)

   Z := Integers ();

   la := Z ! (NonQuadraticResidue (p)); // lambda
   lam := Z ! (1/NonQuadraticResidue (p)); // lambda^-1

   xx, yy := EasterfieldPair (p);
   xx := Z ! xx;
   yy := Z ! yy;

   F := FreeGroup (6); 

   Alpha := [F.1, F.2, F.3, F.4, F.5, F.6];

   family := [
   (Alpha[5], Alpha[6]) = Alpha[3],
   (Alpha[4], Alpha[6]) = Alpha[1]^la,
   (Alpha[3], Alpha[6]) = Alpha[2],
   (Alpha[4], Alpha[5]) = Alpha[2],
   (Alpha[3], Alpha[5]) = Alpha[1],
   (Alpha[3], Alpha[4]) = Id(F)];

   Pres := [];

   // (1) 
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F), 
                  Alpha[5]^p = Id(F), 
                  Alpha[6]^p = Id(F) 
              ] >;
   Append (~Pres, pQuotient(Q,p,3));

   // (2) 
   Q := quo < F | family, [
                  Alpha[4]^p = Alpha[1], 
                  Alpha[5]^p = Id(F), 
                  Alpha[6]^p = Id(F) 
              ] >;
   Append (~Pres, pQuotient(Q,p,3));

   // (3)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F), 
                  Alpha[5]^p = Alpha[1], 
                  Alpha[6]^p = Id(F) 
              ] >;
   Append (~Pres, pQuotient(Q,p,3));

   if (p mod 4) eq 1 then
       Q := quo < F | family, [
                      Alpha[4]^p = Id(F), 
                      Alpha[5]^p = Alpha[1]^la, 
                      Alpha[6]^p = Id(F) 
                  ] >;
       Append (~Pres, pQuotient(Q,p,3));
   end if;

   // (4)
   for x in [1, la] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F), 
                     Alpha[5]^p = Alpha[2]^x, 
                     Alpha[6]^p = Id(F) 
                 ] >;
      Append (~Pres, pQuotient(Q,p,3));
   end for;

   // (5)
   for x in [1, la] do
      for y in [1..(p-1) div 2] do
         Q := quo < F | family, [
                        Alpha[4]^p = Id(F), 
                        Alpha[5]^p = Alpha[2]^x*Alpha[1]^y, 
                        Alpha[6]^p = Id(F) 
                    ] >;
         Append (~Pres, pQuotient(Q,p,3));
      end for;
   end for;

   // (6)
   for y in [1..p-1] do
      Q := quo < F | family, [
                     Alpha[4]^p = Alpha[2], 
                     Alpha[5]^p = Id(F), 
                     Alpha[6]^p = Alpha[1]^y 
                 ] >;
      Append (~Pres, pQuotient(Q,p,3));
   end for;

   // (7)
   for x in [0..p-1] do
      for y in [1..(p-1) div 2] do
         Q := quo < F | family, [
                        Alpha[4]^p = Alpha[2]^x*Alpha[1], 
                        Alpha[5]^p = Id(F), 
                        Alpha[6]^p = Alpha[2]^y 
                   ] >;
         Append (~Pres, pQuotient(Q,p,3));
      end for;
   end for;

   // (8)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F), 
                  Alpha[5]^p = Alpha[1], 
                  Alpha[6]^p = Alpha[2] 
              ] >;
   Append (~Pres, pQuotient(Q,p,3));

   // (9)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F), 
                  Alpha[5]^p = Alpha[2]^lam, 
                  Alpha[6]^p = Alpha[1] 
            ] >;
   Append (~Pres, pQuotient(Q,p,3));

   // (10)
   for y in [1..(p-1) div 2] do
      Q := quo < F | family, [
                     Alpha[4]^p = Id(F), 
                     Alpha[5]^p = Alpha[2]^(lam*y)*Alpha[1], 
                     Alpha[6]^p = Alpha[2]*Alpha[1]^y 
                 ] >;
      Append (~Pres, pQuotient(Q,p,3));
   end for;

   // (11)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F), 
                  Alpha[5]^p = Alpha[1]^-1, 
                  Alpha[6]^p = Alpha[2] 
              ] >;
   Append (~Pres, pQuotient(Q,p,3));

   // (12)
   Q := quo < F | family, [
                  Alpha[4]^p = Id(F), 
                  Alpha[5]^p = Alpha[2]^(-lam*yy mod p)*Alpha[1]^-xx, 
                  Alpha[6]^p = Alpha[2]^xx*Alpha[1]^yy 
             ] >;
   Append (~Pres, pQuotient(Q,p,3));

   // (13)
   if (p mod 4) eq 1 then
      // (13a)
      for xi in [2..p-2] do
         Q := quo < F | family, [
                        Alpha[4]^p = Id(F), 
                        Alpha[5]^p = Alpha[1]^(xi-1), 
                        Alpha[6]^p = Alpha[2]^(1+xi) 
                    ] >;
         Append (~Pres, pQuotient(Q,p,3));
      end for;
   else
   // (13b)
      for xi in [2..(p-1) div 2] do
         Q := quo < F | family, [
                        Alpha[4]^p = Id(F), 
                        Alpha[5]^p = Alpha[1]^(xi-1), 
                        Alpha[6]^p = Alpha[2]^(1+xi) 
                    ] >;
         Append (~Pres, pQuotient(Q,p,3));
      end for;
   end if;

   // (14)
   if (p mod 4) eq 1 then
      for x in [1..(p-1) div 2] do
          Q := quo < F | family, [
                         Alpha[4]^p = Id(F), 
                         Alpha[5]^p = Alpha[2]^(lam*x mod p)*Alpha[1]^-1, 
                         Alpha[6]^p = Alpha[2]*Alpha[1]^x 
                     ] >;
         Append (~Pres, pQuotient(Q,p,3));
      end for;
   else
      // (14b)
      for x in [1..p-1] do
         if (x*x mod p) ne p-la then
            Q := quo < F | family, [
                           Alpha[4]^p = Id(F), 
                           Alpha[5]^p = Alpha[2]^(lam*x mod p)*Alpha[1]^-1, 
                           Alpha[6]^p = Alpha[2]*Alpha[1]^x 
                      ] >;
            Append (~Pres, pQuotient(Q,p,3));
         end if;
      end for;
   end if;

   // (15)
   if (p mod 4) eq 1 then
      // (15a)
      for x in [1..p-1] do
         for y in [1..(p-1) div 2] do
            if (x*x - lam*y*y) mod p ne 1 then
               //print "15a ", x,y;
               Q := quo < F | family, [
                              Alpha[4]^p = Id(F), 
                              Alpha[5]^p = Alpha[2]^(lam*y mod p)*Alpha[1]^(x-1), 
                              Alpha[6]^p = Alpha[2]^(1+x)*Alpha[1]^y 
                          ] >;
               Append (~Pres, pQuotient(Q,p,3));
            end if;
         end for;
      end for;
   else
      // (15b)
      for x in [1..(p-1) div 2] do
         for y in [1..p-1] do
            if (x*x - lam*y*y) mod p ne 1 then
              Q := quo < F | family, [
                             Alpha[4]^p = Id(F), 
                             Alpha[5]^p = Alpha[2]^(lam*y mod p)*Alpha[1]^(x-1), 
                             Alpha[6]^p = Alpha[2]^(1+x)*Alpha[1]^y 
                         ] >;
              Append (~Pres, pQuotient(Q,p,3));
           end if;
         end for;
      end for;
   end if;

   // (16)
   if (p mod 4) eq 1 then
      // (16a)
      for r in [1..(p-1) div 2] do
         Q := quo < F | family, [
                        Alpha[4]^p = Id(F), 
                        Alpha[5]^p = Alpha[2]^(-lam*yy mod p)*Alpha[1]^(r-xx), 
                        Alpha[6]^p = Alpha[2]^((r+xx) mod p)*Alpha[1]^yy 
                    ] >;
         Append (~Pres, pQuotient(Q,p,3));
      end for;
   else
      // (16b)
      for r in [1..p-1] do
         Q := quo < F | family, [
                        Alpha[4]^p = Id(F), 
                        Alpha[5]^p = Alpha[2]^(-lam*yy mod p)*Alpha[1]^(r-xx), 
                        Alpha[6]^p = Alpha[2]^((r+xx) mod p)*Alpha[1]^yy 
                    ] >;
         Append (~Pres, pQuotient(Q,p,3));
      end for;
   end if;

   // (17)
   if (p mod 4) eq 1 then
       // (17a)
      for r in [1..p-1] do
         if (r*r mod p) ne p-1 then
            Q := quo < F | family, [
                           Alpha[4]^p = Id(F), 
                           Alpha[5]^p = Alpha[2]^(lam*(r-yy) mod p)*Alpha[1]^-xx, 
                           Alpha[6]^p = Alpha[2]^xx*Alpha[1]^((r+yy) mod p) 
                       ] >;
            Append (~Pres, pQuotient(Q,p,3));
         end if;
      end for;
   else
      // (17b)
      for r in [1..(p-1) div 2] do
         Q := quo < F | family, [
                        Alpha[4]^p = Id(F), 
                        Alpha[5]^p = Alpha[2]^(lam*(r-yy) mod p)*Alpha[1]^-xx, 
                        Alpha[6]^p = Alpha[2]^xx*Alpha[1]^((r+yy) mod p) 
                    ] >;
         Append (~Pres, pQuotient(Q,p,3));
      end for;
   end if;

   // (18)
   if (p mod 4) eq 1 then
      // (18a)
      for r in [1..(p-1) div 2] do
         for t in [1..p-1] do
            if (r*r - lam*t*t) mod p ne lam then
               Q := quo < F | family, [
                              Alpha[4]^p = Id(F), 
                              Alpha[5]^p = Alpha[2]^(lam*(t-yy) mod p)*Alpha[1]^(r-xx), 
                              Alpha[6]^p = Alpha[2]^((r+xx) mod p)*Alpha[1]^((t+yy) mod p) 
                          ] >;
               Append (~Pres, pQuotient(Q,p,3));
            end if;
         end for;
      end for;
   else
      // (18b)
      for r in [1..p-1] do
         for t in [1..(p-1) div 2] do
            if (r*r - lam*t*t) mod p ne lam then
               Q := quo < F | family, [
                              Alpha[4]^p = Id(F), 
                              Alpha[5]^p = Alpha[2]^(lam*(t-yy) mod p)*Alpha[1]^(r-xx), 
                              Alpha[6]^p = Alpha[2]^((r+xx) mod p)*Alpha[1]^((t+yy) mod p) 
                          ] >;
               Append (~Pres, pQuotient(Q,p,3));
            end if;
         end for;
      end for;
   end if;

   return Pres;

end function;
