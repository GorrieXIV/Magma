freeze;

/* black box recognition procedure for G2(4):2 */

import "../../Presentations/Autm/G24.m":PresentationG24Autm;
 
StandardGeneratorsG24Autm := function (G : Projective := false, Limit := 10000)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {14}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   x := g^7; xw := w^7;

   y, yw := ElementOfOrder (P, {13}, Limit: Fct := Fct);
   if Type (y) eq BoolElt then return false, _; end if;

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c1, cw1 := Random (P);
      c2, cw2 := Random (P);
      c := x^c1;
      z := y^c2;
   until (Fct (c * z) eq 4 and Fct (c * z * z) eq 6 and 
          Fct (c * z * z * z) eq 6) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   cw := xw^cw1; 
   zw := yw^cw2; 
   z := c * z;
   zw := cw * zw;

   return [c, z], [cw, zw];
end function;
