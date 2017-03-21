freeze;

/* black box recognition procedure for Ly */

import "../Presentations/Ly.m":PresentationLy;

StandardGeneratorsLy := function (G : Projective := false, Limit := 3000)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   x, xw := ElementOfOrder (P, 2, Limit: Fct := Fct);
   if Type (x) eq BoolElt then return false, _; end if;
   g, w := ElementOfOrder (P, {20,25,40}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct (g);
   b := g^(o div 5); bw := w^(o div 5);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 14 and Fct (a * b * a * b * a * b^2) eq 67) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
