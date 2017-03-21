freeze;

/* black box recognition procedure for Fi22 */

import "../Presentations/Fi22.m":PresentationFi22;

StandardGeneratorsFi22 := function (G : Projective := false, Limit := 2000)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {14,22,30}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, 13, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 11 and Fct ((a * b)^2 * (a * b * a * b^2)^2 * a * b^2) eq 12) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
