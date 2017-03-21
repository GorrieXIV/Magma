freeze;

/* black box recognition procedure for Fi22:2 */

import "../../Presentations/Autm/Fi22.m":PresentationFi22Autm;
 
StandardGeneratorsFi22Autm := function (G : Projective := false, Limit := 350)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, 22, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, 42, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 18 and Fct (a*b^5) eq 42) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, a * b], [aw, aw * bw];

end function;
