freeze;

/* black box recognition procedure for ^2F4(2) = ^2F4(2)'.2 */

import "../../Presentations/Autm/TF42.m":PresentationTF42Autm;

StandardGeneratorsTF42Autm := function (G : Projective := false, Limit := 100)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {10,16,20}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   y, yw := ElementOfOrder (P, 20, Limit: Fct := Fct);
   if Type (y) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c1, c1w := Random (P);
      c2, c2w := Random (P);
      c3, c3w := Random (P);
      b := y^c1*y^c2*y^c3;
   until Fct (b) eq 12 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   bw := yw^c1w*yw^c2w*yw^c3w;
   b := b^3; bw := bw^3;

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 12 and Fct (a*b*a*b^2*a*b^3) eq 4) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
