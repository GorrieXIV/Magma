freeze;

/* black box recognition procedure for M12 */

import "../Presentations/M12.m":PresentationM12;

StandardGeneratorsM12 := function (G : Projective := false, Limit := 40)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, 8, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);

   nmr0 := Limit;
   repeat
      nmr0 -:= 1;
      b, bw := ElementOfOrder (P, 3, Limit: Fct := Fct);
      if Type (b) eq BoolElt then return false, _; end if;

      nmr := Limit;
      repeat 
         nmr -:= 1;
         c, cw := Random (P);
         a := x^c;
      until Fct (a * b) eq 11 or nmr eq 0;

   until (Fct (a * b * a * b^2) eq 6 and nmr ne 0) or nmr0 eq 0;

   if nmr0 eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;

