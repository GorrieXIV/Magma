freeze;

/* black box recognition procedure for Fi23 */

import "../Presentations/Fi23.m":PresentationFi23;
 
StandardGeneratorsFi23 := function (G : Projective := false, Limit := 100)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {20,28}, Limit: Fct := Fct);
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
      until Fct (a * b) eq 28 or nmr eq 0;

      aw := xw^cw; 
   
   until nmr ne 0 or nmr0 eq 0;
   
   if nmr0 eq 0 then return false, _; end if;

   return [a, b], [aw, bw];

end function;
