freeze;

/* black box recognition procedure for F4(2) */

import "../Presentations/F42.m":PresentationF42;
 
StandardGeneratorsF42 := function (G : Projective := false, Limit := 300)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {16, 20}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, {9}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);

   o := Fct (b);
   b := b^(o div 3); bw := bw^(o div 3);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 17 and 
         Fct((a * b)^4 * (b * a)^2 * b^2 * a * b^2) eq 13 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
      
   return [a, b], [aw, bw];

end function;
