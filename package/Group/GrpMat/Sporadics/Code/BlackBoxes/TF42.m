freeze;

/* black box recognition procedure for ^2F4(2)' */

import "../Presentations/TF42.m":PresentationTF42;
 
StandardGeneratorsTF42 := function (G : Projective := false, Limit := 100)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {10,16}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, {3,6,12}, Limit: Fct := Fct);
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
   until Fct (a * b) eq 13 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
