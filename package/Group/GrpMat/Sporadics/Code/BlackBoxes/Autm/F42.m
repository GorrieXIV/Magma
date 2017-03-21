freeze;

/* black box recognition procedure for F4(2):2 */

import "../../Presentations/Autm/F42.m" : PresentationF42Autm;
 
StandardGeneratorsF42Autm := function (G : Projective := false, Limit := 300)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {26}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, {15, 21, 30}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);

   // x now an involution in class 2E
   
   o := Fct (b);
   b := b^(o div 3); bw := bw^(o div 3);

   // b now in class 3AB
   
   nmr := Limit;
   a := x;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 40 and 
       Fct(a * b * a * b * a * b * b) eq 10 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
