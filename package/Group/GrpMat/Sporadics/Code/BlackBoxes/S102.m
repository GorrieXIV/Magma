freeze;

/* black box recognition procedure for S10(2) */

import "../Presentations/S102.m":PresentationS102;
 
StandardGeneratorsS102 := function (G : Projective := false, Limit := 100)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {34}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, {11,33}, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;
   
   o := Fct(g);
   x := g^(o div 2);
   xw := w^(o div 2);
   
   o := Fct (b);
   b := b^(o div 11); bw := bw^(o div 11);
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 15 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   return [a, b], [aw, bw];

end function;
