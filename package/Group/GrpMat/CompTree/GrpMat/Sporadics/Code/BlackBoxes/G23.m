freeze;

/* black box recognition procedure for G2(3) */

import "../Presentations/G23.m":PresentationG23;
 
StandardGeneratorsG23 := function (G : Projective := false, Limit := 10000)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   x, xw := ElementOfOrder (P, {2}, Limit: Fct := Fct);
   if Type (x) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, {9}, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;
   
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
