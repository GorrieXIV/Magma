freeze;

/* black box recognition procedure for O+10(2) */

import "../Presentations/O10p2.m":PresentationO10p2;
 
StandardGeneratorsO10p2 := function (G : Projective := false, Limit := 200)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {60}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   
   o := Fct(g);
   x := g^(o div 2);
   xw := w^(o div 2);
   
   b := g^(o div 20); bw := w^(o div 20);
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 21 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   return [a, b], [aw, bw];

end function;
