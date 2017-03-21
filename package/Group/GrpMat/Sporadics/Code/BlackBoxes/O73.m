freeze;

/* black box recognition procedure for O7(3) */

import "../Presentations/O73.m":PresentationO73;
 
StandardGeneratorsO73 := function (G : Projective := false, Limit := 500)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {14}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   
   o := Fct(g);
   x := g^(o div 2);
   xw := w^(o div 2);
   
   b := g^(o div 7); bw := w^(o div 7);
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 13 and Fct(a * b * b) eq 20 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   return [a, b], [aw, bw];

end function;
