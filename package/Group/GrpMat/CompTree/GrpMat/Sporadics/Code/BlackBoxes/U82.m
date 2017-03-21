freeze;

/* black box recognition procedure for U8(2) */

import "../Presentations/U82.m":PresentationU82;
 
StandardGeneratorsU82 := function (G : Projective := false, Limit := 500)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {14,22,42,44,66,72,126,132}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, {14,42,126}, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;

   o := Fct(g);
   x := g^(o div 2);
   xw := w^(o div 2);

   o := Fct(b);
   b ^:= o div 14;
   bw ^:= o div 14;
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 85 and Fct (a * b^2) eq 18 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   return [a, b], [aw, bw];

end function;
