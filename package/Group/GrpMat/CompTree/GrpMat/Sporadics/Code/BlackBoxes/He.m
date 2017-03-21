freeze;

/* black box recognition procedure for He */

import "../Presentations/He.m":PresentationHe;
 
StandardGeneratorsHe := function (G : Projective := false, Limit := 100)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {10,28}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   h, v := ElementOfOrder (P, 8, Limit: Fct := Fct);
   if Type (h) eq BoolElt then return false, _; end if;

   o1 := Fct (g); o2 := Fct (h);
   x := g^(o1 div 2); xw := w^(o1 div 2);
   z := h^(o2 div 2); zw := v^(o2 div 2);

   z1 := z; z1w := zw;

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      z2 := z^c;
   until (Fct (z1 * z2) mod 7 eq 0) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   z2w := zw^cw;

   b := (z1 * z2)^(Fct (z1 * z2) div 7);
   bw := (z1w * z2w)^(Fct (z1 * z2) div 7);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 17 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
