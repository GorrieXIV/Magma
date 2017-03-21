freeze;

/* black box recognition procedure for M12:2 */

import "../../Presentations/Autm/M12.m":PresentationM12Autm;

StandardGeneratorsM12Autm := function (G : Projective := false, Limit := 40)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, 8, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   h, v := ElementOfOrder (P, 12, Limit: Fct := Fct);
   if Type (h) eq BoolElt then return false, _; end if;

   o := Fct (g);
   z := g^(o div 2); zw := w^(o div 2);

   nmr := Limit;
   repeat
      nmr -:= 1;
      c, cw := Random (P);
      x := z^c;
   until Fct (x * h) eq 10 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   xw := zw^cw;
   x := (x*h)^5; xw := (xw*v)^5;

   nmr := Limit;
   repeat
      nmr -:= 1;
      c, cw := Random (P);
      y := z^c;
   until Fct (y * x) eq 12 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   yw := zw^cw;
   y := (y*x)^4; yw := (yw*xw)^4;

   nmr := Limit;
   repeat
      nmr -:= 1;
      c, cw := Random (P);
      b := y^c;
   until (Fct (x * b) eq 12 and Fct (x * b * x * b^2) eq 11) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   bw := yw^cw;
   a := x; aw := xw;

   return [a, b], [aw, bw];

end function;
