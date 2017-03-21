freeze;

/* black box recognition procedure for Co2 */

import "../Presentations/Co2.m":PresentationCo2;

StandardGeneratorsCo2 := function (G : Projective := false, Limit := 50)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {16,18,28}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   o1 := Fct (g);
   x := g^(o1 div 2); xw := w^(o1 div 2);

   nmr0 := Limit;
   repeat
      nmr0 -:= 1;

      h, v := ElementOfOrder (P, 15, Limit: Fct := Fct);
      if Type (h) eq BoolElt then return false, _; end if;
   
      o2 := Fct (h);
      b := h^(o2 div 5); bw := v^(o2 div 5);

      nmr := Limit;
      repeat 
         nmr -:= 1;
         c, cw := Random (P);
         a := x^c;
      until Fct (a * b) eq 28 or nmr eq 0;

      aw := xw^cw;
   
   until (nmr ne 0 and Fct (a * b^2) eq 9) or nmr0 eq 0;
   
   if nmr0 eq 0 then return false, _; end if;

   return [a, b], [aw, bw];

end function;
