freeze;

/* black box recognition procedure for Fi24' */

import "../Presentations/Fi24.m":PresentationFi24;
 
StandardGeneratorsFi24 := function (G : Projective := false, Limit := 500)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {22,26,28,60}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   
   o1 := Fct (g);
   x := g^(o1 div 2); xw := w^(o1 div 2);

   nmr0 := 10;
   repeat
      nmr0 -:= 1;

      h, v := ElementOfOrder (P, 39, Limit: Fct := Fct);
      if Type (h) eq BoolElt then return false, _; end if;
      o2 := Fct (h);
      b := h^(o2 div 3); bw := v^(o2 div 3);

      nmr := Limit;
      repeat 
         nmr -:= 1;
         c, cw := Random (P);
         a := x^c;
      until Fct (a * b) eq 29 or nmr eq 0;
   
   until nmr ne 0 or nmr0 eq 0;
   
   if nmr0 eq 0 then return false, _; end if;

   nmr := Limit;
   repeat
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b * a * b * a * b^2) eq 33 or nmr eq 0;
    
   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
