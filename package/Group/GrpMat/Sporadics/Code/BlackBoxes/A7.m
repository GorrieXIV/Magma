freeze;

/* black box recognition procedure for U3(9) */

import "../Presentations/A7.m":PresentationA7;
 
StandardGeneratorsA7 := function (G : Projective := false, Limit := 100)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {6}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
     
   b, bw := ElementOfOrder (P, {5}, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;
      
   x := g^2;
   xw := w^2;
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 7 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
         
   return [a, b], [aw, bw];

end function;
