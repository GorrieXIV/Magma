freeze;

/* black box recognition procedure for J2 */

import "../Presentations/J2.m":PresentationJ2;
 
StandardGeneratorsJ2 := function (G : Projective := false, Limit := 200)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 

   nmr0 := Limit;
   repeat
      nmr0 -:= 1;
      
      x, xw := ElementOfOrder (P, 2, Limit: Fct := Fct);
      if Type (x) eq BoolElt then return false, _; end if;

      nmr1 := Limit;
      repeat
         nmr1 -:= 1;
         b, bw := ElementOfOrder (P, 3, Limit: Fct := Fct);
         if Type (b) eq BoolElt then return false, _; end if;
          
         nmr := Limit;
         repeat 
            nmr -:= 1;
            c, cw := Random (P);
            a := x^c;
         until Fct (a * b) eq 7 or nmr eq 0;
      
      until nmr ne 0 or nmr1 eq 0;
   
   until (nmr1 ne 0 and Fct (a * b * a * b^2) ne 4) or nmr0 eq 0;
   
   if nmr0 eq 0 then return false, _; end if;

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 7 and Fct (a * b * a * b^2) eq 12) or nmr eq 0;
  
   if nmr eq 0 then return false, _; end if;   

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
