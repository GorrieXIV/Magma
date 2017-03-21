freeze;

/* black box recognition procedure for TE6(2) */

import "../Presentations/TE62.m":PresentationTE62;
 
StandardGeneratorsTE62 := function (G : Projective := false, Limit := 2000)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {9, 18}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   z, zw := ElementOfOrder (P, {22}, Limit: Fct := Fct);
   if Type (z) eq BoolElt then return false, _; end if;

     // 3C element
   o := Fct (g);
   b := g^(o div 3); bw := w^(o div 3);
   
   // 2A element
   z ^:= 11;
   zw ^:= 11;

   nmr1 := Limit;
   repeat
       g, w := ElementOfOrder (P, {10,16,20,24}, Limit: Fct := Fct);
       if Type (g) eq BoolElt then return false, _; end if;
       
       // 2A/B element
       o := Fct (g);
       x := g^(o div 2); xw := w^(o div 2);
     
       nmr := Limit;
       repeat 
	   nmr -:= 1;
	   c, cw := Random (P);
       until Fct(z * x^c) eq 6 or Fct(z * x^c) in {1, 3} or nmr eq 0;
       
       if nmr eq 0 then return false, _; end if;

       nmr1 -:= 1;
   until Fct(z * x^c) eq 6 or nmr1 eq 0;

   if nmr1 eq 0 then return false, _; end if;

   // x is now a 2B element
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 19 and Fct ((a * b)^3 * b) eq 33 
   or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
