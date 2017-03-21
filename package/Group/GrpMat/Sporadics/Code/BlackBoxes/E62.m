freeze;
    
/* black box recognition procedure for E6(2) */

import "../Presentations/E62.m":PresentationE62;
 
StandardGeneratorsE62 := function (G : Projective := false, Limit := 2000)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {9, 18, 45, 60, 63, 126}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

     // 3C element
   o := Fct (g);
   b := g^(o div 3); bw := w^(o div 3);
   
   g, w := ElementOfOrder (P, {56, 60, 62, 84, 126}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   // 2A element
   o := Fct (g);
   z := g^(o div 2); zw := w^(o div 2);

   nmr1 := Limit;
   repeat
       g, w := ElementOfOrder (P, {10, 16, 20, 30}, Limit: Fct := Fct);
       if Type (g) eq BoolElt then return false, _; end if;
       
       // 2A/B element
       o := Fct (g);
       x := g^(o div 2); xw := w^(o div 2);
     
       nmr := Limit;
       repeat 
	   nmr -:= 1;
	   c, cw := Random (P);
       until Fct(z * x^c) in {6} or Fct(z * x^c) in {1, 3} or nmr eq 0;
       
       //if nmr eq 0 then return false, _; end if;

       nmr1 -:= 1;
   until Fct(z * x^c) in {6} or nmr1 eq 0;

   if nmr1 eq 0 then return false, _; end if;
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
  until Fct(a * b) eq 62 and Fct((a * b)^2 * b) eq 12 and
      Fct((a * b)^3 * b) eq 93 or nmr eq 0;
  
  if nmr eq 0 then return false, _; end if;

  aw := xw^cw; 
  
  return [a, b], [aw, bw];
end function;
