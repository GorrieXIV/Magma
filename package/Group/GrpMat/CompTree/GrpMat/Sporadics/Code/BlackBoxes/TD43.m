freeze;

/* black box recognition procedure for TD4(3) */

import "../Presentations/TD43.m":PresentationTD43;
 
StandardGeneratorsTD43 := function (G : Projective := false, Limit := 3000)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {42,78,84}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   z, zw := ElementOfOrder (P, {73}, Limit: Fct := Fct);
   if Type (z) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 3); xw := w^(o div 3);
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
      aw := xw^cw; 
      
      found := false;
      for i in [0 .. 5] do
	  b := a^(-1) * z^(5^i);
	  bw := aw^(-1) * zw^(5^i);
	  
	  if Fct(a) eq 3 and Fct(b) eq 13 and Fct(a * b) eq 73 and 
	      Fct(a * b^2) eq 73 and Fct((a * b)^2 * b) eq 13 then
	      found := true;
	      break;
	  end if;
      end for;
   until found or nmr eq 0;

   if nmr eq 0 then return false, _; end if;
   
   return [a, b], [aw, bw];

end function;
