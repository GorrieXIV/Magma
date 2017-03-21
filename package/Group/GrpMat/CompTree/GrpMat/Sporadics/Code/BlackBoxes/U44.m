freeze;

/* black box recognition procedure for U4(4) */

import "../Presentations/U44.m":PresentationU44;
 
StandardGeneratorsU44 := function (G : Projective := false, Limit := 500)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {20, 30}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct(g);
   x := g^(o div 2);
   xw := w^(o div 2);
           
   nmr := Limit;
   repeat 
      nmr -:= 1;
      
      b, bw := ElementOfOrder (P, {4}, Limit: Fct := Fct);
      if Type (b) eq BoolElt then return false, _; end if;
      
      nmr1 := Limit;
      badB := true;
      repeat
	  nmr1 -:= 1;
	  c, cw := Random (P);
	  a := x^c;

	  if Fct (a * b) gt 15 then
	      badB := false;
	  end if;
      until Fct (a * b) eq 20 or nmr1 eq 0;

      if nmr1 eq 0 and not badB then
	  nmr := 0;
      end if;
   until Fct (a * b) eq 20 or nmr eq 0;
  
   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   return [a, b], [aw, bw];

end function;
