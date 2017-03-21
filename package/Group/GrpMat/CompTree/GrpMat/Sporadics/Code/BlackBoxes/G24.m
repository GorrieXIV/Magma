freeze;

/* black box recognition procedure for G2(4) */

import "../Presentations/G24.m":PresentationG24;
 
StandardGeneratorsG24 := function (G : Projective := false, Limit := 1000)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {4, 8, 12}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);

   nmr1 := Limit;
   repeat 
      nmr1 -:= 1;

      y, yw := ElementOfOrder (P, {5,10,15}, Limit: Fct := Fct);
      if Type (y) eq BoolElt then return false, _; end if;

      o := Fct (y);
      if o gt 5 then
	s := Quotrem(o, 5);
	b := y^(o div s); bw := yw^(o div s);
      else
	b := y;
	bw := yw;
      end if;
	
      nmr2 := Limit;
      repeat
	  nmr2 -:= 1;
          c, cw := Random (P);
	  a := x^c;
      until Fct (a * b) eq 13 and Fct (a * b^2) eq 13 or nmr2 eq 0;
  until Fct ((a * b)^2 * b) eq 15 or nmr1 eq 0;

   if nmr1 eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
