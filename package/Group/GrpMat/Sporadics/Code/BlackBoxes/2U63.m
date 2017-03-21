freeze;

/* black box recognition procedure for 2.U6(3) */

import "../Presentations/2U63.m":Presentation2U63;
 
StandardGenerators2U63 := function (G : Projective := false, Limit := 500)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {122}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   t, tw := ElementOfOrder (P, {30,60,120}, Limit: Fct := Order);
   if Type (t) eq BoolElt then return false, _; end if;

   o := Fct(g);
   a := g^(o div 2);
   aw := w^(o div 2);

   o := Order(t);
   t ^:= o div 15;
   tw ^:= o div 15;
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      b := t^c;
   until Fct (a * b) eq 91 and Fct (a * b^2) eq 14 and 
	 Order(a * b) eq 91 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   bw := tw^cw; 
         
   return [a, b], [aw, bw];

end function;
