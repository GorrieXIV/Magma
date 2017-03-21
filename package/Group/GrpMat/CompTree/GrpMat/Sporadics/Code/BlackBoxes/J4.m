freeze;

/* black box recognition procedure for J4:
   two different lists of standard generators defined for J4,
   one of size 2, the other of size 3; the max subgroups
   are recorded as SLPs in the 2 */

import "../Presentations/J4.m":PresentationJ4;

StandardGeneratorsJ4 := function (G : Projective := false, Limit := 7000)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {20,40,44}, 150: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);
   b := g^(o div 4); bw := w^(o div 4);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 37 and Fct (a * b * a * b^2) eq 10) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

   /*
   * Words to get from G1-standard generators of J4, (a,b), to the
   * presentation (G2) generators, (x,y,t).
   * Have <x,y> = M24. <x,z> = 2^6:(S3 x L3(2)) commutes with involution t.
   */

   x := ((a*b*a*b^2)^5)^((a*b)^4);
   xw := ((aw*bw*aw*bw^2)^5)^((aw*bw)^4);
   y := ((a*b^2)^4)^((a*b)^2*(b*a)^18);
   yw := ((aw*bw^2)^4)^((aw*bw)^2*(bw*aw)^18);
   z := (x*y)^2*(x*y^2)^2*(x*y)^3;
   zw := (xw*yw)^2*(xw*yw^2)^2*(xw*yw)^3;
   c := a^(a*b*a*b^3*(a*b*a*b^2)^3);
   cw := aw^(aw*bw*aw*bw^3*(aw*bw*aw*bw^2)^3);
   t := (c*z)^15;
   tw := (cw*zw)^15;

   return [x, y, t], [xw, yw, tw];

end function;
