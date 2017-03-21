freeze;

/* black box recognition procedure for M24 */

 
import "../Presentations/M24.m":PresentationM24;

StandardGeneratorsM24 := function (G : Projective := false, Limit := 150)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, 10, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   h, v := ElementOfOrder (P, 15, Limit: Fct := Fct);
   if Type (h) eq BoolElt then return false, _; end if;

   o1 := Fct (g); o2 := Fct (h);
   x := g^(o1 div 2); xw := w^(o1 div 2);
   b := h^(o2 div 3); bw := v^(o2 div 3);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 23 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   if Fct (a * b * (a * b * a * b^2)^2 * a * b^2) eq 5 then
      b := b^-1;
      bw := bw^-1;
   end if;

   return [a, b], [aw, bw];

end function;
