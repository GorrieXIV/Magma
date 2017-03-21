freeze;

/* black box recognition procedure for M11 */
 
import "../Presentations/M11.m":PresentationM11;

StandardGeneratorsM11 := function (G : Projective := false, Limit := 75)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, 4, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);
   b := g^(o div 4); bw := w^(o div 4);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 11 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   if Fct (a * b * a * b^2 * a * b^3) eq 3 then
      b := b^-1;
      bw := bw^-1;
   end if;

   return [a, b], [aw, bw];

end function;
