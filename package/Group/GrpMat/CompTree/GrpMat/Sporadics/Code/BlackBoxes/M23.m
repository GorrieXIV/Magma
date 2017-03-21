freeze;

/* black box recognition procedure for M23 */

 
import "../Presentations/M23.m":PresentationM23;

StandardGeneratorsM23 := function (G : Projective := false, Limit := 450)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   x, xw := ElementOfOrder (P, 2, Limit: Fct := Fct);
   if Type (x) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, 4, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 23 and (Fct ((a * b)^2 * (a * b * a * b^2)^2 * a * b^2) eq 8 or Fct ((a * b)^2 * (a * b * a * b^2)^2 * a * b^2) eq 11)) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw;

   if Fct ((a * b)^2 * (a * b * a * b^2)^2 * a * b^2) eq 11 then
      b := b^-1;
      bw := bw^-1;
   end if;

   return [a, b], [aw, bw];

end function;
