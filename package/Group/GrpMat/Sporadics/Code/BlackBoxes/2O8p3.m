freeze;

/* black box recognition procedure for 2.O8p(3) */

import "../Presentations/2O8p3.m" : Presentation2O8p3;
 
StandardGenerators2O8p3 := function (G : Projective := false, Limit := 1000)

   Fct := Projective select CentralOrder else Order;
   Fct := Order;
   
   P := RandomProcessWithWords(G); 
   repeat 
      g, gw := ElementOfOrder(P, {10, 14, 18}, Limit: Fct := Fct);
   until Order (g) eq CentralOrder (g);

   if Type (g) eq BoolElt then return false, _; end if;

   h, hw := ElementOfOrder(P, {40}, Limit: Fct := Fct);
   if Type (h) eq BoolElt then return false, _; end if; 

   o := Fct(g);
   x := g^(o div 2);
   xw := gw^(o div 2);

   o := Fct(h);
   b := h^(o div 5);
   bw := hw^(o div 5);
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random(P);
      a := x^c;
   until (Fct(a * b) in {13,26} and Fct(a * b * b) in {14, 28}) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   if Order (a * b) eq 26 then 
      repeat 
         f, x, xw := RandomElementOfOrder (G, 2);
      until IsCentral (G, x);
      a := a * x;
      aw := aw * xw;
   end if;
      
   return [a, b], [aw, bw];

end function;
