freeze;

/* black box recognition procedure for O8p(3) and 2.O8p(3) */

import "../Presentations/O8p3.m" : PresentationO8p3;

StandardGenerators2O8p3 := function (G: Limit := 1000) 

   P := RandomProcessWithWords(G); 
   repeat 
       g, gw := ElementOfOrder(P, {10, 14, 18}, Limit);
   until Order (g) eq CentralOrder (g);
   if Type (g) eq BoolElt then return false, _; end if;

   h, hw := ElementOfOrder(P, {40}, Limit);
   if Type (h) eq BoolElt then return false, _; end if; 

   o := Order(g);
   x := g^(o div 2);
   xw := gw^(o div 2);

   o := Order(h);
   b := h^(o div 5);
   bw := hw^(o div 5);
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random(P);
      a := x^c;
   until (Order(a * b) in {13, 26} and Order (a * b * b) in {14, 28}) or nmr eq 0; 
   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   if Order (a * b) eq 26 then 
      nmr := Limit;
      repeat 
         nmr -:= 1;
         f, x, xw := RandomElementOfOrder (G, 2);
      until IsCentral (G, x) or nmr eq 0;
      if nmr eq 0 then return false, _; end if;
      a := a * x;
      aw := aw * xw;
   end if;

   if not PresentationO8p3(G: UserGenerators := [a, b], Projective := true) then 
      return false, _; 
   end if;

   return [a, b], [aw, bw];
end function;
 
StandardGeneratorsO8p3 := function (G : Projective := false, Limit := 500)

   if Projective then return StandardGenerators2O8p3 (G); end if;

   P := RandomProcessWithWords(G); 

   g, gw := ElementOfOrder(P, {10, 14, 18}, Limit);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Order(g);
   a := g^(o div 2);
   aw := gw^(o div 2);

   NmrTrials := 10;
   trial := 0;
   repeat 
      trial +:= 1;
      h, hw := ElementOfOrder(P, {5, 10, 15, 20}, Limit);
      if Type (h) eq BoolElt then return false, _; end if; 
      o := Order(h);
      x := h^(o div 5);
      xw := hw^(o div 5);
      nmr := Limit; 
      repeat 
         nmr -:= 1;
         c, cw := Random(P);
         b := x^c;
      until Order (a * b) in {13} and Order (a * b * b) in {14} or nmr eq 0;
   until nmr gt 0 or trial ge NmrTrials;

   if trial ge NmrTrials or nmr eq 0 then return false, _; end if;

   bw := xw^cw; 
   
   return [a, b], [aw, bw];
end function;
