freeze;

/* black box recognition procedure for G2(5) */

import "../Presentations/G25.m":PresentationG25;
 
StandardGeneratorsG25 := function (G : Projective := false, Limit := 500)

  Fct := Projective select CentralOrder else Order;
  
  P := RandomProcessWithWords (G); 
  x, xw := ElementOfOrder (P, {2}, Limit: Fct := Fct);
  if Type (x) eq BoolElt then return false, _; end if;

  nmr := Limit;
  repeat
      y, yw := ElementOfOrder (P, {20, 30}, Limit: Fct := Fct);
      if Type (y) eq BoolElt then return false, _; end if;
    
      o := Fct (y);
      b := y^(o div 5); bw := yw^(o div 5);

      nmr1 := Limit;
      repeat 
	  nmr1 -:= 1;

	  c, cw := Random (P);
	  a := x^c;
      until Fct (a * b) eq 7 or
	  Fct (a * b) in {2, 6, 8, 10, 10, 12, 20} or nmr eq 0;
      
      if nmr1 eq 0 then return false, _; end if;
      
  until Fct (a * b) eq 7 or nmr eq 0;

  if nmr eq 0 then return false, _; end if;
  
  aw := xw^cw; 

  // Now got (2, 5B) std gens, convert to (2, 3B)-gens, where we have
  // maximal subgroups etc

  W<x, y> := SLPGroup(2);
  conversion := [x, ((x*y*x*y*x*y^-1)^4)^((x*y^2)^-8*(x*y)^-2)];

  gens := Evaluate(conversion, [a, b]);
  slps := Evaluate(conversion, [aw, bw]);
  
  return gens, slps;
end function;
