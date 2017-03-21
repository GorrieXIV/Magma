freeze;

/* symmetric group of degree d */

PresentationForSn := function (d: SLP := true)
   F := SLP eq true select SLPGroup (2) else FreeGroup (2);
   U := F.1;  // (1, 2) 
   V := F.2;  // (1,2, ..., d)
   Rels := [];
   Append (~Rels, U^2 = 1);
   if d eq 1 then 
      Append (~Rels, U = 1);
      Append (~Rels, V = 1);
   elif d eq 2 then
      Append (~Rels, U = V);
   else 
      Append (~Rels, V^d = 1);
      Append (~Rels, (U*V)^(d-1) = 1);
      Append (~Rels, (U, V)^3 = 1);
   end if;
   for i in [2..(d div 2)] do Append (~Rels, (U, V^i)^2 = 1); end for;
   if SLP eq false then 
      return quo< F | Rels>, _;
   else 
      Rels := [LHS (r) * RHS (r)^-1: r in Rels];
      return F, Rels;
   end if;
end function;

// q = 2^k 
EvenPlusPres := function (d, q)

   assert IsEven (d);
   assert IsEven (q);
   n := d div 2;
   
   F := SLPGroup (8);

   v := F.8;
   y := F.1; x := F.4; 
   t := F.2; s := F.5; 
   delta := F.6; deltad := F.3; z := deltad;
   
   // some of the standard generators are the identity
   rels := [F.i = 1: i in [7]];
   
   a := (x * y)^v;

   // define s in terms of t 
   Append (~rels, t^((x*y)^v) = s);
   Append (~rels, z = delta^a); 

   // Sym(n) presentation on x and v 
   Q, R := PresentationForSn (n: SLP := true);
   gens := [x, v]; 
   R := Evaluate (R, gens);
   rels cat:= [r = Id (F): r in R];

   Append (~rels, y^2 = 1);
   Append (~rels, (x*y)^2 = 1);

   Append (~rels, (x*y, (x*y)^v) = 1);
   Append (~rels, (x*y, v) = (x*y)^(v*x)); 

   Append (~rels, (t, x) = 1);
   Append (~rels, (t^((x*y)^v), t) = 1); 

   Append (~rels, (delta, t) = 1);
   Append (~rels, (delta, z) = 1);
   Append (~rels, (delta, y) = 1);

   if n gt 3 then 
      Append (~rels, (y, x^(v^2)) = 1); 
      Append (~rels, (x*y, (x*y)^(v^2)) = 1); 
      Append (~rels, (t, x^(v^2)) = 1); 
      Append (~rels, (t, s^(v^2)) = 1);
      Append (~rels, (t, t^(v^2)) = 1);
   end if;

   if n gt 4 then 
      Append (~rels, (y, v * (x, v)) = 1);
      Append (~rels, (t, v * (x, v)) = 1);
      Append (~rels, (delta, v * (x, v)) = 1);
   end if;

   tm12 := t^((x*y)^(v*x));
   t1m2 := t^(x^v);
   tm1m2 := t^(y);

   a := x^v * x; // (1,2,3)
   
   Append (~rels, (t, t^v) = 1); 
   Append (~rels, (t, t1m2^v) = 1); 
   Append (~rels, (t, tm12^v) = (t^(x^a))^-1); 
   Append (~rels, (t, tm1m2^v) = s^(x^a));

   // necessary? 
   Append (~rels, (t, tm12) = 1); 
   Append (~rels, (t, t1m2) = 1); 

   Append (~rels, (delta, delta^v) = 1);
   if n gt 3 then 
      Append (~rels, (delta, x^(v^2)) = 1);
      Append (~rels, (delta, t^(v^2)) = 1);
      // is this necessary?
      Append (~rels, (delta, s^(v^2)) = 1);
   end if;
   if n gt 4 then 
      Append (~rels, (delta, v * (x, v)) = 1);
   end if;
   Append (~rels, delta^x = delta^-1);
   Append (~rels, t^(z * v) = t^(v * delta^-2));

   Append (~rels, (delta, delta^v) = 1);
   Append (~rels, (delta, delta^(v^2)) = 1);

   // sl2 presentation on y, t, z 
   Y, S := ClassicalStandardPresentation ("SL", 2, q);
   gens := [y, y, t, z];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   R := [LHS (r) * RHS (r)^-1: r in rels];
   return F, R;
end function;
