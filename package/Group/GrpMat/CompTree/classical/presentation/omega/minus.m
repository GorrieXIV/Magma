freeze;

import "plus.m": MyOmegaPlusPres;
import "minus6.m": MyOMinusPres6, EvenConvert, OddConvert; 

forward GeneratorOfCentre;

// standard presentation for Omega-(d, q)
MyOmegaMinusPres := function (d, q: MinGens := true, Projective := false)
   assert d ge 4;
   assert IsEven (d);
   n := d div 2;
  
   if d eq 4 then
      Q, R := ClassicalStandardPresentation ("SL", 2, q^2: Projective := true); 
      Q := SLPGroup (5);
      if IsEven (q) then 
         R := Evaluate (R, [Q.1^Q.2, Q.1^Q.2, Q.1, Q.3]);
         Append (~R, (Q.1 * Q.1^Q.2 * Q.1) * Q.2^-1);
      else 
         R := Evaluate (R, [Q.i: i in [1, 1, 2, 3]]);
      end if;
      Append (~R, Q.4);
      Append (~R, Q.5);
      return Q, R;
   end if;
      
   if d eq 6 then 
      return MyOMinusPres6 (q: Six := true, Projective := Projective, MinGens := MinGens); 
   end if;

   if MinGens then 
      F := SLPGroup (5);
   else
      F := SLPGroup (5 + 6);
   end if;

   s := F.1; t := F.2; delta := F.3; u := F.4; v := F.5; 

   rels := [];

   if IsEven (q) then 
      words := EvenConvert (d, q);
      words := Evaluate (words, [F.i:i in [1..5]]);
      sp := words[1]; tp := words[2]; deltap := words[3]; s1p := words[4];
      t1p := words[5]; delta1p := words[6]; 
   else 
      sp := ((u^(v^-2))^-1 * s * s^(v^-1))^(v^2);
      s1p := (u^(v^-2))^(v^2);
      delta1p := (delta^-1 * delta^(v^-1))^(v^2);
      deltap := ((delta^-1 * delta^(v^-1))^s)^(v^2);
      t1p, tp := OddConvert (d, q);
      tp := Evaluate (tp, [F.i : i in [1..5]]);
      t1p := Evaluate (t1p, [F.i : i in [1..5]]);
   end if;

   if not MinGens then 
      Append (~rels, sp = F.6);
      Append (~rels, tp = F.7);
      Append (~rels, deltap = F.8);
      Append (~rels, s1p = F.9);
      Append (~rels, t1p = F.10);
      Append (~rels, delta1p = F.11);
   end if;

   // Omega^+(2n,q) presentation on "p" generators
   Y, S := MyOmegaPlusPres (2 * (n - 1), q);
   gens := [sp, tp, deltap, s1p, t1p, delta1p, F.0, v];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   //  Omega^-(6, q) presentation 
   Y, S := MyOMinusPres6 (q: MinGens := true);
   gens := [s, t, delta, u^(v^-2), u^(v^-2)];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   for x in [sp, tp, deltap, s1p, t1p, delta1p] do
      for y in [s, t, delta] do 
         Append (~rels, (x,y) = Id (F));
      end for;
   end for;

   for x in [s1p, v * ((s1p^-1)^(v^-1))] do
      Append (~rels, (s, x) = 1);
      Append (~rels, (t, x) = 1);
      Append (~rels, (delta, x) = 1);
   end for; 

   Append (~rels, (delta^(q - 1), v) = 1);

   if Projective and IsOdd (n) and q mod 4 eq 3 then
      z := GeneratorOfCentre (d, q, F, deltap, v);
      Append (~rels, z = 1);
   end if;

   R := [LHS (r) * RHS (r)^-1: r in rels];
   R := [r : r in R];
   return F, R;
end function;

GeneratorOfCentre := function (d, q, F, deltap, v)
   n := d div 2; 
   if IsOdd (n) and q mod 4 eq 3 then
      z := &*[deltap^(v^(2 * i)): i in [0..d div 4 - 1]];
      z := z^((q - 1) div 2);
      z *:= F.3^((q^2 - 1) div 4);
   else
      z := F.0;
   end if;
   return z;
end function;
