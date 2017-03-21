freeze;

import "evenplus.m": EvenPlusPres;
forward GeneratorOfCentre; 

PresentationForAn := function (n) 
   F := SLPGroup (2);
   a := F.1; b := F.2;
   if IsOdd (n) then 
      // n odd:  a=(1,2,3), b=(1,2,...,n),
      R := [a^3, b^n, (a*b^2)^((n-1) div 2)];
      for j in [2..n - 2] do Append (~R, ((b*a)^j*b^-j)^2); end for;
   else
      // n even:  a=(1,2,3), b=(2,...,n),
      R := [ a^3, b^(n-1), (b^2*a^-1)^(n div 2), (b*a^-1)^(n-1)];
      for j in [1..n div 2 - 1] do
         Append (~R, ((b^-1*a*b^-1)^j*(b^2*a^-1)^j)^2);
         if j le n div 2 - 2 then
            Append (~R, ((b^-1*a*b^-1)^j*(a^-1*b^2)^j*a^-1)^2);
         end if;
      end for;
   end if;
   return R;
end function;

// standard presentation for Omega+(d, q)

MyOmegaPlusPres := function (d, q: Projective := false)
   F := SLPGroup (8);

   assert IsEven (d);
   n := d div 2;
   
   s := F.1; s1 := F.4;
   t := F.2; t1 := F.5;
   d := F.3; d1 := F.6;
   v := F.8;

   // one of the standard generators is the identity 
   rels := [F.7 = 1];

   if n eq 2 then
      // sl2 presentation on s, t, d 
      Y, S := ClassicalStandardPresentation ("SL", 2, q);
      gens := [s, s, t, d, s^0, s^0, s^0, s^0];
      T := Evaluate (S, gens);
      rels cat:= [t = Id (F): t in T];
      // sl2 presentation on s1, t1, d1 
      gens := [s1, s1, t1, d1, s1^0, s1^0, s1^0, s1^0];
      T := Evaluate (S, gens);
      rels cat:= [t = Id (F): t in T];
      Append (~rels, (s, s1) = 1);
      Append (~rels, (s, t1) = 1);
      Append (~rels, (s, d1) = 1);
      Append (~rels, (t, s1) = 1);
      Append (~rels, (t, t1) = 1);
      Append (~rels, (t, d1) = 1);
      Append (~rels, (d, s1) = 1);
      Append (~rels, (d, t1) = 1);
      Append (~rels, (d, d1) = 1);
      Append (~rels, v = s1);
      Append (~rels, s^2 = s1^2);
      if Projective and IsOdd (q) then
         Append (~rels, GeneratorOfCentre (4, q, F) = 1);
      end if;
      R := [LHS (r) * RHS (r)^-1: r in rels];
      return F, [r: r in R];
   elif IsEven (q) then 
      return EvenPlusPres (2 * n, q); 
   end if;

   u := s * s1;
   Append (~rels, d1 = d^(u^v));
   Append (~rels, t1 = (t^-1)^(u^v));

   c := s1^v * s1; // (1,2,3)

   if n eq 3 then
     rels cat:= [c^3 = 1, v = c];
   else 
      if IsEven (n) then r := v * s1^-1; else r := v; end if;
      // Alt (n) defined on c and r 
      R := PresentationForAn (n);
      R := Evaluate (R, [c, r]);
      rels cat:= [r = Id (F): r in R];
   end if;
   
   // 2 
   Append (~rels, s^4 = 1);
   Append (~rels, (s, s1) = 1);
   Append (~rels, u^2 = 1);

   // 3 
   if n gt 3 then 
      Append (~rels, (s, s1^(v^2)) = 1); 
      Append (~rels, (s1, s^(v^2)) = 1); 
      Append (~rels, (s, s^(v^2)) = 1); 
   end if;

   // 4 
   if n gt 4 then Append (~rels, (u, v * (s1, v)) = 1); end if;

   // 5 
   Append (~rels, (u, u^v) = 1);

   // 6 
   Append (~rels, c^(s1) = s1^2 * c^-1);
   Append (~rels, v^(s1) = s1^2 * v * c);

   //  7
   Append (~rels, (u, s^v) = u^v);

   // 9
   Append (~rels, (d, s1) = 1);
   Append (~rels, (d, t1) = 1);
   Append (~rels, (d, d1) = 1);

   // 10 
   if n gt 3 then 
      Append (~rels, (t, s^(v^2)) = 1);
      Append (~rels, (t, s1^(v^2)) = 1);
      // necessary?
      Append (~rels, (t, t^(v^2)) = 1);
   end if;

   // 11 
   if n gt 4 then 
      Append (~rels, (t, v * (s1, v) * ((s1^2)^v)) = 1);
      Append (~rels, (d, v * (s1, v) * ((s1^2)^v)) = 1);
   end if;

   a := s1^v * s1;
   
   tm12 := t^(u^(v*s1));
   t1m2 := t^(s1^v);
   tm1m2 := t^(u);

   // 12 
   Append (~rels, (t, t^v) = 1);
   Append (~rels, (t, tm12^v) = (t^(s1^a))^-1);
   Append (~rels, (t, t1m2^v) = 1);
   b := (t^(u^v))^-1;
   Append (~rels, (t, tm1m2^v) = b^(s1^a));

   // necessary?
   Append (~rels, (t, tm12) = 1);
   Append (~rels, (t, t1m2) = 1);

   // 8 
   // sl2 presentation on s, t, d 
   Y, S := ClassicalStandardPresentation ("SL", 2, q);
   gens := [s, s, t, d];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   // 13
   Append (~rels, (d, d^v) = 1);
   // 14 
   if n gt 3 then 
      Append (~rels, (d, s1^(v^2)) = 1);
      Append (~rels, (d, t^(v^2)) = 1);
   end if;

   // 15
   if n gt 4 then 
      Append (~rels, (d, v *(s1, v)) = 1); 
   end if;

   // 16
   // unnecessary?
   Append (~rels, d^s = d^-1);
   
   // 17
   Append (~rels, t^(d * v) = t^(v * d1^-2));

   // 18
   Append (~rels, (d, d^v) = 1);
   Append (~rels, (d, d^(v^2)) = 1);

   // projective? 
   if Projective then 
      z := GeneratorOfCentre (2 * n, q, F);
      Append (~rels, z = 1);
   end if;

   R := [LHS (r) * RHS (r)^-1: r in rels];
   return F, [r: r in R];
end function;

GeneratorOfCentre := function (d, q, F)
   if q mod 4 eq 3 then
      if IsEven (d div 2) then
         z := &*[F.3^(F.8^(2 * i)): i in [0..d div 4 - 1]];
         z := z^((q - 1) div 2);
      else
         z := F.0;
      end if;
   else
      z := &*[F.3^(F.8^(2 * i)): i in [0..d div 2 - 1]];
      z := z^((q - 1) div 4);
   end if;
   return z;
end function;
