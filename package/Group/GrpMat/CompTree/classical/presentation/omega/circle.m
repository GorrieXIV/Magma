freeze;

import "plus.m": MyOmegaPlusPres; 

ConstructPlus := function (d, q)
   Z := Integers ();
   G := GL(d, q);
   F := GF (q);
   q := #F;
   w := PrimitiveElement(F);
   G := SL(d, F);
   e := Degree(F);

   Q := ClassicalStandardGenerators ("Omega", d, #F);
   Q := [G!Q[i] : i in [1..#Q]];

   ss := Q[1];
   tt := Q[2];
   ddelta := Q[3];
   v := Q[4];

   SS := SLPGroup (5);

   if IsOdd((d+1) div 2) then
      t := (GL(d, F)!(v^-1 * tt*v))^-1;
      T := (SS.2^SS.4)^-1;
      s := (GL(d, F)!(v^-1 * ss*v))^-1;
      S := (SS.1^SS.4)^-1;
   else
      t := GL(d, F)!(v^-1 * tt*v);
      T := SS.2^SS.4;
      s := GL(d, F)!(v^-1 * ss*v);
      S := SS.1^SS.4;
   end if;

   delta := GL(d, F)!(v^-1 * ddelta*v);
   DELTA := SS.3^SS.4;
   r := (t^s)^-1;
   R := (T^S)^-1;

   /* We now find the generators of OmegaPlus(d-1, q)
      as words in the generators for OmegaCircle(d, q).

      t^n sends col d-1 to d-1 + n*col 1 and
      col 2 to n^2*col 1 2n*col d-1 + col 2.
   
      Let a = [1, 1], b = [1, d-1], c = [1, 2].
      We need to solve an^2 + 2bn + c = 0 in order
      to get the power of n we need to kill the [1, 2] position */

   B := (t^v)^-1*t^((q-1) div 2)*t^v;
   a := B[1, d];
   n := Z!(-a/2);

   t2 := t^n*(t^v)^-1*t^((q-1) div 2)*t^v;
   T2 := T^n*(T^SS.4)^-1*T^((q-1) div 2)*T^SS.4;
   r2 := (r^n*(r^v)^-1*r^((q-1) div 2)*r^v)^-1;
   R2 := (R^n*(R^SS.4)^-1*R^((q-1) div 2)*R^SS.4)^-1;

   B := ((t*s)^v)^-1*t^((q-1) div 2)*(t*s)^v;
   a := B[1, d];
   n := Z!(-a/2);

   t1 := (t^n*((t*s)^v)^-1*t^((q-1) div 2)*(t*s)^v)^-1;
   T1 := (T^n*((T*S)^SS.4)^-1*T^((q-1) div 2)*(T*S)^SS.4)^-1;
   r1 := (r^n*((r*s)^v)^-1*r^((q-1) div 2)*(r*s)^v);
   R1 := (R^n*((R*S)^SS.4)^-1*R^((q-1) div 2)*(R*S)^SS.4);

   u := (r1^(t1^-1)*r1^2)^-1;
   U := (R1^(T1^-1)*R1^2)^-1;

   FF := sub<F|w^2>;
   py := FF!w;

   Ot1 := Id(G);
   ot1 := Id(SS);
   for i in [1..e] do
      Ot1 := Ot1*(t1^(delta^-(i-1)))^Z!Eltseq(py)[i];
      ot1 := ot1*(T1^(DELTA^-(i-1)))^Z!Eltseq(py)[i];
   end for;

   Or1 := Id(G);
   or1 := Id(SS);
   for i in [1..e] do
      Or1 := Or1*(r1^(delta^(i-1)))^Z!Eltseq(py)[i];
      or1 := or1*(R1^(DELTA^(i-1)))^Z!Eltseq(py)[i];
   end for;

   Ot2 := Id(G);
   ot2 := Id(SS);
   for i in [1..e] do
      Ot2 := Ot2*(t2^(delta^-(i-1)))^Z!Eltseq(py)[i];
      ot2 := ot2*(T2^(DELTA^-(i-1)))^Z!Eltseq(py)[i];
   end for;

   Or2 := Id(G);
   or2 := Id(SS);
   for i in [1..e] do
      Or2 := Or2*(r2^(delta^(i-1)))^Z!Eltseq(py)[i];
      or2 := or2*(R2^(DELTA^(i-1)))^Z!Eltseq(py)[i];
   end for;

   delta1 := r1*delta*t1;
   DELTA1 := R1*DELTA*T1;
   for j in [1..e] do
      a := Z!Eltseq((w^-1 - 1))[j];
      if IsOdd(j) then
         delta1 := delta1*(r1^(delta^((j-1) div 2)))^a;
         DELTA1 := DELTA1*(R1^(DELTA^((j-1) div 2)))^a;
      else
         delta1 := delta1*(Or1^(delta^((j-2) div 2)))^a;
         DELTA1 := DELTA1*(or1^(DELTA^((j-2) div 2)))^a;
      end if;
   end for;
   delta1 := delta1*Ot1^-1;
   DELTA1 := DELTA1*ot1^-1;
   b := delta1[3, 1];
   for j in [1..e] do
      a := Z!Eltseq(-b/w)[j];
      if IsOdd(j) then
         delta1 := delta1*(r1^(delta^((j-1) div 2)))^a;
         DELTA1 := DELTA1*(R1^(DELTA^((j-1) div 2)))^a;
      else
         delta1 := delta1*(Or1^(delta^((j-2) div 2)))^a;
         DELTA1 := DELTA1*(or1^(DELTA^((j-2) div 2)))^a;
      end if;
   end for;

   delta2 := ((delta1^u)^s)^u;
   DELTA2 := ((DELTA1^U)^S)^U;

   if d eq 3 then
      r1 := Id(G);
      t1 := Id(G);
      r2 := Id(G);
      t2 := Id(G);
      delta1 := delta;
      delta2 := delta;
   end if;

   S1 := Id(SS);
   S2 := Id(SS);

   FF := sub<F|w^2>;
   py := FF!w;

   ot := Id(G);
   TO := Id(SS);
   for i in [1..e] do
      ot := ot*(t^delta^-(i-1))^Z!Eltseq(py)[i];
      TO := TO*(T^DELTA^-(i-1))^Z!Eltseq(py)[i];
   end for;

   ro := Id(G);
   RO := Id(SS);
   for i in [1..e] do
      ro := ro*(r^delta^(i-1))^Z!Eltseq(py)[i];
      RO := RO*(R^DELTA^(i-1))^Z!Eltseq(py)[i];
   end for;

   words := [T2, DELTA1, SS.5, T1, DELTA2];
   u := SS.5;
   s4 := u^-2 * SS.1^(SS.4^2) * u * SS.1^(SS.4^2);
   words := [s4] cat words;
   return words;
end function;

MyO5Pres := function (q: MinGens := true) 
   if MinGens eq false then 
      F := SLPGroup (5 + 6);
   else 
      F := SLPGroup (5);
   end if;
   
   d := 5;
   s := F.1; t := F.2; delta := F.3; u := F.4; v := F.5;

   W := ConstructPlus (d, q);
   Y := Evaluate (W, [s, t, delta, v, u]);
   sp :=  Y[1];  tp := Y[2];  deltap := Y[3]; 
   s1p := Y[4]; t1p := Y[5]; delta1p := Y[6];

   _, b := Valuation (q - 1, 2);
   
   rels := [];

   Y, S := ClassicalStandardPresentation ("SL", 2, q);
   gens := [s1p, s1p, t1p^1, delta1p];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   Y, S := ClassicalStandardPresentation ("SL", 2, q: Projective:=true);
   gens := [s, s, t, delta];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   h1 := delta1p; h2 := delta;
   ua1 := t1p; ua2 := t;
   r1 := s1p; r2 := s;
   w := r1 * r2;

   Append (~rels, h1^r2 = h1 * h2);
   Append (~rels, h2^r1 = h1^2 * h2);
   Append (~rels, w^4 = 1);
   Append (~rels, ua2^(w^2) = ua2^r2);

   Append (~rels, ua1^(w) = tp * sp^-1 * tp);

   Append (~rels, ua1^(h2^-1) = ua1^(h1));

   Append (~rels, h1 * h2 = h2 * h1);

   Append (~rels, (ua1, ua1^w) = Id (F));
   Append (~rels, (ua1, ua2^w) = Id (F));
   Append (~rels, t1p^-2 = (ua2^w, ua2^r2)); 
   Append (~rels, (ua1, ua2) = (ua2^-1)^(w * r2) * ua1^r2);

   // not needed according to CRLG writeup 
   // x := (ua1, ua2);
   // Append (~rels, tp^-1 = t^-1 * x^s1p);

   if not MinGens then
      Append (~rels, sp = F.6);
      Append (~rels, tp = F.7);
      Append (~rels, deltap = F.8);
      Append (~rels, s1p = F.9);
      Append (~rels, t1p = F.10);
      Append (~rels, delta1p = F.11);
   end if;

   E := GF (q);
   I := Integers ();
   w := PrimitiveElement (E);
   R := sub <E | w^-2>;
   k := Eltseq (R!w^1);
   k := [I!x: x in k];
   Append (~rels, ua2^h1 = &*[(ua2^(h2^((q + 1) * (i-1) div 2)))^k[i]:
                              i in [1..#k]]);
   Append (~rels, v = u);

   R := [LHS (r) * RHS (r)^-1: r in rels];
   R := [r : r in R];

   return F, R;
end function;

// standard presentation for Omega(2n+1, q)

MyOmegaPres := function (d, q: MinGens := true)
   assert IsOdd (q);
   assert IsOdd (d);
   n := d div 2;

   if d eq 3 then
      Q, R := ClassicalStandardPresentation ("SL", 2, q: Projective:=true);
      Q := SLPGroup (5);
      R := Evaluate (R, [Q.i: i in [1, 1, 2, 3]]);
      Append (~R, Q.4);
      Append (~R, Q.5);
      return Q, R;
   end if;
      
   if d eq 5 then return MyO5Pres (q: MinGens := MinGens); end if;

   if MinGens then 
      F := SLPGroup (5);
   else
      F := SLPGroup (5 + 6);
   end if;

   s := F.1; t := F.2; delta := F.3; u := F.5; v := F.4; 

   rels := [];

   words := ConstructPlus (d, q);
   words := Evaluate (words, [F.i: i in [1..5]]);
   sp := words[1]; tp := words[2]; deltap := words[3]; s1p := words[4];
   t1p := words[5]; delta1p := words[6]; 

   if not MinGens then 
      Append (~rels, sp = F.6);
      Append (~rels, tp = F.7);
      Append (~rels, deltap = F.8);
      Append (~rels, s1p = F.9);
      Append (~rels, t1p = F.10);
      Append (~rels, delta1p = F.11);
   end if;

   // Omega^+(2n,q) presentation on "p" generators
   Y, S := MyOmegaPlusPres (2 * n, q);
   gens := [sp, tp, deltap, s1p, t1p, delta1p, F.0, v];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   //  Omega(5, q) presentation 
   Y, S := MyO5Pres (q: MinGens := true);
   gens := [s, t, delta, u^(v^-2), u^(v^-2)];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   for x in [sp, tp, deltap, s1p, t1p, delta1p] do
      for y in [s, t, delta] do 
         Append (~rels, (x, y) = Id (F));
      end for;
   end for;

   for x in [s, t, delta] do 
      for y in [u, (u^3)^(v^-2) * v] do 
         Append (~rels, (x, y) = Id (F));
      end for;
   end for;

   R := [LHS (r) * RHS (r)^-1: r in rels];
   R := [r : r in R];
   return F, R;
end function;
