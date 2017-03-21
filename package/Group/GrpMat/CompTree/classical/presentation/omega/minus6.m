freeze;

import "minus.m": GeneratorOfCentre;

EvenConvert := function (d, q)
   
   F := GF (q);
   n := d div 2;
   Q := ClassicalStandardGenerators ("Omega-", d, q);
   G := GL(d, F);

   Q := [GL(d, F)!Q[i] : i in [1..#Q]];
   GGG := sub<GL(d, F)|Q>;
   id := Identity (sub<GL(d, F)|Q>);
   sl := SL(2, #F^2);
   e := Degree (F);
   ee := Degree (GF(#F^2));
   q := #F;
   Z := IntegerRing ();

   tt := GL(d, F)!Q[1];
   rr := GL(d, F)!Q[2];
   ddelta := GL(d, F)!Q[3];
   u := GL(d, F)!Q[4];
   v := GL(d, F)!Q[5];

   SS := SLPGroup (5);

   if IsOdd (d div 2) then
      t := (GL(d, F)!(v^-1*tt*v))^-1;
      T := (SS.1^SS.5)^-1;
      r := (GL(d, F)!(v^-1*rr*v))^-1;
      R := (SS.2^SS.5)^-1;
   else
      t := GL(d, F)!(v^-1*tt*v);
      T := SS.1^SS.5;
      r := GL(d, F)!(v^-1*rr*v);
      R := SS.2^SS.5;
   end if;

   delta := GL(d, F)!(v^-1*ddelta*v);
   DELTA := SS.3^SS.5;
   s := r*t^-1*r;
   S := R*T^-1*R;

   /* We now find the generators of OmegaPlus (d-2, q)
      as words in the generators for OmegaMinus (d, q).

      t^n sends col d-1 to d-1 + n*col 1 and
      col 2 to n^2*col 1 2n*col d-1 + col 2.
   
      Let a = [1, 1], b = [1, d-1], c = [1, 2].
      We need to solve an^2 + 2bn + c = 0 in order
      to get the power of n we need to kill the [1, 2] position */

   r2bar := r *((r^delta)^(r^v))^(delta^-1);
   R2bar := R *((R^DELTA)^(R^SS.5))^(DELTA^-1);
   if (d ne 4) and (d ne 2) then
      zz := Eltseq (r2bar[4, 1]^-1);
   else
      zz := Eltseq (F!1);
   end if;
   r2 := Id (G);
   R2 := Id (SS);
   for i in [1..#zz] do
      if zz[i] eq 1 then
         r2 := r2*r2bar^(delta^(i-1));
         R2 := R2*R2bar^(DELTA^(i-1));
      end if;
   end for;
   
   t2bar := t*((t^delta)^(t^v))^(delta^-1);
   T2bar := T*((T^DELTA)^(T^SS.5))^(DELTA^-1);
   t2 := Id (G);
   T2 := Id (SS);
   for i in [1..#zz] do
      if zz[i] eq 1 then
         t2 := t2*t2bar^(delta^-(i-1));
         T2 := T2*T2bar^(DELTA^-(i-1));
      end if;
   end for;

   r1 := t2^s;
   R1 := T2^S;
   t1 := r2^s;
   T1 := R2^S;
   
   delta2 := (delta*(delta^-1)^v);
   DELTA2 := (DELTA*(DELTA^-1)^SS.5);
   delta1 := ((delta2^u)^s)^u;
   DELTA1 := ((DELTA2^SS.4)^S)^SS.4;

   m := n - 3;
   
   x2 := Q[2]^(v^-m); x1 := Q[1]^(v^-m); x4 := Q[4];
   w2 := SS.2^(SS.5^-m); w1 := SS.1^(SS.5^-m); w4 := SS.4;

   y1 := t2 * x2 * t2 * x1 * x2 * t2 * x4 * x2 * x1;
   w1 := T2 * w2 * T2 * w1 * w2 * T2 * w4 * w2 * w1;
   
   words := [w1, T2, DELTA1, SS.4, T1, DELTA2, SS.0, SS.5];
   return words;
end function;

// convert from minus to plus 
OddConvert := function (d, q)

   F := GF(q);

   Q := ClassicalStandardGenerators ("Omega-", d, #F);
   // adjustment is needed with the standard generators
   Q[1] := (Q[2]^Q[1])^-1;

   Q := [GL(d, F)!Q[i] : i in [1..#Q]];
   PG := sub<GL(d, F)|Q>;
   sl := SL(2, #F^2);
   e := Degree (F);
   ee := 2*e;
   q := #F;
   Z := IntegerRing ();

   rr := GL(d, F)!Q[1];
   tt := GL(d, F)!Q[2];
   ddelta := GL(d, F)!Q[3];
   u := GL(d, F)!Q[4];
   v := GL(d, F)!Q[5];

   SS := SLPGroup (5);

   if IsOdd (d div 2) then
      t := (GL(d, F)!(v^-1 * tt*v))^-1;
      T := (SS.2^SS.5)^-1;
      r := (GL(d, F)!(v^-1 * rr*v))^-1;
      R := (SS.1^SS.5)^-1;
   else
      t := GL(d, F)!(v^-1 * tt*v);
      T := SS.2^SS.5;
      r := GL(d, F)!(v^-1 * rr*v);
      R := SS.1^SS.5;
   end if;

   delta := GL(d, F)!(v^-1 * ddelta*v);
   DELTA := SS.3^SS.5;
   s := r*t^-1*r;
   S := R*T^-1*R;

   /* We now find the generators of OmegaPlus (d-2, q)
      as words in the generators for OmegaMinus (d, q).

      t^n sends col d-1 to d-1 + n*col 1 and
      col 2 to n^2*col 1 2n*col d-1 + col 2.
   
      Let a = [1, 1], b = [1, d-1], c = [1, 2].
      We need to solve an^2 + 2bn + c = 0 in order to get the 
      power of n we need to kill the [1, 2] position */

   P := PolynomialRing (F);
   B := (t^v)^-1*t^((q-1) div 2)*t^v;
   a := B[1, 1];
   b := B[1, d-1];
   c := B[1, 2];
   py := P!(a*P.1^2 + 2*b*P.1 + c);
   if d ne 2 then
      n := Z!Roots (py)[1, 1];
   else
      n := 0;
   end if;

   t2 := t^n*(t^v)^-1*t^((q-1) div 2)*t^v;
   T2 := T^n*(T^SS.5)^-1*T^((q-1) div 2)*T^SS.5;
   r2 := (r^n*(r^v)^-1*r^((q-1) div 2)*r^v)^-1;
   R2 := (R^n*(R^SS.5)^-1*R^((q-1) div 2)*R^SS.5)^-1;

   delta2 := (delta* (delta^-1)^v);
   DELTA2 := (DELTA* (DELTA^-1)^SS.5);
   delta1 := ((delta2^u)^s)^u;
   DELTA1 := ((DELTA2^SS.4)^S)^SS.4;

   B := ((t*s)^v)^-1*t^((q-1) div 2)* (t*s)^v;
   a := B[1, 1];
   b := B[1, d-1];
   c := B[1, 2];
   py := P!(a*P.1^2 + 2*b*P.1 + c);
   if d ne 2 then
      n := Z!Roots (py)[1, 1];
   else
      n := 0;
   end if;

   t1 := (t^n*((t*s)^v)^-1*t^((q-1) div 2)*(t*s)^v)^-1;
   T1 := (T^n*((T*S)^SS.5)^-1*T^((q-1) div 2)*(T*S)^SS.5)^-1;
   r1 := (r^n*((r*s)^v)^-1*r^((q-1) div 2)*(r*s)^v);
   R1 := (R^n*((R*S)^SS.5)^-1*R^((q-1) div 2)*(R*S)^SS.5);

   w1 := Evaluate (T1, [(SS.2^SS.1)^-1, SS.2, SS.3, SS.4, SS.5]);
   w2 := Evaluate (T2, [(SS.2^SS.1)^-1, SS.2, SS.3, SS.4, SS.5]);

   return w1, w2;
end function;

// standard presentation for Omega-(6, q)

MyOMinusPres6 := function (q: Six := false, MinGens := true, Projective := false)
   d := 6; n := 3;

   if MinGens then 
      F := SLPGroup (5);
   else
      F := SLPGroup (5 + 6);
   end if;

   s := F.1; t := F.2; delta := F.3; u := F.4; v := F.5; 

   rels := [];

   if IsEven (q) then 
      words := EvenConvert(d, q);
      words := Evaluate (words, [F.i: i in [1..5]]);
      sp := words[1]; tp := words[2]; deltap := words[3]; s1p := words[4];
      t1p := words[5]; delta1p := words[6]; 
   else 
      sp := ((u^(v^-2))^-1 * s * s^(v^-1))^(v^2);
      s1p := (u^(v^-2))^(v^2);
      delta1p := (delta^-1 * delta^(v^-1))^(v^2);
      deltap := ((delta^-1 * delta^(v^-1))^s)^(v^2);
      t1p, tp := OddConvert (d, q);
      tp := Evaluate (tp, [F.i: i in [1..5]]);
      t1p := Evaluate (t1p, [F.i: i in [1..5]]);
   end if;

   if not MinGens then 
      Append (~rels, sp = F.6);
      Append (~rels, tp = F.7);
      Append (~rels, deltap = F.8);
      Append (~rels, s1p = F.9);
      Append (~rels, t1p = F.10);
      Append (~rels, delta1p = F.11);
   end if;

   Y, S := ClassicalStandardPresentation ("SL", 2, q);
   gens := [s1p, s1p, t1p^1, delta1p];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   Y, S := ClassicalStandardPresentation ("SL", 2, q^2: Projective:=true);
   gens := IsEven (q) select [t^s, t^s, s, delta] else [s, s, t, delta];
   S := Evaluate (S, gens);
   rels cat:= [s = Id (F): s in S];

   h1 := delta1p; h2 := delta; 

   ua1 := t1p;
   ua2 := t;
   r1 := s1p; 
   if IsEven (q) then r2 := t^s; else r2 := s; end if;
   w := r1 * r2;

   Append (~rels, h1^r2 = h1 * h2^(q + 1));
   Append (~rels, h2^r1 = h1 * h2);
   Append (~rels, w^4 = 1);
   Append (~rels, (h1, h2) = 1);

   // Append (~rels, ua2^(w^2) = ua2^(r2));
   // if IsEven (q) then 
   //    Append (~rels, ua1^w = tp * sp * tp);
   // end if;

   Append (~rels, (ua1, ua1^w) = 1);
   if IsOdd (q) then 
      Append (~rels, (ua1, ua2^w) = 1);
   else
      Append (~rels, (ua1, ua2^w) = ua2 * ua1^w);
   end if;
   Append (~rels, ua1^-2 = (ua2^w, ua2^r2));
   if IsOdd (q) then 
      Append (~rels, (ua1, ua2) = ua2^(w) * ua1^(w^3));
      // EQUIVALENT 
      // Append (~rels, (ua1, ua2) = ua2^(v^-1) * ua1^(w^3));
      // Append (~rels, (ua1, ua2) = ua2^(v^-1) * tp^-1);
      // Append (~rels, (ua1, ua2)^-2 = ((ua2^-2)^(v^-1)) * tp^2);
   else 
     Append (~rels, (ua1, ua2) = 1);
   end if;

   if IsEven (q) then
      Append (~rels, ua1^(h2^-2) = ua1^(h1^1));
   else 
      E := GF (q);
      I := Integers ();
      w := PrimitiveElement (E);
      R := sub<E | w^-2>;
      k := Eltseq (R!w^1);
      k := [I!x: x in k];
      Append (~rels, ua1^h2 = &*[(ua1^(h1^(i-1)))^k[i]: i in [1..#k]]);
   end if;

   if IsEven (q) then 
      Append (~rels, ua2^(h1^-2) = ua2^(h2^((q+1))));
   else
      E := GF (q);
      I := Integers ();
      w := PrimitiveElement (E);
      R := sub <E | w^-2>;
      k := Eltseq (R!w^1);
      k := [I!x: x in k];
      Append (~rels, ua2^h1 = &*[(ua2^(h2^((q + 1) * (i-1))))^k[i]: 
                                 i in [1..#k]]);
   end if;

   Append (~rels, v = s1p);
   // assert s1p eq u;
   // Append (~rels, v = u);

   // projective?
   if Projective and q mod 4 eq 3 then
      z := GeneratorOfCentre (d, q, F, deltap, v);
      Append (~rels, z = 1);
   end if;

   // U(4, 3) has exceptional Schur multiplier, need additional relation 
   if Six and q eq 3 then 
      Append (~rels, F.4 * F.2 * F.4^-1 * F.3 * F.2 * F.3 * F.4 * F.2 * F.3 * F.4 * F.2 * F.3 = 1);
   end if;

   R := [LHS (r) * RHS (r)^-1: r in rels];
   R := [r : r in R];
   return F, R;
end function;
