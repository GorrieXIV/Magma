freeze;

//$Id:: sl2q.m 2340 2012-09-30 01:03:09Z eobr007                             $:

/* generators for group of upper-triangular matrices in SL(2, p^e) */

TriangleGens := function (p, e)
   F := GF (p, e);
   w := PrimitiveElement (F);
   a := GL(2, F)  ![w^-1, 0, 0, w];
   b0 := GL(2, F) ![1, 1, 0, 1];
   return [a, b0];
end function;

/* presentation for image of group of upper-tringular matrices in PSL(2, p^e) */
 
UpperTriangle := function (p, e: Projective := true, Linear := false)

   F<a, b0> := SLPGroup (2);
   if p^e eq 2 then
      return F, [a, b0^2];
   elif p^e eq 3 then
      return F, [a^2, b0^3, (a, b0)];
   end if;

   K := GF (p, e);
   w := PrimitiveElement (K);
   I := Integers ();

   E := sub <K | w^2>;
   c := Eltseq (E!w^1);
   c := [I!x: x in c];

   Rels := [];
   if IsEven (p) then 
      b := b0;
      B := [b0];
      for i in [1..e] do B[i + 1] := B[i]^a; end for;
      m := MinimalPolynomial (w^2, GF(p));
   else 
      b1 := &*[(b0^(a^(i)))^c[i + 1]: i in [0..e - 1]];
      b2 := b0^a;
      B := [b0, b1];
      for i in [2..e] do B[i + 1] := B[i - 1]^a; end for;
      m := MinimalPolynomial (w^1, GF(p));
   end if;

   c := Coefficients (m);
   u := [I!x: x in c];
   Append (~Rels, &*[B[i + 1]^u[i + 1]: i in [0..e]]);

   if IsEven (p) then 
      m := Log (w^2, 1 + w^2);
      ell := 2^e - 1;
      return F, Rels cat [a^ell, b^2, b^(a^m) * (b, a)^-1];
   end if;

   if IsSquare (1 + w^1) then  
      m := Log (w^2, 1 + w^1);
      Append (~Rels, b0^(a^m) * (b0 * b1)^-1);
      Append (~Rels, b1^(a^m) * (b1 * b2)^-1);
   else 
      m := Log (w^2, (1 + w^-1));
      Append (~Rels, b1^(a^m) * (b0 * b1)^-1);
      Append (~Rels, b0^(a^(m + 1)) * (b1 * b2)^-1);
   end if;

   ell := (p^e - 1) div 2;
   if Projective then 
      Append (~Rels, a^ell);
   end if;

   if Linear then 
      z := a^ell; 
      Append (~Rels, z^2);
      Append (~Rels, (b0, z));
   end if;

   return F, Rels cat [b0^p,  (b0, b1),  (b1, b2)]; 
end function;

/* generators for SL(2, p^e) */

SL2Gens := function (p, e)

  F := GF (p, e);
  w := PrimitiveElement (F);

  delta := GL(2, F) ![w^-1, 0, 0, w^1];
  tau := GL(2, F) ![1, 1, 0, 1];
  tau1 := GL(2, F) ![1, w^-1, 0, 1];
  Z := GL(2, F) ![0,1,-1,0];

  if e eq 1 then 
     return [tau, Z];
  else 
    return [delta, tau, Z];
  end if;
end function;

/* presentation for PSL(2, p^e) */

Thm84 := function (p, e)
   F := GF (p, e);
   w := PrimitiveElement (F);
   I := Integers ();

   Q<delta, tau, tau1, Z> := SLPGroup (4);
   Rels := [];

   E := sub < F | w^2>;
   c := Eltseq (E!w^1);
   c := [I!x: x in c];
   Append (~Rels, tau1 = &*[(tau^(delta^(i)))^c[i + 1]: i in [0..e - 1]]);

   G := quo <Q | Rels, (tau * Z)^3 = (Z * delta)^2 = Z^2 = (tau1 * Z * delta)^3 = 1>;

   H := UpperTriangle (p, e: Projective := true, Linear := false);
   R := Relations (H);
   gamma := hom < H -> G | [G.i: i in [1..3]]>;
   R := [gamma (x): x in R];
   for r in R do G := AddRelation (G, r); end for;

   return G;
end function;

/* general presentation for SL(2, p^e), where p is odd */

Thm85 := function (p, e)
   F := GF (p, e);
   w := PrimitiveElement (F);
   I := Integers ();

   Q<delta, tau, Z> := SLPGroup (3);
   Rels := [];

   E := sub < F | w^2>;
   c := Eltseq (E!w^1);
   c := [I!x: x in c];
   tau1 := &*[(tau^(delta^(i)))^c[i + 1]: i in [0..e - 1]];

   Rels := [];
   ell := (p^e - 1) div 2;

   Rels cat:= [(tau * Z)^3,  (Z * delta)^2 * Z^-2,  (tau1 * Z * delta)^3, 
                Z^4, delta^ell * Z^-2 ];

   H, R := UpperTriangle (p, e: Projective := false, Linear := false);
   gamma := hom <H -> Q | [Q.i: i in [1..2]]>;
   R := [gamma (x): x in R];

   return Q, Rels cat R;
end function;

/* special presentation for SL(2, p^e) when p^e mod 4 = 3 */

Thm86 := function (p, e)
   F := GF (p, e);
   w := PrimitiveElement (F);
   I := Integers ();

   Q<delta, tau, Z> := SLPGroup (3);

/* 
   E := sub < F | w^-2>;
   c := Eltseq (E!w^-1);
   c := [I!x: x in c];
   tau1 := &*[(tau^(delta^(i)))^c[i + 1]: i in [0..e - 1]];
*/
   n := (p^e + 1) div 4;
   tau1 := (tau^-1)^(delta^n);

   B := [tau, tau1];
   for i in [2..e] do B[i + 1] := B[i - 1]^delta; end for;

   Rels := [];
   m := MinimalPolynomial (w^1, GF(p));
   c := Coefficients (m);
   u := [I!x: x in c];

   l := (p^e - 1) div 2;
   k := Log (w^1, (1 + w^1));
   assert w^k eq 1 + w^1;
   gamma := delta^(k div 2);
   pow := ((-1)^(k)) * n;

   Rels := [&*[B[i + 1]^u[i + 1]: i in [0..e]], Z^4, (tau * Z)^3, 
                 delta * Z * delta * Z^-1, (tau, tau^(delta^n)), 
                 (tau * Z^-1)^3 * Z^-2, 
                 (tau * delta)^-l * tau^p * Z^2,
                 tau^gamma * (tau^-1, delta^pow)^-1];
   return Q, Rels;
end function;

/* presentation for SL(2, 2^e) where e > 1 */

Thm88 := function (p, e)

   if e eq 2 then 
      F<a,b,c> := SLPGroup (3);
      return F, [a^3, b^2, c^2, (a^-1 * c)^2, (b * a^-1)^3, (c * b)^3];
   end if;

   E := GF (p, e);
   w := PrimitiveElement (E);
   I := Integers ();

   F<delta, tau, Z> := SLPGroup (3);
   B := [tau];
   for i in [1..e] do B[i + 1] := B[i]^delta; end for;
   m := MinimalPolynomial (w^2, GF(p));
   c := Coefficients (m);
   u := [I!x: x in c];
   Rels := [];

   m := Log (w^2, 1 + w^2);
   ell := 2^e - 1;
   Rels :=[&*[B[i + 1]^u[i + 1]: i in [0..e]],
            (Z * tau)^3 * Z^-2, (Z * delta)^2 * tau^-2, (tau * delta)^ell * tau^-2,
            tau^(delta^m) * (tau, delta)^-1];
   return F, Rels;
end function;

/* Zassenhaus presentation for SL (2, p) where p is not 17 */

Zassenhaus := function (p)
   if p eq 2 then 
      return Group<s, t | s^p = 1, t^2, (s * t)^3>;
   elif p eq 3 then 
      return Group<s, t | s^p = 1, t^4, (t * s^-1 * t^-1 * s^-1 * t * s^-1)>;
   elif p ne 17 then  
      return Group<s, t | s^p = (s * t)^3, (t^2, s), t^4, (s^2 * t * s^((p^2 + 1) div 2) * t)^3>;
   end if;

end function;

/* Campbell Robertson presentation for SL(2, p), odd prime p */

CR := function (p)
   if p eq 2 then 
      return Group<s, t | s^p = 1, t^2, (s * t)^3>;
   end if;
   r := p mod 3;
   k := p div 3;
   F<y, x> := FreeGroup (2);
   G := quo<F| x^2 = (x * y)^3, (x *y^4 * x * y^((p + 1) div 2))^2 * y^p * x^(2 * k)>;
   return G;
end function;

/* Campbell Robertson presentation for SL(2, p), odd prime p,
   modified for our chosen generators */

ModifiedCR := function (p)
   F<a,b> := SLPGroup (2);
   if p eq 2 then 
      return F, [a^p, b^2, (a * b)^3];
   end if;
   r := p mod 3;
   k := p div 3;
   if r eq 1 then 
     Rels := [b^-2 * (b* (a* b^2))^3,
     (b * (a*b^2)^4 * b * (a * b^2)^((p + 1) div 2))^2 * (a * b^2)^p * b^(2*k)];
   else
      Rels := [b^2 * (b^-1* a)^3,
        (b^-1* a^4* b^-1* a^((p + 1) div 2))^2 * a^p * (b^-1)^(2*k)];
   end if;
   return F, Rels;
end function;

/* presentation for SL(2, p^e) */

PresentationForSL2 := function (p, e)
   if e eq 1 then 
      Q, R := ModifiedCR (p);
   elif IsEven (p) then
      Q, R := Thm88 (p, e);
   elif p^e mod 4 eq 3 then 
      Q, R := Thm86 (p, e);
   else 
      Q, R := Thm85 (p, e);
   end if;
   return Q, R;
end function;

/* 
for p in [2,3,5,7,11,13,17,19,23,29,31] do 
   for e in [1..5] do 
      p, e;
      Q, R := PresentationForSL2 (p, e);
      // ToddCoxeter (Q, sub <Q |>:Hard:=true, Workspace:=10^8);
      X := SL2Gens (p, e);
      Y := Evaluate (R, X);
      assert #Set (Y) eq 1;
   end for;
end for;
*/

/* 
for p in [2,3,5,7,11,13,17,19,23,29,31] do 
   for e in [1..5] do 
      p, e;
      if e eq 1 then 
         Q := ModifiedCR (p);
      elif IsEven (p) then
         Q := Thm88 (p, e);
      elif p^e mod 4 eq 3 then 
         Q := Thm86 (p, e);
      else 
         Q := Thm85 (p, e);
      end if;
      // ToddCoxeter (Q, sub <Q |>:Hard:=true, Workspace:=10^8);
      X := SL2Gens (p, e);
      H:=sub < GL(2, p^e) | X>;
      R:=Relations (Q);
      R := [LHS (x) * RHS (x)^-1: x in R];
      tau := hom < Q -> H | [H.i:i in [1..#X]]>;
      Y := {tau (x): x in R}; Y;
      assert #Y eq 1;
   end for;
end for;
*/

/* 
      Q := UpperTriangle (p, e: Projective:=false, Linear := true);
      X := TriangleGens (p, e);
      H:=sub < GL(2, p^e) | X>;
      R:=Relations (Q);
      R := [LHS (x) * RHS (x)^-1: x in R];
      tau := hom < Q -> H | [H.i:i in [1..#X]]>;
      Y := {tau (x): x in R}; Y;
*/

