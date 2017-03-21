freeze;

// import "../rewriting/orth_minus_char2.m" : find_quad_ext_prim;
//
// function from Allan Steel
function find_quad_ext_prim(K, L)
    /*
    L must be a degree-2 extension of K, where #K = q.
    Return a primitive element alpha of L such that
    alpha^(q + 1) = PrimitiveElement(K).
    */

    q := #K;
    assert #L eq q^2;
    w := PrimitiveElement(K);

    repeat
        flag, alpha := NormEquation(L, w);
        assert flag;
        assert alpha^(q + 1) eq w;
    until IsPrimitive(alpha);
    return alpha;
end function;



/* canonical basis for SL(d, q) */

SLChosenElements := function (G) 

   d := Degree (G);
   F := BaseRing (G); 

   w := PrimitiveElement (F);
   M := MatrixAlgebra (F, d);
   a := Identity (M);
   a[1][1] := 0;
   a[1][2] := 1;
   a[2][1] := -1;
   a[2][2] := 0;

   b := Zero (M);
   for i in [2..d] do
      b[i][i - 1] := -1;
   end for;
   b[1][d] := 1;
   // if d eq 3 then b := b^-1; end if;
 
   t := Identity (M);
   t[1][2] := 1;

   delta := Identity (M);
   delta[1][1] := w;
   delta[2][2] := w^-1;

   P := GL(d, F);
   a := P!a; b := P!b; t := P!t; delta := P!delta;

   return [a, b, t, delta];
 
end function;

/* additional element to generate all of Sp */

SpAdditionalElement := function (F)
   M := MatrixAlgebra (F, 4);
   I := Identity (M);

   I[2][3] := 1;
   I[4][1] := 1;

   I := GL (4, F)!I;
   return I;
end function;

/* canonical basis for Sp(d, q) */

SpChosenElements := function (G) 

   d := Degree (G);
   F := BaseRing (G); 

   w := PrimitiveElement (F);
   M := MatrixAlgebra (F, d);
   a := Identity (M);
   a[1][1] := 0;
   a[1][2] := 1;
   a[2][1] := -1;
   a[2][2] := 0;

   t := Identity (M);
   t[1][2] := 1;

   delta := Identity (M);
   delta[1][1] := w;
   delta[2][2] := w^-1;

   if d ge 4 then 
      p := Zero (M);
      p[1][3] := 1; p[2][4] := 1; p[3][1] := 1; p[4][2] := 1;
      for i in [5..d] do p[i][i] := 1; end for;
   else
      p := Identity (M);
   end if;

   if d ge 4 then 
      b := Zero (M);
      n := d div 2;
      for i in [1..d - 3 by 2] do
         b[i][i + 2] := 1;
      end for; 
      b[d - 1][1] := 1;
      for i in [2..d - 2 by 2] do
         b[i][i + 2] := 1;
      end for; 
      b[d][2] := 1;
   else 
      b := Identity (M);
   end if;

   P := GL(d, F);
   a := P!a; b := P!b; p := P!p; t := P!t; delta := P!delta;
   if d gt 4 then 
      v := P!(DiagonalJoin (Identity (MatrixAlgebra (F, d - 4)),
                            SpAdditionalElement (F)));
   elif d eq 4 then 
      v := SpAdditionalElement (F);
   else
      v := Identity (P);
   end if;

   return [a, b, t, delta, p, v];
end function;

/* additional elements to generate SU */

SUAdditionalElements := function (F: EvenCase := true)
   if EvenCase then d := 4; else d := 3; end if;
   M := MatrixAlgebra (F, d);
   gamma := PrimitiveElement (F);
   q := Isqrt (#F);
   I := Identity (M);
   if EvenCase then  
      I[1][3] := 1;
      I[4][2] := -1;
      J := DiagonalMatrix (F, [gamma, gamma^-q, gamma^-1, gamma^q]);
   else
      if IsEven (q) then
         phi := (Trace (gamma, GF(q)))^-1 * gamma;
      else
         phi := -1/2;
      end if;
      I := M![1, phi, 1, 0, 1, 0, 0, -1, 1];
      J := DiagonalMatrix (F, [gamma, gamma^(-q), gamma^(q - 1)]);
   end if;
   I := GL(d, F)!I;
   J := GL(d, F)!J;
   return I, J;
end function;

/* canonical basis for SU(d, q) */

SUChosenElements := function (G) 

   d := Degree (G);
   E := BaseRing (G); 

   f := Degree (E) div 2;
   p := Characteristic (E);
   q := p^f;
   F := GF(p, f);

   w := PrimitiveElement (E);
   if IsEven (#E) then
      w0 := w^(q + 1);
      alpha := 1;
   else
      alpha := w^((q + 1) div 2);
      w0 := alpha^2; 
   end if;

   M := MatrixAlgebra (E, d);
   a := Zero (M);
   a[1][2] := alpha;
   a[2][1] := alpha^-q;

   for i in [3..d] do a[i][i] := 1; end for;
 
   t := Identity (M);
   t[1][2] := alpha;

   delta := Identity (M);
   if (d eq 3 and p eq 2 and f eq 1) then
      delta[1,2] := w;
      delta[1,3] := w;
      delta[3,2] := w^2;
   else
      delta[1][1] := w0;
      delta[2][2] := w0^-1;
   end if;

   if d ge 4 then 
      p := Zero (M);
      p[1][3] := 1; p[2][4] := 1; p[3][1] := 1; p[4][2] := 1;
      for i in [5..d] do p[i][i] := 1; end for;
   else
      p := Identity (M);
   end if;

   if d ge 4 then 
      b := Zero (M);
      n := d div 2;
      for i in [1..2 * n - 2 by 2] do
         b[i][i + 2] := 1;
      end for; 
      b[2 * n - 1][1] := 1;
       for i in [2..2 * n - 2 by 2] do
          b[i][i + 2] := 1;
     end for; 
      b[2 * n][2] := 1;
      if IsOdd (d) then b[d][d] := 1; end if;
   else 
      b := Identity (M);
   end if;

   P := GL(d, E);
   a := P!a; b := P!b; p := P!p; t := P!t; delta := P!delta;

   if d eq 2 then 
      x := Identity (P);
      y := Identity (P);
   elif d in [3, 4] then 
      x, y := SUAdditionalElements (E: EvenCase := IsEven (d));
   else 
      x, y := SUAdditionalElements (E: EvenCase := IsEven (d));
      f := d - Nrows (x);
      x := GL(d, E) ! (DiagonalJoin (Identity (MatrixAlgebra (E, f)), x)); 
      y := GL(d, E) ! (DiagonalJoin (Identity (MatrixAlgebra (E, f)), y)); 
   end if;

   return [a, b, t, delta, p, x, y];
end function;

/* if SpecialGroup is true, then standard generators
   for SO^0, otherwise for Omega */

SOChosenElements := function (G: SpecialGroup := false)

   n := Degree (G);
   assert IsOdd (n) and n gt 1;

   F := BaseRing (G);
   q := #F;

   w := PrimitiveElement (F);

   MA := MatrixAlgebra (F, n);
      
   A := MatrixAlgebra (F, 2);
 
   M := MatrixAlgebra (F, 3);
   a := M![1,1,2,0,1,0,0,1,1];
   U := Identity (MA);
   InsertBlock (~U, a, n - 2, n - 2);

   b := M![0,1,0,1,0,0,0,0,-1];
   L := Identity (MA);
   InsertBlock (~L, b, n - 2, n - 2);

   delta := M!DiagonalMatrix (F, [w^2, w^-2, 1]);
   D := Identity (MA);
   InsertBlock (~D, delta, n - 2, n - 2);

   Gens := [L, U, D];

   if n eq 3 then 
      h := Identity (MA);
   else 
      I := A![1,0,0, 1];
      h := Zero (MA);
      m := n - 1;
      for i in [1..m div 2 - 1] do
         x := (i - 1) * 2 + 1;
         y := x + 2;
         InsertBlock (~h, I, x, y);
      end for;
      InsertBlock (~h, (-1)^(n div 2 - 1) * I, m - 1, 1);
      h[n][n]:=1;
   end if;
   Append (~Gens, h);

   // EOB -- add additional generator u Oct 2012
   if n gt 3 then
      u := Zero (MA);
      for i in [5..n] do u[i][i] := 1; end for;
      u[1][3] := 1; u[2][4] := 1; u[3][1] := -1; u[4][2] := -1;
   else
      u := Identity (MA);
   end if;
   Append (~Gens, u);

   if SpecialGroup then
      m :=  Identity (MA);
      _, b := Valuation (q - 1, 2);
      m[n - 2][n-2] := w^b;
      m[n - 1][n-1] := w^-b;
      Append (~Gens, m);
   end if;

   P := GL (n, q);
   gens := [P!x: x in Gens];

   return gens;
end function;

/* if SpecialGroup is true, then standard generators
   for SO+, otherwise for Omega+ */

PlusChosenElements := function (G: SpecialGroup := false) 

   n := Degree (G);
   F := BaseRing (G);
   q := #F;

   w := PrimitiveElement (F);
   A := MatrixAlgebra (F, 2);

   if n eq 2 then
      Gens := [A | Identity (A): i in [1..8]];
      if #F gt 3 then x := OmegaPlus(2, F).1; Gens[3] := x; end if;
      if SpecialGroup then
         w := PrimitiveElement (F);
         if IsOdd (q) then Gens[#Gens + 1] := GL(2, F)![w,0,0,w^-1];
         else Gens[#Gens + 1] := A![0,1,1,0]; end if;
      end if;
   else 
      MA := MatrixAlgebra (F, n);
      M := MatrixAlgebra (F, 4);

      s := Zero (MA);
      for i in [5..n] do s[i][i] := 1; end for;
      s[1][4] := -1; s[2][3] := -1; s[3][2] := 1; s[4][1] := 1;

      t4 := M![1,0,0,-1, 0,1,0,0, 0,1,1,0, 0,0,0,1];
      t := Identity (MA);
      InsertBlock (~t, t4, 1, 1);

      delta4 := DiagonalMatrix (F, [w, w^-1, w, w^-1]);
      delta := Identity (MA);
      InsertBlock (~delta, delta4, 1, 1);
      
      s1 := Zero (MA);
      for i in [5..n] do s1[i][i] := 1; end for;
      s1[1][3] := 1; s1[2][4] := 1; s1[3][1] := -1; s1[4][2] := -1;

      t4 := M![1,0,1,0,  0,1,0,0, 0,0,1,0, 0,-1,0,1];
      t1 := Identity (MA);
      InsertBlock (~t1, t4, 1, 1);

      delta4 := DiagonalMatrix (F, [w, w^-1, w^-1, w]);
      delta1 := Identity (MA);
      InsertBlock (~delta1, delta4, 1, 1);
      
      u := Identity (MA);

      I := Identity (A);
      v := Zero (MA);
      for i in [1..n div 2 - 1] do
         x := (i - 1) * 2 + 1;
         y := x + 2;
         InsertBlock (~v, I, x, y);
      end for;
      InsertBlock (~v, (-1)^(n div 2 + 1) * I, n - 1, 1);
      Gens := [s, t, delta, s1, t1, delta1, u, v];
      if SpecialGroup then
         a :=  Identity (MA);
         if IsOdd (q) then
            _, b := Valuation (q - 1, 2);
            a[1][1] := w^b;
            a[2][2] := w^-b;
         else
            a[1][1] := 0; a[1][2] := 1;
            a[2][1] := 1; a[2][2] := 0;
         end if;
         Append (~Gens, a);
      end if;
   end if;

   P := GL (n, F);
   gens := [P!x: x in Gens];
   return gens;
end function;

MinusChar2Elements := function(G: SpecialGroup := false)

   d := Dimension(G);
   F := BaseRing(G);
   q := #F;
   alpha := PrimitiveElement (F);
   K := GF (q^2);
   gamma := PrimitiveElement (K);
   for i in [1..q - 1] do
     if (gamma^i)^(q + 1) eq alpha then
        pow := i; break i;
     end if;
   end for;
   gamma := gamma^pow;
   assert gamma^(q + 1) eq alpha;

   M := MatrixAlgebra(GF(q^2), d);
   if d eq 2 then 
      Gens := [Generic (G) | Identity (G): i in [1..5]];
      O := OmegaMinus (d, q);
      x := O.Ngens (O); 
      Gens[3] := x;
      if SpecialGroup then 
         Gens[#Gens + 1] := SOMinus (2, q).1;
      end if;
   else 

   C := GL(4, GF(q^2))![1, 0, 0, 0, 0, gamma, 1, 0, 0, gamma^q, 1, 0, 0, 0, 0, 1];
   C := Transpose(C);
   CC := GL(4, GF(q^2))![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0];

   sl := SL(2, GF(q^2));
   t := sl![1, 1, 0, 1];
   r := sl![1, 0, 1, 1];
   delta := sl![gamma, 0, 0, gamma^-1];
   deltaq := sl![gamma^q, 0, 0, gamma^-q];

   G := GL(4, GF(q^2));

   t1 := (G!TensorProduct(t, t)^(C^-1))^(CC^-1);
   r1 := (G!TensorProduct(r, r)^(C^-1))^(CC^-1);
   d1 := (G!TensorProduct(delta, deltaq)^(C^-1))^(CC^-1);

   GG := GL(d, GF(q));
   tt := InsertBlock(Id(GG), GL(4, GF(q))!t1, d-3, d-3);
   rr := InsertBlock(Id(GG), GL(4, GF(q))!r1, d-3, d-3);
   dd := InsertBlock(Id(GG), GL(4, GF(q))!d1, d-3, d-3);

   Gens := [tt, rr, dd];
   I := Id(GL(2, GF(q^2)));

   if d gt 4 then
      p := Zero (M);
      InsertBlock (~p, I, 1, 3);
      InsertBlock (~p, -I, 3, 1);
      for i in [5..d] do p[i][i] := 1; end for;
   else
      p := Id(GG);
   end if;
   Append (~Gens, GG!p);

   if d gt 6 then 
      h := Zero (M);
      m := d - 2;
      for i in [1..m div 2 - 1] do
         x := (i - 1) * 2 + 1;
         y := x + 2;
         InsertBlock (~h, I, x, y);
      end for;
      II := IsEven(d div 2) select I else -I;
      InsertBlock (~h, II, m - 1, 1);
      InsertBlock (~h, I, d - 1, d - 1);
      Append (~Gens, h);
   else
      Append (~Gens, GG!p);
   end if;

      if SpecialGroup then 
         a :=  Identity (M);
         a[1][1] := 0;
         a[2][2] := 0;
         a[1][2] := 1;
         a[2][1] := 1;
         Append (~Gens, a);
      end if;

end if;

   return [GL(d, q)! g: g in Gens]; 

end function;

/* if SpecialGroup is true, then standard generators
   for SO-, otherwise for Omega- */

MinusChosenElements := function (G: SpecialGroup := false)

   n := Degree (G);

   F := BaseRing (G);
   q := #F;

   if IsEven (q) then 
      return MinusChar2Elements (G: SpecialGroup := SpecialGroup);
   end if;

   A := MatrixAlgebra (F, 2);
   if n eq 2 then
      Gens := [Identity (A):  i in [1..5]];
      x := OmegaMinus(n, q).1;
      Gens[2] := x;
      if SpecialGroup then
         if q mod 4 eq 1 then
            Gens[#Gens + 1] := -Identity (GL(2, F));
         else
            y := SOMinus (n, q).1;
            Gens[#Gens + 1] := y * x^-1;
         end if;
      end if;
      return [GL(n, q)! x : x in Gens];
   end if;

   w := PrimitiveElement (F);

   MA := MatrixAlgebra (F, n);

   // EE := ext<F | 2>;
   EE := GF (q^2);
   delta := PrimitiveElement(EE);
   mu := delta^((q + 1) div 2);
/* 
   if mu^2 ne w then
       x := find_quad_ext_prim(F, EE);
       E<delta> := sub<EE | x>;
       SetPrimitiveElement(E, delta);
       mu := delta^((q + 1) div 2);
   else
       E := EE;
   end if;
*/
   
   E := EE;
   // EOB Nov 2012 -- we need this to be true but known problem  
   assert mu^2 eq w;

   MA := MatrixAlgebra (F, n);
   
   I := A![1,0,0,1];
 
   M := MatrixAlgebra (F, 4);

   a := A![1,1,0,1];
   b := A![2,0,0,0];
   c := A![0,1,0,0];
   d := A![1,0,0,1];

   U := Identity (MA);
   U[n-3][n-3] := 0; U[n-3][n-2] := 1;
   U[n-2][n-3] := 1; U[n-2][n-2] := 0;
   U[n-1][n-1] := -1;

   a := A![1,0,1,1];
   b := A![0,0,2,0];
   c := A![1,0,0,0];
   d := A![1,0,0,1];
   L := Zero (MA);
   for i in [1..n - 4] do L[i][i] := 1; end for;
   InsertBlock (~L, a, n - 3, n - 3);
   InsertBlock (~L, b, n - 3, n - 1);
   InsertBlock (~L, c, n - 1, n - 3);
   InsertBlock (~L, d, n - 1, n - 1);
   L := Transpose (L);

   a := A![delta^(q + 1), 0, 0, delta^(-q - 1)]; 
   d := A![1/2 * (delta^(q - 1) + delta^(-q + 1)),
           1/2 * mu * (delta^(q - 1) - delta^(-q + 1)),
           1/2 * mu^(-1) * (delta^(q - 1) - delta^(-q + 1)),
           1/2 * (delta^(q - 1) + delta^(-q + 1))];
   D := Zero (MA);
   for i in [1..n - 4] do D[i][i] := 1; end for;
   InsertBlock (~D, a, n - 3, n - 3);
   InsertBlock (~D, d, n - 1, n - 1);
   D := Transpose (D);

   Gens := [U, L, D];

   if n le 4 then 
      p := Identity (MA);
   elif n gt 4 then
      p := Zero (MA);
      InsertBlock (~p, I, 1, 3);
      InsertBlock (~p, -I, 3, 1);
      for i in [5..n] do p[i][i] := 1; end for;
   end if;
   Append (~Gens, p);

   // if n gt 6 then 
      h := Zero (MA);
      m := n - 2;
      for i in [1..m div 2 - 1] do
         x := (i - 1) * 2 + 1;
         y := x + 2;
         InsertBlock (~h, I, x, y);
      end for;
      InsertBlock (~h, (-1)^(n div 2) * I, m - 1, 1);
      InsertBlock (~h, I, n - 1, n - 1);
      Append (~Gens, h);
   // end if;

   if SpecialGroup then
      m := Identity (MA);
      if q mod 4 eq 3 then 
         m[1][1] := -1;
         m[2][2] := -1;
       else
         m[n-1][n-1] := -1;
         m[n][n] := -1;
       end if;
      Append (~Gens, m);
   end if;

   P := GL (n, q);

   gens := [P!x: x in Gens];

   return gens, E;
end function;

intrinsic ClassicalStandardGenerators (type :: MonStgElt, d :: RngIntElt, F :: FldFin : SpecialGroup := false)
-> []
{return the Leedham-Green and O'Brien standard generators for the quasisimple 
 classical group of specified type in dimension d and defining field F; the 
 string type is one of SL, Sp, SU, Omega, Omega+, Omega-
} 
   require type in ["SL", "Sp", "SU", "Omega", "Omega+", "Omega-"]: "Type is not valid";
   require d gt 1: "Dimension is not valid";

   if type eq "Omega" then require IsOdd (d) and IsOdd (#F): "Dimension and field size must be odd"; end if;
   if type in {"Omega+", "Omega-"}  then require (IsEven (d) and d ge 4): 
      "Dimension must be even and at least 4"; end if;
    
   case type:
       when "SL": return SLChosenElements (SL(d, F)), _; 
       when "Sp": return SpChosenElements (Sp(d, F)), _; 
       when "SU": return SUChosenElements (SU(d, ext<F | 2>)), _; 
       when "Omega": return SOChosenElements (Omega(d, F): SpecialGroup := SpecialGroup), _; 
       when "Omega+": return PlusChosenElements (OmegaPlus(d, F): SpecialGroup := SpecialGroup), _; 
       // avoid OmegaMinus -- it sets order, too hard for large d, q  
       when "Omega-": return MinusChosenElements 
          (ChevalleyGroup("2D", d div 2, F): SpecialGroup := SpecialGroup); 
   end case;
end intrinsic;

intrinsic ClassicalStandardGenerators (type :: MonStgElt, d :: RngIntElt, q :: RngIntElt : SpecialGroup := false)
-> []
{return the Leedham-Green and O'Brien standard generators for the quasisimple 
 classical group of specified type in dimension d over field of size q; the 
 string type is one of SL, Sp, SU, Omega, Omega+, Omega-
} 
   require type in ["SL", "Sp", "SU", "Omega", "Omega+", "Omega-"]: "Type is not valid";
   require d gt 1: "Dimension is not valid";
   require IsPrimePower (q): "Field size is not valid";

   return ClassicalStandardGenerators(type, d, GF(q) : SpecialGroup := SpecialGroup);
end intrinsic;

intrinsic ClassicalStandardPresentation (type :: MonStgElt, d :: RngIntElt, q :: RngIntElt: Projective := false)
-> GrpSLP, []
{return the Leedham-Green and O'Brien presentation on standard generators 
 for the quasisimple classical group of specified type in dimension d over 
 field of size q; the string type is one of SL, Sp, SU, Omega+, Omega-, Omega.
 If Projective is true, then return the presentation for the
 corresponding projective group. An SLP group on the standard generators
 and the relations as SLPs in this group are returned
} 
   require type in ["SL", "Sp", "SU", "Omega+", "Omega-", "Omega"]: "Type is not valid";
   require d gt 1: "Dimension is not valid";
   require IsPrimePower (q): "Field size is not valid";
   return ClassicalStandardPresentation(type, d, GF(q) : Projective := Projective);
end intrinsic;

intrinsic ClassicalStandardPresentation (type :: MonStgElt, d :: RngIntElt, F ::FldFin: Projective := false)
-> GrpSLP, []
{return the Leedham-Green and O'Brien presentation on standard generators 
 for the quasisimple classical group of specified type in dimension d over 
 field of size q; the string type is one of SL, Sp, SU, Omega+, Omega-, Omega.
 If Projective is true, then return the presentation for the
 corresponding projective group. An SLP group on the standard generators
 and the relations as SLPs in this group are returned
} 
   require type in ["SL", "Sp", "SU", "Omega+", "Omega-", "Omega"]: "Type is not valid";
   require d gt 1: "Dimension is not valid";

   if type eq "Omega" then require IsOdd (d) and IsOdd (#F): "Dimension and field size must be odd"; end if;
   if type in {"Omega+", "Omega-"}  then require (IsEven (d) and d ge 4): 
      "Dimension must be even and at least 4"; end if;

   case type:
       when "SL": return int_StandardPresentationForSL (d, F: Projective := Projective);
       when "Sp": return int_StandardPresentationForSp (d, F: Projective := Projective);
       when "SU": return int_StandardPresentationForSU (d, F: Projective := Projective);
       when "Omega+": return int_StandardPresentationForOmega (d, F: Projective := Projective, Type := "Omega+");
       when "Omega-": return int_StandardPresentationForOmega (d, F: Projective := Projective, Type := "Omega-");
       when "Omega": return int_StandardPresentationForOmega (d, F: Type := "Omega");
   end case;
end intrinsic;
