freeze;

import "sl2q.m": UpperTriangle, PresentationForSL2;
import "su-3.m": SU3Presentation, SU32Presentation; 
import "even-su.m": EvenSUPresentationGenerators, ConvertToStandard;
import "even-su.m": GeneratorOfCentre, EvenSU;

/////////////////////////////////////////////////////////////////////////
//   standard presentation for SU(n, q)  n odd                         //
//                                                                     //
//   Input two parameters to compute this presentation of SU(n, q)     //
//     n = dimension                                                   //
//     q = field order                                                 //
// 
//   July 2010 
/////////////////////////////////////////////////////////////////////////

OddSU := function (n, q : original := false, Projective := false) 
  
   if n eq 3 then 
      if q eq 2 then 
         W, Rels := SU32Presentation ( : Projective := Projective);
      else 
         W, Rels := SU3Presentation (q); 
         if not original then 
            W, Rels := ConvertToStandard (n, q, Rels); 
         end if;
         if Projective then
            z := GeneratorOfCentre (n, q, W);
            Append (~Rels, z);
         end if;
      end if;
      return W, Rels;
   end if;

   d := n div 2; /* rank */

   // Set up field elements
   E := GF (q^2); 
   e := Degree (E);    
   p := Characteristic (E); 
   w := PrimitiveElement (E);

   if IsEven (p) then
      alpha := w^((q + q^2) div 2);
   else
      alpha := w^((q + 1) div 2);
   end if;
   w0 := alpha^2;

   f := e div 2;
   I := Integers ();

   F := SLPGroup (8);

   T := F.1;     // Transvection t_12(alpha) where alpha =(w^((q + 1) / 2)
   S := F.2;     // Sigma_2143
   D := F.3;     // Diagonal matrix [w^q, w^-1, w, w^-q, 1 ... 1]
   Z := F.4;     // 0, alpha, -alpha^-1 0 : I 
   U := F.5;     // Permutation matrix for the short cycle (1, 3)(2, 4)
   // Permutation matrix for long cycle (1,3,5, ...,n - 1)(2,4,...,n) 
   V := F.6;     

   v := F.7;
   Y := F.8;

   /* presentation for SU(2d, q) */
   Q, R := EvenSU (n - 1, q: original := true);
   images := Ngens (Q) eq 5 select [T, S, D, Z, U] else [T, S, D, Z, U, V]; 
   // tau := hom<Q->F | T, S, D, Z, U, V>;
   tau := hom<Q->F | images>;
   R2d := [tau (r): r in R];

   /* presentation for SU(3, q) */
   G, R3 := SU3Presentation (q);
   if IsEven (p) then t := Z; else t := Y^(-(q + 1) div 2) * Z; end if;
   tau := hom<G->F | v, T, Y, t>;
   R3 := [tau (r): r in R3];
   
   Rels := [];

   if n eq 5 then Append (~Rels, U = V); end if;

   Append (~Rels, 1=(v, Z^U));
   if p eq 2 then 
      Append (~Rels, v^(Z^2) = v^1);
   else 
      Append (~Rels, v^(Z^2) = v^-1);
   end if;

   Append (~Rels, (Y, Z^2) = 1);
   Append (~Rels, (Y, Z^U) = 1);
   Append (~Rels, (Y, D) = 1);
   Append (~Rels, (S, v^Z) = 1); 

   if IsOdd (p) then 
      Append (~Rels, (v, v^U) = (S^-1)^((Z, U) * Y^(q + 1))); 
   else 
      Append (~Rels, (v, v^U) =  S^((Z * U)^2));
   end if;

   if d gt 2 then 
      Append (~Rels, 1=(v, U^V));
      Append (~Rels, (Y, U^V) = 1);
      Append (~Rels, (Y, V*U) = 1);
   end if;
   if d gt 3 then 
      Append (~Rels, 1=(v, V * U));
      Append (~Rels, (S, v^(V^2)) = 1); 
   end if;

   // R9 Steinberg relations 
   Append (~Rels, (v^t, (v^t)^U) = S^-1);
   Append (~Rels, (T, v^U) = 1);
   Append (~Rels, (S, v^t) = 1);

   // delta := (D, Z);

   lhs := (S, v);
   if IsOdd (p) then
      f, l := IsPower (-alpha, q - 2);
      m := Log (w, l);
      delta := Y^m;
      x := -1/2 * (w^-((q + 1) div 2));
      m := Log (w, x);
      rhs := v^(delta * Z * U) * (S^(Y^m))^Z;
   else
      R := sub<E | w^(1 - q)>;
      beta := 1/(1 + w^(q - 1));
      val := 1 + beta;
      k := Eltseq (R!(val));
      k := [I!x: x in k];
      rhs := &*[((S^Z)^(D^(i-1)))^k[i]: i in [1..#k]] * ((v^-1)^t)^U;
   end if;
   Append (~Rels, lhs = rhs); 

   // new relations added July 2010
   Append (~Rels, (Y, Y^U) = 1);
   Append (~Rels, (v, v^(t * U)) = S^t);
   Append (~Rels, (S^D, v^t) = 1);

   Rels := [LHS (r) * RHS (r)^-1: r in Rels];
   Rels cat:= R2d;
   Rels cat:= R3;

   if original then 
      return F, Rels;
   else 
      W, Rels := ConvertToStandard (n, q, Rels);
      if Projective then
         z := GeneratorOfCentre (n, q, W);
         Append (~Rels, z);
      end if;
      return W, Rels;
   end if;

end function;

Transvection := function (d, q, i, j, alpha)
   F := GF (q);
   M := MatrixAlgebra (F, d);
   E := Identity (M);
   E[i][j] := alpha;
   return GL(d, F) ! E;
end function;

Sigma := function (d, q, i, j, k, l, a)

   M := MatrixAlgebra (GF(q^2), d);
   A := Identity (M);
   B := [A[i]: i in [1..d]];
   C := B;
   C[i] := B[i] + a * B[l];
   C[k] := B[k] - a^q * B[j];
   C := &cat ([Eltseq (x): x in C]);
   return GL(d, q^2)!C, M!C;
end function;

/* May 2010 presentation generators for odd dimension SU(d, q) */

OddSUPresentationGenerators := function (d, q)
   E := GF (q^2);
   w := PrimitiveElement (E);
   assert IsOdd (d);
   gens := EvenSUPresentationGenerators (d - 1, q); 
   M := MatrixAlgebra (GF (q^2), d);
   Gens := [Identity (M): i in [1..8]];
   for i in [1..6] do InsertBlock (~Gens[i], gens[i], 1, 1); end for;
   if IsEven (q) then
      phi := Trace(w, GF(q))^(-1) * w;
   else
      phi := -1/2;
   end if;
   v := Gens[7]; v[1][2] := phi; v[1][d] := 1; v[d][2] := -1; 
   Gens[7] := v; 
   w := PrimitiveElement (E);
   Y := Gens[8]; Y[1][1] := w; Y[2][2] := w^-q; Y[d][d] := w^(q - 1);
   Gens[8] := Y; 
   return [GL(d, E)!x : x in Gens];
end function;

/* SLPs to define presentation generators
   in terms of standard generators of SU(d, q) */

OddSUStandardToPresentation := function (d, q)
   if d eq 3 then 
      W := SLPGroup (7);
      E := [W.i: i in [1..7]];
      if IsOdd (q) then
         return [E[6], E[3], E[7], (E[7]^-1)^((q + 1) div 2) * E[1]];
      else
         return [E[6], E[3], E[7], E[1]];
      end if;
   end if;
   U := SLPGroup (7);
   E := [U.i : i in [1..7]];
   x := E[6]; y := E[7]; u := E[5]; z := E[1]; v := E[2];
   if IsOdd (q) then t := (y^v)^(-(q + 1) div 2) * z; else t := z; end if;
   word := ((x^(v^1 * t), x^(v^1 * t * u)))^-1;
   W := [U.3, word, (U.7^U.2)^q * U.7^(U.2^2), U.1, U.5, U.2, U.6^U.2, U.7^U.2];
   return W;
end function;

/* SLPs for standard generators in terms of presentation generators */

OddSUPresentationToStandard := function (d, q)
   W := SLPGroup (8);
   E := [W.i: i in [1..8]];
   if d eq 3 then 
      if IsOdd (q) then
         return [E[3]^((q + 1) div 2) * E[4],
              E[1]^0, E[2], E[3]^(q + 1), E[1]^0, E[1], E[3]];
      else
         return [E[4], E[4]^0, E[2], E[3]^(q+1), E[3]^0, E[1], E[3]];
      end if;
   end if;
   return [E[4], E[6], E[1], E[8]^(q + 1), E[5], E[7]^(E[6]^-1), E[8]^(E[6]^-1)];
end function;

/* 
AttachSpec ("spec");
import "standard.m": SUChosenElements;

for d in [3..23 by 2] do 
for q in [2..100] do
if IsPrimePower (q) then
d, q;
Q, R := OddSU (d, q);
E := SUChosenElements (SU(d, q));
T := Evaluate (R, E);
assert #Set (T) eq 1;
end if;
end for;
end for;

*/
