freeze;

//$Id:: sp.m 2586 2014-04-20 16:11:26Z jbaa004                               $:

import "sl2q.m": UpperTriangle, PresentationForSL2;
import "../recognition/standard.m": SpChosenElements;
forward SpStandardToPresentation, SpPresentationToStandard;

/////////////////////////////////////////////////////////////////////////
//   standard presentation for Sp(n, q)                                //
//   d = n / 2                                                         // 
//                                                                     //
//   Input two parameters to compute this presentation of Sp(n, q)     //
//     n = dimension                                                   //
//     q = field order                                                 //
//     d = n / 2 is Lie rank 
// 
//   October 2008 -- latest revision 
/////////////////////////////////////////////////////////////////////////

intrinsic int_StandardPresentationForSp (n:: RngIntElt, q :: RngIntElt :
      Projective := false) -> GrpSLP, [] 
{return standard presentation for Sp (n, q); if Projective is true, 
 then return presentation for PSp (n, q) }
  
   require n gt 2 and IsEven (n): "Degree must be at least 4 and even";
   require IsPrimePower (q): "Field size is not valid";
   return int_StandardPresentationForSp(n, GF(q) : Projective := Projective);
end intrinsic;

intrinsic int_StandardPresentationForSp (n:: RngIntElt, K :: FldFin :
      Projective := false) -> GrpSLP, [] 
{return standard presentation for Sp (n, K); if Projective is true, 
 then return presentation for PSp (n, K) }
  
   require n gt 2 and IsEven (n): "Degree must be at least 4 and even";

   d := n div 2; /* rank */

   // Set up field elements
   q := #K;
   e := Degree (K);    
   w := PrimitiveElement (K);
   E := sub <K | w^2>;
   p := Characteristic (K); 
   I := Integers ();

   // Define the group
   F := SLPGroup (6);

   T := F.1;     // Transvection t_12(1)
   S := F.2;     // Sigma_2143
   D := F.3;     // Diagonal matrix [w^-1, w, 1 ... 1]
   Z := F.4;     // 0, 1, -1 0 : I 
   U := F.5;     // Permutation matrix for the short cycle (1, 3)(2, 4)

   // Permutation matrix for long cycle (1,3,5, ...,n - 1)(2,4,...,n) 
   V := F.6;
   
   Rels := []; 

   // For this procedure we'll use the standard (Coxeter) presentation 
   // of the symmetric group Sym(d) in terms of the 
   // short cycle U = (1, 3)(2,4) and the 
   // long cycle V = (1, 3, ..., n - 1)(2, 4, ... n)

   Append (~Rels, 1=U^2);
   if d gt 2 then 
      Append (~Rels, 1=V^d);
      Append (~Rels, 1=(U*V)^(d-1));
      Append (~Rels, 1=(U, V)^3);
   end if;
   for i in [2..(d div 2)] do Append (~Rels, 1=(U, V^i)^2); end for;

   /* R2 wreath product Z_4 wr S_d */
   if p eq 2 then 
      Append (~Rels, Z^2 = 1); 
   else 
      Append (~Rels, Z^4 = 1);
   end if;

   if d gt 2 then 
      Append (~Rels, (Z, V * U) = 1);
      Append (~Rels, (Z, U^V) = 1);
   end if;
   Append (~Rels, (Z, Z^U) = 1);
   
   // R3 These relations set up C_4 wr Sym(d-1) as stabilizing T and D 
   if d eq 2 then 
      Append (~Rels, 1=(T, Z^U));
      if e gt 1 then Append (~Rels, 1=(D, Z^U)); end if;
   else 
      Append (~Rels, 1=(T, Z^V));
      Append (~Rels, 1=(T, U^V));
      Append (~Rels, 1=(T, V * U));
      if e gt 1 then 
         Append (~Rels, 1=(D, Z^V));
         Append (~Rels, 1=(D, U^V));
         Append (~Rels, 1=(D, V * U));
      end if;
   end if;

   // R4 
   if IsOdd (p) then 
      Append (~Rels, S^(Z^2) = S^-1); 
   end if;
   Append (~Rels, S^U = S);
   Append (~Rels, S^(U^D) = S);
   if d gt 2 then 
      Append (~Rels, (S, D^(V^2)) = 1);
   end if;

   // R5 These relations set up C_4 wr Sym(d-2) as stabilizing S 
   if d gt 2 then 
      Append (~Rels, 1=(S, Z^(V^2)));
   end if;

   if d gt 3 then 
      Append (~Rels, 1=(S, U^(V^2)));
      Append (~Rels, 1=(S, V * U * U^V));
   end if;

   // R8 Steinberg relations 
   Append (~Rels, (T, T^U) = 1); // type (iii)
   Append (~Rels, (S, T^Z) = 1); // type (iv)

   /* need only one of these */
   i := 0; j := 0; // type (v)
   Append (~Rels, (T^(D^i), S^(D^j)) = 
        (S^(D^(-2 * i+j) * Z))^-1 * (T^(D^(i - j) * Z * U))); 

   /* commutator of Sigma_2143, Sigma_2134 */
   Append (~Rels, (S, S^(Z^U)) = (T^Z)^2); // type (vi)

   if d gt 2 then 
      Append (~Rels, (S, S^V) = 1); // type (vii)
      Append (~Rels, 1=(T, S^V));  // type (x)
   end if;

   /* commutator of Sigma_2143, Sigma_-3465 */
   if d ge 3 then  // type (viii)
      Append (~Rels, (S, S^(Z * V)) = (S^(V * U))^-1);
   end if;

   if d gt 3 then // type (ix)
      Append (~Rels, (S, S^(V^2)) = 1); 
   end if;

   // R6 relations giving presentation for SL(2, q) in D, T, Z 
   G, R := PresentationForSL2 (p, e);
   if e gt 1 then 
      tau := hom<G -> F | D, T, Z>;
   else 
      tau := hom<G -> F | T, Z>;
   end if;
   R6 := [tau (r): r in R];

   // R7 relations giving presentation for GF(p^e): GF(p^e)^* in D and S 
   G, R := UpperTriangle (p, e: Projective := false, Linear := true);
   tau := hom<G -> F | D, T>;
   R7 := [tau (r): r in R];

   /* R9 relation to express U as product of conjugates of S and T */
   b :=  S^Z; 
   c := (S^(Z^U));  
   if IsOdd (p) then 
      y := (Z^-2)^U;
   else 
      y := Identity (F);
   end if;
   Append (~Rels, U = y * c * b^-1 * c);

   Append (~Rels, 1=(D, D^U)); 
   c := (U, D^-1);
   Append (~Rels, S = S^c);

   /* R9 additional relations */
   Append (~Rels, 1=(D, T^U)); 

   /* relation to express D as product of 
      conjugates of transvections when e = 1 */
   if e eq 1 and q gt 2 then 
      product := T^-1; 

      c := (w - 1) / w;
      c := E!c;
      k := Eltseq (c);
      k := [I ! x : x in k];
      product *:= ((&*[(T^(D^(i-1)))^k[i]: i in [1..#k]])^Z)^-1;

      c := w;
      c := E!c;
      k := Eltseq (c);
      k := [I ! x : x in k];
      product *:= (&*[(T^(D^(i-1)))^k[i]: i in [1..#k]]);

      c := (1 - w)/w^2;
      c := E!c;
      k := Eltseq (c);
      k := [I ! x : x in k];
      product *:= ((&*[(T^(D^(i-1)))^k[i]: i in [1..#k]])^Z)^-1;
      Append (~Rels, D = product);
   end if;

   /* obtain presentation for PSp (n, q) by adding relation */
   if IsOdd (p) and Projective then 
      if d eq 2 then 
        Append (~Rels, (Z^2, U) = 1);
      else
        Append (~Rels, (Z * V)^n = 1);
      end if;
   end if;

   Rels := [LHS (r) * RHS (r)^-1: r in Rels];
   Rels cat:= R6;
   Rels cat:= R7;

   if n eq 4 then Append (~Rels, V * U^-1); end if;

   /* rewrite presentation on standard generators */
   A := SpStandardToPresentation (d, q);
   Rels := Evaluate (Rels, A);
   W := Universe (Rels);

   B := SpPresentationToStandard (d, q);
   C := Evaluate (B, A);
   U := Universe (C);
   tau := hom <U -> W | [W.i:i in [1..6]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..#C]];
   Rels cat:= T;

   return W, Rels;

end intrinsic;

/* express presentation generators as words in standard generators */ 

function SpStandardToPresentation(d, q)
    W := SLPGroup(6);
    return [W.3, W.6^(W.2^2), W.4^(-1), W.1, W.5, W.2];
end function;

/* express standard generators as words in presentation generators */ 

function SpPresentationToStandard(d, q)
    W := SLPGroup(6);
    return [W.4, W.6, W.1, W.3^-1, W.5, W.6^2 * W.2 * W.6^-2];
end function;

// latest test ...
/* 
for d in [4..6 by 2] do
for q in [2,3,4,5,8,9, 25, 27] do
 Q, R := int_StandardPresentationForSp(d, q);
 G := Sp (d, q);
 X := SpChosenElements (G);
 I := Evaluate (R, X);
Set (I);
F := SLPToFP (Q, R);
Q := F;
H := sub < Q | Q.1, Q.2, Q.3, Q.4, Q.5, (Q.2 * Q.5)^(Q.2^-1)>;
ToddCoxeter (Q, H:Hard,Print:=10^6, Workspace:=10^8);
I := CosetImage (Q, H);
RandomSchreier (I);
CompositionFactors (I);
if d eq 4 and q eq 2 then continue; end if;
assert AbelianQuotientInvariants (F) eq [];
end for;
end for;

*/

/* 
d := 6; q := 4;
Q, R:= int_StandardPresentationForSp (d, q: Projective:=true);
F := FreeGroup (Ngens (Q));
tau := hom <Q-> F | [F.i: i in [1..Ngens (F)]]>;
Q := quo <F | tau (R)>;

H := sub < Q | Q.1, Q.2, Q.3, Q.4, Q.5, (Q.2 * Q.5)^(Q.2^-1)>;
ToddCoxeter (Q, H:Hard,Print:=10^6, Workspace:=10^8);

*/

/* 
import "standard.m": SpChosenElements;
import "sp.m": SpPresentationToStandard, SpStandardToPresentation;
d := 4; q := 3;
for d in [4,6] do 
for q in [3,5,9] do 
d, q;
 G := Sp (d, q);
 X := SpChosenElements (G);      
 W := SpStandardToPresentation (d, q);
 E := Evaluate (W, X);
 Q, R := int_StandardPresentationForSp (d,q);
 I := Evaluate (R, E);
 assert Set (I) eq {Rep (I)^0};
end for;

 RR := Evaluate (R, W);
 J := Evaluate (RR, X);
 assert Set (J) eq {Rep (J)^0};

 W := SpPresentationToStandard (d, q);
 Y := Evaluate (W, E);
 assert Y eq X;

end for;
end for;

 SS := Universe (RR);
 F := SLPToFP (SS, RR);
 AbelianQuotientInvariants (F);


*/


 
 


/*
load "standard.m";
for d in [6..20 by 2] do 
for p in [3,5,7,11,13,19] do
for e in [1, 2] do 
q := p^e;
d, p, e;
G := Sp (d, q);
X := SpChosenElements (G);
E := [X[3], X[6]^(X[2]^2), X[4]^-1, X[1], X[5], X[2]];
assert IsScalar ((E[4] * E[6])^d);
G, R:= int_StandardPresentationForSp (d, q);
I := Evaluate (R, E);
assert Set (I) eq {Rep (I)^0};
end for;
end for;
end for;
*/
/*
intrinsic testSpPresentation()
    { }
for d in [4..12 by 2] do
   for q in [2, 3, 4, 5, 7, 8, 9, 16] do 
      d, q;
      G := RandomConjugate(Sp(d, q));
      if IsEven (q) then 
         E := SpChosenElements (G);
         CB := Identity (G);
      else 
         E, W, CB := SolveSp(G);
      end if;
      W := SpStandardToPresentation (d, q);
      Q, R := int_StandardPresentationForSp(d, q);
      X := Evaluate(R, W);
      T := Evaluate(X, E^CB);
      //X := Evaluate (W, E^CB);
      //T := Evaluate (R, X);
      assert #Set (T) eq 1;
   end for;
end for;

end intrinsic;
*/
