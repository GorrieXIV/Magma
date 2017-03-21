freeze;

//$Id:: sl.m 2586 2014-04-20 16:11:26Z jbaa004                               $:

import "sl2q.m": PresentationForSL2;
import "centre.m": Scalar, GeneratorOfCentre, ConstructScalar;
import "f-sn.m": PresentationForSn, Index2;
// import "../recognition/standard.m": SLChosenElements; 

forward SLPresentationToStandard, SLStandardToPresentation;

/* relations are on presentation generators; 
   convert to relations on 4 standard generators */

ConvertToStandard := function (d, q, Rels) 
   A := SLStandardToPresentation (d, q);
   Rels := Evaluate (Rels, A);
   W := Universe (Rels);
   B := SLPresentationToStandard (d, q);
   C := Evaluate (B, A);
   U := Universe (C);
   tau := hom <U -> W | [W.i:i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;

   if IsPrime (q) then 
      assert Ngens (W) eq 3;
      G := SL(d, q);
      // S := SLChosenElements (G);
      // f, u := int_SLWordInGen (SL(d, q), S[4]);
      S := ClassicalStandardGenerators ("SL", d, q);
      f, u := ClassicalRewrite (SL(d, q), S, "SL", d, q, S[4]);
/* 
      WordForDelta := function (q)
         Z := Integers ();
         S := SLPGroup (4);
         a := S.3; b := (S.3^S.2)^-1;
         w := PrimitiveElement (GF(q));
         delta := b^(Z!(w^-2 - w^-1)) * a^(Z!w) * b^(Z!(1-w^-1)) * a^-1;
         return delta;
      end function;
      u := WordForDelta (q);
*/
      U := Parent (u);
      tau := hom <W -> U | [U.i: i in [1..3]]>;
      Rels := [tau (r): r in Rels] cat [U.4^-1 * u];
      W := U;
   end if;

   assert Ngens (W) eq 4;
   return W, Rels;
end function;

/////////////////////////////////////////////////////////////////////////
//   Short presentation for SL(d, q)                                   //
//                                                                     //
//   Input two parameters to compute this presentation of SL(d, q)     //
//     d = dimension                                                   //
//     q = field order                                                 //
// 
//   October 2008
/////////////////////////////////////////////////////////////////////////

intrinsic int_StandardPresentationForSL (d :: RngIntElt, q :: RngIntElt: 
       Projective := false) -> GrpSLP, []
{return standard presentation for SL(d, q); if projective, then
 return standard presentation for PSL(d, q)}
  
   require d gt 1: "Degree must be at least 2";
   require IsPrimePower (q): "Field size is not valid";
   return int_StandardPresentationForSL(d, GF(q) : Projective := Projective);
end intrinsic;
 
intrinsic int_StandardPresentationForSL (d :: RngIntElt, K :: FldFin: 
       Projective := false) -> GrpSLP, []
{return standard presentation for SL(d, K); if projective, then
 return standard presentation for PSL(d, K)}
  
   require d gt 1: "Degree must be at least 2";

   // Set up field elements
   q := #K;
   e := Degree (K);    
   p := Characteristic (K); 

   if d eq 2 then 
      Q, R := PresentationForSL2 (p, e);
      if Projective and (q ne 2) then 
         t := GeneratorOfCentre (Q, d, q);
         Append (~R, t);
      end if;
      W, Rels := ConvertToStandard (d, q, R);
      return W, Rels;
   end if;

   // Define the group
   if e eq 1 then F := SLPGroup (3); else F := SLPGroup (4); end if;

   T := F.(1);   // Transvection t_12(1)
   U := F.(2);   // Permutation matrix for the short cycle (1, 2)
   V := F.(3);   // Permutation matrix for the long cycle (1, 2, ..., d)
   if e gt 1 then 
      D := F.(4);   // Diagonal matrix [w^-1, w, 1 ... 1]
   end if;

   Rels := [];

   /* presentation for index 2 subgroup of Z_2 wr Sym (d) */
   if p eq 2 then 
      Q, R := PresentationForSn (d);
   else 
      Q, R := Index2 (d);
   end if;
   tau := hom<Q -> F | [F.2, F.3]>;
   R1 := [tau (r): r in R];

   // R2 These relations set up Sym(d-2) as stabilizing 
   // each t_{12}(b) and D  

   /* these two relations are probably unnecessary */
   Append (~Rels, 1=(T, V*U*V^-1*U*V));
   if e gt 1 then 
      Append (~Rels, 1=(D, V*U*V^-1*U*V));
   end if;

   if d gt 3 then 
      Append (~Rels, 1=(T, V^-2*U*V^2));
      if e gt 1 then Append (~Rels, 1=(D, V^-2*U*V^2)); end if;
   end if;

   // R3 relations giving presentation for SL(2, q) in D, T, U
   G, R := PresentationForSL2 (p, e);
   if e gt 1 then
      tau := hom<G -> F | D, T, U>;
   else
      tau := hom<G -> F | T, U>;
   end if;
   R3 := [tau (r): r in R];

   // R4 
   if e gt 1 then 
      Append (~Rels, (D, D^V) = 1);
      Append (~Rels, (D, (U^2)^V) = 1);
   end if;
   
   // Steinberg relations
   C := (U^2)^(V*U);
   Append (~Rels, T^C= T^-1);

   // Type B0 relations [t_{ij}(a), t_{jk}(b)] = t_{ik}(ab)  
   // type (iii) 
   Append (~Rels, (T, T^V) = (T^(V*U))^-1); 

   // Type B0 relations [t_{ij}(a), t_{kl}(b)] = 1  
   // type (iv)
   Append (~Rels, 1=(T, T^(V*U))); // 12 & 13

   if d gt 3 then Append (~Rels, 1=(T, T^(V^2))); end if; // 12 & 34

   // type (vi)
   if e gt 1 then 
      C := D^(V^(-1));
      Append (~Rels, (T, C^2 * D) = 1);

      C := D^(V^(-1));
      Append (~Rels, (T, D^V * C^-1) = 1);

      C := (U^(-1))^V;
      Append (~Rels, (T, (D^C)^2 * D^-1) = 1);

      if q eq 25 then
         w := PrimitiveElement (K);
         E := sub <K | w^2>;
         c := Eltseq (E!w^-1);
         I := Integers ();
         c := [I!x: x in c];
         Append (~Rels, T^(D^V) = &*[(T^(D^(i)))^c[i + 1]: i in [0..e - 1]]);
      end if;

      if q eq 4 then 
        Append (~Rels, (T, T^(D * V)) = (T^D)^(U^V));
      end if;
   end if;

   if q gt 2 and Projective then
      if IsPrime (q) then 
         Append (~Rels, 1 = GeneratorOfCentre (F, d, q));
      else 
         m := (q - 1) div Gcd (d, q - 1);
         Append (~Rels, 1 = Scalar (D^m, V, U, d));
      end if;
   end if;

   Rels := [LHS (r) * RHS (r)^-1: r in Rels];
   Rels cat:= R1; 
   Rels cat:= R3;

   W, Rels := ConvertToStandard (d, q, Rels);
  
   return W, Rels;
end intrinsic;

/* express presentation generators as words in standard generators */
   
SLStandardToPresentation := function(d, q)

   if IsPrime (q) then W := SLPGroup (3); else W := SLPGroup (4); end if;
   Y := UserGenerators(W);

   if d eq 2 then 
      if IsPrime (q) then
         Z := [Y[3], Y[2]];
      else
         Z := [Y[4]^-1, Y[3], Y[2]];
      end if;
   elif d eq 3 then  
      Z := [Y[3], Y[1], Y[2]];
   elif IsOdd (d) and IsOdd (q) then 
      u := Y[1]^2; v := Y[2];
      minus1 := &*[u^(v^(2 * i + 1)): i in [1..(d - 1) div 2]];
      V := minus1 * v^-1;
      Z := [Y[3], Y[1], V];
   else 
      assert d ge 4 and (IsEven (d) or IsEven (q));
      V := Y[2]^(d - 1); 
      Z := [Y[3], Y[1], V];
   end if;
   if d gt 2 and not IsPrime (q) then Append (~Z, Y[4]^-1); end if;
   return Z;
end function;

/* express standard generators as words in presentation generators */

SLPresentationToStandard := function(d, q)

   if IsPrime (q) then W := SLPGroup (3); else W := SLPGroup (4); end if;
   Y := UserGenerators(W); 

   if d eq 2 then 
      if IsPrime (q) then 
         W := SLPGroup (2); 
         Y := UserGenerators(W);
         Z := [Y[2], Y[2], Y[1], Y[1]^0];
      else 
         W := SLPGroup (3); 
         Y := UserGenerators(W);
         Z := [Y[3], Y[3], Y[2], Y[1]^-1]; 
      end if;
   elif d eq 3 then  
      Z := [Y[2], Y[3], Y[1]];
   elif IsOdd (d) and IsOdd (q) then 
      u := Y[2]^2; v := Y[3]^-1;
      minus1 := &*[u^(v^(2 * i + 1)): i in [1..(d - 1) div 2]];
      V := v * minus1^-1; 
      Z := [Y[2], V, Y[1]];
   else 
      assert d ge 4 and (IsEven (d) or IsEven (q));
      V := (Y[3]^1)^(d - 1); 
      Z := [Y[2], V, Y[1]];
   end if;
   if d gt 2 and not IsPrime (q) then Append (~Z, Y[4]^-1); end if;
   return Z;
end function;
