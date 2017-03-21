freeze;

import "unipotent.m": PGroupStabiliser_;

/* depths is list containing depth of vectors in U;
   w is vector; U basis for subspace in canonical form;
   return weight of w wrt {w, U} */
SubspaceDepth:= function (depths, w, UU)
   n := #depths - Dimension (UU);
   d := Degree (UU);
   F := BaseRing (UU);
   V := VectorSpace (F, d);
   U := Basis (UU);

   dw := Depth (w);
   while dw in depths do
      pos := Position (depths, dw) - n;
      w := w - (w[dw] / U[pos][dw]) * U[pos];
      dw := Depth (w);
   end while;

   if dw ne 0 then return dw; else return d + 1; end if;
end function;

/* echelonise v wrt UU */
EcheloniseVector := function (v, depths, UU)
   U := Basis (UU);
   j := 0;
   for i in [1..#depths] do
      if IsDefined (depths, i) eq true then
         j +:= 1;
         alpha := v[depths[i]];
         if alpha ne 0 then
            v := v - (alpha / U[j][depths[i]]) * U[j];
         end if;
      end if;
   end for;
   return v;
end function;

/* find increasing chain of subspaces of V fixed under X */
PInvariantFlag := function (V, X)
   F := BaseRing (X);
   p := #F;
   d := Degree (X);
   MA := MatrixAlgebra (F, d);
   t := Ngens (X);
   Y := [MA!X.j : j in [1..t]];

   /* clumsy handling of trivial case */
   if t eq 0 then
      B := Basis (V);
      d := #B;
      W := [sub < V | [B[j] : j in [i..d]]> : i in [1..d]];
      Append (~W, sub < V | >);
   else
      W := [V];
      k := 1;
      I := Identity (MA);
      while Dimension (W[k]) ne 0 do
         k +:= 1;
         W[k] := &+[W[k-1] * (Y[j] - I): j in [1..t]];
      end while;
   end if;

   flag := [];
   for i in [1..#W - 1] do
      F, phi := quo < W[i] | W[i + 1] >;
      BF := Basis (F);
      FB := [BF[j] @@ phi : j in [1..Dimension (F)]];
      flag cat:= FB;
   end for;

   Spaces := [sub < V | >] cat
           [sub <V | [flag[i]: i in [#flag..j by -1]]>: j in [#flag..1 by -1]];
   Reverse (~Spaces);

   CB := (GL (d, p) ! &cat[Eltseq (f): f in flag])^-1;
   return flag, CB, Spaces;
end function;

/* return generating set which determines (decreasing) chief series subs
   for matrix group S */
BaseForMatrixGroup := function (S: Verify := true)
   if Type (S) eq GrpMat then
      d, F := BasicParameters (S);
   elif #S gt 0 then
      d := Nrows (Rep (S));
      F := BaseRing (Parent (Rep (S)));
      S := sub < GL (d, F) | S >;
   else
      return [], [];
   end if;

   T, phi := PCGroup (S);
   CS := ChiefSeries (T);
   t := NPCgens (T);
   gens := [CS[i].1 : i in [1..t]];
   X := [gens[i] @@ phi: i in [1..t]];
   if Verify then
      subs := [sub < S | [X[j] : j in [t..i by -1]]> : i in [t..1 by -1]];
      O := [#subs[i] : i in [1..#subs]];
      if #O gt 1 then
         assert {IsPrime (O[i + 1] div O[i]) : i in [1..#O - 1]} eq {true};
         assert {IsNormal (S, subs[i]) : i in [1..#O - 1]} eq {true};
      end if;
   end if;

   return X, sub <GL(d, F) | X>;
end function;

/* depth of u - u * g */
RelativeVectorDepth := function (u, g)
   d := Depth (u - u * g);
   return d eq 0 select Degree (u) + 1 else d;
end function;

FindMultiple := function (p, u, i, k, h)
   if exists (alpha) {alpha : alpha in [1..p - 1] |
               RelativeVectorDepth (u, k * h^alpha) gt i} eq false then
      error "error in FindMultiple";
   end if;

   return alpha;
end function;

BFindMultiple := function (depths, p, u, i, k, h, U)
   if exists (alpha) {alpha : alpha in [1..p - 1] |
      SubspaceDepth (depths, u - u * (k * h^alpha), U) gt i} eq false then
      error "error in FindMultiple";
   end if;

   return alpha;
end function;

VectorMultiple := function (p, u, h, i)
   beta := 0;
   while u[i] ne 0 and beta lt p do
      beta +:= 1;
      u := u * h;
   end while;

   if beta eq p then error "error in VectorMultiple"; end if;

   return beta, u;
end function;

SpaceMultiple := function (p, u, depths, subU, h, i)
   beta := 0;
   u := EcheloniseVector (u, depths, subU);
   while u[i] ne 0 do
      u := u * h;
      beta +:= 1;
      if beta gt p then error "error in SpaceMultiple"; end if;
      u := EcheloniseVector (u, depths, subU);
   end while;

   return beta, u;
end function;

/* return canonical form v for u, an element x in P such that u * x = v,
   and the stabiliser in P of v */
VectorCF := function (X, u)
   d := Degree (u); F := BaseRing (Parent (u));
   if #X eq 0 then
      return u, Identity (GL(d, F)), X;
   end if;

   p := #F;
   d := Nrows (X[1]);

   v := u;
   depth := [RelativeVectorDepth (v, g) : g in X];
   j0 := Minimum (depth);

   x := X[1]^0;
   Y := X;

   while (j0 lt d + 1) do
      g := X[Position (depth, j0)];
      alpha, v := VectorMultiple (p, v, g, j0);
      x := x * g^alpha;
      Y := [];
      for h in X do
         if h ne g then
            if RelativeVectorDepth (v, h) eq j0 then
               beta := FindMultiple (p, v, j0, h, g);
               hh := h * g^beta;
            else
               hh := h;
            end if;
            Append (~Y, hh);
         end if;
      end for;
      X := Y;
      if #X eq 0 then break; end if;
      depth := [RelativeVectorDepth (v, g) : g in X];
      j0 := Minimum (depth);
   end while;

   return v, x, X;
end function;

NextSubspaceCF := function (X, V, UU, depths, index)
   U := Basis (UU);
   d := Degree (UU);
   p := #BaseRing (UU);
   t := #U;
   v := U[index];
   subU := sub < V | [U[i] : i in [index + 1..t]]>;

   depth := [SubspaceDepth (depths, v - v * g, subU) : g in X];
   j0 := Minimum (depth);

   x := X[1]^0;
   Y := X;

   while (j0 lt d + 1) do
      g := X[Position (depth, j0)];
      v := EcheloniseVector (v, depths, subU);
      alpha, v := SpaceMultiple (p, v, depths, subU, g, j0);
      x := x * g^alpha;
      Y := [];
      for h in X do
         if h ne g then
            if SubspaceDepth (depths, v - v * h, subU) eq j0 then
               beta := BFindMultiple (depths, p, v, j0, h, g, subU);
               hh := h * g^beta;
            else
               hh := h;
            end if;
            Append (~Y, hh);
         end if;
      end for;
      X := Y;
      if #X eq 0 then break; end if;
      depth := [SubspaceDepth (depths, v - v * g, subU) : g in X];
      j0 := Minimum (depth);
   end while;

   UU := UU * x;
   depths[index] := Depth (v);

   return x, UU, depths, X;
end function;

/* determine canonical form for U under action of X;
   return canonical form UC, element trans where U^trans = UC,
   and stabiliser in X of UC */
SubspaceCF := function (X, U)
   d := Degree (U); F := BaseRing (U);

   if #X eq 0 then
       return U, Identity (GL(d, F)), X;
   end if;

   V := VectorSpace (F, d);

   UB := Basis (U);
   t := #UB;
   CF, trans, X := VectorCF (X, UB[t]);
   U := U * trans;
   UB := Basis (U);
   depths := [];
   depths[t] := Depth (UB[t]);
   for i in [t - 1..1 by -1] do
      if #X eq 0 then break; end if;
      temp, U, depths, X := NextSubspaceCF (X, V, U, depths, i);
      trans *:= temp;
   end for;

   return U, trans, X;
end function;

/* S is a p-group; U is a subspace of natural module;
   return canonical form UC for U, matrix trans where
   U^trans = UC, and generators for stabiliser in S of UC;

   if ComputeBase is false, we assume that the generators
   of S are a decreasing chief series for S */
PGroupStabiliser := function (S, U : ComputeBase := false)
    /* Construct the empty SLP group, which will be ignored in this case */
    W := SLPGroup(#S);

    /* Call PGroupStabiliser_ in unipotent.m, and ignore the transsp and XSLP return values */
    UC, trans, _, X, _, length := PGroupStabiliser_(S, U, W : ComputeBase := ComputeBase);

    /* Convert the X value into a space as expected from OldPGroupStabiliser */
    return UC, trans, sub < GL(Degree(U),BaseRing(U)) | X >, length;
end function;