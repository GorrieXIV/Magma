
/* construct symmetric square repn of GL (d, q);
    randomly conjugate it by an element of the larger GL
    so that the basis is not visible */

MySymmetricSquare := function (d, q: Full := false)
   G := Full eq false select SL(d, q) else GL(d, q);
   M := GModule (G);
   M := SymmetricSquare (M);
   M := [ActionGenerator (M, i): i in [1..Ngens (G)]];
   k := Nrows (Rep (M));
   H := sub <GL (k, q) | M>;
   g := Random (GL(k, q));
   H := sub < GL (k, q) | [g^-1 * H.i * g : i in [1..Ngens (H)]]>;
   return H;
end function;

/* construct alternating square repn of GL (d, q);
   randomly conjugate it by an element of the larger GL
   so that the basis is not visible */

MyAlternatingSquare := function (d, q: Full := false)
   G := Full select GL(d, q) else SL(d, q);
   M := GModule (G);
   M := ExteriorSquare (M);
   M := [ActionGenerator (M, i): i in [1..Ngens (G)]];
   k := Nrows (Rep (M));
   H := sub <GL (k, q) | M>;
   return H^Random (GL(k, q));
end function;

ConstructDual := function (G)
   M := GModule (G);
   U := Dual (M);
   T := TensorProduct (U, M);
   A := ActionGroup (T);
   return A;
end function;

MyAdjointRepresentation := function (d, q: Full := false)
   G := Full select GL(d, q) else SL(d, q);
   G := ConstructDual (G);
   M := GModule (G);
   CF := CompositionFactors (M);
   flag := exists(k){ k: k in [1..#CF] | Dimension (CF[k]) 
                  in {d^2 - 1, d^2 - 2}};
   assert flag;
   return ActionGroup (CF[k]);
end function;

TensorProd := function (U)
   a := U[1];
   for i in [2..#U] do
      a := TensorProduct (a, U[i]);
   end for;
   return a;
end function;

MyDeltaRepresentation := function (d, q, e: Full := false)
   G := Full eq false select SL(d, q) else GL(d, q);
   F := GF (q);
   p := Characteristic (F);
   X := [G.i: i in [1..Ngens (G)]];
   Y := [FrobeniusImage (G.i, e): i in [1..Ngens (G)]];
   Z := [TensorProd ([X[i], Y[i]]): i in [1..#X]];
   return sub < GL (d^2, F) | Z>;
end function;

DeltaSquare := function (G, e)
   if Type (G) eq GrpMat then
      d := Degree (G);
      F := BaseRing (G);
      X := [G.i: i in [1..Ngens (G)]];
      Y := [FrobeniusImage (G.i, e): i in [1..Ngens (G)]];
      Z := [KroneckerProduct (X[i], Y[i]): i in [1..#X]];
      return sub <GL (d^2, F) | Z>;
   else
      h := FrobeniusImage (G, e);
      return TensorProduct (G, h);
   end if;
end function; 

MyOtherRepresentation := function (d, q, e: Full := false)
   G := Full eq false select SL(d, q) else GL(d, q);
   F := GF (q);
   M := GModule (G);
   U := Dual (M);
   H := ActionGroup (U);
   p := Characteristic (F);
   X := [H.i: i in [1..Ngens (G)]];
   Y := [FrobeniusImage (G.i, e): i in [1..Ngens (G)]];
   Z := [TensorProd ([X[i], Y[i]]): i in [1..#X]];
   return sub < GL (d^2, F) | Z>;
end function;
