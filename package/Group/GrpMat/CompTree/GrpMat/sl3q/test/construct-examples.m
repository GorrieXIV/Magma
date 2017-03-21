MyExteriorPower := function (G, t)
   M := GModule (G);
   N := ExteriorPower (M, t);
   G := ActionGroup (N);
   return G;
end function;

MySymmetricPower := function(G, t)
   M := GModule (G);
   N := SymmetricPower (M, t);
   G := ActionGroup (N);
   return G;
end function;

MyDeltaRepresentation := function (G,e)
d:=Degree(G);
   F := BaseRing(G);
d :=Degree (G);
   p := Characteristic (F);
   X := [G.i: i in [1..Ngens (G)]];
   Y := [FrobeniusImage (G.i, e): i in [1..Ngens (G)]];
   Z := [KroneckerProduct (X[i], Y[i]): i in [1..#X]];
G:=sub<GL(d^2,F) | Z>;
M:=GModule (G);
factors:=CompositionFactors(M);
dim, index:= Maximum([Dimension(x): x in factors]);
M:=factors[index];
return RandomConjugate(MatrixGroup(M));
end function;

MyOtherRepresentation := function (G, e)
   F := BaseRing (G);
   q := #F;
   d := Degree (G);
   M := GModule (G);
   U := Dual (M);
   H := ActionGroup (U);
   p := Characteristic (F);
   X := [H.i: i in [1..Ngens (G)]];
   Y := [FrobeniusImage (G.i, e): i in [1..Ngens (G)]];
   Z := [KroneckerProduct (X[i], Y[i]): i in [1..#X]];
   G := sub < GL (d^2, F) | Z>;
M:=GModule (G);
factors:=CompositionFactors(M);
dim, index:= Maximum([Dimension(x): x in factors]);
M:=factors[index];
return RandomConjugate(MatrixGroup(M));
end function;

ConstructDual := function (G)
   M := GModule (G);
   U := Dual (M);
   T := TensorProduct (U, M);
   A := ActionGroup (T);
   return A;
end function;

MyAdjointRepresentation := function (G)
d:=Degree(G);
   G := ConstructDual (G);
   M := GModule (G);
   CF := CompositionFactors (M);
   flag := exists(k){ k: k in [1..#CF] | Dimension (CF[k]) 
                  in {d^2 - 1, d^2 - 2}};
   assert flag;
   return ActionGroup (CF[k]);
end function;



DifferentOnes := function (S, MyCompare)

   if #S le 1 then return S, [i : i in [1..#S]]; end if;
   D := [S[1]];
   for i in [2..#S] do
     if forall {j : j in [1..#D] | 
                 MyCompare (S[i], D[j]) eq false}  then 
        Append (~D, S[i]);
     end if;
   end for;
   pos := [Position (S, D[i]) : i in [1..#D]];
   return D, pos;
end function;

ConstructReps := function (G)
   M:=GModule (G);
   T := TensorProduct (M, M);
   T := TensorProduct (T, M);
   CF := CompositionFactors (T);
   N := [(SymmetricPower (M, i)): i in [2..5]] cat 
        [(ExteriorPower (M, i)): i in [2..4]]; 
   N := [x : x in N | Dimension (x) gt 0];
   if #N gt 0 then 
      CF2 := &cat[CompositionFactors (x): x in N];
   else 
      CF2 := [];
   end if;
   if Degree (G) le 8 then 
      T := TensorProduct (M, M);
      T := TensorProduct (T, T);
      CF3 := CompositionFactors (T);
   else
      CF3 := [];
   end if;

   CF := CF cat CF2 cat CF3;
   CF := DifferentOnes (CF, IsIsomorphic);
   F := BaseRing (G);
   A := MyDeltaRepresentation (G, Degree (F) + 1);
   B := MyOtherRepresentation (G, Degree (F) + 2);
   
   return [ActionGroup (x): x in CF | Dimension (x) gt 1] cat [A, B]; 
end function;
