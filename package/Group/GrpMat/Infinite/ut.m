freeze;

// generators for UT(n, R)

UT := function (n, R)
   MA := MatrixAlgebra (R, n);
   p := Characteristic (R);
   L := [];
   for i in [1..n-1] do 
      for j in [1..n-i] do
         r := Identity (MA);
         r[j][i+j] := 1;
         Append (~L, r);
      end for;
   end for;
   return [GL(n, R) ! l: l in L];
end function;

// pc-presentation for UT(n, R) and corresponding matrices 

PCPresentationUT := function (n, R)
   U := UT(n, R);
   n := Binomial (n, 2);
   F := FreeGroup (#U);
   E := [F.i : i in [1..Ngens (F)]];
   I := [i : i in [1..#U] | HasFiniteOrder (U[i])];
   J := [i : i in [1..#U] | HasFiniteOrder (U[i]) eq false];
   Um1 := [u^-1: u in U];
   Rels := [];
   for i in [1..n-1] do
      for j in [i+1..n-1] do
         for e in [-1,+1] do
            lhs := E[j]^(E[i]^e);
            // w := U[j]^(U[i]^e);
            w := (U[j], U[i]^e);
            if IsIdentity (w) then
               x := Identity (F);
            else 
               pos := Position (U, w);
               if pos eq 0 then 
                  pos := Position (Um1, w);
                  sign := -1;
               else 
                  sign := 1;
               end if;
               x := E[pos]^sign;
               rhs := F.j * x;
               Append (~Rels, lhs = rhs);
            end if;
         end for;
      end for;
   end for;    
   Q := quo< GrpGPC : F | Rels: Check := false>;
   return Q, U;
end function;

// given a matrix A in <U> = UT(n, q) return it as word in P, isomorphic copy 

MatrixToWord := function (P, A, U)
   word := Identity (P);
   offset := 0;
   n := Nrows (A);
   for j in [1..n - 1] do 
     exp := [A[i][i+j]: i in [1..n-j]];
     mat := &*[U[offset + i]^exp[i]: i in [1..#exp]];
     word *:= &*[P.(offset + i)^exp[i]: i in [1..#exp]];
     offset +:= #exp;
     A := mat^-1 * A;
   end for;
   return word;
end function;

// G is unipotent matrix group defined over Q;
// return change-of-basis matrix so that conjugate is over Z 

ConjugateToIntegers := function (G)
   d := Degree (G);
   F := BaseRing (G);
   Z := Integers ();
   if IsTrivial (G) then 
      H := sub<GL(d, Z) | >; 
      return H, Identity (GL(d, F));
   end if;
   f, cb := IsUnipotent (G);
   if not f then error "Input group is not unipotent"; end if;
   assert f;
   G := G^cb;
   DiagEntry := function (U, i, C)
      return LCM ([Denominator (C[j]^-1 * U[k][j][i]): j in [1..i-1], 
         k in [1..#U]]);
   end function;
   U := [G.i: i in [1..Ngens (G)]];
   C := [1];
   for i in [2..d] do 
      C[i] := DiagEntry(U, i, C);
   end for;
   C := DiagonalMatrix (F, C);
   CB := GL(d, F) ! C;
   H := G^CB;
   H := sub<GL(d, Z) | [H.i: i in [1..Ngens (H)]]>;
   return H, cb * CB;
end function;
