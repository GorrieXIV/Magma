import "sl-natural.m": SLWordInGen;

// write A as SLP in standard generators of Omega^0 
OmegaCircleWordInGen := function (G, A) 

   d := Dimension(G);
   F := BaseRing(G);
   q := #F;
   w := PrimitiveElement(F);
   G := SL(d, F);
   e := Degree(F);

   Z := IntegerRing();

   Q := ClassicalStandardGenerators ("Omega", d, #F);
   Q := [G!Q[i] : i in [1..#Q]];

   ss := Q[1];
   tt := Q[2];
   ddelta := Q[3];
   v := Q[4];

   SS := SLPGroup (5);

   if IsOdd((d+1) div 2) then
      t := (GL(d, F)!(v^-1 * tt*v))^-1;
      T := (SS.2^SS.4)^-1;
      s := (GL(d, F)!(v^-1 * ss*v))^-1;
      S := (SS.1^SS.4)^-1;
   else
      t := GL(d, F)!(v^-1 * tt*v);
      T := SS.2^SS.4;
      s := GL(d, F)!(v^-1 * ss*v);
      S := SS.1^SS.4;
   end if;

   delta := GL(d, F)!(v^-1 * ddelta*v);
   DELTA := SS.3^SS.4;
   r := (t^s)^-1;
   R := (T^S)^-1;

   /* We now find the generators of OmegaPlus(d-1, q)
      as words in the generators for OmegaCircle(d, q).

      t^n sends col d-1 to d-1 + n*col 1 and
      col 2 to n^2*col 1 2n*col d-1 + col 2.
   
      Let a = [1, 1], b = [1, d-1], c = [1, 2].
      We need to solve an^2 + 2bn + c = 0 in order
      to get the power of n we need to kill the [1, 2] position */

   B := (t^v)^-1*t^((q-1) div 2)*t^v;
   a := B[1, d];
   n := Z!(-a/2);

   t2 := t^n*(t^v)^-1*t^((q-1) div 2)*t^v;
   T2 := T^n*(T^SS.4)^-1*T^((q-1) div 2)*T^SS.4;
   r2 := (r^n*(r^v)^-1*r^((q-1) div 2)*r^v)^-1;
   R2 := (R^n*(R^SS.4)^-1*R^((q-1) div 2)*R^SS.4)^-1;

   B := ((t*s)^v)^-1*t^((q-1) div 2)*(t*s)^v;
   a := B[1, d];
   n := Z!(-a/2);

   t1 := (t^n*((t*s)^v)^-1*t^((q-1) div 2)*(t*s)^v)^-1;
   T1 := (T^n*((T*S)^SS.4)^-1*T^((q-1) div 2)*(T*S)^SS.4)^-1;
   r1 := (r^n*((r*s)^v)^-1*r^((q-1) div 2)*(r*s)^v);
   R1 := (R^n*((R*S)^SS.4)^-1*R^((q-1) div 2)*(R*S)^SS.4);

   u := (r1^(t1^-1)*r1^2)^-1;
   U := (R1^(T1^-1)*R1^2)^-1;

   FF := sub<F|w^2>;
   py := FF!w;

   Ot1 := Id(G);
   ot1 := Id(SS);
   for i in [1..e] do
      Ot1 := Ot1*(t1^(delta^-(i-1)))^Z!Eltseq(py)[i];
      ot1 := ot1*(T1^(DELTA^-(i-1)))^Z!Eltseq(py)[i];
   end for;

   Or1 := Id(G);
   or1 := Id(SS);
   for i in [1..e] do
      Or1 := Or1*(r1^(delta^(i-1)))^Z!Eltseq(py)[i];
      or1 := or1*(R1^(DELTA^(i-1)))^Z!Eltseq(py)[i];
   end for;

   Ot2 := Id(G);
   ot2 := Id(SS);
   for i in [1..e] do
      Ot2 := Ot2*(t2^(delta^-(i-1)))^Z!Eltseq(py)[i];
      ot2 := ot2*(T2^(DELTA^-(i-1)))^Z!Eltseq(py)[i];
   end for;

   Or2 := Id(G);
   or2 := Id(SS);
   for i in [1..e] do
      Or2 := Or2*(r2^(delta^(i-1)))^Z!Eltseq(py)[i];
      or2 := or2*(R2^(DELTA^(i-1)))^Z!Eltseq(py)[i];
   end for;

   delta1 := r1*delta*t1;
   DELTA1 := R1*DELTA*T1;
   for j in [1..e] do
      a := Z!Eltseq((w^-1 - 1))[j];
      if IsOdd(j) then
         delta1 := delta1*(r1^(delta^((j-1) div 2)))^a;
         DELTA1 := DELTA1*(R1^(DELTA^((j-1) div 2)))^a;
      else
         delta1 := delta1*(Or1^(delta^((j-2) div 2)))^a;
         DELTA1 := DELTA1*(or1^(DELTA^((j-2) div 2)))^a;
      end if;
   end for;
   delta1 := delta1*Ot1^-1;
   DELTA1 := DELTA1*ot1^-1;
   b := delta1[3, 1];
   for j in [1..e] do
      a := Z!Eltseq(-b/w)[j];
      if IsOdd(j) then
         delta1 := delta1*(r1^(delta^((j-1) div 2)))^a;
         DELTA1 := DELTA1*(R1^(DELTA^((j-1) div 2)))^a;
      else
         delta1 := delta1*(Or1^(delta^((j-2) div 2)))^a;
         DELTA1 := DELTA1*(or1^(DELTA^((j-2) div 2)))^a;
      end if;
   end for;

   delta2 := ((delta1^u)^s)^u;
   DELTA2 := ((DELTA1^U)^S)^U;

   if d eq 3 then
      r1 := Id(G);
      t1 := Id(G);
      r2 := Id(G);
      t2 := Id(G);
      delta1 := delta;
      delta2 := delta;
   end if;

   S1 := Id(SS);
   S2 := Id(SS);

   FF := sub<F|w^2>;
   py := FF!w;

   ot := Id(G);
   TO := Id(SS);
   for i in [1..e] do
      ot := ot*(t^delta^-(i-1))^Z!Eltseq(py)[i];
      TO := TO*(T^DELTA^-(i-1))^Z!Eltseq(py)[i];
   end for;

   ro := Id(G);
   RO := Id(SS);
   for i in [1..e] do
      ro := ro*(r^delta^(i-1))^Z!Eltseq(py)[i];
      RO := RO*(R^DELTA^(i-1))^Z!Eltseq(py)[i];
   end for;

   GetBBTransvection := function(BB)
      // T := t2^-1;
      TT := T2^-1;
      // T := T^Z!Eltseq(BB)[1];
      TT := TT^Z!Eltseq(BB)[1];

      for r in [2..e] do
         if IsEven(r) then
            // o := Ot2^-1;
            oo := ot2^-1;
            // o := o^(delta1^-Z!((r-2)/2));
            oo := oo^(DELTA1^-Z!((r-2)/2));
            // o := o^Z!Eltseq(BB)[r];
            oo := oo^Z!Eltseq(BB)[r];
            // T := T*o;
            TT := TT*oo;
         else
            // o := t2^-1;
            oo := T2^-1;
            // o := o^(delta1^-Z!((r-1)/2));
            oo := oo^(DELTA1^-Z!((r-1)/2));
            // o := o^Z!Eltseq(BB)[r];
            oo := oo^Z!Eltseq(BB)[r];
            // T := T*o;
            TT := TT*oo;
         end if;
      end for;

      return TT;
   end function;

   GetAOne := procedure(~A, ~S1, ~S2)
      if A[1, 1] eq 0 then
         A := t*A;
         S1 := T*S1;
      end if;

      i := 3;
      while A[i, 1] eq 0 do
         i := i+1;
         if i eq d+1 then break; end if;
      end while;
   
      /* if A[1, 1] or A[1, 2] are the only non-zero entries
         on the first column */
      if (i eq d+1) or (i eq d) then
         /* A := r1*A; sticks values in the first column */
         AddRow(~A, 1, 1, 3);
         AddRow(~A, -1, 4, 2);
         S1 := R1*S1;
         i := 3;
         while A[i, 1] eq 0 do i := i+1; end while;
      end if;
   
      i := 4;
      j := 0;
      if A[4, 1] eq 0 then
         if A[3, 1] ne 0 then
            // A := (s^u)*A;
	      SwapRows(~A, 3, 4);
	      MultiplyRow(~A, -1, d);
	      S1 := (S^U)*S1;
         else
            i := 5;
            while A[i, 1] eq 0 do
               i := i+1;
               if i eq d+1 then break; end if;      
	      end while;
         end if;
         if i eq d+1 then
            /* if we are here, the only non-zero entries in the first
               column are in the first two rows;
               This should not happen as we have already used r1 to
               stick values in the other positions */
         elif A[4, 1] ne 0 then
            S1 := S1; // do nothing
         else
            if IsEven(i) then j := i div 2; else j := Z!(i/2 + 1/2); end if;
	    A := ((v*u^-1)^(j-2))*A;
	    S1 := ((SS.4*U^-1)^(j-2))*S1;
	    if A[4, 1] eq 0 then
	       // A := (s^u)*A;
	       SwapRows(~A, 3, 4);
	       MultiplyRow(~A, -1, d);
	       S1 := (S^U)*S1;
	    end if;
         end if;
      end if;
   
      BB := (1-A[1, 1])/A[4, 1];
      TT := GetBBTransvection(BB);
      // A := T*A;
      AddRow(~A, BB, 4, 1);
      AddRow(~A, -BB, 2, 3);
      S1 := TT*S1;

      if j ne 0 then
         A := ((v*u^-1)^-(j-2))*A;
         S1 := ((SS.4*U^-1)^-(j-2))*S1;
      end if;
   end procedure;

   KillRow := procedure(~A, ~S1, ~S2)
      for i in [2..((d-1) div 2)] do
         a := A[1, 4];
         S2 := S2*(T2^Z!Eltseq(a)[1]);
         // A := A*(t2^Z!Eltseq(a)[1]); 
         AddColumn(~A, -Eltseq(a)[1], 1, 4);
         AddColumn(~A, Eltseq(a)[1], 3, 2);
         for r in [2..e] do
            if IsEven(r) then
               S2 := S2* ((ot2^-1)^(DELTA1^-Z!((r-2)/2)))^-Z!Eltseq(a)[r];
               // A := A* ((Ot2^-1)^(delta1^-Z!((r-2)/2)))^Z!Eltseq(a)[r]; 
               AddColumn(~A, -Eltseq(a)[r]*w^(r-1), 1, 4);
               AddColumn(~A,  Eltseq(a)[r]*w^(r-1), 3, 2);
            else
	       S2 := S2* ((T2^-1)^(DELTA1^-Z!((r-1)/2)))^-Z!Eltseq(a)[r];
	       // A := A* ((t2^-1)^(delta1^-Z!((r-1)/2)))^-Z!Eltseq(a)[r]; 
	       AddColumn(~A, -Eltseq(a)[r]*w^(r-1), 1, 4);
               AddColumn(~A,  Eltseq(a)[r]*w^(r-1), 3, 2);
            end if;
         end for;
	 
         a := A[1, 3];
         S2 := S2*(T1^-Z!Eltseq(a)[1]);
         /* A := A*(t1^-Z!Eltseq(a)[1]); */
         AddColumn(~A, -Eltseq(a)[1], 1, 3);
         AddColumn(~A,  Eltseq(a)[1], 4, 2);
         for r in [2..e] do
            if IsEven(r) then
               S2 := S2* ((ot1^-1)^(DELTA2^-Z!((r-2)/2)))^Z!Eltseq(a)[r];
	       // A := A* ((Ot1^-1)^(delta2^-Z!((r-2)/2)))^Z!Eltseq(a)[r]; 
               AddColumn(~A, -Eltseq(a)[r]*w^(r-1), 1, 3);
               AddColumn(~A,  Eltseq(a)[r]*w^(r-1), 4, 2);
            else
               S2 := S2* ((T1^-1)^(DELTA2^-Z!((r-1)/2)))^Z!Eltseq(a)[r];
               // A := A* ((t1^-1)^(delta2^-Z!((r-1)/2)))^Z!Eltseq(a)[r]; 
               AddColumn(~A, -Eltseq(a)[r]*w^(r-1), 1, 3);
               AddColumn(~A,  Eltseq(a)[r]*w^(r-1), 4, 2);
	      end if;
         end for;
            
         S2 := S2*SS.4*(U^-1);
         /* A := A*v*(u^-1); rotates the 2..d/2-1 blocks */
         for m in [(((d+1) div 2) -2)..2 by -1] do
            SwapColumns(~A, 2*m-1, 2*m+1);
            SwapColumns(~A, 2*m, 2*m+2);
         end for;
         if IsEven((d+1) div 2) then
            MultiplyColumn(~A, -1, 3);
            MultiplyColumn(~A, -1, 4);
         end if;
      end for;

     // A := A*(u*v^-1)^((d+1) div 2 - 2); 
     // S2 := S2*(U*SS.4^-1)^((d+1) div 2 - 2); 
   end procedure;

   KillColumn := procedure(~A, ~S1, ~S2)
      for i in [2..((d-1) div 2)] do
         a := A[4, 1];
         S1 := (R2^Z!Eltseq(a)[1])*S1;
         // A := (r2^Z!Eltseq(a)[1])*A;
         AddRow(~A, -Eltseq(a)[1], 1, 4);
         AddRow(~A, Eltseq(a)[1], 3, 2);
         for r in [2..e] do
            if IsEven(r) then
               S1 := ((or2^-1)^(DELTA1^Z!((r-2)/2)))^-Z!Eltseq(a)[r]*S1;
               // A := ((Or2^-1)^(delta1^Z!((r-2)/2)))^-Z!Eltseq(a)[r]*A;
               AddRow(~A, -Eltseq(a)[r]*w^(r-1), 1, 4);
               AddRow(~A,  Eltseq(a)[r]*w^(r-1), 3, 2);
            else
   	       S1 := ((R2^-1)^(DELTA1^Z!((r-1)/2)))^-Z!Eltseq(a)[r]*S1;
               // A := ((r2^-1)^(delta1^Z!((r-1)/2)))^-Z!Eltseq(a)[r]*A;
               AddRow(~A, -Eltseq(a)[r]*w^(r-1), 1, 4);
               AddRow(~A,  Eltseq(a)[r]*w^(r-1), 3, 2);
            end if;
         end for;
    
         a := A[3, 1];
         S1 := (R1^Z!-Eltseq(a)[1])*S1;
         // A := (r1^Z!-Eltseq(a)[1])*A;
         AddRow(~A, -Eltseq(a)[1], 1, 3);
         AddRow(~A,  Eltseq(a)[1], 4, 2);
         for r in [2..e] do
            if IsEven(r) then
               S1 := ((or1^-1)^(DELTA2^Z!((r-2)/2)))^Z!Eltseq(a)[r]*S1;
               // A := ((Or1^-1)^(delta2^Z!((r-2)/2)))^Z!Eltseq(a)[r]*A;
               AddRow(~A, -Eltseq(a)[r]*w^(r-1), 1, 3);
               AddRow(~A,  Eltseq(a)[r]*w^(r-1), 4, 2);
            else
               S1 := ((R1^-1)^(DELTA2^Z!((r-1)/2)))^Z!Eltseq(a)[r]*S1;
               // A := ((r1^-1)^(delta2^Z!((r-1)/2)))^Z!Eltseq(a)[r]*A;
               AddRow(~A, -Eltseq(a)[r]*w^(r-1), 1, 3);
               AddRow(~A,  Eltseq(a)[r]*w^(r-1), 4, 2);
            end if;
         end for;
         
         S1 := SS.4*(U^-1)*S1;
         // A := v*(u^-1)*A;
         for m in [2..(((d+1) div 2) -2)] do
            SwapRows(~A, 2*m-1, 2*m+1);
   	 SwapRows(~A, 2*m, 2*m+2);
         end for;
         if IsEven((d+1) div 2) then
            MultiplyRow(~A, -1, d-2);
            MultiplyRow(~A, -1, d-1);
         end if;
      end for;
   end procedure;

   UsingT := procedure(~A, ~S1, ~S2)
      if d ne 3 then
         a := A[1, d];
         for z in [1..e] do
            n := Eltseq(a)[z]/2;
            A := A*((t^(delta1^-(z-1)))^-Z!n);
            // AddColumn(~A, -n*w^(z-1), 1, 2);
            // AddColumn(~A, -2*n*w^-(z-1), 1, 2);
            S2 := S2*((T^(DELTA1^-(z-1)))^-Z!n);
         end for;
      else
         a := FF!A[1, d];
         for z in [1..e] do
            n := Eltseq(a)[z]/2;
            A := A*((t^(delta1^-(z-1)))^-Z!n);
            S2 := S2*((T^(DELTA^-(z-1)))^-Z!n);
         end for;
      end if;
   end procedure;

   UsingTS := procedure(~A, ~S1, ~S2)
      if d ne 3 then
         a := A[d, 1];
         for z in [1..e] do
            n := Eltseq(a)[z];
            A := (((t^s)^(delta1^(z-1)))^Z!n)*A;
            // AddColumn(~A, -n*w^(z-1), 1, 2);
            // AddColumn(~A, -2*n*w^-(z-1), 1, 2);
            S1 := (((T^S)^(DELTA1^(z-1)))^Z!n)*S1;
         end for;
      else
         a := FF!A[d, 1];
         for z in [1..e] do
            n := Eltseq(a)[z];
            A := (((t^s)^(delta1^(z-1)))^Z!n)*A;
            S1 := (((T^S)^(DELTA^(z-1)))^Z!n)*S1;
         end for;
      end if;
   end procedure;

   GetAOneByT := procedure(~A, ~S1, ~S2)
      a := A[1, 1];
      b := A[2, 1];
      c := A[d, 1];
      while (b eq 0) or (c eq 0) do
         A := A*t^s;
         S2 := S2*T^S;
         a := A[1, 1];
         b := A[2, 1];
         c := A[d, 1];
      end while;
      P := PolynomialRing(F);
      py := a - 1 + b*P.1^2 + 2*c*P.1;
      if a eq 1 then
         n := 0;
      else
         if #Roots(py) ne 0 then
            n := Roots(py)[1, 1];
         else
            n := 0;
         end if;
      end if;
      A := t^Z!n*A;
      S1 := T^Z!n*S1;

   end procedure;

   UnSymSquare := function(A)
      if Degree(A) ne 3 then
         return false;
      end if;
      q := #BaseRing(A);
      a := Root(A[1, 1], 2);
      if a ne 0 then
         b := A[1, 2]/(2*a);
         c := A[2, 1]/a;
      else
         c := Root(A[3, 1], 2);
         b := A[2, 2]/c;
      end if;
      if b ne 0 then
         d := A[2, 3]/b;
      else
         d := A[2, 2]/a;
      end if;

      return GL(2, q)![a, b, c, d];
   end function;

   AA := A;
   for i in [1..((d+1) div 2 - 2)] do
      GetAOne(~A, ~S1, ~S2);
      KillRow(~A, ~S1, ~S2);
      KillColumn(~A, ~S1, ~S2);

      UsingT(~A, ~S1, ~S2);
      UsingTS(~A, ~S1, ~S2);

      A := v*A*(v^-1);
      S2 := S2*(SS.4^-1);
      S1 := SS.4*S1;
   end for;

   CB2 := GL(3, F)![1, 0, 0, 0, 0, 1, 0, 1, 0];
   A := v*A*(v^-1);
   S2 := S2*(SS.4^-1);
   S1 := SS.4*S1;

   EB := ExtractBlock(A, d-2, d-2, 3, 3);
   if EB notin SL(3, F) then
      // return false, A, S1^-1 * S2^-1;
      return false, S1^-1 * S2^-1;
   end if;
   B := SL(3, F)!EB;

   B := B^CB2;
   x1 := UnSymSquare(B);
   x1 := MatrixAlgebra(F, 2)!x1;
   x1 := x1 / Root(Determinant(x1), 2);
   _, w1 := SLWordInGen(SL(2, F), GL(2, F) ! x1);

   psi := hom<Parent(w1) -> SS|SS.1, SS.1, SS.2, SS.3>;

   word := S1^-1 * psi(w1) * S2^-1;

   /* Evaluate(word, Q) eq AA should be true */
   return IsIdentity (A * Evaluate(psi(w1^-1), Q)), word;
end function;

intrinsic SOCircleWordInGen(G:: GrpMat, A:: GrpMatElt) -> BoolElt, GrpSLPElt
{write A as SLP in standard generators of SO^0}
   _, _, J := OrthogonalForm(G);
   sn := SpinorNorm(A, J);
   if sn eq 0 then
      flag, word := OmegaCircleWordInGen(G, A);
   else
      d := Dimension(G);
      F := BaseRing(G);
      QQ := ClassicalStandardGenerators ("Omega", d, #F: SpecialGroup := true);
      sp := GL(d, F)!QQ[#QQ];
      A *:= sp;
      flag, word := OmegaCircleWordInGen(G, A);
      SS := Parent (word);
      S := SLPGroup (6);
      phi := hom<SS -> S | S.1, S.2, S.3, S.4, S.5>;
      word := phi (word);
      word *:= S.6^-1;
   end if;
   return flag, word;
end intrinsic;
