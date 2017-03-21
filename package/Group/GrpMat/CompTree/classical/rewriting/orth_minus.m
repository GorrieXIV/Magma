// import "../../GrpMat/ClassicalRec/sld2.m":OrthogonalForm2;
import "sl-natural.m": SLWordInGen;
import "orth_minus_char2.m": OmegaMinusChar2WordInGen; 

// write A as SLP in standard generators for Omega^-
OmegaMinusWordInGen := function (G, A) 

   F := BaseRing (G);

   if Characteristic (F) eq 2 then 
      flag, word := OmegaMinusChar2WordInGen (G, A);
      return flag, word;
   end if;

   d := Dimension (G);

   Q := ClassicalStandardGenerators ("Omega-", d, #F);

   // adjustment to the standard generators
   Q[1] := (Q[2]^Q[1])^-1;

   Q := [GL(d, F)!Q[i] : i in [1..#Q]];
   PG := sub<GL(d, F)|Q>;
   ww := PrimitiveElement (GF (#F^2));
   w := PrimitiveElement (F);
   sl := SL (2, #F^2);
   e := Degree (F);
   ee := 2*e;
   q := #F;
   Z := IntegerRing ();

   rr := GL(d, F)!Q[1];
   tt := GL(d, F)!Q[2];
   ddelta := GL(d, F)!Q[3];
   u := GL(d, F)!Q[4];
   v := GL(d, F)!Q[5];

   SS := SLPGroup (5);

   if IsOdd (d div 2) then
      t := (GL(d, F)!(v^-1 * tt*v))^-1;
      T := (SS.2^SS.5)^-1;
      r := (GL(d, F)!(v^-1 * rr*v))^-1;
      R := (SS.1^SS.5)^-1;
   else
      t := GL(d, F)!(v^-1 * tt*v);
      T := SS.2^SS.5;
      r := GL(d, F)!(v^-1 * rr*v);
      R := SS.1^SS.5;
   end if;

   delta := GL(d, F)!(v^-1 * ddelta*v);
   DELTA := SS.3^SS.5;
   s := r*t^-1*r;
   S := R*T^-1*R;

   /* We now find the generators of OmegaPlus (d-2, q)
      as words in the generators for OmegaMinus (d, q).

      t^n sends col d-1 to d-1 + n*col 1 and
      col 2 to n^2*col 1 2n*col d-1 + col 2.
   
      Let a = [1, 1], b = [1, d-1], c = [1, 2].
      We need to solve an^2 + 2bn + c = 0 in order to get the 
      power of n we need to kill the [1, 2] position */

   P := PolynomialRing (F);
   B := (t^v)^-1*t^((q-1) div 2)*t^v;
   a := B[1, 1];
   b := B[1, d-1];
   c := B[1, 2];
   py := P!(a*P.1^2 + 2*b*P.1 + c);
   if d ne 2 then
      n := Z!Roots (py)[1, 1];
   else
      n := 0;
   end if;

   t2 := t^n*(t^v)^-1*t^((q-1) div 2)*t^v;
   T2 := T^n*(T^SS.5)^-1*T^((q-1) div 2)*T^SS.5;
   r2 := (r^n*(r^v)^-1*r^((q-1) div 2)*r^v)^-1;
   R2 := (R^n*(R^SS.5)^-1*R^((q-1) div 2)*R^SS.5)^-1;

   delta2 := (delta* (delta^-1)^v);
   DELTA2 := (DELTA* (DELTA^-1)^SS.5);
   delta1 := ((delta2^u)^s)^u;
   DELTA1 := ((DELTA2^SS.4)^S)^SS.4;

   B := ((t*s)^v)^-1*t^((q-1) div 2)* (t*s)^v;
   a := B[1, 1];
   b := B[1, d-1];
   c := B[1, 2];
   py := P!(a*P.1^2 + 2*b*P.1 + c);
   if d ne 2 then
      n := Z!Roots (py)[1, 1];
   else
      n := 0;
   end if;

   t1 := (t^n*((t*s)^v)^-1*t^((q-1) div 2)*(t*s)^v)^-1;
   T1 := (T^n*((T*S)^SS.5)^-1*T^((q-1) div 2)*(T*S)^SS.5)^-1;
   r1 := (r^n*((r*s)^v)^-1*r^((q-1) div 2)*(r*s)^v);
   R1 := (R^n*((R*S)^SS.5)^-1*R^((q-1) div 2)*(R*S)^SS.5);

   S1 := Id (SS);
   S2 := Id (SS);

   FF := sub<GF (#F^2)|ww^2>;
   py := FF!ww;

   ot := Id (PG);
   TO := Id (SS);
   for i in [1..ee] do
      ot := ot*(t^delta^-(i-1))^Z!Eltseq (py)[i];
      TO := TO*(T^DELTA^-(i-1))^Z!Eltseq (py)[i];
   end for;

   ro := Id (PG);
   RO := Id (SS);
   for i in [1..ee] do
      ro := ro*(r^delta^(i-1))^Z!Eltseq (py)[i];
      RO := RO*(R^DELTA^(i-1))^Z!Eltseq (py)[i];
   end for;

   FF := sub<F|w^2>;
   py := FF!w;

   // Ot1 := Id (G);
   ot1 := Id (SS);
   for i in [1..e] do
      // Ot1 := Ot1*(t1^(delta2^-(i-1)))^Z!Eltseq (py)[i]; 
      ot1 := ot1*(T1^(DELTA2^-(i-1)))^Z!Eltseq (py)[i];
   end for;

   // Or1 := Id (G);
   or1 := Id (SS);
   for i in [1..e] do
      // Or1 := Or1* (r1^(delta2^(i-1)))^Z!Eltseq (py)[i]; 
      or1 := or1* (R1^(DELTA2^(i-1)))^Z!Eltseq (py)[i];
   end for;

   /* zz := Log (-w^2); 
      -1 = w^((q-1) div 2) and so the answer is (q-1)/2 + 2. */
   zz := ((q-1) div 2) + 2;

   // Ot2 := Id (G);
   ot2 := Id (SS);
   if IsEven (zz) then
      for i in [1..e] do
         // Ot2 := Ot2*(t2^(delta1^-((zz div 2) + (i-2))))^Z!Eltseq (py)[i]; 
         ot2 := ot2*(T2^(DELTA1^-((zz div 2) + (i-2))))^Z!Eltseq (py)[i];
      end for;
   else
      // Ot2 := Ot2*(t2^(delta1^-(zz div 2))); 
      ot2 := ot2*T2^(DELTA1^-(zz div 2));
   end if;

   // Or2 := Id (G);
   or2 := Id (SS);
   if IsEven (zz) then
      for i in [1..e] do
         // Or2 := Or2*(r2^(delta1^((zz div 2) + (i-2))))^Z!Eltseq (py)[i]; 
         or2 := or2*(R2^(DELTA1^((zz div 2) + (i-2))))^Z!Eltseq (py)[i];
      end for;
   else
      /* Or2 := Or2*(r2^(delta1^(zz div 2))); */
      or2 := or2*R2^(DELTA1^(zz div 2));
   end if;

   GetBBTransvection := function (BB)
      // T := t2^-1;
      TT := T2^-1;
      // T := T^Z!Eltseq (BB)[1];
      TT := TT^Z!Eltseq (BB)[1];

      for r in [2..e] do
         if IsEven (r) then
            // o := Ot2;
            oo := ot2;
            // o := o^(delta1^-Z!((r-2)/2));
            oo := oo^(DELTA1^-Z!((r-2)/2));
            // o := o^Z!Eltseq (BB)[r];
            oo := oo^Z!Eltseq (BB)[r];
	    // T := T*o;
            TT := TT*oo;
         else
            // o := t2^-1;
            oo := T2^-1;
            // o := o^(delta1^-Z!((r-1)/2));
            oo := oo^(DELTA1^-Z!((r-1)/2));
            // o := o^Z!Eltseq (BB)[r];
            oo := oo^Z!Eltseq (BB)[r];
            // T := T*o;
            TT := TT*oo;
         end if;
      end for;
      return TT;
   end function;

   GetAOne := procedure (~A, ~S1, ~S2)
      if A[1, 1] eq 0 then 
         i := Depth (A[1]);
         // find which block we need
         if IsEven (i) then j := i div 2; else j := Z!(i/2 + 1/2); end if;
         if i eq 2 then
            // A := A*s;
	    SwapColumns (~A, 1, 2);
	    MultiplyColumn (~A, -1, d-1);
	    S2 := S2*S;
         else
            // A := A* (u*v^-1)^(j-2)* (u*v)^(j-2)*u; 
	    if IsOdd (j) then
               /* j odd - swap blocks 1 and j and negate 2..j-1 */
	       SwapColumns (~A, 1, 2*j - 1);
	       SwapColumns (~A, 2, 2*j);
	       for y in [3..2*j-2] do
	          MultiplyColumn (~A, -1, y);
	       end for;
	    else
               /* j even - swap blocks 1 and j and negate 1 (new)..j-1 */
	       SwapColumns (~A, 1, 2*j - 1);
	       SwapColumns (~A, 2, 2*j);
	       for y in [1..2*j-2] do
	          MultiplyColumn (~A, -1, y);
	       end for;	    
	    end if;
            S2 := S2*(SS.4*SS.5^-1)^(j-2)*(SS.4*SS.5)^(j-2)*SS.4; 
         end if;
         if A[1, 1] eq 0 then
            // A := A*s;
	    SwapColumns (~A, 1, 2);
	    MultiplyColumn (~A, -1, d-1);
	    S2 := S2*S;
         end if;
      end if; 

      i := 3;
      while A[i, 1] eq 0 do
         i := i+1; if i eq d+1 then break; end if;
      end while;
   
      /* if A[1, 1] or A[1, 2] are the only non-zero entries
         on the first column */
      if (i eq d+1) or (i eq d) or (i eq d-1) then
         // A := r1*A; sticks values in the first column 
         AddRow (~A, 1, 1, 3);
         AddRow (~A, -1, 4, 2);
         S1 := R1*S1;
         i := 3;
         while A[i, 1] eq 0 do i := i+1; end while;
      end if;
   
      i := 4;
      j := 0;
      if A[4, 1] eq 0 then
         if A[3, 1] ne 0 then
            // A := (s^u)*A;
	    SwapRows (~A, 3, 4);
	    MultiplyRow (~A, -1, d-1);
	    S1 := (S^SS.4)*S1;
         else
            i := 5;
            while A[i, 1] eq 0 do
               i +:= 1; if i eq d+1 then break; end if;      
	    end while;
         end if;
         if i eq d+1 then
            /* if we are here, the only non-zero entries in the first
               column are in the first two rows
	       Conjecture: this case never occurs */
         elif A[4, 1] ne 0 then
            S1 := S1; // do nothing
         else
            if IsEven (i) then j := i div 2; else j := Z! (i/2 + 1/2); end if;
            A := ((v*u^-1)^(j-2))*A;
	    S1 := ((SS.5*SS.4^-1)^(j-2))*S1;
	    if A[4, 1] eq 0 then
	       // A := (s^u)*A;
	       SwapRows (~A, 3, 4);
	       MultiplyRow (~A, -1, d-1);
	       S1 := (S^SS.4)*S1;
	    end if;
         end if;
      end if;
   
      BB := (1-A[1, 1])/A[4, 1];
      TT := GetBBTransvection (BB);
      // A := T*A;
      AddRow (~A, BB, 4, 1);
      AddRow (~A, -BB, 2, 3);
      S1 := TT*S1;

      if j ne 0 then
         A := ((v*u^-1)^-(j-2))*A;
         S1 := ((SS.5*SS.4^-1)^-(j-2))*S1;
      end if;
   end procedure;

   KillRow := procedure (~A, ~S1, ~S2)
      for i in [2.. (d div 2) - 1] do
         a := A[1, 4];
         S2 := S2* (T2^Z!Eltseq (a)[1]);
         // A := A * (t2^Z!Eltseq (a)[1]); 
         AddColumn (~A, -Eltseq (a)[1], 1, 4);
         AddColumn (~A,  Eltseq (a)[1], 3, 2);
         for r in [2..e] do
            if IsEven (r) then
               S2 := S2 * ((ot2^-1)^(DELTA1^-Z! ((r-2)/2)))^Z!Eltseq (a)[r];
               // A := A * ((Ot2^-1)^(delta1^-Z! ((r-2)/2)))^Z!Eltseq (a)[r]; 
               AddColumn (~A, -Eltseq (a)[r]*w^(r-1), 1, 4);
               AddColumn (~A,  Eltseq (a)[r]*w^(r-1), 3, 2);
            else
	       S2 := S2 * ((T2^-1)^(DELTA1^-Z! ((r-1)/2)))^-Z!Eltseq (a)[r];
               // A := A * ((t2^-1)^(delta1^-Z! ((r-1)/2)))^-Z!Eltseq (a)[r]; 
               AddColumn (~A, -Eltseq (a)[r]*w^(r-1), 1, 4);
               AddColumn (~A,  Eltseq (a)[r]*w^(r-1), 3, 2);
            end if;
         end for;
	 
         a := A[1, 3];
         S2 := S2*(T1^-Z!Eltseq (a)[1]);
         // A := A*(t1^-Z!Eltseq (a)[1]); 
         AddColumn (~A, -Eltseq (a)[1], 1, 3);
         AddColumn (~A,  Eltseq (a)[1], 4, 2);
         for r in [2..e] do
            if IsEven (r) then
               S2 := S2*((ot1^-1)^(DELTA2^-Z!((r-2)/2)))^Z!Eltseq (a)[r];
               // A := A*((Ot1^-1)^(delta2^-Z!((r-2)/2)))^Z!Eltseq (a)[r]; 
               AddColumn (~A, -Eltseq (a)[r]*w^(r-1), 1, 3);
               AddColumn (~A,  Eltseq (a)[r]*w^(r-1), 4, 2);
            else
               S2 := S2*((T1^-1)^(DELTA2^-Z!((r-1)/2)))^Z!Eltseq (a)[r];
               // A := A*((t1^-1)^(delta2^-Z!((r-1)/2)))^Z!Eltseq (a)[r]; 
               AddColumn (~A, -Eltseq (a)[r]*w^(r-1), 1, 3);
               AddColumn (~A,  Eltseq (a)[r]*w^(r-1), 4, 2);
	      end if;
         end for;
            
         S2 := S2*SS.5*SS.4^-1;
         /* A := A*v* (u^-1); rotates the 2..d/2-1 blocks */
         for m in [((d div 2)-2)..2 by -1] do
            SwapColumns (~A, 2*m-1, 2*m+1);
            SwapColumns (~A, 2*m, 2*m+2);
         end for;
         if IsEven (d div 2) then
            MultiplyColumn (~A, -1, 3);
            MultiplyColumn (~A, -1, 4);
         end if;
      end for;

     // A := A* (u*v^-1)^(d div 2 - 2); 
     // S2 := S2* (SS.4*SS.5^-1)^(d div 2 - 2); 
   end procedure;

   KillColumn := procedure (~A, ~S1, ~S2)
      for i in [2..d div 2 - 1] do
         a := A[4, 1];
         S1 := (R2^Z!Eltseq (a)[1])*S1;
         // A := (r2^Z!Eltseq (a)[1])*A;
         AddRow (~A, -Eltseq (a)[1], 1, 4);
         AddRow (~A, Eltseq (a)[1], 3, 2);
         for r in [2..e] do
            if IsEven (r) then
               S1 := ((or2^-1)^(DELTA1^Z! ((r-2)/2)))^Z!Eltseq (a)[r]*S1;
               // A := ((Or2^-1)^(delta1^Z! ((r-2)/2)))^Z!Eltseq (a)[r]*A; 
               AddRow (~A, -Eltseq (a)[r]*w^(r-1), 1, 4);
               AddRow (~A,  Eltseq (a)[r]*w^(r-1), 3, 2);
            else
               S1 := ((R2^-1)^(DELTA1^Z! ((r-1)/2)))^-Z!Eltseq (a)[r]*S1;
               // A := ((r2^-1)^(delta1^Z! ((r-1)/2))) ^-Z!Eltseq (a)[r]*A; 
               AddRow (~A, -Eltseq (a)[r]*w^(r-1), 1, 4);
               AddRow (~A,  Eltseq (a)[r]*w^(r-1), 3, 2);
            end if;
         end for;
 
         a := A[3, 1];
         S1 := (R1^Z!-Eltseq (a)[1])*S1;
         // A := (r1^Z!-Eltseq (a)[1])*A;
         AddRow (~A, -Eltseq (a)[1], 1, 3);
         AddRow (~A, Eltseq (a)[1], 4, 2);
	 for r in [2..e] do
            if IsEven (r) then
               S1 := ((or1^-1)^(DELTA2^Z!((r-2)/2)))^Z!Eltseq (a)[r] *S1;
               // A := ((Or1^-1)^(delta2^Z!((r-2)/2))) ^Z!Eltseq (a)[r] *A; 
               AddRow (~A, -Eltseq (a)[r]*w^(r-1), 1, 3);
               AddRow (~A,  Eltseq (a)[r]*w^(r-1), 4, 2);
            else
               S1 := ((R1^-1)^(DELTA2^Z!((r-1)/2)))^Z!Eltseq (a)[r] *S1;
               // A := ((r1^-1)^(delta2^Z!((r-1)/2)))^Z!Eltseq (a)[r]*A; 
               AddRow (~A, -Eltseq (a)[r]*w^(r-1), 1, 3);
               AddRow (~A,  Eltseq (a)[r]*w^(r-1), 4, 2);
            end if;
         end for;      
      
         S1 := SS.5*SS.4^-1*S1;
         // A := v*u^-1*A;
         for m in [2..(d div 2-2)] do
            SwapRows (~A, 2*m-1, 2*m+1);
            SwapRows (~A, 2*m, 2*m+2);
         end for;
         if IsEven (d div 2) then
            MultiplyRow (~A, -1, d-2);
            MultiplyRow (~A, -1, d-3);
         end if;
      end for;
   end procedure;

   AA := A;

   KK := [t, ot];
   for i in [1..e-1] do
      Append (~KK, t^(delta^-i));
      Append (~KK, ot^(delta^-i));
   end for;

   KSLP := [T, TO];
   for i in [1..e-1] do
      Append (~KSLP, T^(DELTA^-i));
      Append (~KSLP, TO^(DELTA^-i));
   end for;

   K := sub<SL (d, F)|KK>;

   RR := [r, ro];
   for i in [1..e-1] do
      Append (~RR, r^(delta^-i));
      Append (~RR, ro^(delta^-i));
   end for;

   RSLP := [R, RO];
   for i in [1..e-1] do
      Append (~RSLP, R^(DELTA^-i));
      Append (~RSLP, RO^(DELTA^-i));
   end for;

   KK2 := [Transpose (RR[i]): i in [1..#RR]];
   K2 := sub<SL (d, F)|KK2>;

   /* Once you have killed the 3rd to (d-2)-th positions on the top row
      of A, this function will kill of the d-1 and d slots on the top row. 
      As A preserves an orthogonal form, the 2nd slot is also killed.  */

   KillSupportK := function (A, S2)
      p := Characteristic (F);
      V := VectorSpace (GF (p), 2*e);
      b := [&cat[Eltseq (KK[i, 1, d-1]), Eltseq (KK[i, 1, d])]: i in [1..#KK]];
      V := sub<V|b>;
      v := V!(&cat[Eltseq (A[1, d-1]), Eltseq (A[1, d])]);
      CBV := GL(2*e, GF (p))!&cat (b);

      u := v^(CBV^-1);
   
      for i in [1..2*e] do
         A := A* (K.i^-Z!u[i]);
         S2 := S2* (KSLP[i]^-Z!u[i]);
      end for;

      return A, S2;
   end function;

   /* Once you have killed the 3rd to (d-2)-th positions in the first    
      column of A, this function will kill of the d-1 and d slots in
      the first column. As A preserves an orthogonal form, the 2nd slot
      is also killed.  */

   KillSupportK2 := function (A, S1)

      p := Characteristic (F);
      V := VectorSpace (GF (p), 2*e);
      b := [&cat[Eltseq (KK2[i, 1, d-1]), Eltseq (KK2[i, 1, d])]: i in [1..#KK2]];
      V := sub<V|b>;
      v := V!(&cat[Eltseq (A[1, d-1]), Eltseq (A[1, d])]);
      CBV := GL(2*e, GF (p))!&cat (b);

      u := v^(CBV^-1);
   
      for i in [1..2*e] do
         A := A* (K2.i^-Z!u[i]);
         S1 := (RSLP[i]^-Z!u[i])*S1;
      end for;

      return A, S1;
   end function;

   for i in [1.. (d div 2 - 2)] do
      GetAOne (~A, ~S1, ~S2);
      KillRow (~A, ~S1, ~S2);
      KillColumn (~A, ~S1, ~S2);

      A, S2 := KillSupportK (A, S2);
      A := Transpose (A);
      A, S1 := KillSupportK2 (A, S1);
      A := Transpose (A);

      A := v*A*v^-1;
      S2 := S2*SS.5^-1;
      S1 := SS.5*S1;
   end for;

   if d eq 2 then
      // Q := MinusChosenElements (G);
      Q := ClassicalStandardGenerators ("Omega-", d, #F);
      Q := [SL (d, F)!Q[i] : i in [1..#Q]];
      py := MinimalPolynomial (A);
      py := PolynomialRing (GF (q^2))!py;
      beta := Roots (py)[1, 1];

      pygen := MinimalPolynomial (Q[2]);
      pygen := PolynomialRing (GF (q^2))!pygen;
      alpha := Roots (pygen)[1, 1];

      kappa := Log (alpha, beta);

      if A eq Q[2]^kappa then
         word := SS.2^kappa;
         flag := IsIdentity (A*Q[2]^-kappa);
      else
         word := SS.2^-kappa;
         flag := IsIdentity (A*Q[2]^kappa);
      end if;
   else
      A := v*A*v^-1;
      S2 := S2*SS.5^-1;
      S1 := SS.5*S1;

      B := GL(4, GF (q^2))!Submatrix (A, d-3, d-3, 4, 4);
      gamma := PrimitiveElement (GF (q^2));
      alpha := gamma^Z!((q+1)/2);

      /* C or CC are now WRONG because the generators have changed. 
         Find the new C and CC.  */
      C := GL(4, GF (q^2))![1, 0, 0, 0, 0, alpha, 1, 0, 0, -alpha, 1, 0, 0, 0, 0, 1];
      C := Transpose (C);
      CC := GL(4, GF (q^2))![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0];

      _, y := IsProportional ((B^CC)^C, 2);
      x := y[2];
      y := y[1];
      det := Determinant (x);
      /* Let BB be the image of B in SL (2, q^2). x tensor y is BB tensor
         BB^q. As scalars can be carried across the 2 factors, x may be a
         multiple of BB. Hence, we divide x by Root (det, 2) to get BB.  */

      /* this is the image of B in PSL (2, q^2) */
      x := x / Root (det, 2);
      _, wword := SLWordInGen (sl, sl!x);
      phi := hom<Parent (wword) -> SS | S^(SS.5^-1), S^(SS.5^-1), SS.2, SS.3>;
      flag := IsIdentity (A * (Evaluate (phi (wword), Q))^-1);
      S2 *:= (phi (wword)^-1);
      word := S1^-1* S2^-1;
   end if;

   phi := hom<Parent (word) -> SS | 
              [SS.2 * SS.1 * SS.2] cat [SS.i : i in [2 .. 5]]>;
   return flag, phi (word);
end function;

/* 
intrinsic SOMinusWordInGen (G :: GrpMat, A :: GrpMatElt) -> BoolElt, GrpSLPElt
{write A as word in standard generators of SO^-}

   if Degree (G) gt 2 then
      _, _, J := OrthogonalForm (G);
   else
      error "Degree must be at least 4"; 
      // flag,  _, J := OrthogonalForm2 (G);
   end if;

   sn := SpinorNorm (A, J);

   if sn eq 0 then
      flag, word := OmegaMinusWordInGen (G, A);
      SS := Parent (word);
      S := SLPGroup (6);
      phi := hom<SS -> S | [S.i : i in [1..Ngens (SS)]]>;
      word := phi (word);
   else
      d := Dimension (G);
      F := BaseRing (G);
      QQ := ClassicalStandardGenerators ("Omega-", d, #F: SpecialGroup := true);
      sp := GL(d, F)!QQ[#QQ];
      A *:= sp;
      flag, word := OmegaMinusWordInGen (G, A);
      SS := Parent (word);
      S := SLPGroup (6);
      phi := hom<SS -> S | S.1, S.2, S.3, S.4, S.5>;
      word := phi (word);
      word *:= S.6^-1;
   end if;

   return flag, word;
end intrinsic;
*/
