// import "rewriting.m": SUChosenElements;
import "su-natural_odd.m": UnitaryOddCBM;

/* returns the generator x in SU (2d, q) embedded in SU (2d+1, q).
   the top 4 by 4 block of this matrix looks like this:
   [1  0  1  0]
   [0  1  0  0]
   [0  0  1  0]
   [0  1  0  1]
*/

GetXS := function (F, SLP)

   e := Degree (F);
   q := Characteristic (F)^(e div 2);
   Z := IntegerRing ();

   sss := (q^2 + q) div 2;
   xs := SLP.6^SLP.2;
   ss := SLP.1*(SLP.7^SLP.2)^sss;
   /* beta := (xs*SLP.5)^-1 *SLP.5*ss*SLP.5; */
   beta := xs^-1*ss*((xs*SLP.5)^-1)*(SLP.5*ss*SLP.5)*ss*SLP.5*xs^-1;
   xs := ((beta^SLP.5*ss*xs^-1)^(SLP.5*ss*SLP.5))^-1;
   xs := (SLP.6^SLP.2)^2*xs;
   xs := (((SLP.6^SLP.2)^ss)^SLP.2)^2*xs;

   return xs;
end function;

/* return the matrix with top row [1 0 -BB 0 0 0 0 0] */

GetBBTransvection := function (BB, SLP)

   F := Parent (BB);
   e := Degree (F);
   Z := IntegerRing ();

   xs := GetXS (F, SLP);
   OOX := xs^((SLP.7^SLP.2)^-1);

   // T := x^-1;
   TT := xs^-1;
   // T := T^Z!Eltseq (BB)[1];
   TT := TT^Z!Eltseq (BB)[1];

   for r in [2..e] do
      // o := OX^-1;
      oo := OOX^-1;
      // o := o^((y^v)^-Z!r);
      oo := oo^((SLP.7^SLP.2)^-Z! (r-2));
      // o := o^Z!Eltseq (BB)[r];
      oo := oo^Z!Eltseq (BB)[r];
      // T := T*o;
      TT := TT*oo;
   end for;

   return TT;
end function;

GetAOne := procedure (~A, ~S1, ~S2)

   SLP := Parent (S1);
   F := BaseRing (A);
   w := PrimitiveElement (F);
   d := Nrows (A);
   Z := IntegerRing ();
   e := Degree (F);
   q := Characteristic (F)^(e div 2);
   a := Root (w^(q+1), 2);
   xs := GetXS (F, SLP);

   i := 3;
   while A[i, 1] eq 0 do
      i +:= 1; if i eq d+1 then break; end if;
   end while;
   if i eq d then i := d+1; end if;

   /* if A[1, 1] or A[1, 2] is the only non-zero
      entry on the first column */
   if i eq d+1 then
      // A := A*s*xs*s^-1; sticks values in the first column 
      SwapColumns (~A, 1, 2); // s
      MultiplyColumn (~A, a, 2); // s
      MultiplyColumn (~A, a^-q, 1); // s
      AddColumn (~A, 1, 1, 3); // x
      AddColumn (~A, -1, 4, 2); // x
      SwapColumns (~A, 1, 2); // s
      MultiplyColumn (~A, -a, 2); // s
      MultiplyColumn (~A, -a^-q, 1); // s
      S2 *:= SLP.1*xs*SLP.1^-1;
      i := 3;
      while A[i, 1] eq 0 do i +:= 1; end while;
   end if;
  
   bool := false;
   bool2 := false;
   i := 3;
   j := 0;
   if A[3, 1] eq 0 then
      if A[4, 1] ne 0 then
         // A := (s^u)*A;
         SwapRows (~A, 3, 4);
         MultiplyRow (~A, a, 3);
         MultiplyRow (~A, a^-q, 4);
         S1 := (SLP.1^SLP.5)*S1;
         bool := true;
      else
         i := 5;
         while A[i, 1] eq 0 do
            i +:= 1;
            if i eq d+1 then break; end if;      
         end while;
      end if;
      if i eq d+1 then
         /* if we are here, the only non-zero entries in the
            first column are in the first two rows */
         i := 4;
         // A := xs*A;
         AddRow (~A, 1, 3, 1);
         AddRow (~A, -1, 2, 4);
         S1 := xs*S1;
         bool2 := true;
      elif A[3, 1] ne 0 then
         S1 := S1; // i.e. do nothing
      else
         if IsEven (i) then 
            j := i div 2;
         else 
            j := Z!(i/2 + 1/2); 
         end if;
         /* A := ((v*u^-1)^(j-2))*A; */
         B := ZeroMatrix (F, d, d);
         B[1] := A[1];
         B[2] := A[2];
         B[d] := A[d];
         for y in [3..d-(2* (j-2))-1] do
            B[y] := A[y + 2*(j-2)];
         end for;
         for y in [d-(2*(j-2))..d-1] do
            B[y] := A[y - (d-(2*(j-2))+1) + 4];
         end for;
         A := B;
         S1 := ((SLP.2*SLP.5^-1)^(j-2))*S1;
      end if;
      if (A[3, 1] eq 0) and (A[4, 1] ne 0) then
         // A := (s^u)*A;
         SwapRows (~A, 3, 4);
         MultiplyRow (~A, a, 3);
         MultiplyRow (~A, a^-q, 4);
         S1 := (SLP.1^SLP.5)*S1;
         bool := true;
      end if;
   end if;
  
   BB := (1-A[1, 1])/A[3, 1];
   TT := GetBBTransvection (BB, SLP);
   // A := T^-1*A;
   AddRow (~A, BB, 3, 1);
   AddRow (~A, -BB^q, 2, 4);
   S1 := TT^-1*S1;

   if j ne 0 then
      // A := ((v*u^-1)^-(j-2))*A;
      S1 := ((SLP.2*SLP.5^-1)^-(j-2))*S1;
      B := ZeroMatrix (F, d, d);
      B[1] := A[1];
      B[2] := A[2];
      B[d] := A[d];
      for y in [3..(2*j-2)] do
         B[y] := A[y + d-2*j + 5 - 4];
      end for;
      for y in [3..d-2*(j-2)-1] do
         B[y + 2* (j-2)] := A[y];
      end for;
      A := B;
   end if;

   if bool then
      // A := ((s^-1)^u)*A;
      SwapRows (~A, 3, 4);
      MultiplyRow (~A, -a, 3);
      MultiplyRow (~A, -a^-q, 4);
      S1 := ((SLP.1^-1)^SLP.5)*S1;
   end if;

   if bool2 then
      // A := x^-1*A;
      AddRow (~A, -1, 3, 1);
      AddRow (~A, 1, 2, 4);
      S1 := xs^-1*S1;
   end if;

end procedure;

/* This function returns an SLP for the transpose of x^v */

GetXVTranspose := function (F, SLP, d)

   e := Degree (F);
   q := Characteristic (F)^(e div 2);
   Z := IntegerRing ();

   /* xv := ((x^(v*s))^((y^v)^q)); */
   xv := (SLP.6^(SLP.2*SLP.1))^((SLP.7^SLP.2)^q);

   if d ne 3 then
      alpha := (q + 4) div 2;
   else
      if e ne 2 then
         beta := (-q^3 - q^2 + 4*q - 2) div 2;
         while (beta / (q - 2)) ne (beta div (q-2)) do
            beta +:= q^2 - 1;
         end while;
         alpha := beta div (q - 2);
      else
         alpha := 0;
      end if;
   end if;
   // xv := xv^(y^alpha); 
   xv := xv^(SLP.7^alpha);

   return xv;
end function;

UnitaryOddChar2WordInGen := function (G, A)

   d := Dimension (G);
   F := BaseRing (G);
   w := PrimitiveElement (F);
   G := SL (d, F);
   e := Degree (F);

   Z := IntegerRing ();
   p := Characteristic (F);
   q := p^(e div 2);
   a := Root (w^(q+1), 2);
   P := PolynomialRing (F);
   py := P.1^q + P.1 + 1;
   phi := (Trace (w, GF(q)))^-1 * w;

   CB := UnitaryOddCBM (G);
   // Q := SUChosenElements (SU (d, F)); 
   // next 5 lines added by csaba 
   Q := ClassicalStandardGenerators( "SU", d, q );
   if e gt 2 then
       Q[1] := Q[1]^(Q[4]^(-p^(e div 2 - 2)));
       Q[3] := Q[3]^(Q[4]^(-p^(e div 2 - 2)));
   end if;

   SLP := SLPGroup (7);
   S1 := Id (SLP);
   S2 := Id (SLP);

   A := G!A;
   A := G!(A^CB);
   AA := A;

   xs := GetXS (F, SLP);

   FF := sub<F | w^2>;
   py := FF!F.1;

   /* py is now a polynomial in w^2 that is equal to w*/
   /* OOX is the element that looks like x^v
      but with an omega in the [1, 3] slot */

   OOX := xs^((SLP.7^SLP.2)^-1);

   block := (d-1) div 2; /* the number of blocks */

   /* kills the A[1, 3] entry */
   KillPlace := procedure (~A, ~S1, ~S2)
      pytemp := A[1, 3];
      aa := Eltseq (pytemp);
      for r in [1..e] do
         S2 *:= (xs^((SLP.7^SLP.2)^-(r-1)))^-Z!aa[r];
         /* A := A* ((xxs^((y^v)^-(r-1)))^-Z!aa[r]); */
         AddColumn (~A, -aa[r]*w^(r-1), 1, 3);
         AddColumn (~A,  aa[r]*(w^q)^(r-1), 4, 2);
      end for;
   end procedure;

   /* kills A[1, 1] using A[3, 1] = 1 */
   KillRow := procedure (~A, ~S1, ~S2)
      pytemp := A[1, 1];
      aa := Eltseq (pytemp);
      for r in [1..e] do
         S1 := ((xs^((SLP.7^SLP.2)^-(r-1)))^-Z!Eltseq (pytemp)[r])*S1;
         /* A := ((xxs^((y^v)^-(r-1)))^-Z!Eltseq (pytemp)[r])*A; */
         AddRow (~A, -aa[r]*w^(r-1), 3, 1);
         AddRow (~A,  aa[r]*(w^q)^(r-1), 2, 4);
      end for;
   end procedure;

   UsingT := procedure (~A, ~S1, ~S2)
      F3 := sub<F | a>;
      py2 := F3!A[1, 2];
      order := (Order (a) - 1) div 2;

      for z in [1..#Eltseq (py2)] do
         if Eltseq (py2)[z] eq 1 then
            if IsOdd (z) then
               pw := ((z-1) div 2) + order;
               /* A := A * ((t^((y^v)^-pw))); */
               S2 *:= SLP.3^((SLP.7^SLP.2)^-pw);
               AddColumn (~A, Eltseq (py2)[z]*a^(z-1), 1, 2);
            else
               pw := (z div 2) - 1;
               /* A := A* ((t^((y^v)^-pw))); */
               S2 *:= SLP.3^((SLP.7^SLP.2)^-pw);
               AddColumn (~A, Eltseq (py2)[z]*a^(z-1), 1, 2);
            end if;
         end if;
      end for;
   end procedure;

   xv := GetXVTranspose (F, SLP, d);

   for k in [1..block-1] do
      GetAOne (~A, ~S1, ~S2);

      for l in [1..block-1] do
         KillPlace (~A, ~S1, ~S2);

         /* A := A*u*s*u;
            swaps the third and fourth columns so
            that we can work on the f part of the block.  */
         MultiplyColumn (~A, a, 3);
         MultiplyColumn (~A, a^-q, 4);
         SwapColumns (~A, 3, 4);
         S2 *:= SLP.5*SLP.1*SLP.5;

         KillPlace (~A, ~S1, ~S2);

         /* A := A* ((u*s*u)^-1);
            swaps the third and fourth columns back again */
         SwapColumns (~A, 3, 4);
         MultiplyColumn (~A, a^-1, 3);
         MultiplyColumn (~A, a^q, 4);
         S2 *:= (SLP.5*SLP.1*SLP.5)^-1;

         /* A := A* (v*u);
            vu is the (2.. (d-1)/2) cycle on the blocks */
         for i in [2.. ((d-1) div 2 - 1)] do
            SwapColumns (~A, 2*i - 1, d-2);
            SwapColumns (~A, 2*i, d-1);
         end for;
         S2 *:= SLP.2*SLP.5;
      end for;

      /* we now wish to times A by powers of (x^v)^(y^z) for
         different z to kill the [1, d] place */

      F3 := sub<F | w^(q-1)>;
      py2 := F3!A[1, d];

      for z in [1..#Eltseq (py2)] do
         aa := Eltseq (py2)[z];
         /* A := A*(((x^v)^(y^(z-1)))^Z!Eltseq (py2)[z]); */
         /* aa is either 0 or 1 */
         AddColumn (~A, aa * phi, 1, 2);
         AddColumn (~A, aa * (w^-(q-1))^(z-1), d, 2);
         AddColumn (~A, aa * (w^(q-1))^(z-1), 1, d);
         S2 *:= ((SLP.6^SLP.2)^(SLP.7^(z-1)))^Z!Eltseq (py2)[z];
      end for;

      /* we now wish to times A by powers of t^(y^-z) for
         different z to kill the [1, 2] place */

      UsingT (~A, ~S1, ~S2);

      /* now we do the second column */
      for l in [1..block-1] do

         /* A := u*A; swaps row 1 and 3 and 2 and 4 */
         SwapRows (~A, 1, 3);
         SwapRows (~A, 2, 4);
         S1 := SLP.5*S1;
         KillRow (~A, ~S1, ~S2);
         /* A := s*A; swaps row 2 and 1 */
         SwapRows (~A, 1, 2);
         MultiplyRow (~A, a, 1);
         MultiplyRow (~A, a^-q, 2);
         S1 := SLP.1*S1;
         KillRow (~A, ~S1, ~S2);
         /* A := s^-1*A; swaps 1 and 2 back again */
         MultiplyRow (~A, a^-1, 1);
         MultiplyRow (~A, a^q, 2);
         SwapRows (~A, 1, 2);
         S1 := SLP.1^-1 * S1;
         /* A := u*A; returns the rows to their original position */
         SwapRows (~A, 1, 3);
         SwapRows (~A, 2, 4);
         S1 := SLP.5*S1;
         /* A := v*u*A;
            rotates the 2 to d/2 blocks as rows */
         for m in [2.. ((d-1) div 2 -1)] do
            SwapRows (~A, 2*m-1, 2*m+1);
            SwapRows (~A, 2*m, 2*m+2);
         end for;
         S1 := SLP.2*SLP.5*S1;
      end for;

      /* we now multiply A by powers of (x^v)^(y^z) for
         different z to kill the [d, 1] place */

      F3 := sub<F | w^(q-1)>;
      py2 := F3!A[d, 1];

      for z in [1..#Eltseq (py2)] do
         aa := Eltseq (py2)[z];
         /* A := ((xv^(y^-(z-1)))^Z!Eltseq (py2)[z]) * A; */
         /* aa is either 0 or 1 */
         AddRow (~A, -aa * phi, 1, 2);
         AddRow (~A,  aa * (w^-(q-1))^(z-1), d, 2);
         AddRow (~A, -aa * (w^(q-1))^(z-1), 1, d);
         S1 := ((xv^(SLP.7^-(z-1))) ^Z!Eltseq (py2)[z]) * S1;
      end for;

      /* A := s^-1 * A * s; */
      SwapColumns (~A, 1, 2);
      MultiplyColumn (~A, a^-q, 1);
      MultiplyColumn (~A, a, 2);
      SwapRows (~A, 1, 2);
      MultiplyRow (~A, a^q, 1);
      MultiplyRow (~A, a^-1, 2);
      S1 := SLP.1^-1 * S1;
      S2 *:= SLP.1;

      UsingT (~A, ~S1, ~S2);

      /* A := s*A*s^-1; */
      SwapColumns (~A, 1, 2);
      MultiplyColumn (~A, a^-1, 1);
      MultiplyColumn (~A, a^q, 2);
      SwapRows (~A, 1, 2);
      MultiplyRow (~A, a, 1);
      MultiplyRow (~A, a^-q, 2);
      S1 := SLP.1 *S1;
      S2 *:= SLP.1^-1;

      /* A := A^(v^-1); */
      B := Transpose (A);
      C := ZeroMatrix (F, d, d);
      for i in [1..d-3] do
         C[i] := B[i + 2];
      end for;
      C[d-2] := B[1];
      C[d-1] := B[2];
      C[d] := B[d];
      A := Transpose (C);

      C := ZeroMatrix (F, d, d);
      B := A;
      for i in [1..d-3] do
         C[i] := B[i + 2];
      end for;
      C[d-2] := B[1];
      C[d-1] := B[2];
      C[d] := B[d];
      A := C;

      S2 *:= SLP.2^-1;
      S1 := SLP.2*S1;
   end for;

   if A[1, 1] eq 0 then
      /* A := A*s; */
      SwapColumns (~A, 1, 2);
      MultiplyColumn (~A, a, 2);
      MultiplyColumn (~A, a^-q, 1);
      S2 *:= SLP.1;
   end if;

   /* returns ts, which evaluates to t transpose */
   GetTS := function ()
      /* ts := (t^((y^v)^-1))^s; */
      ts := (SLP.3^((SLP.7^SLP.2)^-1))^SLP.1;
      return ts;
   end function;

   /* returns the SLP that evaluates to the transvection
      [1, gamma, 0, 1] */
   GetGammaTransvection := function (gamma)
      FF := sub<F | a^4>;
      beta := FF! (gamma * a^-1);
      vv := Eltseq (beta);
      T := Id (SLP);
      for i in [1..#vv] do
         T *:= (SLP.3^(SLP.4^-(i-1)))^Z!vv[i];
      end for;
      return T;
   end function;

   /* returns the SLP that evaluates to the transvection
      [1, 0, gamma, 1] */
   GetGammaTransvectionTranspose := function (gamma)
      FF := sub<F | a^4>;
      beta := FF!(gamma * a^-1);
      vv := Eltseq (beta);
      T := Id (SLP);
      ts := GetTS ();
      for i in [1..#vv] do
         T *:= (ts^(SLP.4^(i-1)))^Z!vv[i];
      end for;
      return T;
   end function;

   UsingTFor3 := function (C, S)
      s := Q[1]^(Q[2]^-1);
      F3 := sub<F | a>;
      py2 := F3!(C[d-2, d-1]/C[d-2, d-2]);
      order := (Order (a) - 1) div 2;
      T := SLP.3^(SLP.2^-1);

      for z in [1..#Eltseq (py2)] do
         if Eltseq (py2)[z] eq 1 then
            if IsOdd (z) then
               pw := ((z-1) div 2) + order;
               /* C := C* ((t^(y^- pw))); */
               S *:= T^(SLP.7^-pw);
               AddColumn (~C, Eltseq (py2)[z]*a^(z-1), d-2, d-1);
            else
               pw := (z div 2) - 1;
               /* A := A* ((t^(y^-pw))); */
               S *:= T^(SLP.7^-pw);
               AddColumn (~C, Eltseq (py2)[z]*a^(z-1), d-2, d-1);
            end if;
         end if;
      end for;

      /* C := s^-1*C*s; */
      SwapColumns (~C, d-2, d-1);
      MultiplyColumn (~C, a^-q, d-2);
      MultiplyColumn (~C, a, d-1);
      SwapRows (~C, d-2, d-1);
      MultiplyRow (~C, a^q, d-2);
      MultiplyRow (~C, a^-1, d-1);
      S := (SLP.1^(SLP.2^-1))^-1 * S * (SLP.1^(SLP.2^-1));

      F3 := sub<F | a>;
      py2 := F3!(C[d-2, d-1]/C[d-2, d-2]);

      for z in [1..#Eltseq (py2)] do
         if Eltseq (py2)[z] eq 1 then
            if IsOdd (z) then
               pw := ((z-1) div 2) + order;
               /* C := C* ((t^(y^- pw))); */
               S *:= T^(SLP.7^-pw);
               AddColumn (~C, Eltseq (py2)[z]*a^(z-1), d-2, d-1);
            else
               pw := (z div 2) - 1;
               /* A := A* ((t^(y^-pw))); */
               S *:= T^(SLP.7^-pw);
               AddColumn (~C, Eltseq (py2)[z]*a^(z-1), d-2, d-1);
            end if;
         end if;
      end for;

      /* C := s*C*s^-1; */
      SwapColumns (~C, d-2, d-1);
      MultiplyColumn (~C, a^-1, d-2);
      MultiplyColumn (~C, a^q, d-1);
      SwapRows (~C, d-2, d-1);
      MultiplyRow (~C, a, d-2);
      MultiplyRow (~C, a^-q, d-1);
      S := (SLP.1^(SLP.2^-1)) * S * (SLP.1^(SLP.2^-1))^-1;

      return C, S;
   end function;

   /* This function creates a diagonal element that can be used to 
      make the [1, 1] entry of A = 1 */

   Dim3GetAOne := procedure (~A, ~S1, ~S2)

      /* A := A^(v^-1); */
      B := Transpose (A);
      C := ZeroMatrix (F, d, d);
      for i in [1..d-3] do
         C[i] := B[i + 2];
      end for;
      C[d-2] := B[1];
      C[d-1] := B[2];
      C[d] := B[d];
      A := Transpose (C);

      C := ZeroMatrix (F, d, d);
      B := A;
      for i in [1..d-3] do
         C[i] := B[i + 2];
      end for;
      C[d-2] := B[1];
      C[d-1] := B[2];
      C[d] := B[d];
      A := C;

      S2 *:= SLP.2^-1;
      S1 := SLP.2*S1;

      P := PolynomialRing (F);
      xx := A[d-2, d-2]^-1;
      py := phi^2* (xx + P.1)^(q+1) + 1 + P.1;
      y := Q[7];
      if #Roots (py) ne 0 then
         yy := Roots (py)[1, 1];
      else
         ycount := 0;
         while #Roots (py) eq 0 do
            /* A := A*y; */
            MultiplyColumn (~A, w, d-2);
            MultiplyColumn (~A, w^-q, d-1);
            MultiplyColumn (~A, w^(q-1), d);
            S2 *:= SLP.7;
            ycount +:= 1;
            xx := A[d-2, d-2]^-1;
            py := phi^2 * (xx + P.1)^(q+1) + 1 + P.1;
         end while;
         yy := Roots (py)[1, 1];
      end if;

      aa := xx + yy;

      blob2 := Q[6]^(CB^-1);

      oldblob3 := SL (3, F)![1, 0, 0, aa, 1, 0, phi * aa^(q+1), -aa^q, 1];
      oldblob3 := InsertBlock (Id (G), oldblob3, (d-3) div 2 + 1, (d-3) div 2 + 1);
      xxv := Evaluate (xv, Q)^(Q[2]^-1);
      FF := sub<F | w^(q-2)>;
      beta := aa;
      v := Eltseq (FF!beta);
      blob3 := Id (G);
      BLOB3 := Id (SLP);
      for i in [1..#v] do
         blob3 *:= (xxv^(y^-(i-1)))^Z!v[i];
         BLOB3 *:= ((xv^(SLP.2^-1))^(SLP.7^-(i-1)))^Z!v[i];
      end for;

      beta := blob3[d-1, d-2] - phi * aa^(q+1);
      t := (Q[3]^Q[1])^(Q[2]^-1);
      T := (SLP.3^SLP.1)^(SLP.2^-1);
      f := t[d-1, d-2];
      F3 := sub<F | f>;
      py2 := F3!beta;
      order := (Order (f) - 1) div 2;

      for z in [1..#Eltseq(py2)] do
         if Eltseq (py2)[z] eq 1 then
            if IsOdd (z) then
               pw := ((z-1) div 2) + order;
               /* blob3 := blob3 * ((t^(y^-pw))); */
               BLOB3 *:= T^(SLP.7^-pw);
               AddRow (~blob3, Eltseq (py2)[z]*f^(z-1), d-2, d-1);
            else
               pw := (z div 2) - 1;
               /* blob3 := blob3 * ((t^(y^-pw))); */
               BLOB3 *:= T^(SLP.7^-pw);
               AddRow (~blob3, Eltseq (py2)[z]*f^(z-1), d-2, d-1); 
            end if;
         end if;
      end for;

      blob3 := CB*blob3*CB^-1;

      /* blob4 is a matrix that will make the [1, 2] entry of the 3*3 
         middle section of blob2*blob3 = 0 */

      x := Q[6];
      FF := sub<F | w^(q-2)>;
      beta := -((blob2*blob3)[(d-3) div 2 + 1, (d-3) div 2 + 2])/
               ((blob2*blob3)[(d-3) div 2 + 1, (d-3) div 2 + 1]);
      v := Eltseq (FF!beta);
      blob4 := Id (G);
      BLOB4 := Id (SLP);
      for i in [1..#v] do
         blob4 *:= (x^(y^(i-1)))^Z!v[i];
         BLOB4 *:= (SLP.6^(SLP.7^(i-1)))^Z!v[i];
      end for;

      /* blob1 is a matrix that will make the [2, 1] entry of the 3*3 
         middle section of blob2*blob3 = 0 */

      xxv := Evaluate (xv, Q)^(Q[2]^-1);
      FF := sub<F | w^(q-2)>;
      beta := -((blob2*blob3)[(d-3) div 2 + 2, (d-3) div 2 + 1])/
               ((blob2*blob3)[(d-3) div 2 + 1, (d-3) div 2 + 1]);
      v := Eltseq (FF!beta);
      blob1 := Id (G);
      BLOB1 := Id (SLP);
      for i in [1..#v] do
         blob1 *:= (xxv^(y^-(i-1)))^Z!v[i];
         BLOB1 *:= ((xv^(SLP.2^-1))^(SLP.7^-(i-1)))^Z!v[i];
      end for;

      blob := CB^-1*(blob1^(CB^-1)*blob2*blob3*blob4^(CB^-1))*CB;
      BLOB := BLOB1*SLP.6*BLOB3*BLOB4;

      blob, BLOB := UsingTFor3 (blob, BLOB);

      A  *:= blob;
      S2 *:= BLOB;

      A := Q[2]^-1*A*Q[2];
      S1 := SLP.2^-1*S1;
      S2 *:= SLP.2;

   end procedure;

   Dim3GetAOne (~A, ~S1, ~S2);

   /* If d = 3, we need to consider sub<F | w^(q-2)> instead because the 
      conjugates of xy by powers of y by xv now affect the top row. */

   if d eq 3 then
      F3 := sub<F | w^(q-2)>;
      xxv := Evaluate (xv, Q);
      if e ne 2 then
         py2 := F3!A[d, 1];
      else
         py2 := A[d, 1];
         deltaT := (Q[4]^Q[1])*xxv;
         DELTAT := (SLP.4^SLP.1)*xv;
      end if;
      y := Q[7];

      if e ne 2 then
         for z in [1..#Eltseq (py2)] do
            aa := Eltseq (py2)[z];
            A := ((xxv^(y^-(z-1)))^Z!Eltseq (py2)[z]) * A;
            /* For the first line, in place of Eltseq
               we need the general rule, which is
               a_n = a_n-1 - n-1 - 1/2* (w^-(q+1))^(z-1); a_1 = -1/2.
               This means that a_n = n* (-1/2) - (1..n-1) */
            /* AddRow (~A, -aa * ((-w^-(q+1))^(z-1))/F!2 - aa * (aa-1)/2, 1, 2);
               AddRow (~A,  aa * (w^-(2*q-1))^(z-1), d, 2);
               AddRow (~A, -aa * (w^(q-2))^(z-1), 1, d); */
            S1 := ((xv^(SLP.7^-(z-1)))^Z!Eltseq (py2)[z]) * S1;
         end for;
      else
         a1 := Z!Eltseq (py2)[1];
         a2 := Z!Eltseq (py2)[2];
         A := xxv^a1 * deltaT^a2 * A;
         /* AddRow (~A, -aa * ((-w^-(q+1))^(z-1))/F!2 - aa* (aa-1)/2, 1, 2);
            AddRow (~A,  aa * (w^-(2*q-1))^(z-1), d, 2);
            AddRow (~A, -aa * (w^(q-2))^(z-1), 1, d); */
         S1 := xv^a1 * DELTAT^a2 * S1;
      end if;
   else
      F3 := sub<F | w^(q-1)>;
      py2 := F3!A[d, 1];

      for z in [1..#Eltseq (py2)] do
         aa := Eltseq (py2)[z];
         // A := ((xv^(y^-(z-1)))^Z!Eltseq (py2)[z]) * A; 
         /* For the first line, in place of Eltseq
            we need the general rule, which is
            a_n = a_n-1 - n-1 - 1/2; a_1 = -1/2.
            This means that a_n = n* (-1/2) - (1..n-1) */
         AddRow (~A, -aa * phi, 1, 2);
         AddRow (~A,  aa * (w^-(q-1))^(z-1), d, 2);
         AddRow (~A, -aa * (w^(q-1))^(z-1), 1, d);
         S1 := ((xv^(SLP.7^-(z-1)))^Z!Eltseq (py2)[z]) * S1;
      end for;
   end if;

   if e ne 2 then
      py2 := F3!A[1, d];
   else
      py2 := A[1, d];
   end if;

   if d eq 3 then
      if e ne 2 then
         for z in [1..#Eltseq (py2)] do
            aa := Eltseq (py2)[z];
            x := Q[6];
            v := Q[2];
            A := A*(((x^v)^(y^(z-1)))^-Z!Eltseq (py2)[z]);
            /* AddColumn (~A, aa * ((w^-(q+1))^(z-1))/F!2 - aa*(aa-1)/2, 1, 2);
               AddColumn (~A,  aa * (w^-(2*q-1))^(z-1), d, 2);
               AddColumn (~A, -aa * (w^(q-2))^(z-1), 1, d); */
            S2 *:= ((SLP.6^SLP.2)^(SLP.7^(z-1)))^-Z!Eltseq (py2)[z];
         end for;
      else
         a1 := Z!Eltseq (py2)[1];
         a2 := Z!Eltseq (py2)[2];
         A := A * Q[6]^a1 * Q[4]^a2;
         /* AddRow (~A, -aa* ((-w^-(q+1))^(z-1))/F!2 - aa* (aa-1)/2, 1, 2);
            AddRow (~A, aa * (w^-(2*q-1))^(z-1), d, 2);
            AddRow (~A, -aa * (w^(q-2))^(z-1), 1, d); */
         S2 *:= SLP.6^a1 * SLP.4^a2;
      end if;
   else
      for z in [1..#Eltseq (py2)] do
         aa := Eltseq (py2)[z];
         /* A := A* (( (x^v)^(y^(z-1))) ^Z!Eltseq (py2)[z]); */
         /* aa is either 0 or 1 */
         AddColumn (~A, aa * phi, 1, 2);
         AddColumn (~A, aa * (w^-(q-1))^(z-1), d, 2);
         AddColumn (~A, aa * (w^(q-1))^(z-1), 1, d);
         S2 *:= ((SLP.6^SLP.2)^(SLP.7^(z-1)))^Z!Eltseq (py2)[z];
      end for;
   end if;

   UsingT (~A, ~S1, ~S2);

   /* A := s^-1 * A * s; */
   SwapColumns (~A, 1, 2);
   MultiplyColumn (~A, a^-q, 1);
   MultiplyColumn (~A, a, 2);
   SwapRows (~A, 1, 2);
   MultiplyRow (~A, a^q, 1);
   MultiplyRow (~A, a^-1, 2);

   S1 := SLP.1^-1 * S1;
   S2 *:= SLP.1;

   UsingT (~A, ~S1, ~S2);

   /* A := s*A*s^-1; */
   SwapColumns (~A, 1, 2);
   MultiplyColumn (~A, a^-1, 1);
   MultiplyColumn (~A, a^q, 2);
   SwapRows (~A, 1, 2);
   MultiplyRow (~A, a, 1);
   MultiplyRow (~A, a^-q, 2);

   S1 := SLP.1 *S1;
   S2 *:= SLP.1^-1;

   word := (S1^-1)* (S2^-1);

   if d eq 3 and q eq 2 then 
      return IsIdentity (A), (S1^-1)* (S2^-1);
   end if;

   /* May 2010 change in generating set for odd dim, even char */
   W := SLPGroup (7);
   if e gt 2 then 
      pow := 2^((e div 2) - 2);
   else 
      pow := 0;
   end if;
   a := 2^(e - 1) - 1;

   tau := hom<SLP -> W | [W.4^-a * W.1, W.2, W.3^(W.4^(-pow)), W.4, W.5, W.6, W.7]>;
   return IsIdentity (A), tau (word);
end function;
