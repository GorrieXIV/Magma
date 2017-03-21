import "su-natural_odd.m": UnitaryOddWordInGen;

function UnitaryCBM (G)
   F := BaseRing (G);
   d := Dimension (G);
   M := KMatrixSpace (F, d, d); 
   b := Basis (M);
   G := SL (d, F);

   CB := ZeroMatrix (F, d, d);
   for i in [1..(d div 2)] do
      CB := CB + b[(i-1)*d + 2*i - 1];
   end for;
   for i in [1..(d div 2)] do
      CB := CB + b[(d div 2)*d + i*d - 2*i + 2];
   end for;
   return G!CB;
end function; 

// write A as SLP in standard generators for SU
UnitaryWordInGen := function (G, A) 

   if IsOdd (Degree (G)) then
      return UnitaryOddWordInGen (G, A);
   end if;

   W := SLPGroup (7);
   d := Dimension (G);
   F := BaseRing (G);
   
   w := PrimitiveElement (F);
   if w ne F.1 then
      F := sub<F | w>;
      w := F!w;
   end if;
   G := SL (d, F);
   e := Degree (F);

   Z := IntegerRing ();
   p := Characteristic (F);
   q := p^(e div 2);

   CB := UnitaryCBM (G);

   A := G!A;
   A := G!(A^CB);
   AA := A;

   SLP := SLPGroup (7);
   S1 := Id (SLP);
   S2 := Id (SLP);
   a := w^((q+1) div 2);
   if IsEven (q) then
      a := Root (w^(q+1), 2);
   end if;

   phi := hom<SLP -> W | W.4, W.1, W.3, W.5, W.2, W.6^(W.2^2), W.7^(W.2^2)>;

   dys := SLP.1 * SLP.7^-1;

   FF := sub<F | w^2>;
   py := FF!F.1;

   /* py is now a polynomial in w^2 that is equal to w
      the next piece of code creates the element that looks like x but
      with an omega in the [1, 3] slot */

   py := Eltseq (py);
   py := [Z!x : x in py];
   
   X := &*[(SLP.6^(SLP.7^-(i-1)))^py[i]: i in [1..e]];

   block := d div 2; // the number of blocks 

   GetBBTransvection := function (BB)
      BB := Eltseq (BB);
      BB := [Z!b : b in BB];
      T := SLP.6^-1;
      T := T^BB[1];

      for r in [2..e] do
         if IsEven (r) then
            o := X^-1;
            o := o^(SLP.7^-((r-2) div 2));
         else
            o := SLP.6^-1;
            o := o^(SLP.7^-((r-1) div 2));
         end if;
         o := o^BB[r];
         T *:= o;
      end for;
      return T;
   end function;

   GetAOne := procedure (~A, ~S1, ~S2)
      if A[1, 1] eq 0 then 
         i := Depth (A[1]);
         /* find which block we need */
         if IsEven (i) then j := i div 2;
         else j := Z!(i/2 + 1/2); end if;
         if i eq 2 then
            // A := A*s;
	    SwapColumns (~A, 1, 2);
	    MultiplyColumn (~A, a, 2);
	    MultiplyColumn (~A, a^-q, 1);
	    S2 *:= SLP.2;
         else
            /* A := A* (u*v^-1)^(j-2)* (u*v)^(j-2)*u; 
               swap blocks 1 and j */
            SwapColumns (~A, 1, 2*j - 1);
            SwapColumns (~A, 2, 2*j);
            S2 *:= (SLP.4 * SLP.5^-1)^(j-2)* (SLP.4 * SLP.5)^(j-2) * SLP.4; 
         end if;
         if A[1, 1] eq 0 then
            // A := A*s;
            SwapColumns (~A, 1, 2);
            MultiplyColumn (~A, a, 2);
            MultiplyColumn (~A, a^-q, 1);
            S2 *:= SLP.2;
         end if;
      end if; 

      i := 2;
      while A[i, 1] eq 0 do
         i := i+1;
         if i eq d+1 then break; end if;
      end while;
   
      /* if A[1, 1] is the only non-zero entry on the first column */
      if i eq d+1 then
         /* A := A*s*x*s^-1; sticks values in the first column */
         SwapColumns (~A, 1, 2);
         MultiplyColumn (~A, a, 2);
         MultiplyColumn (~A, a^-q, 1);
         AddColumn (~A, 1, 1, 3);
         AddColumn (~A, -1, 4, 2);
         SwapColumns (~A, 1, 2);
         MultiplyColumn (~A, -a, 2);
         MultiplyColumn (~A, -a^-q, 1);
         S2 *:= SLP.2 * SLP.6 * SLP.2^-1;
         i := 3;
         while A[i, 1] eq 0 do i := i+1; end while;
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
	    S1 := (SLP.2^SLP.4) * S1;
	    bool := true;
         else
            while A[i, 1] eq 0 do
               i := i+1; if i eq d+1 then break; end if;      
	    end while;
         end if;
         if i eq d+1 then
            /* if we are here, the only non-zero entries in the first
               column are in the first two rows */
	    i := 4;
            // A := x*A;
	    AddRow (~A, 1, 3, 1);
	    AddRow (~A, -1, 2, 4);
	    S1 := SLP.6 * S1;
	    bool2 := true;
         elif A[3, 1] ne 0 then
            S1 := S1; // do nothing
         else
            if IsEven (i) then j := i div 2; else j := Z!(i/2 + 1/2); end if;
            // A := ((v*u^-1)^(j-2))*A; 
            B := ZeroMatrix (F, d, d);
            B[1] := A[1];
            B[2] := A[2];
            for y in [3..d-(2*(j-2))] do
               B[y] := A[y + 2 * (j-2)];
            end for;
            for y in [d-(2*(j-2))+1..d] do
               B[y] := A[y - (d-(2*(j-2))+1) + 3];
	    end for;
	    A := B;
	    S1 := ((SLP.5 * SLP.4^-1)^(j-2)) * S1;
         end if;
         if (A[3, 1] eq 0) and (A[4, 1] ne 0) then
            // A := (s^u)*A;
            SwapRows (~A, 3, 4);
            MultiplyRow (~A, a, 3);
            MultiplyRow (~A, a^-q, 4);
            S1 := (SLP.2^SLP.4) * S1;
            bool := true;
         end if;
      end if;
   
      BB := (1-A[1, 1])/A[3, 1];
      TT := GetBBTransvection (BB);
      // A := T^-1 * A;
      AddRow (~A, BB, 3, 1);
      AddRow (~A, -BB^q, 2, 4);
      S1 := TT^-1 * S1;

      if j ne 0 then
         /* A := ( (v*u^-1)^-(j-2))*A; */
         S1 := ((SLP.5 * SLP.4^-1)^-(j-2)) * S1;
         B := ZeroMatrix (F, d, d);
         B[1] := A[1];
         B[2] := A[2];
         for y in [3..(2*j-2)] do
            B[y] := A[y + d-2*j + 5 - 3];
         end for;
         for y in [3..d-2*(j-2)] do
            B[y + 2*(j-2)] := A[y];
         end for;
         A := B;
      end if;

      if bool eq true then
         // A := ( (s^-1)^u)*A;
         SwapRows (~A, 3, 4);
         MultiplyRow (~A, -a, 3);
         MultiplyRow (~A, -a^-q, 4);
         S1 := ((SLP.2^-1)^SLP.4) * S1;
      end if;
   end procedure;

   /* kill the A[1, 3] entry */
   KillPlace := procedure (~A, ~S1, ~S2)
      pytemp := FF!A[1, 3];
      for r in [1..e] do
         S2 *:= (SLP.6^(SLP.7^-(r-1)))^-Z!Eltseq (pytemp)[r];
         // A := A*((x^(y^-(r-1)))^-Z!Eltseq (pytemp)[r]); 
         AddColumn (~A, -Eltseq (pytemp)[r] * w^(2*r-2), 1, 3);
         AddColumn (~A,  Eltseq (pytemp)[r] * (w^q)^(2*r-2), 4, 2);
      end for;
   end procedure;

   KillRow := procedure (~A, ~S1, ~S2)
      pytemp := FF!A[1, 1];

      for r in [1..e] do
         S1 := ((SLP.6^(SLP.7^-(r-1)))^-Z!Eltseq (pytemp)[r])*S1;
         // A := ((x^(y^-(r-1)))^-Z!Eltseq (pytemp)[r])*A; 
         AddRow (~A, -Eltseq (pytemp)[r] * w^(2*r-2), 3, 1);
         AddRow (~A,  Eltseq (pytemp)[r] * (w^q)^(2*r-2), 2, 4);
      end for;
   end procedure;

   /* return ts, which evaluates to t transpose */
   GetTS := function ()
      if d ne 2 then
         if IsOdd (q) then
            n := (q + 1) div 2;
            ts := (SLP.3^SLP.2)^(SLP.7^n);
         else
            ts := (SLP.3^SLP.2)^(SLP.1^(q div 2));
         end if;
      else
         FF := sub<F | a^4>;
         beta := FF!(a^(q+1));
         vv := Eltseq (beta);
         ts := Id (SLP);
         for i in [1..#vv] do
            ts *:= (SLP.3^(SLP.1^-(i-1)))^Z!vv[i];
         end for;
         ts := ts^SLP.2;
      end if;
      return ts;
   end function;

   /* returns the SLP that evaluates to the transvection [1, gamma, 0, 1] */
   GetGammaTransvection := function (gamma)
      FF := sub<F | a^4>;
      beta := FF!(gamma * a^-1);
      v := Eltseq (beta);
      T := Id (SLP);
      for i in [1..#v] do
         T *:= (SLP.3^(SLP.1^-(i-1)))^Z!v[i];
      end for;
      return T;
   end function;

   /* returns the SLP that evaluates to the transvection [1, 0, gamma, 1] */
   GetGammaTransvectionTranspose := function (gamma)
      FF := sub<F | a^4>;
      beta := FF!(gamma * a^-1);
      v := Eltseq (beta);
      T := Id (SLP);
      ts := GetTS ();
      for i in [1..#v] do
         T *:= (ts^(SLP.1^(i-1)))^Z!v[i];
      end for;
      return T;
   end function;

   for k in [1..block-1] do
      GetAOne (~A, ~S1, ~S2);

      for l in [1..block-1] do
         KillPlace (~A, ~S1, ~S2);

         /* A := A*u*s*u; swaps the third and fourth columns so 
            that we can work on the f part of the block. */
         MultiplyColumn (~A, a, 3);
         MultiplyColumn (~A, a^-q, 4);
         SwapColumns (~A, 3, 4);
         S2 *:= SLP.4 * SLP.2 * SLP.4;

         KillPlace (~A, ~S1, ~S2);

         /* A := A*((u*s*u)^-1);
            swaps the third and fourth columns back again */
         SwapColumns (~A, 3, 4);
         MultiplyColumn (~A, a^-1, 3);
         MultiplyColumn (~A, a^q, 4);
         S2 *:= (SLP.4 * SLP.2 * SLP.4)^-1;

         /* A := A* (v*u);
            vu is the (2..d/2) cycle on the blocks */
         for i in [2..(d div 2 - 1)] do
            SwapColumns (~A, 2*i - 1, d-1);
            SwapColumns (~A, 2*i, d);
         end for;
         S2 *:= SLP.5 * SLP.4;
      end for;

      /* we now multiply A by powers of t^(y^-z) for different z 
         to kill the [1, 2] place */

      FF := sub<F | a >;
      py2 := FF!A[1, 2];
      /* Conjugating t by y^-1 cubes the power of w in the [1, 2] place of t. 
         t^(y^-z) raises the power of w in the [1, 2] place of t by 2z + 1. 
         Even powers of a in the [1, 2] place can't be done as such elements 
         are not in the group. */
      for z in [1..#Eltseq (py2) div 2] do
         // A := A*((t^(y^-(z-1)))^-Z!Eltseq (py2)[2*z]); 
         AddColumn (~A, -Eltseq (py2)[2*z]*a^(2*z-1), 1, 2);
         S2 *:= (SLP.3^(SLP.7^-(z-1)))^-Z!Eltseq (py2)[2*z];
      end for;

      if (p eq 2) then
         for z in [1..#Eltseq (py2) div 2] do
            // A := A*(((t^(dy^(q div 2)))^y^-(z-1))^-Z!Eltseq (py2)[2*z -1])
            AddColumn (~A, -Eltseq (py2)[2*z -1]*a^(2*z -2), 1, 2);
            S2 *:= ((SLP.3^(dys^(q div 2)))^SLP.7^-(z-1))^-Z!Eltseq (py2)[2*z -1];
         end for;
      end if;

      if (p eq 2) and IsOdd (#Eltseq (py2)) then
         z := #Eltseq (py2) div 2 + 1;
         // A := A*((t^(dy^(q div 2)))^y^-z)^-Z!Eltseq (py2)[2*z -1]); 
         AddColumn (~A, -Eltseq (py2)[2*z -1]*a^(2*z -2), 1, 2);
         S2 *:= ((SLP.3^(dys^(q div 2)))^SLP.7^-(z-1))^-Z!Eltseq (py2)[2*z -1];
      end if;

      /* now we do the second column */
      for l in [1..block-1] do
         // A := u*A; swaps row 1 and 3 and 2 and 4 
         SwapRows (~A, 1, 3);
         SwapRows (~A, 2, 4);
         S1 := SLP.4 * S1;
         KillRow (~A, ~S1, ~S2); // kills the A[1, 1] place
         // A := s*A; swaps row 2 and 1 
         SwapRows (~A, 1, 2);
         MultiplyRow (~A, a, 1);
         MultiplyRow (~A, a^-q, 2);
         S1 := SLP.2 * S1;
         KillRow (~A, ~S1, ~S2); // kills the A[1, 1] place
         // A := s^-1*A; // swaps 1 and 2 back again
         MultiplyRow (~A, a^-1, 1);
         MultiplyRow (~A, a^q, 2);
         SwapRows (~A, 1, 2);
         S1 := SLP.2^-1 * S1;
         // A := u*A; returns the rows to their original position 
         SwapRows (~A, 1, 3);
         SwapRows (~A, 2, 4);
         S1 := SLP.4 * S1;
         // A := v*u*A; rotates the 2 to d/2 blocks as rows 
         for m in [2..((d div 2) -1)] do
            SwapRows (~A, 2*m-1, 2*m+1);
            SwapRows (~A, 2*m, 2*m+2);
         end for;

         S1 := SLP.5 * SLP.4 * S1;
      end for;

      // A := s^-1 * A * s; 
      SwapColumns (~A, 1, 2);
      MultiplyColumn (~A, a^-q, 1);
      MultiplyColumn (~A, a, 2);
      SwapRows (~A, 1, 2);
      MultiplyRow (~A, a^q, 1);
      MultiplyRow (~A, a^-1, 2);

      S1 := SLP.2^-1 * S1;
      S2 *:= SLP.2;

      FF := sub<F | a>;
      py2 := FF!A[1, 2];

      /* Conjugating t by y^-1 cubes the power of w in the [1, 2] place of t. 
         t^(y^-z) raises the power of w in the [1, 2] place of t by 2z + 1 */

      for z in [1..#Eltseq (py2) div 2] do
         // A := ((t^(y^-(z-1)))^-Z!Eltseq (py2)[2*z])*A; 
         AddColumn (~A, -Eltseq (py2)[2*z]*a^(2*z-1), 1, 2);
         S1 := ((SLP.3^(SLP.7^-(z-1)))^-Z!Eltseq (py2)[2*z])*S1;
      end for;

      if (p eq 2) then
         for z in [1..#Eltseq (py2) div 2] do
            // A := A*(((t^(dy^(q div 2)))^y^-(z-1))^-Z!Eltseq (py2)[2*z -1]); 
            AddColumn (~A, -Eltseq (py2)[2*z -1]*a^(2*z -2), 1, 2);
            S2 *:= ((SLP.3^(dys^(q div 2)))^SLP.7^-(z-1))^-Z!Eltseq (py2)[2*z -1];
         end for;
      end if;

      if (p eq 2) and IsOdd (#Eltseq (py2)) then
         z := #Eltseq (py2) div 2 + 1;
         // A := A*((t^(dy^(q div 2)))^y^-z) ^-Z!Eltseq (py2)[2*z -1]); 
         AddColumn (~A, -Eltseq (py2)[2*z -1]*a^(2*z -2), 1, 2);
         S2 *:= ((SLP.3^(dys^(q div 2)))^SLP.7^-(z-1))^-Z!Eltseq (py2)[2*z -1];
      end if;

      // A := s*A*s^-1; 
      SwapColumns (~A, 1, 2);
      MultiplyColumn (~A, a^-1, 1);
      MultiplyColumn (~A, a^q, 2);
      SwapRows (~A, 1, 2);
      MultiplyRow (~A, a, 1);
      MultiplyRow (~A, a^-q, 2);

      S1 := SLP.2 *S1;
      S2 *:= SLP.2^-1;

      B := Transpose (A);
      C := ZeroMatrix (F, d, d);
      for i in [1..d-2] do
         C[i] := B[i + 2];
      end for;
      C[d-1] := B[1];
      C[d] := B[2];
      A := Transpose (C);

      C := ZeroMatrix (F, d, d);
      B := A;
      for i in [1..d-2] do
         C[i] := B[i + 2];
      end for;
      C[d-1] := B[1];
      C[d] := B[2];
      A := C;

      S2 *:= SLP.5^-1;
      S1 := (SLP.5) * S1;
   end for;

   if A[1, 1] eq 0 then
      // A := A*s;
      SwapColumns (~A, 1, 2);
      MultiplyColumn (~A, a, 2);
      MultiplyColumn (~A, a^-q, 1);
      S2 *:= SLP.2;
   end if;

   if A[1, 2] eq 0 then
      // A := A*t;
      AddColumn (~A, a, 1, 2);
      S2 *:= SLP.3;
   end if;

   // Getting a 1 in the (1, 1) place 
   ts := GetTS ();
   FF := sub<F | a>;
   py2 := FF!((1-A[1, 1])/A[1, 2]);
   if d ne 2 then
      if IsOdd (q) then
         for z in [1..#Eltseq (py2) div 2] do
            // A := A* ((tts^(y^(z-1)))^Z!Eltseq (py2)[2*z -1]); 
            AddColumn (~A, Eltseq (py2)[2*z]*a^(2*z-1), 2, 1);
            S2 *:= (ts^(SLP.7^(z-1)))^Z!Eltseq (py2)[2*z];
         end for;
      else
         for z in [1..#Eltseq (py2)] do
            if IsEven (z) then
               index := (z + 1) div 2 - 1;
            else
               index := q div 2 + (z + 1) div 2 - 2;
            end if;
            // A := A*((tts^(y^index)))^Z!Eltseq (py2)[z]); 
            AddColumn (~A, Eltseq (py2)[z]*a^(z-1), 2, 1);
            S2 *:= (ts^(SLP.7^index))^Z!Eltseq (py2)[z];
 
         end for;
      end if;
   else
      T := GetGammaTransvectionTranspose (py2);
      AddColumn (~A, py2, 2, 1);
      S2 *:= T;
   end if;

   FF := sub<F | a>;
   py2 := FF!A[1, 2];
   if d ne 2 then
      for z in [1..#Eltseq (py2) div 2] do
         // A := A*((t^(y^-(z-1)))^-Z!Eltseq (py2)[2*z]); 
         AddColumn (~A, -Eltseq (py2)[2*z]*a^(2*z-1), 1, 2);
         S2 *:= (SLP.3^(SLP.7^-(z-1)))^-Z!Eltseq (py2)[2*z];
      end for;
   else
      gamma := A[1, 2];
      tran := GetGammaTransvection (gamma);
      AddColumn (~A, -gamma, 1, 2);
      S2 *:= tran^-1;
   end if;

   if (p eq 2) and (A[1, 2] ne 0) then
      for z in [1..#Eltseq (py2) div 2] do
         // A := A*(((t^(dy^(q div 2)))^y^-(z-1))^-Z!Eltseq (py2)[2*z -1]); 
         AddColumn (~A, -Eltseq (py2)[2*z -1]*a^(2*z -2), 1, 2);
         S2 *:= ((SLP.3^(dys^(q div 2)))^SLP.7^-(z-1))^-Z!Eltseq (py2)[2*z -1];
      end for;
   end if;

   if (p eq 2) and (IsOdd (#Eltseq (py2))) and (A[1, 2] ne 0) then
      z := #Eltseq (py2) div 2 + 1;
      // A := A*((t^(dy^(q div 2)))^y^-z)^-Z!Eltseq (py2)[2*z -1]); 
      AddColumn (~A, -Eltseq (py2)[2*z -1]*a^(2*z -2), 1, 2);
      S2 *:= ((SLP.3^(dys^(q div 2)))^SLP.7^-(z-1))^-Z!Eltseq (py2)[2*z -1];
   end if;

   // A := s^-1 * A * s;
   SwapColumns (~A, 1, 2);
   MultiplyColumn (~A, a^-q, 1);
   MultiplyColumn (~A, a, 2);
   SwapRows (~A, 1, 2);
   MultiplyRow (~A, a^q, 1);
   MultiplyRow (~A, a^-1, 2);

   S1 := SLP.2^-1 * S1;
   S2 *:= SLP.2;

   FF := sub<F | a>;
   py2 := FF!A[1, 2];
   if d ne 2 then
      for z in [1..#Eltseq (py2) div 2] do
         // A := ((t^(y^-(z-1)))^-Z!Eltseq (py2)[2*z])*A; 
         AddColumn (~A, -Eltseq (py2)[2*z]*a^(2*z-1), 1, 2);
         S1 := ((SLP.3^(SLP.7^-(z-1)))^-Z!Eltseq (py2)[2*z])*S1;
      end for;
   else
      gamma := A[1, 2];
      tran := GetGammaTransvection (gamma);
      AddColumn (~A, -gamma, 1, 2);
      S2 *:= tran^-1;
   end if;

   if (p eq 2) and (A[1, 2] ne 0) then
      for z in [1..#Eltseq (py2) div 2] do
         // A := A*(((t^(dy^(q div 2)))^y^-(z-1))^-Z!Eltseq (py2)[2*z -1]);
         AddColumn (~A, -Eltseq (py2)[2*z -1]*a^(2*z -2), 1, 2);
         S2 *:= (((SLP.3^(dys^(q div 2)))^SLP.7^-(z-1))^-Z!Eltseq (py2)[2*z -1]);
      end for;
   end if;

   if (p eq 2) and IsOdd (#Eltseq (py2)) and (A[1, 2] ne 0) then
      z := #Eltseq (py2) div 2 + 1;
      // A := A*((t^(dy^(q div 2)))^y^-z)^-Z!Eltseq (py2)[2*z -1]); 
      AddColumn (~A, -Eltseq (py2)[2*z -1]*a^(2*z -2), 1, 2);
      S2 *:= (((SLP.3^(dys^(q div 2)))^SLP.7^-(z-1))^-Z!Eltseq (py2)[2*z -1]);
   end if;

   // A := s*A*s^-1;
   SwapColumns (~A, 1, 2);
   MultiplyColumn (~A, a^-1, 1);
   MultiplyColumn (~A, a^q, 2);
   SwapRows (~A, 1, 2);
   MultiplyRow (~A, a, 1);
   MultiplyRow (~A, a^-q, 2);

   S1 := SLP.2 * S1;
   S2 *:= SLP.2^-1;

   word := S1^-1 * S2^-1;
   word := phi (word);

   /* May 2010 - reflect change in generating set for even characteristic */
   if p eq 2 then
      E := [W.i: i in [1..Ngens (W)]];
      s := E[1]; v := E[2]; t := E[3];
      delta := E[4]; u := E[5]; x := E[6]; y := E[7];
      Delta := ((y^(v^2))^s)^-1;
      Gamma := Delta^(q^2 div 2);
      t := t^(Gamma^(q - 2));
      s := s^(Gamma^(q - 2));
      word := Evaluate (word, [s, v, t, delta, u, x, y]);
   end if;

   return IsIdentity (A), word;
end function;
