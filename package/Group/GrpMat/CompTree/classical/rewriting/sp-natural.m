function SymplecticCBM (G)
   F := BaseRing (G);
   d := Dimension (G);
   M := KMatrixSpace (F, d, d); 
   b := Basis (M);
   G := SL (d, F);

   CB := ZeroMatrix (F, d, d);
   for i in [1..d div 2] do
      CB := CB + b[(i-1)*d + 2*i - 1];
   end for;
   for i in [1..d div 2] do
      CB := CB + b[(d div 2)*d + i*d - 2*i + 2];
   end for;
   return G!CB;
end function;

/* BB is an element of GF (q). This algorithm returns the
   transvection with BB in the [2, 1] position */

GetBBTransvection := function (BB, SLP)

   F := Parent (BB);
   
   e := Degree (F);
   Z := IntegerRing ();
   w := PrimitiveElement (F);

   FF := sub<F | w^2>;
   py := FF!F.1;

   py := Eltseq (py);
   py := [Z!x : x in py];

   B := Eltseq (BB);
   B := [Z!b: b in B];

   O := &*[(SLP.3^SLP.1^-(i-1))^py[i] : i in [1..e]];

   T := SLP.3^-1;
   T := (T^SLP.2)^B[1];

   for r in [2..e] do
      if IsEven (r) then
         o := O^-1;
         o := o^(SLP.1^-((r-2) div 2));
         o := (o^SLP.2)^B[r];
      else
         o := SLP.3^-1;
         o := o^(SLP.1^-((r-1) div 2));
         o := (o^SLP.2)^B[r];
      end if;
      T *:= o;
   end for;

   return T;
end function;

// This function gets a 1 in the [1, 1] position of A.  S1 and S2 are SLPs. 

GetAOne := procedure (~A, ~S1, ~S2)

   SLP := Parent (S1);
   F := BaseRing (A);
   w := PrimitiveElement (F);
   d := Nrows (A);
   Z := IntegerRing ();

   if A[1, 1] ne 1 then
      i := 2;
      while A[1, i] eq 0 do
         i +:= 1;
         if i eq d+1 then break; end if;
      end while;

      if i eq d+1 then
         AddColumn (~A, 1, 1, 2);
         S2 *:= SLP.3;
         i := 2;
      end if;
   
      if i eq 2 then
         /* here we add the necessary multiple of column 2
            to column 1 to make A[1, 1] = 1 */
         BB := (1-A[1, 1]) / A[1, 2];
         T := GetBBTransvection (BB, SLP);
         AddColumn (~A, BB, 2, 1);
         S2 *:= T;
      else
         /* the case where A[1, 2] = 0; 
            we move the non-zero entry to position 4 */
         BB := (1-A[1, 1]) / A[1, i];
         T := GetBBTransvection (BB, SLP);

         /* decide which block the non-zero entry is in */
         if IsEven (i) then j := i div 2; else j := Z!(i/2 + 1/2); end if;

         /* we get the non-zero entry into the second block */
         if j eq 2 then
            A := A;
         else
            /* A := A*(u*v^-1)^(j-2)*(u*v)^(j-2)*(u*v^-1)^(j-2)*(u*v)^(j-2)*u;
               swaps block 2 with block j to get the block
               with the non-zero entry as the second block of A */
            SwapColumns (~A, 3, 2*j - 1);
            SwapColumns (~A, 4, 2*j);
            S2 *:= (SLP.4*SLP.5^-1)^(j-2) * (SLP.4*SLP.5)^(j-2) *
                   (SLP.4*SLP.5^-1)^(j-2) * (SLP.4*SLP.5)^(j-2) * SLP.4;
         end if;

         // A := A*s; puts the entry you wish to make equal to 1 in A[1, 2] 
         MultiplyColumn (~A, -1, 1);
         SwapColumns (~A, 1, 2);
         S2 *:= SLP.2;
         // A := A*u; puts the entry you wish to make equal to 1 in A[1, 4] 
         SwapColumns (~A, 1, 3);
         SwapColumns (~A, 2, 4);
         S2 *:= SLP.4;
      
         /* we now add column 4 to 1 and column 2 to 3 in order that,
            when we stick all the columns back again, there will be a
            non-zero entry in the A[1, 2] position */
         if IsEven (i) then 
            AddColumn (~A, 1, 4, 1);
            AddColumn (~A, 1, 2, 3);
            S2 *:= SLP.6;
         else
            MultiplyColumn (~A, -1, 1); // s
            SwapColumns (~A, 1, 2); // s
            AddColumn (~A, 1, 4, 1); // x
            AddColumn (~A, 1, 2, 3); // x
            SwapColumns (~A, 1, 2); // s^-1
            MultiplyColumn (~A, -1, 1); // s^-1
            S2 *:= SLP.2 * SLP.6 * (SLP.2 ^-1);
         end if;
      
         // we now proceed to stick all the columns back again 
         SwapColumns (~A, 1, 3);
         SwapColumns (~A, 2, 4);
         S2 *:= SLP.4^-1;
         SwapColumns (~A, 1, 2); // s^-1
         MultiplyColumn (~A, -1, 1); // s^-1
         S2 *:= SLP.2^-1;
         if j ne 2 then
            /* swaps block 2 with block j */
	    SwapColumns (~A, 3, 2*j -1);
	    SwapColumns (~A, 4, 2*j);
            S2 *:= (((SLP.4*SLP.5^-1)^(j-2) * (SLP.4*SLP.5)^(j-2) *
                   (SLP.4*SLP.5^-1)^(j-2) * (SLP.4*SLP.5)^(j-2) * SLP.4)^-1);
         end if;
         BB := (1-A[1, 1]) / A[1, 2];
         T := GetBBTransvection (BB, SLP);
         AddColumn (~A, BB, 2, 1);
         S2 *:= T;
      end if;
   end if;

   assert A[1, 1] eq 1;
end procedure;

// write A as SLP in standard generators of Sp
SymplecticWordInGen := function (G, A) 
   W := SLPGroup (6);
   d := Degree (G);
   F := BaseRing (G);
   G := SL (d, F);
   e := Degree (F);
   CB := SymplecticCBM (G);
   A := G!(A^CB);

   SLP := SLPGroup (6);
   S1 := Id (SLP);
   S2 := Id (SLP);
   Z := IntegerRing ();

   // This homomorphisms maps the original generating set to the new one
   phi := hom<SLP -> W | W.4, W.1^-1, W.3, W.5, W.2, W.6^(W.2^2)>;

   /* We wish to find the matrix whose top row is [1 w 0 .. 0],
      has 1s on the leading diagonal and 0s everywhere else.
      We construct the subfield FF of F generated by w^2. This
      subfield has order greater than half of the order of F
      and hence is equal to F. By then coercing w into FF, magma
      will write w as a polynomial py in powers of the generator
      of FF. So w is written as a polynomial in w^2.
      t^(delta^-1) gives us the matrix with [1 w^2 0 .. 0] on
      the top row and t^(delta^-a) gives you the matrix with
      [1 w^2a 0 .. 0] on the top row. Hence, you can use py to
      find the powers of t^(delta^-1) needed to give the matrix
      with [1 w 0 .. 0] on the top row.  */

   w := PrimitiveElement (F);
   FF := sub<F|w^2>;
   py := FF!F.1;

   /* py is now a polynomial in w^2 that is equal to w */

   py := Eltseq (py);
   py := [Z!x : x in py];
   O := &*[(SLP.3^SLP.1^-(i-1))^py[i]: i in [1..e]];

   /* the number of blocks preserved by the Weyl group */
   block := d div 2;

   /* kill the A[1, 3] entry */
   KillPlace := procedure (~A, ~S1, ~S2)
      aa := Eltseq (A[1, 3]);
      for r in [1..e] do
         S2 *:= (SLP.6^(SLP.1^(r-1)))^Z!aa[r];
      end for;
      AddColumn (~A, A[1, 3], 4, 1);
      AddColumn (~A, A[1, 3], 2, 3);
   end procedure;

   for k in [1..block] do
      GetAOne (~A, ~S1, ~S2);

      /* A := A*s; swaps first two columns */
      MultiplyColumn (~A, -1, 1); // s
      SwapColumns (~A, 1, 2); // s
      S2 *:= SLP.2;

      for l in [1..block-1] do
         KillPlace (~A, ~S1, ~S2);
         /* A := A*u*s*u;
            swaps the third and fourth columns so that 
            we can work on the f part of the block */
         SwapColumns (~A, 3, 4);
         MultiplyColumn (~A, -1, 4);
         S2 *:= SLP.4 * SLP.2 * SLP.4;

         KillPlace (~A, ~S1, ~S2);
         /* A := A*((u*s*u)^-1);
            swaps the third and fourth columns back again */
         MultiplyColumn (~A, -1, 4);
         SwapColumns (~A, 3, 4);
         S2 *:= (SLP.4 * SLP.2 * SLP.4)^-1;
         /* A := A * (v*u);
            vu is the (2..d/2) cycle on the blocks */
         for i in [2..(d div 2 - 1)] do
            SwapColumns (~A, 2*i - 1, d-1);
            SwapColumns (~A, 2*i, d);
         end for;
         S2 *:= SLP.5 * SLP.4;
      end for;

      /* A := A*(s^-1);
         swaps first two columns back again */
      SwapColumns (~A, 1, 2); // s^-1
      MultiplyColumn (~A, -1, 1); // s^-1
      S2 *:= SLP.2^-1;
      S2 *:= (SLP.3^Z!-Eltseq (A[1, 2])[1]);

      T := Id (SLP);
      A12 := Eltseq (A[1,2]);
      A12 := [Z!a: a in A12];
      for r in [2..e] do
         if IsEven (r) then
            o := O^(SLP.1^-((r-2) div 2));
         else
            o := SLP.3^(SLP.1^-((r-1) div 2));
         end if;
         o := o^A12[r];
         T *:= o;
      end for;

      for r in [1..e] do
         AddColumn (~A, -Eltseq (A[1, 2])[r]*w^(r-1), 1, 2);
      end for;
      S2 *:= T^-1;

      /* now we do the second row */

      // A := s*A; // swaps the first two rows
      SwapRows (~A, 1, 2);
      MultiplyRow (~A, -1, 1);
      S1 := SLP.2*S1;

      for l in [1..block-1] do
         KillPlace (~A, ~S1, ~S2);
         /* A := A*u*s*u;
            swaps the third and fourth columns so that we can 
            work on the f part of the block */
         SwapColumns (~A, 3, 4);
         MultiplyColumn (~A, -1, 4);
         S2 *:= SLP.4 * SLP.2 * SLP.4;

         KillPlace (~A, ~S1, ~S2);
         /* A := A*((u*s*u)^-1);
            swaps the third and fourth columns back again */
         MultiplyColumn (~A, -1, 4);
         SwapColumns (~A, 3, 4);
         S2 *:= (SLP.4 * SLP.2 * SLP.4)^-1;

         for i in [2..d div 2 - 1] do
            SwapColumns (~A, 2*i - 1, d-1);
            SwapColumns (~A, 2*i, d);
         end for;
         S2 *:= SLP.5 * SLP.4;
      end for;

      /* A := A* (s^-1);
         swaps first two columns back again */
      SwapColumns (~A, 1, 2);
      MultiplyColumn (~A, -1, 1);
      S2 *:= SLP.2 ^-1;

      S2 *:= (SLP.3^Z!-Eltseq (A[1, 2])[1]);
      T := Id (SLP);
      for r in [2..e] do
         if IsEven (r) then
            o := O^(SLP.1^-((r-2) div 2));
         else
            o := SLP.3^(SLP.1^-((r-1) div 2));
         end if;
         o := o^Z!Eltseq (A[1, 2])[r];
         T *:= o;
      end for;
      S2 *:= T^-1;
      for r in [1..e] do
         AddColumn (~A, -Eltseq (A[1, 2])[r]*w^(r-1), 1, 2);
      end for;

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
      S1 := SLP.5 * S1;
   end for;

   word := S1^-1 * S2^-1;
   word := phi (word);

   return IsIdentity (A), word;
end function;
