freeze;

import "sl2.m": IsSL2Basis, SL2Basis, SetSL2Basis, MyHom;

/* get a random element of G and return it both as a
   straight-line program and as an element */

RandomWord := function (G) 

   if not assigned G`SLPGroup and not assigned G`SLPGroupHom then
      "Input group must have associated SLPGroup and homomorphism";
      return false, _;
   end if;

   B := G`SLPGroup;

   if not assigned B`RandomProcess then
      P := RandomProcess (B: Scramble := 100);
      B`RandomProcess := P;
   else
      P := B`RandomProcess;
   end if;

   w := Random (P);
   gamma := G`SLPGroupHom;
   g := gamma (w);
   return g, w;

end function;

/* recognise SL(2, q) in its natural representation; 
   algorithm of Conder & Leedham-Green Ohio Proceedings;
   if G is SL(2, q), then return true and store 
   SL2Basis tuple in G; it has four components:
   the Chevalley basis;
   the SLPs for the elements of the Chevalley basis;
   the change-of-basis matrix;
   the identity matrix [used as a place holder for the
      change-of-basis matrix constructed in symmetric power]  */

CompleteSL2Basis := function (G)

   E := BaseRing (G);
   e := Degree (E);
   Z := Integers ();

   SLB := SL2Basis (G);
   B := SLB[1];
   L := B[1]; D := B[2]; U := B[3]; 
   W := SLB[2]; wL := W[1]; wU := W[3]; wD := W[2];

   /* make leading entry in diagonal element the 
      standard primitive element for E */
   x := PrimitiveElement (E);
   t := D[1][1];
   // "Discrete log call 4:";
   u := Log (t);
   R := RingOfIntegers (#E - 1);
   v := Z ! (Solution (R!u, R!1));
   D := GL(2, E) ! [x, 0, 0, x^-1]; wD := wD^(v);

   K := sub < E| x^2>;

   a := U[1][2];
   coeffs := Eltseq (K ! a^-1);
   coeffs := [Z!c: c in coeffs];

   /* standard basis element [1, 1, 0, 1] */
   US := GL (2, E) ![1,1,0,1];
   wUS := &*[(wU^(wD^-i))^coeffs[i + 1]: i in [0..#coeffs - 1]];

   /* set up complete basis for upper triangular matrices */
   UB := [GL(2, E) ! [1, x^(2 * i), 0, 1]: i in [0..e - 1]];
   wUB := [wUS^(wD^-i): i in [0..e - 1]];

   a := L[2][1];
   coeffs := Eltseq (K ! a^-1);
   coeffs := [Z!c: c in coeffs];

   /* standard basis element [1, 0, 1, 1] */
   LS := GL (2, E) ![1,0,1,1];
   wLS := &*[(wL^(wD^i))^coeffs[i + 1]: i in [0..#coeffs - 1]];

   /* set up complete basis for lower triangular matrices */
   LB := [GL(2, E) ! [1, 0, x^(2 * i), 1]: i in [0..e - 1]];
   wLB := [wLS^(wD^i): i in [0..e - 1]];

   B := <[* LB, D, UB *], [* wLB, wD, wUB *], SLB[3], SLB[4]>; 
  
   SetSL2Basis (G, B);
   
   return true;
end function;

ConstructSL2Basis := function (G: ReportTime := false)

   if Degree (G) ne 2 then "Degree must be 2"; return false; end if;

   Basis := SL2Basis (G);
   if Type (Basis) ne BoolElt then return true; end if;

   F := BaseRing (G);
   q := #F;

   gl := GL (2, F);

   // Find a diagonalisable element P of G of order q - 1 
   
   if not assigned G`SLPGroup then
      U := UserGenerators (G);
      G`SLPGroup := SLPGroup (#U);
      G`SLPGroupHom := MyHom (G, G`SLPGroup, U);
      assert [G`SLPGroupHom (G`SLPGroup.i): i in [1..#U]] eq U;
   end if;

   NmrTries := Maximum (100, Degree (G));
   found := false;
   repeat 
      x, wx := RandomWord (G);
      o := Order (x);
      if o mod (q - 1) eq 0 then 
         P := x^(o div (q - 1)); 
         found := true;
      end if;
      NmrTries -:= 1;
   until found or NmrTries eq 0;

   if NmrTries eq 0 then 
      vprint sl2q: "Did not find an element of order ", q - 1;
      return false;
   end if;
   wP := wx^(Order (x) div (q - 1)); 

   // Find eigenvectors of P 
   evs := SetToSequence (Eigenvalues(P)); 
   if (#evs ne 2) then 
      vprint sl2q: "P has a single eigenvalue", evs;
      return false;
   end if;
   v1 := Rep (Generators (Eigenspace (P, evs[1][1])));
   v2 := Rep (Generators (Eigenspace (P, evs[2][1])));

   /* Take a random conjugate A of P within G and diagonalise A by a 
      matrix Q the rows of which are eigenvectors for A 
      - make sure the entries of v1 * Q^-1 and v2 * Q^-1 are non-zero */

   ok := false;
   while not (ok) do 
      r, wr := RandomWord (G); 
      A := r * P * r^-1;
      evs := SetToSequence (Eigenvalues (A)); 
      a := evs[1][1];
      // assert (a * evs[2][1]) in {1, F!-1};
      if not (a * evs[2][1] in {1}) then 
         vprint sl2q: "Eigenvalues of A are not mutually inverse", evs;
         return false;
      end if; 
      w1 := Rep (Generators (Eigenspace (A, evs[1][1])));
      w2 := Rep (Generators (Eigenspace (A, evs[2][1]))); 
      Q := gl![w1[1], w1[2], w2[1], w2[2]];
      Qm1 := Q^-1; t1 := v1 * Qm1; t2 := v2 * Qm1;
      ok := (t1[1] ne 0) and (t1[2] ne 0) 
            and (t2[1] ne 0) and (t2[2] ne 0);
   end while; 
   wA := wr * wP * wr^-1;

   Anew := Q * A * Qm1;
   if Anew ne gl![a, 0, 0, a^-1] then 
      vprint sl2q: "Q * A * Q^-1 is not as expected, but =", Anew;
      return false;
   end if;

   /*  Choose a random matrix B in G such that there exists an 
       integer j for which C := A^j * B fixes the eigenvector 
       v1 of the original matrix P */

   v1q := v1 * Qm1;
   if v1q[1] eq 0 then 
      vprint sl2q: "Problem with modified vector v1 = ", v1q;
      return false;
   end if;
   x := v1q[2] * v1q[1]^-1;

   if ReportTime then "Discrete log call 1:"; end if;
   k := Log(a); 
   repeat 
      R, wR := RandomWord (G); B := Q * R * Qm1; wB := wR;
      sq := (x^2 * B[2][1] - x * B[2][2]) * (B[1][2] - x * B[1][1]); 
      while not (IsPower (sq, 2)) or (sq eq 0) do 
         R, wR := RandomWord (G); B := Q * R * Qm1; wB := wR;
         sq := (x^2 * B[2][1] - x * B[2][2]) * (B[1][2] - x * B[1][1]);
      end while;
      sq *:= (B[1][2] - x * B[1][1])^-2; 
      gcd, l, m := XGCD (k, q - 1); 
      if gcd ne 1 then 
         vprint sl2q: "a does not generate the multiplicative group";
         return false;
      end if;
      if ReportTime then "Discrete log call 2:"; end if;
      m := Log (Sqrt (sq));
      j := l * m mod (q - 1);
      B := R; wB := wR; C := A^j * B; wC := wA^j * wB;
   until (P, C) ne Identity (G);

   /* Repeat this process to find another B and some integer j for 
      which D := A^j * B fixes the eigenvector v2 of the original 
      matrix P */

   v2q := v2 * Qm1;
   if v2q[1] eq 0 then
      vprint sl2q: "Problem with modified vector v2 = ", v2q;
      return false;
   end if;
   x := v2q[2] * v2q[1]^-1;
   repeat 
      R, wR := RandomWord (G); B := Q * R * Qm1; wB := wR;
      sq := (x^2 * B[2][1] - x * B[2][2]) * (B[1][2] - x * B[1][1]);
      while not (IsPower (sq, 2)) or (sq eq 0) do
         R, wR := RandomWord (G); B := Q * R * Qm1; wB := wR;
         sq := (x^2 * B[2][1] - x * B[2][2]) * (B[1][2] - x * B[1][1]);
      end while; 
      sq *:= (B[1][2] - x * B[1][1])^-2;
      gcd, l, m := XGCD (k, q - 1);
      if gcd ne 1 then
         vprint sl2q: "a does not generate the multiplicative group";
         return false;
      end if;
      if ReportTime then "Discrete log call 3:"; end if;
      m := Log (Sqrt (sq));
      j := l * m mod (q - 1);
      B := R; wB := wR; D := A^j * B; wD := wA^j * wB;
   until (P, D) ne Identity (G);

   /* Conjugate the matrix P and the commutators [P, C] and [P, D] 
      by a new matrix Q the rows of which are eigenvectors for P */  

   Q := gl![v1[1], v1[2], v2[1], v2[2]]; Qm1 := Q^-1;

   Pnew := Q * P * Qm1; wPnew := wP;

   X := (P, C); X := Q * X * Qm1; wX := (wP, wC);
   Y := (P, D); Y := Q * Y * Qm1; wY := (wP, wD);

   gens := [X, Pnew, Y]; words := [wX, wPnew, wY]; 
   if not IsSL2Basis (gens) then 
      error "Error in ConstructSL2Basis"; 
   end if;

   SetSL2Basis (G, <gens, words, Q, Q^0>);

   return CompleteSL2Basis (G); 
end function;
