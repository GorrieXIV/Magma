freeze;

/* find action of G on W and on V / W;
   return actions and change of basis matrix */

FindAction := function (G, V, W)

   if Dimension (W) eq 0 then 
      return G, sub <G |>, Identity (G); 
   end if;

   F := BaseRing (G);
   d := Degree (G);
   P := GL (d, F);;

   B := Basis (V);
   BasisW := Basis (W);

   dimW := Dimension (W);
   dimQ := d - dimW;

   /* note basis elements of W */
   pos := [Position (Eltseq (BasisW[i]), 1) : i in [1..#BasisW]];

   /* insert those basis elements of V not in W as first rows of 
     matrix C used to change basis */

   C := [];
   for i in [1..#B] do 
      if not (Depth (B[i]) in pos) then 
         C := C cat Eltseq (B[i]);
      end if; 
   end for;

   /* now insert basis of W as last rows of C */ 
   C := C cat (&cat[ Eltseq (BasisW[i]) : i in [1..#BasisW]]);

   /* C^-1 is the change of basis matrix */
   C := P!C;
   Cinv := C^-1;
   
   Al := MatrixAlgebra (F, d);
   A := [x^(Cinv) : x in Generators (G)];
   A := [Al!x : x in A];

   S := [];
   Q := [];

   for i in [1..#A] do
      Q[i] := ExtractBlock (A[i], 1, 1, dimQ, dimQ);
      S[i] := ExtractBlock (A[i], dimQ + 1, dimQ + 1, dimW, dimW);
   end for;

   Sub := sub < GL (dimW, F) | S >;
   Quo := sub < GL (dimQ, F) | Q >;

   return Sub, Quo, Cinv;

end function;

/* find action of elements of Gens on W and on V / W, 
   given change of basis matrix, C */

SubQuotAction := function (Gens, W, C)

   g := Rep (Gens); 
   G := Parent (g);
   F := BaseRing (G);
   d := Degree (G);
   Al := MatrixAlgebra (F, d);

   A := [x^C : x in Gens];
   A := [Al!x : x in A];

   S := [];
   Q := [];
   dimW := Dimension (W);
   dimQ := d - dimW;

   for i in [1..#A] do
      Q[i] := ExtractBlock (A[i], 1, 1, dimQ, dimQ);
      S[i] := ExtractBlock (A[i], dimQ + 1, dimQ + 1, dimW, dimW);
   end for;

   Sub := [ GL (dimW, F) ! S[i] : i in [1..#S]];
   Quo := [ GL (dimQ, F) ! Q[i] : i in [1..#Q]];

   return Sub, Quo;

end function;
