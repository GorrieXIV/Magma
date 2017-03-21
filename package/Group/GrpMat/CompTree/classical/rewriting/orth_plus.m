// import "../../GrpMat/ClassicalRec/sld2.m":OrthogonalForm2;
import "sl-natural.m": SLWordInGen;

OmegaCBM := function (G)
   F := BaseRing (G);
   w := PrimitiveElement (F);
   d := Dimension (G);
   M := MatrixAlgebra (F, d);
   sl := SL (d, F);

   /* goes from the form defined for G above to the form defined for GG below */
   CB := Zero (M);
   for i in [1..d div 2] do
      CB[i, 2*i - 1] := 1;
   end for;
   for i in [1..d div 2] do
      CB[(d div 2) + i, d - 2*i + 2] := 1;
   end for;
   CB := sl!CB;
   return CB;
end function;

// write A as word in standard generators of Omega^+
OmegaPlusWordInGen := function (G, A)

   W := SLPGroup (8);
   F := BaseRing (G);
   w := PrimitiveElement (F);
   d := Dimension (G);
   M := MatrixAlgebra (F, d);
   sl := SL (d, F);
   S := SLPGroup (7);
   S1 := Id (S);
   S2 := Id (S);
   e := Degree (F);
   phi := hom<S -> W|W.6, W.3, W.5, W.2, (W.5^W.4)^-1, (W.2^W.1)^-1, W.8>;
   
   Z := IntegerRing ();
   
   if d ne 2 then
      // CB := GL (d, F)![1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 1];
      CB := M!Id (sl);
      CB[2, 2] := 0;
      CB[3, 3] := 0;
      CB[2, 3] := -1;
      CB[3, 2] := 1;
      CB := sl!CB;
      /* goes from the form originally defined for delta1, t1, r1 etc. 
         to the form defined for GG below */
      CB2 := M!Id (sl);
      CB2[2, 2] := 0;
      CB2[2, 4] := -1;
      CB2[4, 4] := 0;
      CB2[4, 2] := 1;
      CB2 := sl!CB2;
      /* goes from the form defined for G above to the form defined 
         for GG below */
      CB3 := OmegaCBM (G);
   else
      CB := Id (G);
      CB2 := Id (G);
      CB3 := Id (G);
   end if;
   
   /* send the first w in delta1 to the first w in G.2 and 
      the first w^-1 in delta1 to the SECOND w^-1 in G.2; 
      then shuffle the 1s along. */
   
   // u := t1^2*(t1^r1);
   uu := S.3^2*(S.3^S.5);
   ss := (S.6*(S.4^-1)*S.6)*uu^-1;
   
   FF := sub<F|w^2>;
   py := FF!w;
   
   // Ot1 := Id (G);
   ot1 := Id (S);
   for i in [1..e] do
      // Ot1 := Ot1* (t1^(delta1^-(i-1)))^Z!Eltseq (py)[i];
      ot1 := ot1*(S.3^(S.1^-(i-1)))^Z!Eltseq (py)[i];
   end for;
   
   // Or1 := Id (G);
   or1 := Id (S);
   for i in [1..e] do
      // Or1 := Or1*(r1^(delta1^(i-1)))^Z!Eltseq (py)[i];
      or1 := or1*(S.5^(S.1^(i-1)))^Z!Eltseq (py)[i];
   end for;
   
   /* zz := Log (-w^2); */
   if IsOdd (#F) then
      zz := (#F - 1) div 2 + 2;
   else
      zz := 2;
   end if;
   
   // Ot2 := Id (G);
   ot2 := Id (S);
   if IsEven (zz) then
      for i in [1..e] do
         // Ot2 := Ot2*(t2^(delta2^-((zz div 2) + (i-2))))^Z!Eltseq (py)[i];
         ot2 := ot2*(S.4^(S.2^-((zz div 2) + (i-2))))^Z!Eltseq (py)[i];
      end for;
   else
      // Ot2 := Ot2*(t2^(delta2^-(zz div 2)));
      ot2 := ot2*(S.4^(S.2^-(zz div 2)));
   end if;
   
   // Or2 := Id (G);
   or2 := Id (S);
   if IsEven (zz) then
      for i in [1..e] do
         // Or2 := Or2*(r2^(delta2^((zz div 2) + (i-2))))^Z!Eltseq (py)[i];
         or2 := or2*(S.6^(S.2^((zz div 2) + (i-2))))^Z!Eltseq (py)[i];
      end for;
   else
      // Or2 := Or2*(r2^(delta2^(zz div 2)));
      or2 := or2*(S.6^(S.2^(zz div 2)));
   end if;
   
   GetBBTransvection := function (BB)
      // T := t2^-1;
      TT := S.4^-1;
      // T := T^Z!Eltseq (BB)[1];
      TT := TT^Z!Eltseq (BB)[1];
   
      for r in [2..e] do
         if IsEven (r) then
            // o := Ot2;
            oo := ot2;
            // o := o^(delta2^-Z!((r-2)/2));
            oo := oo^(S.2^-Z!((r-2)/2));
            // o := o^Z!Eltseq (BB)[r];
            oo := oo^Z!Eltseq (BB)[r];
            // T := T*o;
            TT := TT*oo;
         else
            // o := t2^-1;
            oo := S.4^-1;
            // o := o^(delta2^-Z!((r-1)/2));
            oo := oo^(S.2^-Z!((r-1)/2));
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
         if IsEven (i) then 
            j := i div 2;
         else 
            j := Z! (i/2 + 1/2); 
         end if; // find which block we need
         if i eq 2 then
            // A := A*s;
   	    SwapColumns (~A, 1, 2);
            SwapColumns (~A, 3, 4);
            S2 *:= ss;
         else
            // A := A * (u*v^-1)^(j-2)* (u*v)^(j-2)*u;
            /* j odd - swap blocks 1 and j and negate 2..j-1 */
            if IsOdd (j) then
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
            S2 *:= (uu*S.7^-1)^(j-2)*(uu*S.7)^(j-2)*uu; 
         end if;
         if A[1, 1] eq 0 then
            // A := A*s;
   	    SwapColumns (~A, 1, 2);
            SwapColumns (~A, 3, 4);
            S2 *:= ss;
         end if;
      end if; 
   
      i := 2;
      while A[i, 1] eq 0 do
         i +:= 1; if i eq d+1 then break; end if;
      end while;
      
      /* if A[1, 1] is the only non-zero entry on the first column */
      if i eq d+1 then
         // A := r1*A; 
         // sticks values in the first column
         AddRow (~A, 1, 1, 3);
         AddRow (~A, -1, 4, 2);
         S1 := S.5*S1;
         i := 3;
         while A[i, 1] eq 0 do i +:= 1; end while;
      end if;
      
      i := 4;
      j := 0;
      if A[4, 1] eq 0 then
         if A[3, 1] ne 0 then
            // A := (s^u)*A;
   	    SwapRows (~A, 1, 2);
            SwapRows (~A, 3, 4);
            S1 := (ss^uu)*S1;
         else
            i := 5;
            while A[i, 1] eq 0 do
               i +:= 1; if i eq d+1 then break; end if;      
   	    end while;
         end if;
         if i eq d+1 then
            /* if we are here, the only non-zero entries in the 
               first column are in the first two rows */
            // conjecture: this case never occurs 
         elif A[4, 1] ne 0 then
            S1 := S1; // do nothing
         else
            if IsEven (i) then j := i div 2; else j := Z! (i/2 + 1/2); end if;
            // A :=((v*u^-1)^(j-2))*A;
   	    B := ZeroMatrix (F, d, d);
            B[1] := A[1];
            B[2] := A[2];
            for y in [3..d-(2*(j-2))] do
   	       B[y] := A[y + 2* (j-2)];
            end for;
            for y in [d-(2*(j-2))+1..d] do
               B[y] := A[y -(d-(2*(j-2))+1) + 3];
            end for;
            A := B;
            if IsOdd (d div 2) then
   	       for m in [d-(2*(j-2))+1..d] do
   	          MultiplyRow (~A, -1, m);
               end for;
            end if;
            S1 :=((S.7*uu^-1)^(j-2))*S1;
            if A[4, 1] eq 0 then
   	       // A := (s^u)*A;
               SwapRows (~A, 1, 2);
   	       SwapRows (~A, 3, 4);
               S1 := (ss^uu)*S1;
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
         // A :=((v*u^-1)^-(j-2))*A;
         S1 :=((S.7*uu^-1)^-(j-2))*S1;
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
         if IsOdd (d div 2) then
            for m in [3..2*j-2] do
               MultiplyRow (~A, -1, m);
            end for;
         end if;
      end if;
   end procedure;
   
   KillRow := procedure (~A, ~S1, ~S2)
      for i in [2..d div 2] do
         a := A[1, 4];
         S2 *:= (S.4^Z!Eltseq (a)[1]);
         // A := A*(t2^Z!Eltseq (a)[1]);
         AddColumn (~A, -Eltseq (a)[1], 1, 4);
         AddColumn (~A, Eltseq (a)[1], 3, 2);
         for r in [2..e] do
            if IsEven (r) then
               S2 *:= ((ot2^-1)^(S.2^-Z!((r-2)/2)))^Z!Eltseq (a)[r];
   	       // A := A*((Ot2^-1)^(delta2^-Z!((r-2)/2)))^Z!Eltseq (a)[r];
   	       AddColumn (~A, -Eltseq (a)[r]*w^(r-1), 1, 4);
               AddColumn (~A, Eltseq (a)[r]*w^(r-1), 3, 2);
            else
   	       S2 *:= ((S.4^-1)^(S.2^-Z!((r-1)/2)))^-Z!Eltseq (a)[r];
   	       // A := A*((t2^-1)^(delta2^-Z!((r-1)/2)))^-Z!Eltseq (a)[r];
   	       AddColumn (~A, -Eltseq (a)[r]*w^(r-1), 1, 4);
               AddColumn (~A, Eltseq (a)[r]*w^(r-1), 3, 2);
            end if;
         end for;
   	 
         a := A[1, 3];
         S2 *:= S.3^-Z!Eltseq (a)[1];
         // A := A* (t1^-Z!Eltseq (a)[1]);
         AddColumn (~A, -Eltseq (a)[1], 1, 3);
         AddColumn (~A, Eltseq (a)[1], 4, 2);
         for r in [2..e] do
            if IsEven (r) then
               S2 *:= ((ot1^-1)^(S.1^-Z!((r-2)/2)))^Z!Eltseq (a)[r];
   	       // A := A*((Ot1^-1)^(delta1^-Z!((r-2)/2)))^Z!Eltseq (a)[r];
   	       AddColumn (~A, -Eltseq (a)[r]*w^(r-1), 1, 3);
               AddColumn (~A, Eltseq (a)[r]*w^(r-1), 4, 2);
            else
   	       S2 *:= ((S.3^-1)^(S.1^-Z!((r-1)/2)))^Z!Eltseq (a)[r];
   	       // A := A*((t1^-1)^(delta1^-Z!((r-1)/2)))^Z!Eltseq (a)[r];
   	       AddColumn (~A, -Eltseq (a)[r]*w^(r-1), 1, 3);
               AddColumn (~A, Eltseq (a)[r]*w^(r-1), 4, 2);
   	    end if;
         end for;
               
         S2 *:= S.7 * (uu^-1);
         // A := A*v* (u^-1); // rotates the 2..d/2 blocks
         for m in [(d div 2-1)..2 by -1] do
            SwapColumns (~A, 2*m-1, 2*m+1);
            SwapColumns (~A, 2*m, 2*m+2);
         end for;
         if IsOdd (d div 2) then
            MultiplyColumn (~A, -1, 3);
            MultiplyColumn (~A, -1, 4);
         end if;
      end for;
   end procedure;
   		
   KillColumn := procedure (~A, ~S1, ~S2)
      for i in [2..d div 2] do
         a := A[4, 1];
         S1 := (S.6^Z!Eltseq (a)[1])*S1;
         // A := (r2^Z!Eltseq (a)[1])*A;
         AddRow (~A, -Eltseq (a)[1], 1, 4);
         AddRow (~A, Eltseq (a)[1], 3, 2);
         for r in [2..e] do
            if IsEven (r) then
               S1 :=((or2^-1)^(S.2^Z!((r-2)/2)))^Z!Eltseq (a)[r]*S1;
               // A :=((Or2^-1)^(delta2^Z!((r-2)/2)))^Z!Eltseq (a)[r]*A;
               AddRow (~A, -Eltseq (a)[r]*w^(r-1), 1, 4);
               AddRow (~A, Eltseq (a)[r]*w^(r-1), 3, 2);
            else
               S1 :=((S.6^-1)^(S.2^Z!((r-1)/2)))^-Z!Eltseq (a)[r] *S1;
               // A :=((r2^-1)^(delta2^Z!((r-1)/2)))^-Z!Eltseq (a)[r]*A;
               AddRow (~A, -Eltseq (a)[r]*w^(r-1), 1, 4);
               AddRow (~A, Eltseq (a)[r]*w^(r-1), 3, 2);
   	    end if;
         end for;
   	 
         a := A[3, 1];
         S1 := (S.5^Z!-Eltseq (a)[1])*S1;
         // A := (r1^Z!-Eltseq (a)[1])*A;
         AddRow (~A, -Eltseq (a)[1], 1, 3);
         AddRow (~A, Eltseq (a)[1], 4, 2);
   	 for r in [2..e] do
            if IsEven (r) then
               S1 :=((or1^-1)^(S.1^Z!((r-2)/2)))^Z!Eltseq (a)[r] *S1;
   	       // A :=((Or1^-1)^(delta1^Z!((r-2)/2)))^Z!Eltseq (a)[r]*A;
   	       AddRow (~A, -Eltseq (a)[r]*w^(r-1), 1, 3);
               AddRow (~A, Eltseq (a)[r]*w^(r-1), 4, 2);
            else
   	       S1 :=((S.5^-1)^(S.1^Z!((r-1)/2)))^Z!Eltseq (a)[r] *S1;
   	       // A :=((r1^-1)^(delta1^Z!((r-1)/2)))^Z!Eltseq (a)[r]*A;
   	       AddRow (~A, -Eltseq (a)[r]*w^(r-1), 1, 3);
               AddRow (~A, Eltseq (a)[r]*w^(r-1), 4, 2);
   	    end if;
         end for;      
         
         S1 := S.7* (uu^-1)*S1;
         // A := v* (u^-1)*A;
         for m in [2..(d div 2-1)] do
            SwapRows (~A, 2*m-1, 2*m+1);
   	    SwapRows (~A, 2*m, 2*m+2);
         end for;
         if IsOdd (d div 2) then
            MultiplyRow (~A, -1, d-1);
            MultiplyRow (~A, -1, d);
         end if;
      end for;
   end procedure;
   
   A := A^CB3;
   AA := A;
   
   for k in [1.. (d div 2 - 2)] do
      GetAOne (~A, ~S1, ~S2);
      KillRow (~A, ~S1, ~S2);
      KillColumn (~A, ~S1, ~S2);
   
      /* A := A^(v^-1); */
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
   
      MultiplyColumn (~A, -1, d-1);
      MultiplyColumn (~A, -1, d);
      MultiplyRow (~A, -1, d-1);
      MultiplyRow (~A, -1, d);
   
      S1 := S.7*S1;
      S2 *:= S.7^-1;
   end for;
   
   if d eq 2 then
      // Q := PlusChosenElements (G);
      Q := ClassicalStandardGenerators ("Omega+", d, #F);
      Q := [SL (d, F)!Q[i] : i in [1..#Q]];
      alpha := Log (A[1, 1]);
      beta := Log (Q[3][1, 1]);
      if beta ne 0 then
         gamma := (alpha * #F) div beta;
      else
         gamma := 0;
      end if;
      word := S.3^gamma;
      A := A*Q[3]^-gamma;
      phi := hom<S -> W | W.1, W.2, W.3, W.4, W.5, W.6, W.7>;
      word := phi (word);
   else
      CB4 := GL (4, F)![1, 0, 0, 0,
                        0, 0, 0, 1,
                        0, 1, 0, 0,
                        0, 0, -1, 0];
   
      EB := ExtractBlock (A, 1, 1, 4, 4);
      if EB notin SL (4, F) then
         // return false, A, S1^-1 * S2^-1;
         return false, S1^-1 * S2^-1;
      end if;
      B := SL (4, F)!EB;
   
      _, x1 := IsProportional (B^CB4, 2);
      x2 := x1[1];
      x1 := x1[2];
      if IsSquare (Determinant (x1)) eq false then
         // return false, A, S1^-1 * S2^-1;
         return false, S1^-1 * S2^-1;
      end if;
   
      x1 := x1/Root (Determinant (x1), 2);
      x2 := x2/Root (Determinant (x2), 2);
      _, w1 := SLWordInGen (SL (2, F), GL (2, F)! x1);
      _, w2 := SLWordInGen (SL (2, F), GL (2, F)! x2);
   
      sll := SL (2, F);
      psi1 := hom<Parent (w1) -> W|W.4, W.4, W.5, W.6>;
      psi2 := hom<Parent (w2) -> W|W.1, W.1, W.2, W.3>;
   
      word := phi (S1^-1) * psi2 (w2) * psi1 (w1) * phi (S2^-1);
      // Q := PlusChosenElements (G);
      Q := ClassicalStandardGenerators ("Omega+", d, #F);
      Q := [SL (d, F)!Q[i] : i in [1..#Q]];
   
      if A * Evaluate (psi2 (w2^-1) * psi1 (w1^-1), Q) ne Id (G) then
         x1 := -x1;
         _, w1 := SLWordInGen (SL (2, F), GL (2, F)! x1);
         _, w2 := SLWordInGen (SL (2, F), GL (2, F)! x2);
         sll := SL (2, F);
         psi1 := hom<Parent (w1) -> W|W.4, W.4, W.5, W.6>;
         psi2 := hom<Parent (w2) -> W|W.1, W.1, W.2, W.3>;
         word := phi (S1^-1) * psi2 (w2) * psi1 (w1) * phi (S2^-1);
      end if;
   
      A := A * Evaluate (psi2 (w2^-1) * psi1 (w1^-1), Q);
   end if;
   
   return IsIdentity (A), word;
end function;

intrinsic SOPlusWordInGen (G :: GrpMat, A :: GrpMatElt) -> BoolElt, GrpSLPElt
{write A as word in standard generators of SO^+}

   if Degree (G) gt 2 then
      _, _, J := OrthogonalForm (G);
   else 
      error "Degree must be at least 4";
      // flag, _, J := OrthogonalForm2 (G);
   end if;
   
   if Degree (G) eq 2 and #BaseRing (G) eq 2 then
      sn := IsIdentity (A) select 0 else 1;
   else 
      sn := SpinorNorm (A, J);
   end if;

   if sn eq 0 then
      flag, word := OmegaPlusWordInGen (G, A);
      SS := Parent (word);
      S := SLPGroup (9);
      phi := hom<SS -> S | S.1, S.2, S.3, S.4, S.5, S.6, S.7, S.8>;
      word := phi (word);
   else
      d := Dimension (G);
      F := BaseRing (G);
      QQ := ClassicalStandardGenerators( "Omega+", d, #F: SpecialGroup := true);
      CB := OmegaCBM (G);
      sp := GL (d, F)!QQ[#QQ]^(CB^-1);
      A *:= sp;
      flag, word := OmegaPlusWordInGen (G, A);
      SS := Parent (word);
      S := SLPGroup (9);
      phi := hom<SS -> S | S.1, S.2, S.3, S.4, S.5, S.6, S.7, S.8>;
      word := phi (word);
      word *:= S.9^-1;
   end if;

   return flag, word;
end intrinsic;
