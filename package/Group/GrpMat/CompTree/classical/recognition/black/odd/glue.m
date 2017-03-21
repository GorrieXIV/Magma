freeze;

import "split.m": SmallestFaithful, DegreeToRank;
import "omega8.m": MyRecogniseOmega8P;
import "base-omega.m": MyRecogniseOmegaPlus4;
import "base.m": MyRecogniseSL4, MyRecogniseSp4, MyRecogniseSU4;

// Determine the form preserved by G
MyClassicalForms := function (G, type)
   if type in ["D", "2D", "B"] then
      flag, otype, form := OrthogonalForm (G);
      return flag, otype, form;
   elif type eq "C" then
      flag, form := SymplecticForm (G);
      return flag, form;
   elif type eq "2A" then
      flag, form := UnitaryForm (G);
      return flag, form;
   end if;
   if flag eq false then error "Error in MyClassicalForms"; end if;
end function;

// non-orthogonal cases: construct involution I whose centraliser contains the glue element 
NonOrthogonal_Inv := function (E1, W1, E2, W2, f, F, type)
   p := Characteristic(F);
   if type eq "2A" then
      F := GF(p, Degree (F) div 2);
   end if;
   q := #F;

   wb1 := W1[2]; /* wb1 is the cycle in G1 */

   m := (q - 1) div 2;

   /* construct u = Diagonal ([1, ... 1, -1, -1]) */
   delta := E1[4];
   if type eq "A" then k := f - 2; end if;
   if type eq "C" or type eq "2A" then k := (f div 2) - 1; end if;
   wdelta := W1[4]; wu := wdelta^m; wu := wu^(wb1^k);
   delta  := E1[4];  u :=  delta^m;  u :=  u^(E1[2]^k);

   /* construct v = Diagonal ([-1,-1, ... 1]) */
   wdelta := W2[4]; wv := wdelta^m;
   delta  := E2[4];  v :=  delta^m;
   wI := wu * wv;
   I := u * v;
   return u, v, I, wu, wv, wI;
end function;

// construct the involution I whose centraliser contains the glue element 
// E1 and E2 are standard generators for two factors, one of dimension f 
// W1 and W2 corresponding words

ConstructInvolution := function (E1, W1, E2, W2, f, F, type)
   q := #F;
   if type in {"B", "D", "2D"} then 
      if q mod 4 eq 3 then
         if type eq "D" then
            Index1 := [1..6];
            Index2 := Index1;
            k := -2; l := 0;
         elif type eq "2D" then
            k := 0; l := -2;
            Index2 := [1..6];
            Index1 := [6..11];
         elif type eq "B" then
            k := 0; l := -2;
            Index2 := [1..6];
            Index1 := [#E1 - 5..#E1];
         end if;
      else
         k := 0; l := 2;
         Index2 := [1..6];
         Index1 := [6..11];
      end if;

      if q mod 4 eq 3 then
          Base1 := [E1[i]^E1[8]^k : i in Index1];
         WBase1 := [W1[i]^W1[8]^k : i in Index1];
          Base2 := [E2[i]^E2[8]^l : i in Index2];
         WBase2 := [W2[i]^W2[8]^l : i in Index2];
          u := Base1[4]^2; v := Base2[4]^2;
          wu := WBase1[4]^2; wv := WBase2[4]^2;
          // I := Base1[4]^2 * Base2[4]^2;
          I := u * v;
         wI := wu * wv;
         // wI := WBase1[4]^2 * WBase2[4]^2;
      else
         Base1 := []; Base2 := [];
         WBase1 := []; WBase2 := [];
         m := (q - 1) div 4;
         if type eq "D" then
             k := (f div 2) - 1;
             u := ((E1[3] * E1[6])^m)^E1[8]^k;
            wu := ((W1[3] * W1[6])^m)^W1[8]^k;
             v :=  (E2[3] * E2[6])^m;
            wv :=  (W2[3] * W2[6])^m;
         else
            if f in [3, 4] then
                u := (E1[3]^(Order (E1[3]) div 2));
               wu := (W1[3]^(Order (E1[3]) div 2));
            else
                u := ((E1[3]^(Order (E1[3]) div 2)))^E1[4];
               wu := ((W1[3]^(Order (E1[3]) div 2)))^W1[4];
            end if;
         end if;			
          v := ((E2[3] * E2[6])^m)^E2[8]^-1;
 	 wv := ((W2[3] * W2[6])^m)^W2[8]^-1;
 	  I :=  u * v;
 	 wI := wu * wv;
      end if;
   else
      u, v, I, wu, wv, wI := NonOrthogonal_Inv (E1, W1, E2, W2, f, F, type);

      if type eq "A" then k := f - 2; end if;
      if type eq "C" or type eq "2A" then k := (f div 2) - 1; end if;
 	
       // generators for two SL(2, q) 
       Base1 := [E1[1]^(E1[2]^k), E1[3]^(E1[2]^k), E1[4]^(E1[2]^k)];
      WBase1 := [W1[1]^(W1[2]^k), W1[3]^(W1[2]^k), W1[4]^(W1[2]^k)];
       Base2 := [E2[1], E2[3], E2[4]];
      WBase2 := [W2[1], W2[3], W2[4]];
   end if;

   return I, wI, Base1, WBase1, Base2, WBase2, u, wu, v, wv;
end function;

// Construct a standard basis for standard O+(4, q) generators
LineUpOmegaPlus4Generators := function (E, F)
   j := 1;
   repeat
      i := 1;
      repeat
         ev1 := Setseq (Eigenvalues (E[2]))[i][1];
         ev2 := Setseq (Eigenvalues (E[5]))[j][1];
         ev3 := Setseq (Eigenvalues (E[3]))[1][1];
         V2 := Eigenspace (E[2], ev1) meet Eigenspace (E[5], ev2)
               meet Eigenspace (E[3], ev3);
         if Dimension (V2) eq 0 then
            ev3 := Setseq (Eigenvalues (E[3]))[2][1];
            V2 := Eigenspace (E[2], ev1) meet Eigenspace (E[5], ev1) 
                  meet Eigenspace (E[3], ev3);
         end if;
         i +:= 1;
      until (Dimension (V2) eq 1) or (i gt #Eigenvalues (E[2]));
      j +:= 1;
   until (Dimension (V2) eq 1) or (j gt #Eigenvalues (E[5]));

   w2 := Basis (V2)[1];
   v2 := Eltseq (w2);
   w3 := (w2^E[1]^-1);
   v3 := Eltseq (w3);
   w1 := (w3^E[4]^-1);
   v1 := Eltseq (w1);
   w4 := -(w2^E[4]^-1);
   v4 := Eltseq (w4);
   return v1 cat v2 cat v3 cat v4;
end function;

// Omega+(8, F) glue
SpecialOrthogonalGlue := function (Z, WZ, F, type)
   p := Characteristic (F);
   q := #F;

   /* construct a faithful action of Z */
   if Type (Z) eq GrpMat and q ne 3 then
      flag, G3, index1, cob1 := SmallestFaithful (Z, <"D", 4, #F>);
      if not flag then
	 error "OrthogonalGlue: SmallestFaithful failed";
      end if;
   else
      G3 := Z;
   end if;

   m := Ngens (G3);
   // assert m eq Ngens (Z);
   U := UserGenerators (G3);
   m := #U; assert m eq Ngens (Z);
   if q eq 3 then
      Index2 := [m-4, m-3, m-2, m-1, m, m-2];
      Index1 := [m-9, m-8, m-7, m-6, m-5, m-7];
   else
      Index2 := [m-5, m-4, m-3, m-2, m-1, m];
      Index1 := [m-11, m-10, m-9, m-8, m-7, m-6];
   end if;
   Base1 := [U[i] : i in Index1];
   Base2 := [U[i] : i in Index2];

   // set up Omega+(8, q) generators in G3
   E, W := MyRecogniseOmega8P (G3, F, "D");

   Base1Words := []; Base2Words := []; base1 := []; base2 := [];
   H3 := sub<Generic (G3) | E >;
   e := ClassicalStandardGenerators ("Omega+", 8, q);
   H := sub<GL(8, q) | e>;

   if q eq 3 then
      T := CompositionTree (H3);
      tau := CompositionTreeNiceToUser (H3);
      for i in [1..6] do
         flag, w := CompositionTreeElementToWord (H3, Base1[i]); 
         w := tau (w);
         Base1Words[i] := w;
         base1[i] := Evaluate (Base1Words[i], [e[i] : i in [1,2,3,4,5,8]]);
         flag, w := CompositionTreeElementToWord (H3, Base2[i]); 
         w := tau (w);
         Base2Words[i] := w;
         base2[i] := Evaluate (Base2Words[i], [e[i] : i in [1,2,3,4,5,8]]);
      end for;
   else
      for i in [1..6] do
         flag, w := ClassicalRewrite (H3, E, "Omega+", 8, q, Base1[i]); 
         if not flag then error "OrthogonalGlue: Failed rewrite"; end if;
         Base1Words[i] := w;
         flag, w := ClassicalRewrite (H3, E, "Omega+", 8, q, Base2[i]); 
         if not flag then error "OrthogonalGlue: Failed rewrite 2"; end if;
         Base2Words[i] := w;
         // Evaluate Base[1-2]Words on e to obtain their images in Omega+(8,q)
         base1[i] := Evaluate (Base1Words[i], e);
         base2[i] := Evaluate (Base2Words[i], e);
      end for;
   end if;

   // assert Evaluate (Base1Words, E) eq Base1;
   // assert Evaluate (Base2Words, E) eq Base2; 

   x1 := sub<GL(8, q) | [base1[i] : i in [1..6]] cat [base2[i] : i in [1..6]]>;
   // assert Ngens (x1) eq 12;

   M := GModule (x1);
   S := IndecomposableSummands (M);
   a, phi := sub<M | S[1]>;
   A := phi (Basis (a));

   b, phi := sub<M | S[2]>;
   B := phi (Basis (b));

   /* w1 and <w2, w3> are fixed by x1 */
   w := []; z := [];
   for i in [1..4] do
      w[i] := [A[i][j] : j in [1..8]];
      z[i] := [B[i][j] : j in [1..8]];
   end for;
   CB1 := GL(8, q)!(w cat z);

   x2 := x1^(CB1^-1);    
   block := ExtractBlock (x2.1, 1, 1, 4, 4); // x2.1 is an element of base1

   if (type in ["B", "2D"] and not (IsScalar (block))) or 
      (type eq "D" and IsScalar (block)) then
      // (type eq "D" and IsIdentity (block)) then
      CB1 := GL(8, q)! (z cat w);
      x2 := x1^(CB1^-1);
   end if;
   newbase1 := []; newbase2 := [];
   if type eq "D" then
      index1 := 1; index2 := 5;
   else
      index1 := 5; index2 := 1;
   end if;
   
   if q eq 3 then t := 5; else t := 6; end if;
   for i in [1..t] do
      newbase1[i] := GL(4,q)!ExtractBlock (x2.i, index1, index1, 4, 4);
      newbase2[i] := GL(4,q)!ExtractBlock (x2.(i + t), index2, index2, 4, 4);
   end for;

   cb1 := LineUpOmegaPlus4Generators (newbase1, F);
   cb2 := LineUpOmegaPlus4Generators (newbase2, F);

   cb1 := GL(4, q)!cb1; cb2 := GL(4, q)!cb2;
   if type eq "D" then
      CB2 := GL(8, q)!DiagonalJoin (cb1, cb2);
   else
      CB2 := GL(8, q)!DiagonalJoin (cb2, cb1);
   end if;
   cb := CB2 * CB1;

   flag, otype, form := OrthogonalForm (H^cb^-1);
   alpha := form[5][6]^-1;
   beta := form[7][8]^-1;
   c := GL(8, F)!DiagonalMatrix (F, [1, 1, 1, 1, alpha, 1, beta, 1]);
   COB := c * cb;
   flag, otype, form := OrthogonalForm (H^COB^-1);
   
   // Possible to compute a word in O+(4,q) instead of O+(8,q)?
   glue := GL(8, q)![1,0,0,0,0,0,0,0,  0,1,0,0,0,0,0,0, 
                     0,0,0,0,1,0,0,0,  0,0,0,0,0,1,0,0, 
                     0,0,-1,0,0,0,0,0, 0,0,0,-1,0,0,0,0, 
                     0,0,0,0,0,0,1,0,  0,0,0,0,0,0,0,1];
   flag, wglue := ClassicalRewrite (H, e, "Omega+", 8, q, glue^COB);
   if not flag then error "OrthogonalGlue: Failed rewrite 3"; end if;
   wglue := Evaluate (wglue, W);
   return wglue;
end function;

// revised orthogonal glue for q = 3 mod 4 
OrthogonalGlue := function (Z, WZ, F, type)
   p := Characteristic (F);
   q := #F;
   if q eq 3 then return SpecialOrthogonalGlue (Z, WZ, F, type); end if;

   /* construct a faithful action of Z */
   if Type (Z) eq GrpMat and q ne 3 then
      flag, G3, index1, cob1 := SmallestFaithful (Z, <"D", 4, #F>);
      if not flag then
	 error "OrthogonalGlue: SmallestFaithful failed";
      end if;
   else
      G3 := Z;
   end if;

   m := Ngens (G3);
   // assert m eq Ngens (Z);
   U := UserGenerators (G3);
   m := #U; assert m eq Ngens (Z);
   if q eq 3 then
      Index2 := [m-4, m-3, m-2, m-1, m, m-2];
      Index1 := [m-9, m-8, m-7, m-6, m-5, m-7];
   else
      Index2 := [m-5, m-4, m-3, m-2, m-1, m];
      Index1 := [m-11, m-10, m-9, m-8, m-7, m-6];
   end if;
   Base1 := [U[i] : i in Index1];
   Base2 := [U[i] : i in Index2];

   // set up Omega+(8, q) generators in G3
   //   E, W := MyRecogniseOmega8P (G3, F, "D");

   // set up Omega+(8, q) generators in G3
   f, E, W := Internal_RecogniseOmegaPlus8 (G3, #F);
   if not f then error "OrthogonalGlue: Failed Internal_RecogniseOmegaPlus8"; end if;

   Base1Words := []; Base2Words := []; base1 := []; base2 := [];
   e := ClassicalStandardGenerators ("Omega+", 8, q);
   H := sub<GL(8, q) | e>;
   for i in [1..6] do
      flag, w := ClassicalRewrite (G3, E, "Omega+", 8, q, Base1[i]); 
      if not flag then error "OrthogonalGlue: Failed rewrite"; end if;
      Base1Words[i] := w;
      flag, w := ClassicalRewrite (G3, E, "Omega+", 8, q, Base2[i]); 
      if not flag then error "OrthogonalGlue: Failed rewrite 2"; end if;
      assert flag;
      Base2Words[i] := w;
      // Evaluate Base[1-2]Words on e to obtain their images in Omega+(8,q)
      base1[i] := Evaluate (Base1Words[i], e);
      base2[i] := Evaluate (Base2Words[i], e);
   end for;

   x1 := sub<GL(8, q) | [base1[i] : i in [1..6]] cat [base2[i] : i in [1..6]]>;
   // assert Ngens (x1) eq 12;

   M := GModule (x1);
   S := IndecomposableSummands (M);
   a, phi := sub<M | S[1]>;
   A := phi (Basis (a));

   b, phi := sub<M | S[2]>;
   B := phi (Basis (b));
  
   Base := [Eltseq (a): a in A] cat [Eltseq (b): b in B];
   CB1 := GL(8, q)!Base;
   x2 := x1^(CB1^-1);    

   if type eq "B" or type eq "2D" then 
      L := [GL(4, q)! ExtractBlock (x2.i, 1, 1, 4, 4): i in [1..12]];
      list := [i : i in [1..12] | IsScalar(L[i])];
      if list eq [1,2,3,10,11,12] then
         vprint ClassicalRecognition: "zero case";
         p := GL(8, q) ! PermutationMatrix (F, [1,2,7,8,3,4,5,6]);
      elif list eq [4..9] then
         vprint ClassicalRecognition: "first case ...";
         p := GL(8, q) ! PermutationMatrix (F, [3,4,5,6,1,2,7,8]);
      elif list eq [7..12] then
         vprint ClassicalRecognition: "second case ...";
         p := GL(8, q) ! PermutationMatrix (F, [5,6,7,8,1,2,3,4]);
      elif list eq [4,5,6,10,11,12] then 
         vprint ClassicalRecognition: "third case ...";
         p := GL(8, q) ! PermutationMatrix (F, [3,4,7,8,1,2,5,6]);
      else
         assert list eq [1,2,3,4,5,6];
         vprint ClassicalRecognition: "identity case ...";
         p := Identity (GL(8, q));
      end if;
      CB1 := p * CB1; 
   elif type eq "D" then 
      L := [GL(4, q)! ExtractBlock (x2.i, 5, 5, 4, 4): i in [1..12]];
      list := [i : i in [1..12] | IsScalar(L[i])];
      if list eq [1..6] then 
         vprint ClassicalRecognition: "second case ...";
         p := GL(8, q) ! PermutationMatrix (F, [5,6,7,8,1,2,3,4]);
      else
         assert list eq [7..12]; 
         vprint ClassicalRecognition: "identity case ...";
         p := Identity (GL(8, q));
      end if;
      CB1 := p * CB1; 
   end if;

   x2 := x1^(CB1^-1);
   L := [GL(4, q)! ExtractBlock (x2.i, 1, 1, 4, 4): i in [1..12]];
   list := [i : i in [1..12] | IsScalar(L[i])];
   
   A := [GL(4, q) ! ExtractBlock (x2.i, 1, 1, 4, 4): i in [1..12]];
   vprint ClassicalRecognition: "Scalar list for A ", [i : i in [1..12] | IsScalar(A[i])];

   B := [GL(4, q) ! ExtractBlock (x2.i, 5, 5, 4, 4): i in [1..12]];
   vprint ClassicalRecognition: "Scalar list for B ", [i : i in [1..12] | IsScalar(B[i])];

   b1 := [x : x in A | IsScalar (x) eq false];
   x := Order (b1[2]);
   y := Order (b1[5]);
   if y gt x then
      b1[5] := b1[5]^2;
   elif x gt y then 
      b1[2] := b1[2]^2;
   end if;
   assert Order (b1[2]) eq Order (b1[5]);
   cb1 := LineUpOmegaPlus4Generators (b1, F);
   cb1 := GL(4, q)!cb1; 

   b2 := [x : x in B | IsScalar (x) eq false];
   x := Order (b2[2]);
   y := Order (b2[5]);
   if y gt x then
      b2[5] := b2[5]^2;
   elif x gt y then 
      b2[2] := b2[2]^2;
   end if;
   assert Order (b2[2]) eq Order (b2[5]);
   cb2 := LineUpOmegaPlus4Generators (b2, F);
   cb2 := GL(4, q)!cb2;

   CB2 := GL(8, q)!DiagonalJoin (cb1, cb2);

   cb := CB2 * CB1;

   x3 := x1^(cb^-1);

   // ensure that the form preserved by H^(cb^-1) is standard 
   flag, otype, form := OrthogonalForm (H^cb^-1);
   alpha := form[5][6]^-1;
   beta := form[7][8]^-1;
   c := GL(8, F)!DiagonalMatrix (F, [1, 1, 1, 1, alpha, 1, beta, 1]);
   COB := c * cb;

   // is x3 subset H^(COB^-1)? 
   flag, otype, form := OrthogonalForm (H^COB^-1);
   assert forall{i: i in [1..12] | form eq x3.i * form * Transpose (x3.i)}; 

   // Possible to compute a word in O+(4,q) instead of O+(8,q)?
   glue := GL(8, q)![1,0,0,0,0,0,0,0,  0,1,0,0,0,0,0,0, 
                     0,0,0,0,1,0,0,0,  0,0,0,0,0,1,0,0, 
                     0,0,-1,0,0,0,0,0, 0,0,0,-1,0,0,0,0, 
                     0,0,0,0,0,0,1,0,  0,0,0,0,0,0,0,1];
   flag, wglue := ClassicalRewrite (H, e, "Omega+", 8, q, glue^COB);
   if not flag then error "OrthogonalGlue: Failed rewrite 3"; end if;
   wglue := Evaluate (wglue, W);
   return wglue;
end function;

// base is standard SL2 gens; base[2] is transvection; base[3] is diagonal 
// find common eigenvector
GetBasisVector := function (base)
   Evt := Setseq (Eigenvalues (base[2]));
   assert #Evt eq 1;
   Evd := Setseq (Eigenvalues (base[3]));
   Vt := Eigenspace (base[2], Evt[1][1]);
   i := 0;
   repeat
      i +:= 1;
      v := Evd[i][1];
      Vd := Eigenspace (base[3], v);
      V := Vt meet Vd;
   until Dimension (V) eq 1 or i eq 3;
   if Dimension (V) ne 1 then error "Failure in SX4Glue: GetBasisVector"; end if;
   w := Basis (V)[1];
   ww := Eltseq (w);
   return ww, w; 
end function;

// base1 and base2 are standard SX(2, q) generators in SX(4, q) 
// compute standard basis for SX(4, q)
LineUpSL2s := function (base1, base2, F, type)
   v2, w2 := GetBasisVector (base1);
   v4, w4 := GetBasisVector (base2);
   if type in ["A", "C"] then
      v1 := Eltseq (-w2^base1[1]);
      v3 := Eltseq (-w4^base2[1]);
   elif type eq "2A" then
      p := Characteristic (F);
      E := GF(p, Degree (F) div 2);
      q := #E;
      gamma := PrimitiveElement (F);
      alpha := gamma^((q+1) div 2);
      v1 := Eltseq (alpha^q * (w2^base1[1]));
      v3 := Eltseq (alpha^q * (w4^base2[1]));
   end if;
   cb := GL(4, F)!(v1 cat v2 cat v3 cat v4);
   return cb;
end function;

// G3 is isomorphic to SX(4,q);
// Base1 and Base2 are subsets of standard SX(4,q) generators;
// they each generate SL(2, q);
// to compute a standard basis for SX(4,q) compute the images of 
// Base1 and Base2 in SX(4,q);
// return standard generators for G3, images of two SL(2, q)
ComputeImageOfSL2s := function (G3, F, type)

   m := Ngens (G3);
   // 2 copies of SX(2, q) in G3 
   Base1 := [G3.(m-5), G3.(m-4), G3.(m-3)];
   Base2 := [G3.(m-2), G3.(m-1), G3.m];

   FF := F;
   if type eq "A" then
      RecogniseSX4 := MyRecogniseSL4;
      newtype := "SL";
      e := ClassicalStandardGenerators ("SL", 4, #F);
   end if;

   if type eq "C" then
      RecogniseSX4 := MyRecogniseSp4;
      newtype := "Sp";
      e := ClassicalStandardGenerators ("Sp", 4, #F);
   end if;

   if type eq "2A" then
      p := Characteristic (F);
      FF := GF(p, Degree (F) div 2);
      q := #FF;
      RecogniseSX4 := MyRecogniseSU4;
      newtype := "SU";
      e := ClassicalStandardGenerators ("SU", 4, #FF);
   end if;

   e := [GL(4, F)!t: t in e];
   H := sub<GL(4, F) | e>;
   E, W := RecogniseSX4 (G3, F);

   Base1Words := [**]; Base2Words := [**]; base1 := [**]; base2 := [**];
   for i in [1..3] do
      flag, Base1Words[i] := ClassicalRewrite (G3, E, newtype, 4, #FF, Base1[i]);
      if not flag then error "ComputeImagesOfSL2: Failed rewrite"; end if;
      flag, Base2Words[i] := ClassicalRewrite (G3, E, newtype, 4, #FF, Base2[i]);
      if not flag then error "ComputeImagesOfSL2: Failed rewrite 2"; end if;
      base1[i] := Evaluate (Base1Words[i], e);
      base2[i] := Evaluate (Base2Words[i], e);
   end for;
   return E, W, base1, base2, H;
end function;

// compute the glue element in Z
SX4ForGlue := function (Z, WZ, F, n, type, FinalCall, IsMatrixGroup, IsOrthogonal)
   p := Characteristic (F);
   if type eq "2A" then
      E := GF(p, Degree (F) div 2);
      q := #E;
      e := Degree (E);
   else
      q := #F;
   end if;

   // construct a faithful action of Z 
   if IsMatrixGroup and not (IsOrthogonal) and q ne 3 then
      r := DegreeToRank (type, 4);
      flag, G3, index1, cob1 := SmallestFaithful (Z, <type, r, q>);
      if not flag then
         error "A SX4ForGlue: SmallestFaithful failed";
      end if;
   else
      G3 := Z;
   end if;

tt := Cputime ();

   // orthogonal glue element
   if IsOrthogonal then
      // construct isomorphism to Omega+(4, F) via standard generators E3 
      // and Omega rewriting
      U := UserGenerators (G3);
      m := #U;
      u := U[m - 1]; v := U[m];
      f, tau, _,_,_, E3, W3:=MyRecogniseOmegaPlus4 (G3, F: StandardOnly:=false);
      H3 := sub<Generic (G3) | E3>;

      e := ClassicalStandardGenerators ("Omega+", 4, #F); 
      H := sub<GL(4, q) | e>;
      CB := TransformForm (H: Restore := true);
      
      // compute images of u and v in standard Omega+4 
      u := Function (tau) (u);
      v := Function (tau) (v);
      u := u^(CB^-1); v := v^(CB^-1);

      // Diagonalise the elements u and v, and then compute the 
      // correct standard orthogonal basis
      Ev1 := [Setseq (Eigenvalues (u))[i][1] : i in [1..2]];
      Ev2 := [Setseq (Eigenvalues (v)) [i][1] : i in [1..2]];
      V1 := Eigenspace (u, Ev1[2]);
      V2 := Eigenspace (v, Ev2[2]);

      B1 := [Eltseq (x) : x in Basis (V1)];
      B2 := [Eltseq (x) : x in Basis (V2)];
      cb := GL(4, q)! (B1[1] cat B1[2] cat B2[1] cat B2[2]); 
      flag, otype, Hform := OrthogonalForm (H^cb^-1);

      index := 1;
      CB := Identity (H);
      for i in [1..2] do
         form := ExtractBlock (Hform, index, index, 2, 2);
         CBs := TransformForm (form, "orthogonalplus": Restore := true);
         InsertBlock (~CB, CBs, index, index);
         index +:= 2;
      end for;

      CB := GL(4,q)!(CB^-1);
      COB := CB * cb;
      // H now preserves the standard orthogonal form, 
      // so we can compute a word for the glue element in H
      flag, otype, form := OrthogonalForm (H); 
      glue := GL(4, q)![0, 0,1,0, 
                        0, 0,0,1, 
                       -1, 0,0,0, 
                        0,-1,0,0];
      found, wglue := ClassicalRewriteNatural ("Omega+", Identity (H), glue^COB);
      if not flag then error "SX4ForGlue: Failed rewrite 1"; end if;
      wglue := Evaluate (wglue, W3);
      // "total time to end of glue is ", Cputime (tt);
      return glue, wglue;
   end if;

   // E are standard generators for G3 
   // G3 contains 2 copies of SL(2, q)
   // base1 and base2 are their images in GL(4, q)
   E, W, base1, base2, H := ComputeImageOfSL2s (G3, F, type);

   //line up the SL2 generators in GL4
   cb := LineUpSL2s (base1, base2, F, type);

   // compute the glue element
   if type eq "A" then
      COB := cb;
      T := CompositionTree (H: KnownLeaf := true);
      tau := CompositionTreeNiceToUser (H);
      glue := GL(4, F)![1,0, 0,0, 
                        0,0,-1,0, 
                        0,1, 0,0, 
                        0,0, 0,1];
      found, wglue := ClassicalRewriteNatural ("SL", Identity (H), glue^COB);
      if not found then error "SX4ForGlue: Failed rewrite 2"; end if;
      wglue := Evaluate (wglue, W);
      return glue, wglue;
   end if;

   if type eq "C" then
      flag, form := MyClassicalForms (H^(cb^-1), "C");
      t := form[3][4];
      alpha := form[1][2]^-1;
      beta := form[3][4]^-1;
      COB2 := GL(4, F)!DiagonalMatrix (F, [alpha, 1, beta, 1]);
      COB := COB2 * cb;
      glue := GL(4, F)![0,0,1,0, 
                        0,0,0,1, 
                        1,0,0,0, 
                        0,1,0,0];
      found, wglue := ClassicalRewriteNatural ("Sp", Identity (H), glue^COB);
      if not found then error "SX4ForGlue: Failed rewrite 3"; end if;
      wglue := Evaluate (wglue, W);
      return glue, wglue;
   end if;

   if type eq "2A" and IsOdd (n) then
      flag, form := MyClassicalForms (H^(cb^-1), type);
      t := form[3][4];
      alpha := form[1][2]^-1;
      beta := form[3][4]^-1;
      COB2 := GL(4, F)!DiagonalMatrix (F, [alpha, 1, beta, 1]);
      COB := COB2 * cb;
      glue := GL(4, F)![0,0,1,0, 
                        0,0,0,1, 
                        1,0,0,0, 
                        0,1,0,0];
      found, wglue := ClassicalRewriteNatural ("SU", Identity (H), glue^COB);
      if not found then error "SX4ForGlue: Failed rewrite 4"; end if;
      wglue := Evaluate (wglue, W);
      // assert Evaluate (wglue, UserGenerators (H)) eq glue^COB;
      return glue, wglue;
   end if;

   if type eq "2A" then
      flag, form := MyClassicalForms (H^(cb^-1), type);
      a := form[1][2]; b := form[2][1]; assert a eq 1; assert b eq 1;
      c := form[3][4]; d := form[4][3];

      COB := cb;

      Base1A := [base1[i]^cb^-1 : i in [1..3]];
      Base2A := [base2[i]^cb^-1 : i in [1..3]];
      t1 := Base1A[2]; t2 := Base2A[2];
      x := t1[1][2]; y := t2[3][4];
      value := c^-1 * x^-1 * y;

      // glue must conjugate transvection t1 to t2: so t must be (q+1)st-root of value
      // glue must have determinant 1 so v^2 = t^-2, it must preserve form and have order 2
      // T := AllRoots (value, q + 1);
      T := [Root (value, q + 1)];
      for t in T do 
         // r := SquareRoot (t^-2);
         // for v in [r, -r] do 
         v := t^-1;
         glue := GL(4, F)! [0,0,t,0, 
                               0,0,0,t, 
                               v,0,0,0, 
                               0,v,0,0];
         // assert t1^glue eq t2; 
         // assert Determinant (glue) eq 1;
         found := glue * form * Transpose (FrobeniusImage (glue, e)) eq form 
                     and Order (glue) eq 2;
         if found then 
            found, wglue := ClassicalRewriteNatural ("SU", Identity (H), 
glue^COB);
            if not found then error "SX4ForGlue: Failed rewrite 5"; end if;
            wglue := Evaluate (wglue, W);
            return glue, wglue;
         end if;    
      end for;
      error "No solution found in SX4Glue for 2A case";
   end if;
end function;
