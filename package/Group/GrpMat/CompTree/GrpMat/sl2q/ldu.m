freeze;

import "sl2.m": IsSL2Basis, SL2Basis, MyHom;

/* given a canonical generating set gens for (P)SL(2, q),
   write g as word in gens */

SL2ElementToSLP := function (G, g)
   
   if Determinant (g) ne 1 then return false; end if;

   Z := Integers ();
   E := BaseRing (Parent (g));

   SLB := SL2Basis (G);
   LB := SLB[1][1]; wLB := SLB[2][1];
   UB := SLB[1][3]; wUB := SLB[2][3];

//   cb := SLB[3];
//   h := g;

   /* primitive element for field */
   D := SLB[1][2]; 
   x := D[1][1];
   K := sub <E | x^2>;

   /* if necessary interchange columns by 
      premultiplying g by C = 0, 1, -1, 0 */
   if g[1][1] eq 0 or g[2][2] eq 0 then 
      B := UB[1]; wB := wUB[1];
      coeffs := Eltseq (K!(-1));
      coeffs := [Z!c: c in coeffs];
      // A1 := &*[LB[i]^coeffs[i]: i in [1..#coeffs]];
      wA1 := &*[wLB[i]^coeffs[i]: i in [1..#coeffs]];
      // C := B * A1; 
      wC := wB * wA1;
      coeffs := Eltseq (K!(1));
      coeffs := [Z!c: c in coeffs];
      // A2 := &*[UB[i]^coeffs[i]: i in [1..#coeffs]];
      wA2 := &*[wUB[i]^coeffs[i]: i in [1..#coeffs]];
      // C := C * A2; 
      wC := wC * wA2;
      C := GL(2, E) ! [0, 1, -1, 0];
      g := C * g; 
      word := wC^-1;
 //    LM := [C];
   else
//      LM := [LB[1]^0];
      word := wLB[1]^0; 
   end if;

   /* zero out 2, 1 entry of g */
   x := -(g[2][1] / g[1][1]);
   coeffs := Eltseq (K!x); coeffs := [Z!c: c in coeffs];
   A := &*[LB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wLB[i]^coeffs[i]: i in [1..#coeffs]];
   word *:= wA^-1;
//   Append (~LM, A);
   g := A * g; 

   /* zero out 1, 2 entry of g */
   x := -(g[1][2] / g[2][2]);
   coeffs := Eltseq (K!x); coeffs := [Z!c: c in coeffs];
   A := &*[UB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wUB[i]^coeffs[i]: i in [1..#coeffs]];
   word *:= wA^-1;
//   Append (~LM, A);

   g := A * g; 
   /* construct resulting diagonal matrix g as product of basis elements */
   a := g[1][1];
   c := a - 1;

 //  RM := [];
   /* construct 1, c, 0, 1 */
   coeffs := Eltseq (K!c); coeffs := [Z!c: c in coeffs];
   // A := &*[UB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wUB[i]^coeffs[i]: i in [1..#coeffs]];
   second := wA;
   // Append (~RM, A);

   /* construct 1 + c, c, 1, 1 via column operation */
   B := LB[1];
   wB := wLB[1];
   // C := A * B;
   second := second * wB;
   // Append (~RM, B);

   /* construct 1 + c, 0 , 1, (1 + c)^-1 by column operation */
   coeffs := Eltseq (K! (-c / (1 + c))); coeffs := [Z!c: c in coeffs];
   // A := &*[UB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wUB[i]^coeffs[i]: i in [1..#coeffs]];
   // Append (~RM, A);
   second := second * wA;
   // C := C * A; 

   /* finally construct 1 + c, 0, 0, (1 + c)^-1 by column operation */
   coeffs := Eltseq (K! (-1 / (1 + c))); coeffs := [Z!c: c in coeffs];
   // A := &*[LB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wLB[i]^coeffs[i]: i in [1..#coeffs]];
   second := wA * second;
   // Append (~RM, A);
   // C := A * C; 
   // assert h eq LM[1]^-1 * LM[2]^-1 * LM[3]^-1 * RM[4] * RM[1] * RM[2] * RM[3];
   word := word * second;
   return word;
   
end function;

OldSL2ElementToSLP := function (gens, rm) 

   flag, DM, LM, UM := IsSL2Basis (gens);
   if not flag then error "Basis not supplied"; end if;

   P := Parent (Rep (gens));
   F := BaseRing (P);
   q := #F;
   p := Characteristic (F);

   t := DM[1][1];  // Element t should be a primitive element of F 
   if not IsPrimitive (t) then error "Basis not supplied"; end if;

   x := LM[2][1]; // off-diagonal entry of lower-triangular generator L   
   y := UM[1][2]; // off-diagonal entry of upper-triangular generator U

   //  Define the three formal generators (for "word" purposes) 
   W<L, D, U> := SLPGroup (3);
   freegens := [L, D, U];

   // Define the corresponding three generator matrices 
   mgens := [LM, DM, UM];  

   // In the case where q is odd, and t is a primitive element of GF(q),  
   // find integers r and s such that  t = t^{2r} + t^{2s} 
   // for use later in finding suitable powers of L and U 

/* 
   if (q mod 2 eq 1) then 
tt := Cputime ();
     if exists (r){i: i in [0..q] | Log (t - t^(2*i)) mod 2 eq 0} then
"here we are";
"2";time         s := Log (t - t^(2*r)) div 2;
      else 
         error "No exponents r and s found";
      end if; 
   end if;
*/

tt := Cputime ();
   if IsOdd (q) then 
     for i in [0..q - 1] do 
        flag, root := IsSquare (t - t^(2 * i));
        if flag then 
           r := i; 
           s := Log (root);
           break;
        end if;
    end for;
  end if;
"time to here is", Cputime (tt);

   // If top left entry zero then multiply by UM^{-1} 
   // otherwise leave matrix as is

   if (rm[1][1] eq 0) then 
      wordseq := [3, 1]; mx := UM^-1 * rm;
   else 
      wordseq := []; mx := rm;
   end if;

   a := mx[1][1]; b := mx[1][2];
   c := mx[2][1]; d := mx[2][2];

   // Echelonisation easily gives LDU - decomposition of matrix 
   // [ a  b ]  as  [  1       0 ] [ a    0    ] [ 1  a^{-1}b ]
   // [ c  d ]      [ a^{-1}c  1 ] [ 0  a^{-1} ] [ 0    1     ]
   // and now need to express each of the 3 RHS matrices in terms 
   // of the given generators L, D and U 

   if (q mod 2 eq 0) then 
      if (c ne 0) then 
"3";   time       px := Log (x^-1*a^-1*c);  
          if (px mod 2 eq 0) then 
             px2 := px div 2; 
          else 
             px2 := (px + q - 1) div 2;
          end if;
          wordseq := wordseq cat [2, - px2, 1, 1, 2, px2];
      end if;
      // px2 chosen so that xt^{2px2} = a^{-1}c
      // to give 1st matrix as D^{-px2}LD^{px2} 
"4";time      py := Log (a); wordseq := wordseq cat [2, py];
      // py chosen so that t^{py} = a
      // to give 2nd matrix as D^{py} 
      if (b ne 0) then 
"5"; time         pz := Log (a^-1*b*y^-1);
         if (pz mod 2 eq 0) then 
            pz2 := pz div 2; 
         else 
            pz2 := (pz + q - 1) div 2;
         end if;
         wordseq cat:= [2, pz2, 3, 1, 2, -pz2];
      end if;
      // pz2 chosen so that t^{2pz2}y = a^{-1}b
      // to give 3rd matrix as D^{pz2}UD^{-pz2} 
   else 
      if (c ne 0) then
         px := Log (x^-1*a^-1*c);
         if (px mod 2 eq 0) then 
            px2 := px div 2;
            wordseq cat:= [2, -px2, 1, 1, 2, px2];
            // px2 chosen so that xt^{2px2} = a^{-1}c
            // to give 1st matrix as D^{-px2}LD^{px2} 
         else 
            pxr := r + ((px - 1) div 2);
            pxs := s + ((px - 1) div 2);
            wordseq cat:= [2, - pxr, 1, 1, 2, pxr - pxs, 1, 1, 2, pxs];
         end if;
      end if;
      // pxr and pxs chosen so xt^{2pxr} + xt^{2pxs} = a^{-1}c
      // to give 1st matrix as (D^{-pxr}LD^{pxr})(D^{-pxs}LD^{pxs}) 
      py := Log (a); wordseq := wordseq cat [2, py];
      // py chosen so that t^{py} = a
      // to give 2nd matrix as D^{py} 
      if (b ne 0) then 
         pz := Log (a^-1*b*y^-1);
         if (pz mod 2 eq 0) then 
            pz2 := pz div 2;
            wordseq cat:= [2, pz2, 3, 1, 2, -pz2];
            // pz2 chosen so that t^{2pz2}y = a^{-1}b
            // to give 3rd matrix as D^{pz2}UD^{-pz2} 
         else 
            pzr := r + ((pz - 1) div 2); 
            pzs := s + ((pz - 1) div 2); 
            wordseq cat:= [2, pzr, 3, 1, 2, - pzr + pzs, 3, 1, 2, - pzs];
         end if;
      end if;
      // pzr and pzs chosen so t^{2pzr}y + t^{2pzs}y = a^{-1}b
      // to give 3rd matrix as (D^{pzr}UD^{-pzr})(D^{pzs}UD^{-pzs}) 
   end if; 

   checkmatrix := Id (P); checkword := Id (W);
   for i in [1..(#wordseq div 2)] do 
       checkmatrix *:= mgens[wordseq[2*i - 1]]^wordseq[2*i];
       checkword   *:= freegens[wordseq[2*i - 1]]^wordseq[2*i];
   end for;
   assert checkmatrix eq rm;

   K := sub <GL(2, F) | mgens>;
   tau := MyHom (K, W, mgens);
   assert tau (checkword) eq rm;

   return checkword, tau;

end function;
