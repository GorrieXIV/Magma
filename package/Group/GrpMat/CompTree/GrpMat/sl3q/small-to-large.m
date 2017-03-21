freeze;

/* standard generators for root groups of SL(3, q) */

function StandardMatrices(F, S)
   z := F.1;
   p := Characteristic(F);
   e := Degree(F);
   M := MatrixAlgebra(F, 3);
   
   L := [];

   offset := 1;
   B := [];
   for i in [0..e - 1] do
      b := Identity(M);
      b[2][1] := z^(i);
      Append(~B, <z^i, b, S.(offset + i)>);
   end for;
   L[1] := B;

   offset := 1 * e + 1;
   B := [];
   for i in [0..e - 1] do
      b := Identity(M);
      b[3][2] := z^(i);
      Append(~B, <z^i, b, S.(offset + i)>);
   end for;
   L[2] := B;

   offset := 2 * e + 1;
   B := [];
   for i in [0..e - 1] do
      b := Identity(M);
      b[3][1] := z^(i);
      Append(~B, <z^i, b, S.(offset + i)>);
   end for;
   L[3] := B;

   offset := 3 * e + 1;
   B := [];
   for i in [0..e - 1] do
      b := Identity(M);
      b[1][2] := z^(i);
      Append(~B, <z^i, b, S.(offset + i)>);
   end for;
   L[4] := B;

   offset := 4 * e + 1;
   B := [];
   for i in [0..e - 1] do
      b := Identity(M);
      b[2][3] := z^(i);
      Append(~B, <z^i, b, S.(offset + i)>);
   end for;
   L[5] := B;

   offset := 5 * e + 1;
   B := [];
   for i in [0..e - 1] do
      b := Identity(M);
      b[1][3] := z^(i);
      Append(~B, <z^i, b, S.(offset + i)>);
   end for;
   L[6] := B;

   return L;
end function; 

/* given matrices corresponding to basis for particular root
   group, construct matrix corresponding to label */

ConstructRootElement := function (Labels, label: Words := true)
   Mats := [Labels[i][2]: i in [1..#Labels]];
   Z := Integers ();
   coeffs := Eltseq (label);
   coeffs := [Z!c: c in coeffs];
   if Words eq true then 
      Words := [Labels[i][3]: i in [1..#Labels]]; 
      return &*[Mats[i]^(Z!coeffs[i]) : i in [1..#Mats]],
          &*[Words[i]^(Z!coeffs[i]) : i in [1..#Mats]];
   else 
      return &*[Mats[i]^(Z!coeffs[i]) : i in [1..#Mats]], _;
   end if;
end function;

/* Carter Elements Chapter 12 */
nElement := function (F, Labels, index, t: Words := true)
   Inverses := [4,5,6,1,2,3];
   inv := Inverses[index];
   a, wa := ConstructRootElement (Labels[inv], F!t: Words := Words);
   b, wb := ConstructRootElement (Labels[index], (F!-t)^-1: Words := Words);
   if Words then 
      return a * b * a, wa * wb * wa;
   else 
      return a * b * a, _;
   end if;
end function;

/* Carter Elements Chapter 12 */
hElement := function (F, Labels, index, t: Words := true)
   x, wx := nElement (F, Labels, index, t: Words := Words);
   y, wy := nElement (F, Labels, index, -1: Words := Words);
   if Words then 
      return x * y, wx * wy;
   else
      return x * y, _;
   end if;
end function;

function SetupSL3StandardConstructiveMembership(G, F)
   e := Degree(F);
   W := SLPGroup(6 * e);
   S := StandardMatrices(F, W); 

   /* delta */
   //delta, wdelta := hElement (F, S, 1, omega: Words:=true);
   
   /* u */ 
   u1, wu1 := hElement (F, S, 1, -1: Words:=true); 
   a, wa := nElement (F, S, 1, 1: Words:=true); 
   u := (a * u1); wu := (wa * wu1);
   u := G!u;
   
   /* v */ 
   v1, wv1 := hElement (F, S, 1, -1: Words:=true); 
   a, wa := nElement (F, S, 1, 1: Words:=true); 
   b := a * v1; wb := wa * wv1;
   c, wc := nElement (F, S, 2, 1: Words:=true); 
   v := (c^-1 * b); wv := wc^-1 * wb;
   v := G!v;
   
   S := [[GL(3, F)! S[i][j][2]: j in [1..e]]: i in [1..#S]];  

   return [* S, u, v, wu, wv, W *];
end function;

/* return element A as SLP in generators of root subgroups of G */

RowColOpIdx := [[6, 1, 3],
		[4, 6, 2],
		[6, 5, 6]];

function SL3StandardConstructiveMembership(G, data, element)
    A := element;

   d := Degree(G);
   F := BaseRing(G);
   e := Degree(F);
   S := data[1];
   u := data[2];
   v := data[3];
   wu := data[4];
   wv := data[5];
   W := data[6];
   omega := PrimitiveElement (F);

   V, inc := VectorSpace(F, PrimeField(F));
   
   S1 := W!1;
   S2 := W!1;
   
   RowOp := function(i, j, A, r)
      n := RowColOpIdx[i][j];
      return G!S[n][r]*A;
   end function;
   
   RowOpp := function(i, j, S, r)
      n := RowColOpIdx[i][j];
      return W.(e*(n-1) + r)*S;
   end function;
   
   ColOp := function(i, j, A, r)
      n := RowColOpIdx[i][j];
      return G!(A*S[n][r]);
   end function;
   
   ColOpp := function(i, j, S, r)
      n := RowColOpIdx[i][j];
      return S*W.(e*(n-1) + r);
   end function;
   
   // get 1 in the (1, 1) entry of element A 
   
   R := IntegerRing();
   Z := ZeroMatrix(F, d, d);
   y := ZeroMatrix(R, d, 1);
   Z2 := ZeroMatrix(F, d, 2);
   
   for k in [1..d-1] do
   
      A := G!A;
      A := A^((v^-1)^(k-1)); 
      // moves the first, second, kth  column and row out of the way
      
      S1 := (wv)^(k-1)*S1;
      S2 := S2*((wv^-1)^(k-1));
      
      if A[1, 1] eq 0 then
         i := 2;
         while A[1, i] eq 0 do
            i +:= 1;
         end while;
         A := A*(u*v^-1)^(i-2)*(u*v)^(i-2)*u; 
         // swaps column 1 with column i, this will never move 
         // any columns that have already been done because they 
         // will always contain a 0 in the first row at this stage.
         S2 := S2*(wu*wv^-1)^(i-2)*(wu*wv)^(i-2)*wu;
         y[k, 1] := i;
      end if;
      
      if A[1, 1] ne 1 then
         i := 2; 
         if {A[i, 1] eq 0 : i in [2..d]} eq {true} then
            A := A*(S[4][1]^u);
            S2 := S2*(W.(1+ e*3)^wu);
         end if;
         while A[i, 1] eq 0 do 
            i +:= 1;
         end while;
         BB := (A[1, 1]-1)/A[i, 1];
         T := G!S[4][1]^-1;
         TT := W.(1+e*3)^-1;
         T := (T^(((v*u)^(i-2))))^R!inc(BB)[1];
         TT := (TT^(((wv*wu)^(i-2))))^R!inc(BB)[1];
         Z2[k, 1] := inc(BB)[1]; 
         for r in [2..e] do
            T := T*((G!(S[4][r]^-1)^(((v*u)^(i-2))))^R!inc(BB)[r]); 
            TT := TT*(((W.(e*3+r)^-1)^(((wv*wu)^(i-2))))^R!inc(BB)[r]);
         end for;
         A := T*A;
         S1 := TT*S1;
      end if;
      
      for j in [2..d-(k-1)] do
         for r in [1.. e] do 
            // needs to go up to the power of the characteristic of the field
            while inc(A[j, 1])[r] ne 0 do
               A := RowOp(1, j, A, r);
               Z[j +(k-1), k] := Z[j+(k-1), k] +omega^(r-1);
               S1 := RowOpp(1, j, S1, r); 
            end while;
         end for;
      end for;
      
      for j in [2..d-(k-1)] do
         for r in [1.. e] do
            while inc(A[1, j])[r] ne 0 do
               A := ColOp(j, 1, A, r);
               Z[k, j+(k-1)] := Z[k, j+(k-1)] + omega^(r-1);
               S2 := ColOpp(j, 1, S2, r);
            end while;
         end for;
      end for;
      A := G!A;
      
      A := A^(v^(k-1)); 
      // moves the rows and columns back to their original position
      
      S1 := ((wv^-1)^(k-1))*S1;
      S2 := S2*(wv^(k-1));      
   end for;
      
   return IsIdentity(A), (S1^-1*S2^-1);
end function;

function SL3SmallToLargeNew(data, h, rootElts)
    H := data`StdCopy;
    F := CoefficientRing(H);    
    flag, slp := SL3StandardConstructiveMembership(H, data`StandardRootData, h);
    assert flag;
    return Evaluate(slp, rootElts);
end function;
  
