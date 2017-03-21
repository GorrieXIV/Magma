freeze;

/* code to decompose V \otimes V^\delta representation of H where 
   SL(d, q) \leq Class(d,q) \leq GL(d, q) 
   Kay Magaard, Eamonn O'Brien, and Akos Seress 

   Non-SL cases added July 2013 
   Brian Corr and Eamonn O'Brien
*/

import "construct.m": MyDeltaRepresentation;

import "reduce.m": ReduceGeneratingSet;

import "basics.m": getExtensionDegree, ChooseSingerElt, ScalarMultiple, 
   ScaleMatrix2, ScaleMatrix, FindScalarMultipleOverSubfield, fixSigns,
   IdentifyForm, SatisfiesForm, FixForm; 

FindEigenspacesSL := function (G, e, s, ev, TypeString) 
   n := Degree (G);
   flag, d := IsSquare (n);
   F := BaseRing (G);
   q := #F;
   E := GF(q^d);
   p := Characteristic (F);

   EV := &join(ev);
   MA := MatrixAlgebra (E, d);
   for f in ev do
      if #f eq 1 then continue; end if; 
      v := f[1]; 
      C := [x: x in EV | v^(q + 1) / x in EV and x^(1 + p^e) eq v^(1 + q * p^e)];
      /* candidates for l_1 l_2 */
      C := [x : x in C | not x in [f[1], f[2]]];
      // vprint SmallDegree: "Length of C is ", #C;
      if #C eq 0 then continue; end if;

      good := true;
      first := {@ v^(q^j): j in [0..d - 1] @};
      L := Zero (MA);
     
      /* diagonal entries */
      for i in [1..d] do 
         L[i][i] := first[i]; 
      end for;
      
      Original := L;
      for c in C do 
         L := Original;
         L[1][2] := c;
         L[2][1] := L[1][1] * L[2][2] / L[1][2];
         for i in [2..d - 1] do
            L[i][i + 1] := L[i - 1][i]^q;
         end for;
         L[d][1] := L[d - 1][d]^q;
         for i in [2..d - 1] do
            L[i + 1][1] := (L[1][1] * L[i][i] * L[i + 1][i + 1]) /(L[i][i + 1] * L[1][i]);
            if not (L[i+1][1] eq L[1][1] * (L[2][1] / L[1][1])^((q^i - 1) div (q - 1))) then 
               good := false; continue c; 
            end if;
            L[1][i + 1] := L[1][1] * L[i + 1][i + 1] / L[i+1][1];
         end for;
         for i in [3..d - 1] do
            for j in [1..d - i] do
               L[j + 1][j + i] := L[j][j + i - 1]^q;
            end for;
         end for;
         for i in [2..d - 1] do
            for j in [2..d - i + 1] do
               L[i - 1 + j][j] := L[i - 2 + j][j - 1]^q;
            end for;
         end for;
      end for;
      if good and (Set(Eltseq(L)) eq Set(EV)) then 
         break f;
      end if;
   end for;
   
   try 
      L := Eltseq (L);
      ES := [Eigenspace (s, e).1: e in L];
      CB := GL(n, E) ! &cat ([Eltseq (x): x in ES]);
      return true, CB, CB^(-1);
   catch e;
      return false,_,_;
   end try;
end function;

FindEigenspacesSOOdd := function (G, e, s, ev, TypeString) 
   n := Degree (G);
   flag, d := IsSquare (n);
   F := BaseRing (G);
   q := #F;
   dprime := d-1;
   E := GF(q^dprime);
   p := Characteristic (F);
   EV := &join(ev);
   MA := MatrixAlgebra (E, d);

   for f in ev do 
      v := f[1]; 
      if #f eq 1 then continue; end if;
      L := Zero (MA);

      for i in [1..dprime] do
         for j in [1..dprime] do
            val := v^(q^(i-1) + p^e *q^(j-1));            
            if not val in EV then continue f; end if;
            L[i][j] := val;
         end for;
         val := v^(q^(i-1));            
         if not val in EV then continue f; end if;
         L[i][d] := val;
         val := v^(p^e*q^(i-1));            
         if not val in EV then continue f; end if;
         L[d][i] := val;
      end for;
      L[d][d] := 1;
      break;
   end for;

   try
      L := Eltseq (L);
      ES := [Eigenspace (s, e).1: e in L];
      CB := &cat ([Eltseq (x): x in ES]);
      CB := GL (n, E) ! CB;   
      if (Determinant(CB) eq 0) then return false, _,_; end if;
      CB := MatrixAlgebra ( E,n) ! CB;
      return true, CB, CB^(-1);
   catch e;
      return false, _,_;
   end try;
end function;

FindEigenspacesSOPlus := function (G, e, s, ev, TypeString) 
   n := Degree (G);
   flag, d := IsSquare (n);
   F := BaseRing (G);
   q := #F;
   dprime := d-2;
   E := GF(q^dprime);
   p := Characteristic (F);

   EV := &join(ev);
   MA := MatrixAlgebra (E, d);

   //four candidates for m1^(1+p^e)
   twos := &join([x: x in ev | #x eq 2]);

   //try all 4
   for t in [1..#twos] do
      roots := AllRoots (twos[t], p^e+1);
      if #roots eq 0 then continue t; end if;

      for s in [1..#roots]^Random(SymmetricGroup(#roots)) do
         m1 := roots[s];
         if not (m1^(1+q*p^e) in twos and m1^(q+p^e) in twos and m1^(q+q*p^e) in twos) then
            continue s;
         end if;

         m1l1 := [x[1]: x in ev | x[1]/m1 * m1^q in &join(ev) and #x gt 2];
         if #m1l1 eq 0 then continue s; end if;

         m1l1 := m1l1[1];
         m2l1 := m1l1/m1 * m1^q;

         L := Zero (MA);
         L[d-1][1] := m1l1;
         L[d][1] := m2l1;

         for i in [2..dprime] do
            L[d][i] := L[d-1][i-1]^q;
            L[d-1][i] := L[d][i-1]^q;
         end for;

         powerofl1 := m1l1*m2l1;
         l1squared := powerofl1^(q^dprime div (p^e));
         l1 := Sqrt(l1squared);
   
         m2 := m1^q;
         l1m1 := l1 * m1^(p^e);

         if not l1m1 in EV then l1m1 := -l1m1; end if;
         if not l1m1 in EV then continue s; end if;

         L[1][d-1] := l1m1;   
         l1m2 := l1 * m2^(p^e);
         if not l1m2 in EV then l1m2 := -l1m2; end if;
         if not l1m2 in EV then continue s; end if;

         L[1][d] := l1m2;
         for i in [1..dprime] do
            for j in [1..dprime] do
               val := l1^(q^(i-1) + p^e *q^(j-1));
               if not val in EV then continue s; end if;
               L[i][j] := val;
            end for;
            if i eq 1 then continue; end if;
            L[i][d] := L[i-1][d-1]^q;
            L[i][d-1] := L[i-1][d]^q;
         end for;
   
         val := m1*m1^(p^e);
         if not val in EV then val := -val; if not val in EV then continue s; end if; end if;
         L[d-1][d-1] := val;

         val := m1*m2^(p^e);
         if not val in EV then val := -val; if not val in EV then continue s; end if; end if;
         L[d-1][d] := val;

         val := m2*m1^(p^e);
         if not val in EV then val := -val; if not val in EV then continue s; end if; end if;
         L[d][d-1] := val;

         val := m2*m2^(p^e);
         if not val in EV then val := -val; if not val in EV then continue s; end if; end if;
         L[d][d] := val;

         //if we reach this point then all the eigenvalues are labelled
         if n eq #Set(Eltseq(L)) then break t; end if;
      end for;
   end for;
   
   try 
      L := Eltseq (L);
      ES := [Eigenspace (s, e).1: e in L];
      CB := MatrixAlgebra (E, n)!&cat ([Eltseq (x): x in ES]);
      CB := GL (n, E) ! CB;
      return true, CB, CB^(-1);
   catch e;
      return false, _,_;
   end try;
end function;

FindIndex := function (i, j, d)
   return (i - 1) * d + j;
end function;

FindRatio := function (K, A, C, p, e, i, j, k, l)
   d := Nrows (A);
   a := FindIndex (i, j, d);
   b := FindIndex (k, l, d);
   c := FindIndex (j, j, d);
   e := FindIndex (j, l, d);
   f := FindIndex (i, k, d);
   g := FindIndex (k, k, d);
   if (C[k][k] * K[c][e] * K[f][g] * A[k][k] ne 0) then 
      return (C[j][j] * K[a][b] * K[g][g] * A[j][j])/(C[k][k] * K[c][e] * K[f][g] * A[k][k]);
   else 
      return false;
   end if;
end function;

/* G is tensor product; e is degree of Frobenius */
 
DetermineConstants := function (G, CB, CBinv, e, TypeString: Hard := Hard)
   F := BaseRing (G);
   n := Degree (G);
   d := Isqrt (n);
   q := #F;
   p := Characteristic (F);
   dprime := getExtensionDegree (d, TypeString);

   R := RandomProcess (G);
   P := Parent (CB);

   repeat 
      g := Random (R);
      K := CB * P ! g * CB^-1;
      
      index := FindIndex (1, 1, d);
      /* a_11^(p^e + 1) */
      k := K[index][index];

      E := GF (q^dprime);
      MA := MatrixAlgebra (E, d);

      A := Zero (MA);
      // vprint SmallDegree: "Polynomial test ...";
      PR<x> := PolynomialRing (E);
      f := x^(p^e + 1) - k;
      has_root, root := HasRoot (f);
   until &*[K[i][i]: i in [1..d]] ne 0 and K[1][2] ne 0 and has_root;

   w := PrimitiveElement (E);

   // Limit := 100;
   // if (Hard eq false and p^e + 1 gt Limit) then MaxNmr := Limit; else MaxNmr := p^e + 1; end if;
   // "MaxNmr is ", MaxNmr;
   MaxNumber := p^e + 1;

   for a11 in [root] do 
      A[1][1] := a11;
      for i in [2..d] do
          index := FindIndex (i, 1, d);
          ell := K[index][index];
          r := (ell / k);
          A[i][i] := A[1][1] * r;
      end for;

      for k in [0..MaxNumber] do 
         vprint SmallDegree: "Delta k is ", k;
         C := Zero (MA);
         C[1][1] := w^k;
         for i in [2..dprime] do
            C[i][i] := C[i - 1][i - 1]^q;
         end for;
      
         // record (p^e + 1)-th power of A[i][j] 
         i := 1; j := 2;
         a := FindIndex (1, 1, d);
         b := FindIndex (1, 2, d);
         c := FindIndex (2, 2, d);
         P12 := (K[b][c] * K[a][b]) / (A[j][j]^(p^e) * A[i][i]) * C[j][j] / C[i][i];
         a := FindIndex (1, 2, d);
         b := FindIndex (2, 2, d);

         if (P12 eq 0) then continue k; end if;
         if (A[2][2] eq 0) then continue k; end if;

         X := K[a][b]^(p^e + 1) * C[2][2]^(p^e + 1) / (P12 * A[2][2]^(p^e*(p^e + 1)));

         //"All roots computation ";
         RR := AllRoots (X, p^e + 1);

         for r in RR do
            C[1][2] := r;
            for ell in [3..dprime] do 
               MyRatio := FindRatio (K, A, C, p, e, 1, 2, ell, ell);
               if MyRatio cmpeq false or MyRatio eq 0 then continue r; end if;
               C[1][ell] := C[1][2] * C[1][ell - 1]^q / (C[ell][ell] * MyRatio);
            end for;
            C[2][1] := C[1][dprime]^q;
      
            /* check */
            MyRatio := FindRatio (K, A, C, p, e, 1, 2, 1, 1);
            if MyRatio cmpeq false or MyRatio eq 0 then continue r; end if;
            if C[1][1] ne C[1,2] * C[2,1] / (C[1,1] * MyRatio) then 
               continue r; 
            end if;

            for j in [2..dprime - 1] do
               C[j][j + 1] := C[j - 1][j]^q;
            end for;
            C[dprime][1] := C[dprime - 1][dprime]^q;

            for ell in [3..dprime] do 
               for j in [2..dprime + 1 - ell] do
                  C[j][j + ell - 1] := C[j - 1][j + ell-2]^q;
               end for;
               C[dprime + 2 - ell][1] := C[dprime + 1 - ell][dprime]^q;
               for j in [dprime + 3 - ell..dprime] do
                  C[j][j -(dprime + 1 - ell)] := C[j - 1][j - (dprime + 1 - ell) - 1]^q;
               end for;
            end for;

            //if dprime is d-1 then compute c_d1 
            if (dprime le d-1) then
               i := d;
               j := 1;
               if K[2][FindIndex(i,j,d)] eq 0 then continue r; end if;
               power := (C[1][2]^(1+p^e) * K[1][FindIndex(i,i,d)] * 
                             K[FindIndex(2,2,d)][FindIndex(j,j,d)]^(p^e) / (K[2][FindIndex(i,j,d)]^(1+p^e)));
               PR<x> := PolynomialRing (E);
               f := x^(1 + p^e) - power;
               has_root, root := HasRoot (f); 
               if not has_root then continue r; end if;
               C[d][1] := root;
            end if;
            if (dprime le d-2) then
               i := d-1;
               j := 1;
               if K[2][FindIndex(i,j,d)] eq 0 then continue r; end if;
               power := (C[1][2]^(1+p^e) * K[1][FindIndex(i,i,d)] * 
                             K[FindIndex(2,2,d)][FindIndex(j,j,d)]^(p^e) / (K[2][FindIndex(i,j,d)]^(1+p^e)));
               PR<x> := PolynomialRing (E);
               f := x^(1 + p^e) - power;
               has_root, root := HasRoot (f); 
               if not has_root then continue r; end if;
               C[d-1][1] := root;
            end if;
            return true, C;
         end for;
      end for;
   end for;
   return false, _;
end function;

/* decompose g in G; CB is change-of-basis;
   C is matrix of constants; e is degree of Frobenius */
Reconstruct := function (G, g, C, CB, CBinv, e, q, TypeString)
   F := BaseRing (G);
   n := Degree (G);
   d := Isqrt (n);
   p := Characteristic (F);

   dprime := getExtensionDegree (d, TypeString);

   P := Parent (CB);

   K := CB * P!g * CBinv;

   index := FindIndex (1, 1, d);
   /* a_11^(p^e + 1) */
   k := K[index][index];

   E := BaseRing (P);

   MA := MatrixAlgebra (GF(q^dprime), d);

   A := Zero (MA);
   // choose a root to give a_11 
   PR<x> := PolynomialRing (GF(q^dprime));
   f := x^(p^e + 1) - k;
   found, root := HasRoot (f);
   if not found then return false, _; end if;

   A[1][1] := root;

   for i in [1..d] do
      index := FindIndex (i, 1, d);
      ell := K[index][index];
      if k eq 0 then return false, _; end if;
      r := (ell / k);
      A[i][i] := A[1][1] * r;
   end for;
   
   for i in [1..dprime] do 
      for j in [1..dprime] do 
         if i eq j then continue; end if;
         a := FindIndex (i, j, d);
         b := FindIndex (j, j, d);
         if A[j][j] eq 0 then return false, _; end if;
         A[i][j] := (K[a][b] * C[j][j]) / (C[i][j] * A[j][j]^(p^e));
      end for;
   end for;

   if dprime le d-1 then 
      for i in [1..dprime] do
         A[i][d] := K[FindIndex(i,1,d)][FindIndex(d,1,d)] * C[d][1]/(C[i][1] * A[1][1]^(p^e));
         A[d][i] := K[FindIndex(d,1,d)][FindIndex(i,1,d)] * C[i][1]/(C[d][1] * A[1][1]^(p^e));
      end for;
   end if;

   if dprime eq d-2 then
      for i in [1..dprime] do
         A[i][d-1] := K[FindIndex(i,1,d)][FindIndex(d-1,1,d)] * C[d-1][1]/(C[i][1] * A[1][1]^(p^e));
         A[d-1][i] := K[FindIndex(d-1,1,d)][FindIndex(i,1,d)] * C[i][1]/(C[d-1][1] * A[1][1]^(p^e));
      end for;
      i := d;
      A[i][d-1] := K[FindIndex(i,1,d)][FindIndex(d-1,1,d)] * C[d-1][1]/(C[i][1] * A[1][1]^(p^e));
      A[d-1][i] := K[FindIndex(d-1,1,d)][FindIndex(i,1,d)] * C[i][1]/(C[d-1][1] * A[1][1]^(p^e));
   end if;

   return true, A;
end function;

TryReconstruct := function (G, g, C, CB, CBinv, e, q, TypeString, trials, tryWithoutRandomElt)
   if tryWithoutRandomElt then
      flag, A := Reconstruct (G, g, C, CB, CBinv, e, q, TypeString);
      if flag then return true, A; end if;
   end if;

   for i in [1..trials] do
      h := Random(G);
      flag1, A1 := Reconstruct (G, g*h^(-1), C, CB, CBinv, e, q, TypeString);
      if (flag1 eq false) then continue; end if;
      flag2, A2 := Reconstruct (G, h, C, CB, CBinv, e, q, TypeString);
      if (flag2 eq false) then continue; end if;
      return true, A1*A2;
   end for;
   return false, _;
end function;

FixScalars := function (G, A, q, e, TypeString: Limit := Maximum (Ngens (G) * 10000, q), 
      fct := MyDeltaRepresentation, Hard := true)
   N := GModule (G);
   K := BaseRing (N);

   M := fct (A, e);

   // possible that G is defined over a smaller field than A 
   if BaseRing (M) ne K then 
      vprint SmallDegree: "Groups defined over different fields";
      flag, M := IsOverSmallerField (M, Degree (K));
      if not flag or BaseRing (M) ne K then 
         error "FixScalars failure"; 
      end if;
   end if;

   M := GModule (M);
   if IsIsomorphic (N, M) then 
      vprint SmallDegree: "No scaling needed in FixScalars"; 
      return true, A; 
   end if;

   if Hard then Limit := 10^3; end if;
//   if Hard eq false then return true, A; end if;

   vprint SmallDegree: "Work harder to fix scalars ...";
   d := Degree (A);

   // an attempt to resolve the scalars problems -- does not work
   /* 
   NmrGens := 3;
   if Ngens (A) gt NmrGens then
      qq := TypeString eq "2A" select Isqrt (q) else q;
      found, B := ReduceGeneratingSet (G, TypeString, d, qq);
      if found then return true, B; 
      end if;
   end if;
   */

   F := GF(q);
   p := Characteristic (F);
   MA := MatrixAlgebra (F, d);

   gens := [MA!A.i: i in [1..Ngens (A)]];
   myRootsOfUnity := AllRoots (One (GF(q)), d*(p^e + 1));
   myRootsOfUnity := AllRoots (One (GF(q)), d);
   vprint SmallDegree: "Number of roots of units is ", #myRootsOfUnity;
   nmr := 0;
   repeat
         nmr +:= 1;
         if nmr mod 1000 eq 0 then vprint SmallDegree: "FixScalars nmr is ", nmr; end if;
         myList := gens;
         for i in [1..Ngens(A)] do
            myList[i] := myList[i] * ScalarMatrix (d, Random (myRootsOfUnity));
         end for;
         // rescale generators to have determinant 1 
         myList := [ScaleMatrix (myList[i]): i in [1..#myList]];
         myGrp := sub<Generic (A) | myList>;
         M := fct (myGrp, e);
         // possible that G is defined over a smaller field than A 
         if BaseRing (M) ne K then
            flag, M := IsOverSmallerField (M, Degree (K));
            if not flag or BaseRing (M) ne K then 
               error "FixScalars failure"; 
            end if;
         end if;
         M := GModule (M);
         found := IsIsomorphic (N, M);
   until found or nmr gt Limit;

   if found then 
        vprint SmallDegree: "Number to fix scalars and Frobenius degree are ", nmr, e; 
        return true, myGrp;
   else 
        vprint SmallDegree: "FixScalars failed"; 
        return false, _;
   end if;
end function;

RecogniseDelta := function (GG, TypeString, q: FrobeniusDegree := [], NumberRandom := 100, Hard := true)
   vprint SmallDegree: "Trying to recognise G as the Frobenius case";
   G := GG;
   n := Degree (G);
   p := Characteristic (BaseRing (G));
   flag, d := IsSquare (n);
   dprime := getExtensionDegree (d, TypeString);
   if flag eq false then 
      vprint SmallDegree: "Representation is not the Frobenius square"; 
      return false, _;
   end if;
   
   if (#BaseRing(G) ne q) then
      if (#BaseRing(G) lt q) then 
         G := sub<GL(n,q) | [G.i : i in [1..Ngens (G)]]>; 
      else 
         flag, K := IsOverSmallerField (G);
         if flag then 
            G := K;
         else   
            vprint SmallDegree: "Recognition for Delta failed: "
             cat "This is not the correct field size.";
            return false, _;
         end if;
      end if;
   end if;

   FormTrial := Hard eq true select 10^7 else 10^4; 
   counter := 0; outer := 0;
   repeat
      outer +:= 1;
      repeat
         counter +:= 1;
         vprint SmallDegree: "\nSelect special element ", counter;
         found, s, ev, ones := ChooseSingerElt (G, TypeString, d);
         if found eq false then
            vprint SmallDegree: 
               "Could not find a special element: Representation is probably not the Frobenius square of" , TypeString;
            return false, _;
         end if;

         F := BaseRing (G);
         f := Degree (F);
         if TypeString eq "2A" then f := f div 2; end if;
         if FrobeniusDegree cmpeq [] then 
            for deg in [1..f - 1] do 
               vprint SmallDegree: "Trying Frobenius degree ", deg;
               if (TypeString eq "B" or (TypeString eq "2A" and IsEven (d))) then
                  found, CB, CBinv := FindEigenspacesSOOdd (G, deg, s, ev, TypeString);
               elif (TypeString eq "D") then
                  found, CB, CBinv := FindEigenspacesSOPlus (G, deg, s, ev, TypeString);
               else
                  found, CB, CBinv := FindEigenspacesSL (G, deg, s, ev, TypeString);
               end if;
               if found then e := deg; break; end if;
            end for;
         else
            if Type (FrobeniusDegree) cmpeq SeqEnum and #FrobeniusDegree eq 1 then 
               FrobeniusDegree := FrobeniusDegree[1];
            end if;
            if not (FrobeniusDegree in [1..f - 1]) then return false, _, _; end if;
            if (TypeString eq "B" or (TypeString eq "2A" and IsEven (d))) then
               found, CB, CBinv := FindEigenspacesSOOdd (G, FrobeniusDegree, s, ev, TypeString);
            elif (TypeString eq "D") then
               found, CB, CBinv := FindEigenspacesSOPlus (G, FrobeniusDegree, s, ev, TypeString);
            else
               found, CB, CBinv := FindEigenspacesSL (G, FrobeniusDegree, s, ev, TypeString);
            end if;
            if found then e := FrobeniusDegree; end if;
         end if;
         if not found then continue; end if;

         vprint SmallDegree: "Eigenspaces found. Frobenius degree is", e;
         found, C := DetermineConstants (G, CB, CBinv, e, TypeString: Hard := Hard);
         vprint SmallDegree: "Succeeded in labelling constants? ", found;
      until found or counter gt NumberRandom;

      if found eq false then
         vprint SmallDegree: 
         "Could not find the constants Cij: Representation is probably not the Frobenius square of type" , TypeString;
         return false, _;
      else 
         vprint SmallDegree: "Constants Cij have been computed.";
      end if;

      X := [];
      for i in [1..Ngens(G)] do
         flag, MyGen := TryReconstruct (G, G.i, C, CB, CBinv, e, q, TypeString, NumberRandom, true);
         if (Determinant (MyGen) eq 0) then break i; end if;
         MyGen := ScaleMatrix (MyGen);
         if MyGen cmpeq false then break i; end if;
         Append (~X, MyGen);
      end for;
      
      good := false;
      if #X eq Ngens (G) then 
         H := sub <GL(d, q^dprime) | X>;
         if IsAbsolutelyIrreducible (H) then 
            flag, A := IsOverSmallerField (H, Degree(BaseRing(G)): Scalars := true);
         else 
            flag := false;
         end if;
         if not flag then
            vprint SmallDegree: "Recognition for delta representation:"
               cat "Representation cannot be written over smaller field";
            return false, _;
         end if;
         good := #BaseRing(A) eq q;
      end if;
   until good or outer gt NumberRandom;

   if not good then return false, _; end if;

   gens := [ScaleMatrix (A.i) : i in [1..Ngens (A)]];
   A := sub<GL(d, q) | gens>;


   //find and store a form defining our group (for testing preimage)
   found, A, form := FixForm (A, TypeString: FormTrial := FormTrial);

   if TypeString ne "A" and not found then
      vprint SmallDegree:
         "Construction of preimage failed. Input group is probably not Frobenius representation of ", TypeString;
      return false, _;
   end if;

   gens := [ScaleMatrix (A.i) : i in [1..Ngens (A)]];
   A := sub<GL(d, q) | gens>;

   SCB := H`SmallerFieldChangeOfBasis;

   vprint SmallDegree: "Delta: Frobenius degree e = ", e;
   vprint SmallDegree: "Delta: Now FixScalars ...";
   found, A := FixScalars (GG, A, q, e, TypeString : Hard := Hard);
   if not found then return false, _; end if;

   GG`SmallDegree := <"DeltaSquare", CB, CBinv, e, C, SCB, SCB^(-1), TypeString, form, q, A>;
   return true, A;
end function;

DeltaPreimage := function (G, g, limit: NumberRandom := 100)
   vprint SmallDegree: "Computing preimage (Frobenius case)";
   R := G`SmallDegree; 
   CB := R[2]; CBinv := R[3]; e := R[4]; C := R[5]; SCB := R[6]; SCBinv := R[7]; 
   TypeString := R[8]; form := R[9]; A := R[11]; q := R[10]; 

   for count in [1..limit] do
      flag, h := TryReconstruct (G, g, C, CB, CBinv, e, q, TypeString, NumberRandom, count eq 1); 
      if not flag then return false, _; end if;
      if Determinant (h) eq 0 then continue count; end if;

      // write the matrix over the subfield
      im := SCBinv*h*SCB;
      im := ScaleMatrix2 (im);
      if (im cmpeq false) then continue count; end if;

      im := FindScalarMultipleOverSubfield (im, GF(q));
      if (im cmpeq false) then continue count; end if;

      im := ScaleMatrix(im);
      im := GL(#Rows(im), BaseRing(im))!im;

      if TypeString eq "A" then 
         return true, im;
      elif TypeString eq "2A" then    
         F := BaseRing (G);
         deg := Degree (F) div 2;
         q := Isqrt (#F);
         if form cmpeq false or im * form * Transpose (FrobeniusImage (im, deg)) eq form then 
            return true, im;
         else 
            myRootsOfUnity := AllRoots (One (BaseRing(im)), #Rows(im));
            for myRoot in myRootsOfUnity do
               mat := im * ScalarMatrix (#Rows(im), myRoot);
               if form cmpeq false or mat * form * Transpose (FrobeniusImage (mat, deg)) eq form then 
                  return true, GL(#Rows(im), BaseRing(im)) ! mat;
               end if;
            end for;
         end if;
      elif TypeString in ["B", "D", "2D", "C"] and im * form * Transpose (im) eq form then 
         return true, im;
      else 
         myRootsOfUnity := AllRoots (One (BaseRing(im)), #Rows(im));
         for myRoot in myRootsOfUnity do
            mat := im * ScalarMatrix (#Rows(im), myRoot); 
            if form cmpeq false or mat * form * Transpose (mat) eq form then 
               return true, GL(#Rows(im), BaseRing(im)) ! mat;
            end if;
         end for;
      end if;
   end for;
   vprint SmallDegree: "Construction of preimage failed."; 
   return false, _;
end function;
