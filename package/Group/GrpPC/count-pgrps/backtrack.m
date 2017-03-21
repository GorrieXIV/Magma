freeze;
/* earlier version of conjugacy class code is now replaced
   by Scott's version */
   
FACTOR := 100;

/* number of occurrences of each integer in partition */

PartitionMultiplicities := function (part)

   return [#[x: x in part | x eq i] : i in [1..Maximum (part)]];

end function;

BackTrack := function (M)

   if Set (M) eq {1} then return [M]; end if;

   n := #M;
   m := [1 : i in [1..n + 1]];

   IndexList := [i: i in [1..#M] | M[i] ge 2];
   len := #IndexList;
   Append (~IndexList, n + 1);

   Solns := [];
   repeat
      index := 1;
      m[IndexList[index]] +:= 1;
      while (index le len and m[IndexList[index]] gt M[IndexList[index]]) do
         m[IndexList[index]] := 1;
         index +:= 1;
         m[IndexList[index]] +:= 1;
      end while;
      Append (~Solns, Prune (m));
   until (index gt len);

   return Solns;

end function;

IndecomposableMatrix := function (F, C, c, I, k, b)

   base := k * c;

   MA := MatrixAlgebra (F, b * base);
   A := Zero (MA);

   MJ := MatrixAlgebra (F, base);
   J := Zero (MJ);

   for j in [1..k] do
      index := c * (j - 1) + 1;
      InsertBlock (~J, C, index, index);
      if j lt k then 
         InsertBlock (~J, I, c * j + 1, index);
      end if;
   end for;

   for j in [1..b] do
      index := (j - 1) * c * k + 1;
      InsertBlock (~A, J, index, index);
   end for;

   return A;

end function;

/* given a particular partition Gamma and the companion matrices C 
   for each of the monic irreducible polynomials of degree
   at most d, write down a conjugacy class representative */

ClassRep := function (G, C, Gamma)

   F := BaseRing (G);
   d := Degree (G);

   A := MatrixAlgebra (F, d);
   R := Zero (A); offset := 1;

   for i in [1..#Gamma] do 
      if #Gamma [i] ne 0 then 
         gamma := Gamma[i] cat [0];
         c := Degree (Parent (C[i]));
         I := Identity (MatrixAlgebra (F, c));
         for k in [1..#gamma - 1] do 
            b := gamma[k] - gamma[k + 1];
            J := IndecomposableMatrix (F, C[i], c, I, k, b); 
            InsertBlock (~R, J, offset, offset); 
            offset +:= Degree (Parent (J));
         end for;
      end if;
   end for;

   return R;

end function;

DSequence := function (m)

   d := [];
   for index in [1..#m] do 
      one := index gt 1 select &+[m[i] * i: i in [1..index - 1]] else 0;  
      two := (&+[m[i]: i in [index..#m]]) * index;
      d[index] := one + two;
   end for;

   return d;

end function;

FormProduct := function (q, mdeg, m, d)
   
   fac := q^mdeg;
   x := [[(fac^(d[i]) - fac^(d[i] - k)) : k in [1..m[i]]] : i in [1..#m]];
   return &*(&cat(x));

end function;

/* given irreducible polynomials and partition gamma 
   which determines a class rep, determine class size */

ClassLength := function (P, q, gamma)

   total := 1;
   for i in [1..#gamma] do 
      if #gamma [i] eq 0 then continue; end if;
      lambda := DualPartition (gamma[i]);
      m := PartitionMultiplicities (lambda);
      mdeg := Degree (P[i]);
      d := DSequence (m);
      total *:= FormProduct (q, mdeg, m, d);
   end for;

   return total;
   
end function;

/* write down reps of conjugacy classes of GL (d, q);
   also determine size of each class */

MyConjugacyClassesGL := function (d, q) 

   if d lt 1 then 
      error "ClassReps: Argument 1 (", d ,") must be at least 1";
   end if;

   if IsPrimePower (q) eq false then 
      error "ClassReps: Argument 2 (", q ,") is not a prime-power";
   end if;

   gl := GL (d, q);
   order := OrderGL (d, q);

   F := BaseRing (gl);

   /* irreducible monic polynomials of degree at most d - 1 */
   Poly := &join[AllIrreduciblePolynomials (F, k) : k in [1..d - 1]];
   Poly := SetToSequence (Poly);  
   Sort (~Poly);
   vprint User1: "# irreducible polynomials to consider is ", #Poly;

   /* which linear combinations of the degrees sum up to d? */ 
   Degrees := [Degree (poly): poly in Poly];
   M := [d div Degrees[i] : i in [1..#Poly]];
   t := Cputime ();

   /* companion matrices for each polynomial */
   Comp := [* *];
   for i in [1..#Poly] do
      Comp[i] := CompanionMatrix (Poly[i]);
   end for; 

   t := Cputime ();
   /* required partitions */
   Parts := [Partitions (delta) : delta in [0..d]];
   Reps := []; NmrElts := 0; NmrReps := 0;

   /* for each class rep, determine the number of fixed spaces */
   nn := #M;
   lenm := nn + 1;
   delta := [0 : i in [1..lenm]];
   M[lenm] := 0;
   Degrees[lenm] := 0;

   x := 0;
   repeat 
      index := 1;
      delta[index] +:= 1;
      x +:= Degrees[index];
      while (index le nn and (delta[index] gt M[index] or x gt d)) do
         x -:= delta[index] * Degrees[index];
         delta[index] := 0;
         index +:= 1;
         delta[index] +:= 1;
         x +:= Degrees[index];
      end while;

      if x eq d then 

         IndexList := [i : i in [1..#delta] | delta[i] gt 0];
         Gamma := [Parts [delta[i] + 1] : i in IndexList]; 
         nmr := [#Gamma[i]: i in [1..#Gamma]]; 
         P := [Poly[i] : i in IndexList];
         C := [* *]; for i in IndexList do Append (~C, Comp[i]); end for;

         L := BackTrack (nmr);
         Gamma := [[Gamma[i][L[j][i]]: i in [1..#L[j]]]: j in [1..#L]];

         for gamma in Gamma do
            R := ClassRep (gl, C, gamma);
            if Determinant (R) ne 0 then 
               NmrReps +:= 1;
               if NmrReps mod FACTOR eq 0 then 
                  vprint User1: "Processing representative %o\n", NmrReps;
               end if;
               len := order div ClassLength (P, q, gamma);
               NmrElts +:= len;
               Append (~Reps, <gl!R, len>);
            end if;
         end for;

      end if;
   until (index gt nn);

   /* now deal with polynomials of degree d */
   P := SetToSequence (AllIrreduciblePolynomials (F, d));

   for i in [1..#P] do
      gamma := [[1]];
      C := CompanionMatrix (P[i]);
      R := ClassRep (gl, [C], gamma);
      if Determinant (R) ne 0 then 
         NmrReps +:= 1;
         if NmrReps mod FACTOR eq 0 then 
            vprintf User1: "Processing representative %o\n", NmrReps;
         end if;
         len := order div ClassLength ([P[i]], q, gamma);
         NmrElts +:= len;
         Append (~Reps, <gl!R, len>);
      end if;
   end for;
      
   assert NmrElts eq order;

   return Reps;

end function;
