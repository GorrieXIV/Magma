freeze;

import "numbers.m": ProperDivisors;

/* compute a hash value for a collection of objects S,
   and return result modulo prime M */

HashSet := function (S, M)

   h := &+[Hash (T) : T in S];
   return h mod M + 1;

end function;

/* does h commute with all elements of X? */

ElementCommutes := function (h, X)

   id := h^0;
   return forall {x : x in X | (x, h) eq id};

end function;

/* first non-zero entry of B */

FirstNonZeroEntry := function (B)

   if B eq Zero (Parent (B)) then return false, false; end if; 

   E := Eltseq (B);

   index := 0;
   
   repeat index +:= 1; until E[index] ne 0;
   
   return E[index], index;

end function;

/* is f a n-th power of some polynomial? */

IsPowerOfPolynomial := function (f, n)

   factors := Factorisation (f);
   // vprint Smash: "factorisation of char poly of element is ", factors;

   mults := {factors[i][2] : i in [1..#factors]};

   return forall {y : y in mults | y mod n eq 0}, factors;

end function;

procedure DeletePair (~List, d, r)

   Exclude (~List, r);
   Exclude (~List, d div r);

end procedure;

procedure Swap (~x, i, j)

   local temp;

   temp := x[j];
   x[j] := x[i];
   x[i] := temp;

end procedure;

/* bubble sort sequences x and length in parallel according to
   increasing order on length */

procedure BubbleSort (~length, ~x)

   local i, j, swap, temp, len;

   swap := true;
   len := #x;

   i := 1;
   while (i le len and swap) do
      swap := false;
      for j in [len..i + 1 by -1] do
         if (length[j] lt length[j - 1]) then
            swap := true;
            Swap (~x, j - 1, j);
            Swap (~length, j - 1, j);
         end if;
      end for;
      i +:= 1;
   end while;

end procedure;

/* bubble sort sequences x and length in parallel according to
   decreasing order on length */

procedure ReverseBubbleSort (~length, ~x)

   local i, j, swap, temp, len;

   swap := true;
   len := #x;

   i := 1;
   while (i le len and swap) do
      swap := false;
      for j in [len..i + 1 by -1] do
         if (length[j] gt length[j - 1]) then
            swap := true;
            Swap (~x, j - 1, j);
            Swap (~length, j - 1, j);
         end if;
      end for;
      i +:= 1;
   end while;

end procedure;

/* evaluate polynomial f in matrix A */

EvaluateImage := function (f, A)

   local M, B;

   M := MatrixAlgebra (BaseRing (Parent (A)), Degree (Parent (A)));
   B := M!A;
   return Evaluate (f, B);

end function;

/* find space of V centralised by g mod W */

CentralisedMod := function (G, g, W) 

   F := BaseRing (G);
   d := Degree (G);
   V := VectorSpace (F, d);
   Al := MatrixAlgebra (F, d);
   A := Al!g - Identity (Al);
   Q, f := quo < V | W >;
   x := &cat[Eltseq (f(V.i)): i in [1..Ngens (V)]];
   R := RMatrixSpace (F, d, Dimension (Q));
   x := A * R!x;
   K := Kernel (x);
   return K;

end function;

/* find space centralised by g */

CentralisedSpace := function (g)

   G := Parent (g);
   F := CoefficientRing (G);
   A := MatrixAlgebra (F, Degree (G));

   a := A!g;
   N := NullSpace (a - Identity (A));
   vprint Smash: "Nullspace has dimension ", Dimension (N);

   return N;

end function;

/* find space centralised by collection of elements, S */

CentralisedSpaceSet := function (S)

   C := [CentralisedSpace (g) : g in S];
   Common := C[1];
   for i in [2..#C] do
      Common := Common meet C[i];
   end for;

   return Common;

end function;

/* find space centralised by collection of elements, S, mod space W */

CentralisedSpaceSetMod := function (G, S, W)

   C := [CentralisedMod (G, g, W) : g in S];
   Common := C[1];
   for i in [2..#C] do
      Common := Common meet C[i];
   end for;

   return Common;

end function;

ComplementSpace := function (g)

   G := Parent (g);
   F := CoefficientRing (G);
   f<x> := MinimalPolynomial (g);

   facs := Factorisation (f);
   factors := [facs[i][1] : i in [1..#facs]];

   pos := Position (factors, x - 1);
   rem := pos eq 0 select f else f div (facs[pos][1]^facs[pos][2]);
 
   h := EvaluateImage (rem, g);
   
   A := MatrixAlgebra (F, Degree (G));

   a := A!h;
   N := NullSpace (a);
   vprint Smash: "Complement has dimension ", Dimension (N);

   return N;

end function;

ComplementSpaceSet := function (S)

    return &+[ComplementSpace (g) : g in S];

end function;

/* return set of non-trivial commutators of elements in S */

FormCommutators := function (S)

   return #S eq 0 select {} else
         {(S[i], S[j]) : j in [i + 1..#S], i in [1..#S]} diff {S[1]^0};

end function;

/* if power of an element in Elements is also in Elements, remove it */

procedure EliminateRepetitions (~Elements, ~Orders)

   if #Elements le 1 then return; end if;

   i := 0;
   repeat
      i +:= 1;
      g := Elements[i];
      o := Orders [i];
      D := ProperDivisors (o);
      for x in D do
         h := g^x;
         index := Position (Elements, h);
         if index ne 0 then
            Remove (~Elements, index);
            Remove (~Orders, index);
         end if;
      end for;
   until i eq #Elements;

end procedure;
