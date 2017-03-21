freeze;

function setup(X)
   // X: m by n matrix over Z 
   // returns: ideal I to be passed to solve

   m := NumberOfRows(X);
   n := NumberOfColumns(X);
   P := PolynomialRing(GF(2), n + m, "elim", n);
   AssignNames(~P, ["x" cat IntegerToString(i): i in [1 .. n]] cat
                   ["y" cat IntegerToString(i): i in [1 .. m]]);

   I := ideal<P | [P.(n + j) - &*[P.i^X[j][i]: i in [1 .. n]]: j in [1 .. m]]>;
   Groebner(I: Walk := false);

   return I;
end function;

function solve (I, W) 
   // I: ideal from setup
   // W: length n vector over Z 
   // returns: true and length m vector V such that V*X = W if possible, false
   //          otherwise

   P := Generic(I);
   n := NumberOfColumns(W);
   F := NormalForm(&*[P.i^W[i]: i in [1 .. n]], I); 
   if forall {j: j in [1 .. n] | Degree(F, j) eq 0} then
       return true, RSpace (Integers(), Rank(P) - n) !
           [Degree(F, j): j in [n + 1 .. Rank(P)]];
   end if;
   return false, 0;    
end function;

FindNonNegativeSolution := function (A, t)

   I := setup (A);
   a, b := solve (I, t);
   return a, b;

end function;
