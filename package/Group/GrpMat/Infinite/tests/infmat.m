InfRatGrp := function(n)

   n1 := n - 1;
   Q:= Rationals();
   MA:= MatrixAlgebra(Q,n);
   e:= Identity(MA);

   d:= Zero(MA);
   d[n][1]:= 1;
   for i in [1..n1] do
     d[i][i+1]:= 1;
   end for;

   a:=DiagonalMatrix( Q, [i : i in [1..n1]] cat [Factorial(n1)^-1] ); 
   b:=DiagonalMatrix(Q, Reverse([i : i in [1..n1]]) cat [Factorial(n1)^-1]); 
  // a:=DiagonalMatrix(Q, [x : x in [1..n1]] cat [1/Factorial(12)] );
  // b:=DiagonalMatrix(Q, Reverse([n : x in [1..n1]]) cat [1/Factorial(12)] );

   G:= sub<GL(n,Q)|a*d, b*d>;
   return G;

end function;

