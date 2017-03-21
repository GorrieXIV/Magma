

PositiveTestAFF:= function(n,q);

/*n should be greater than 10 to be safe with the
definition of the infinite order matrices*/

 R<X> := FunctionField(GF(q));
  P<Y> := PolynomialRing(R);
  F<alpha> := FunctionField(Y^2 - 1/X);

// F<X>:= FunctionField(GF(q));

G:= GL(n,F);

H:= GL(n,GF(q));

MA:= MatrixAlgebra(F,n);


h1:= Id(MA);

h1[n][n]:= (Y^2+1)/(X^5-X^2+X);

h1[1][n]:= X+1;

h1[1][1]:=(Y^5-Y^2+Y)/(X^2+1);

h1[2][1]:=1-X;

h1[2][n]:= Y^20+X^15+X^10+X^5+1;


h2:= Id(MA);

h2[n][n]:= (Y^7+Y^6+1)*(Y^3+X^2+X+1);

h2[1][n]:= X^2+Y+1;

h2[1][1]:=(X^3+Y^2+X+1)/(X^7+X^6+1);

h2[2][1]:=1-Y^2;

h2[2][n]:= Y^50+X^35+X^20+X^13+X^2+1;


h3:= Id(MA);

h3[n][n]:= (Y^17+X^5+111111)/(X^3+X^2+X+1);

h3[1][n]:= Y^112+X;

h3[1][1]:=(Y^3+X^2+X+1)/(X^17+X^5+111111);

h3[2][1]:=1-Y^2;

h3[2][n]:= X^5+Y^3+X^2+X+1;


h4:= Id(MA);

h4[n][n]:= (X^7+X^5-X^90)/(X^3+X^2+X+1);

h4[1][n]:= X^112+X^3;

h4[1][1]:=(X^3+X^2+X+1)/(X^7+X^5-X^90);

h4[2][1]:=1-Y^230;

h4[2][n]:= Y/(X^1000-1);


h5:= Id(MA);

h5[n][n]:= (X^27+X^15-X^9)/(X^3-X^2-X+1);

h5[1][n]:= X^12+X^3+X+29;

h5[1][n-1]:= X^12+X^3+X+29;

h5[1][1]:=(X^3-X^2-X+1)/(X^27+X^15-X^9);

h5[2][1]:=1-X^230;

h5[3][n]:= (X^91-X^7+13)/(X^10-100*X);


h6:= Id(MA);

h6[n][n]:= (X^7+X^5-X^90)/(X^3+X^2+X+1);

h6[1][n]:= X^112+X^3;

h6[1][1]:=(X^3+X^2+X+1)/(X^7+X^5-X^90);

h6[2][1]:=X^7-X^23;

h6[2][n-1]:= X/(X^101-119*X);


h7:= Id(MA);

h7[n][n]:= (X^7+X^5-X^90)/(X^3+X^2+X+1);

h7[1][n]:= X^53+X^35;

h7[1][1]:=(X^3+X^2+X+1)/(X^7+X^5-X^90);

h7[2][1]:=X^67-X^22;

h7[2][n-2]:= X/(X^1000-1);


h8:= Id(MA);

h8[n][n]:= (X^17-X^5+X^90)/(X^3+X^2+X+1);

h8[1][n-1]:= X^2+X^3;

h8[1][1]:=(X^3+X^2+X+1)/(X^17-X^5+X^90);

h8[2][1]:=1-X^230;

h8[2][n]:= X/(X^1000-1);


l:= [];

for i in [1..Ngens(H)] do;
l:= Append(l,MA!H.i);
end for;

lit:= [];

for x in l do;
lit:= Append(lit,h1*x*h1^-1);
end for;

triu:= sub<G|lit>;

triu2:= sub<G|lit,h1,h2, h3, h4, h5, h6, h7, h8>;

return triu, triu2;

end function;

