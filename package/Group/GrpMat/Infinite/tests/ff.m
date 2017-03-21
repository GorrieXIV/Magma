freeze;

/* function field examples */

TestFF := function(n)
F<X,Y,Z>:= FunctionField(Rationals (),3);
G:= GL(n,F);
I := Integers ();
H:= GL(n,I);
MA:= MatrixAlgebra(F,n);

h1:= Id(MA);
h1[n][n]:= (X^2+Y+Z+1)/(Z^5-X^2*Z+Z*X*Y);
h1[1][n]:= X+1;
h1[1][1]:=(Z^5-X^2*Z+Z*X*Y)/(X^2+Y+Z+1);
h1[2][1]:=1-X*Y*Z;
h1[2][n]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;

h2:= Id(MA);
h2[n][n]:= (X^7+Z^6+1)/(Y^3+X^2+X+1);
h2[1][n]:= X^2+X+1;
h2[1][1]:=(Y^3+X^2+X+1)/(X^7+Z^6+1);
h2[2][1]:=1-X^2;
h2[2][n]:= X^50+Y^35+X^20+X^13+Y^2+1;

h3:= Id(MA);
h3[n][n]:= (X^17+X*Y^5+1)/(Z^2*Y^3*X^3+X^2+X+1);
h3[1][n]:= X^112+X;
h3[1][1]:=(Z^2*Y^3*X^3+X^2+X+1)/(X^17+X*Y^5+1);
h3[2][1]:=1-X^2;
h3[2][n]:= X^5*Z^10+X^3+X^2+X+1;

h4:= Id(MA);
h4[n][n]:= (X^7+X^5-X^90)/(X^3+X^2+X+1);
h4[1][n]:= X*Y^112+X^3;
h4[1][1]:=(X^3+X^2+X+1)/(X^7+X^5-X^90);
h4[2][1]:=1-X^230;
h4[2][n]:= X/(Z^100-1);

h5:= Id(MA);
h5[n][n]:= (Z^27+X^15-X^9)/(X^3-X^2-X+1);
h5[1][n]:= X^12+X^3+X+29;
h5[1][n-1]:= X^12+X^3+X+29;
h5[1][1]:=(X^3-X^2-X+1)/(Z^27+X^15-X^9);
h5[2][1]:=1-X^230;
h5[3][n]:= (X^91-X^7+13)/(X*Y^10-100*X*Y*Z^6);

h6:= Id(MA);
h6[n][n]:= (X^7+X^5-X^90)/(Y^3+X^2*Z^7+X+1);
h6[1][n]:= Z^112+X^3;
h6[1][1]:=(Y^3+X^2*Z^7+X+1)/(X^7+X^5-X^90);
h6[2][1]:=X^7-Z^23;
h6[2][n-1]:= X/(X^101-119*Y);

h7:= Id(MA);
h7[n][n]:= (X^7+X^5-Y^10*Z^90)/(X^3+X^2+X+1);
h7[1][n]:= X^53+X^35;
h7[1][1]:=(X^3+X^2+X+1)/(X^7+X^5-Y^10*Z^90);
h7[2][1]:=X^67-X^22;
h7[2][n-2]:= X/(Z^100-1);

h8:= Id(MA);
h8[n][n]:= (X^17-X^5+X^90)/(X^3+X^2+X+1);
h8[1][n-1]:= X^2+Z^3;
h8[1][1]:=(X^3+X^2+X+1)/(X^17-X^5+X^90);
h8[2][1]:=1-Y^230;
h8[2][n]:= X^5*Y/(Z*X^100-1);

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

/* algebraic function field examples */

TestAFF:= function(n)
R<u> := FunctionField (Rationals ());
P<y> := PolynomialRing (R);
f := u * y^3 + 3 * u^2 * y + 1;
F := ext < R | f >;
X := y; Y := -y; Z := 2 * y;

G:= GL(n,F);
MA:= MatrixAlgebra(F,n);
I := Integers ();
H := GL (n, I);

h1:= Id(MA);
h1[n][n]:= 
(Z^5-X^2*Z+Z*X*Y);
h1[1][n]:= X+1;
h1[1][1]:=(X^2+Y+Z+1);
h1[2][1]:=1-X*Y*Z;
h1[2][n]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;

h2:= Id(MA);
h2[n][n]:= (X^7+Z^6+1)*
(Y^3+X^2+X+1);
h2[1][n]:= X^2+X+1;
h2[1][1]:=(Y^3+X^2+X+1)*(X^7+Z^6+1);
h2[2][1]:=1-X^2;
h2[2][n]:= X^50+Y^35+X^20+X^13+Y^2+1;

h3:= Id(MA);
h3[n][n]:= (X^17+X*Y^5+1)*(Z^2*Y^3*X^3+X^2+X+1);
h3[1][n]:= X^112+X;
h3[1][1]:=(Z^2*Y^3*X^3+X^2+X+1)*(X^17+X*Y^5+1);
h3[2][1]:=1-X^2;
h3[2][n]:= X^5*Z^10+X^3+X^2+X+1;

h4:= Id(MA);
h4[n][n]:= (X^7+X^5-X^90)*(X^3+X^2+X+1);
h4[1][n]:= X*Y^112+X^3;
h4[1][1]:=(X^3+X^2+X+1)*(X^7+X^5-X^90);
h4[2][1]:=1-X^230;
h4[2][n]:= X*(Z^100-1);

h5:= Id(MA);
h5[n][n]:= (Z^27+X^15-X^9)*(X^3-X^2-X+1);
h5[1][n]:= X^12+X^3+X+29;
h5[1][n-1]:= X^12+X^3+X+29;
h5[1][1]:=(X^3-X^2-X+1)*(Z^27+X^15-X^9);
h5[2][1]:=1-X^230;
h5[3][n]:= (X^91-X^7+13)*(X*Y^10-100*X*Y*Z^6);

h6:= Id(MA);
h6[n][n]:= (X^7+X^5-X^90)*(Y^3+X^2*Z^7+X+1);
h6[1][n]:= Z^112+X^3;
h6[1][1]:=(Y^3+X^2*Z^7+X+1)*(X^7+X^5-X^90);
h6[2][1]:=X^7-Z^23;
h6[2][n-1]:= X*(X^101-119*Y);

h7:= Id(MA);
h7[n][n]:= (X^7+X^5-Y^10*Z^90)*(X^3+X^2+X+1);
h7[1][n]:= X^53+X^35;
h7[1][1]:=(X^3+X^2+X+1)*(X^7+X^5-Y^10*Z^90);
h7[2][1]:=X^67-X^22;
h7[2][n-2]:= X*(Z^100-1);

h8:= Id(MA);
h8[n][n]:= (X^17-X^5+X^90)*(X^3+X^2+X+1);
h8[1][n-1]:= X^2+Z^3;
h8[1][1]:=(X^3+X^2+X+1)*(X^17-X^5+X^90);
h8[2][1]:=1-Y^230;
h8[2][n]:= X^5*Y*(Z*X^100-1);

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
