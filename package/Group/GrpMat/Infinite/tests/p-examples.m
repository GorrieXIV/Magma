
SetVerbose ("CompositionTree", 0);
SetVerbose ("Infinite", 1);

SetEchoInput (true);

q := 5^2;

Q := GF (5^2);
 F<t>:= RationalFunctionField (Q);
 M:= MatrixAlgebra (F, 3);
 a:= M![-1, 2*t^2, -2*t^4 - 2*t^3 - 2*t^2, 0, 1, 0, 0, 0, 1];
 b:= M![1, 0, 0, 1/t^2, -1, (2*t^3 - 1)/(t - 1), 0, 0, 1];
 c:= M![t, -t^3 + t^2, t^5 - t^2 - t, t^2, -t^4, (t^8 - t^5 + 1)/(t^2 -
t), (t - 1)/t, -t^2 + t, t^4 - t];
 G:= sub<GL(3,F)|a,b,c>;
time f := IsFinite(G);
f;
IsSolubleByFinite (G);

 F<t>:= RationalFunctionField (Q);
 M:= MatrixAlgebra (F, 6);
 a:= M![2, 2*t^2, 4, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0,
0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1];
 b:= M![(4*t + 4)/t, 4*t, (t + 1)/t, 0, t, t^2 + t, 0, 4, 0, 0, 0,
1/t, 4/t, t^2 + 4*t, 1/t, 0, 0, 0, 0, 4*t, 0, 0, 0, 0, 0, 0, 4, 4,
0, 0, 0, 0, 0, 4, 0, 0];
 G:= sub<GL(6,F)|a,b>;
time f := IsFinite(G);
f;
IsSolubleByFinite (G);

F<t>:= RationalFunctionField (Q);
M:=MatrixAlgebra (F, 2);
a := M![t,0,1,t];
b := M![t^2 + t + 1, t, 0, 1];
c:= M![t/(t^2 + t + 1),0,1,1/t];
A := sub <M | a, b, c>;
H := sub <GL(2, F) | a, b, c>;
time f :=IsFinite (H);
f;
IsSolubleByFinite (H);

F<t, u>:= RationalFunctionField (Q, 2);
M:= MatrixAlgebra (F, 2);
a := M![t * u,0,1,t/(t * u + t + 1)];
b := M![t^2 + t + 1, t, 0, 1];
c:= M![t/(u * t^2 + t + u ),0,u,(u * t^2 + t)/t];
A := sub <M | a, b, c>;
H := sub <GL(2, F) | a, b, c>;
time f :=IsFinite (H);
f;
IsSolubleByFinite (H);


d := 8;
F := GF(q);
K<t>:= RationalFunctionField (F, 1);
S := ScalarMatrix (K, d, t); 
T := ScalarMatrix (K, d, -t); 
G := sub <GL(d, K) | S, T>;
time f :=IsFinite(G);
f;
IsSolubleByFinite (G);

d := 2;
F := GF(q);
K<t>:= RationalFunctionField (F, 1);
G := sub<GL(2, K) |  [1/t, 1/(t+ 1), 1, 1]>;
time f :=IsFinite(G);
f;
IsSolubleByFinite (G);

d := 3;
F := GF (q);
K<t, u>:= RationalFunctionField (F, 2);
G := sub<GL(3, K) |  [1/t, 0,0, 0, 1/(t+ 1), 0, 0, 0, 1/(t+2)], 
  [1/t, 1/(t+ 1), 1/u, 0, 1, 1/(1+u), 0, 0, 1/(u + 1) ]>;
time f :=IsFinite(G);
f;
IsSolubleByFinite (G);

 G := GL (2, K);
 a := G![1,1,0,-1];
 b:= G![1/(2), 1, 0, 1/3];
 H := sub <GL(2, K) | a, b>;
time f :=IsFinite(H);
f;
IsSolubleByFinite (H);

 L<t> := RationalFunctionField (GF (q));
 G := GL (2, L);
 a := G![t,1,0,-1];
 b:= G![t/(t + 1), 1, 0, 1/t];
 H := sub <GL(2, L) | a, b>;
time f :=IsFinite(H);
f;
IsSolubleByFinite (H);

F := GF (q);
R<u> := FunctionField (F);
v := u; w := -2 * v;
Px<X> := PolynomialRing (R);
Py<Y> := PolynomialRing (R);
f :=  Y^2- 3 * u * X * Y^2  + v * X^3;
facs := Factorisation (f);
F:=ext <R | facs[2][1]>;
n := 3;
G:= GL(n,F);
Z := 4 * X * Y;
MA:= MatrixAlgebra(F,n);
h1:= Id(MA);
h1[n][n]:= (X^2+Y+Z+1);
h1;
h1[1][n]:= X+1;
h1[1][n]:= X+1;
h1[1][1]:=(Z^5-X^2*Z+Z*X*Y);
h1[2][1]:=1-X*Y*Z;
h1[2][n]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;
h2:= Id(MA);
h2[n][n]:= (X^7+Z^6+1);
h2[1][n]:= X^2+X+1;
h2[1][1]:=(Y^3+X^2+X+1);
h2[2][1]:=1-X^2;
h2[2][n]:= X^50+Y^35+X^20+X^13+Y^2+1;
G := sub< GL(n, F) | h1, h2>;
time f :=IsFinite(G);
f;
IsSolubleByFinite (G);

R<u> := FunctionField (GF (q));
P<y> := PolynomialRing (R);
f := u * y^3 + 3 * u^2 * y + 1;
IsSeparable (f);
F := ext < R | f>;
Z := -14 * X * Y;
MA:= MatrixAlgebra(F,n);
h1:= Id(MA);
h1[n][n]:= (X^2+Y+Z+1);
h1;
h1[1][n]:= X+1;
h1[1][n]:= X+1;
h1[1][1]:=(Z^5-X^2*Z+Z*X*Y);
h1[2][1]:=1-X*Y*Z;
h1[2][n]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;
h2:= Id(MA);
h2[n][n]:= (X^7+Z^6+1);
h2[1][n]:= X^2+X+1;
h2[1][1]:=(Y^3+X^2+X+1);
h2[2][1]:=1-X^2;
h2[2][n]:= X^50+Y^35+X^20+X^13+Y^2+1;
G := sub< GL(n, F) | h1, h2>;
 time f :=IsFinite(G);
f;
IsSolubleByFinite (G);


Q := GF (q);
R<x> := FunctionField(Q);
P<y> := PolynomialRing(R);
P2<z> := PolynomialRing(R);
f := x * y^2- 3 * x * y^2 * z + 6 * x;
if IsIrreducible (f) eq false then
  facs := Factorisation (f);
  f := facs[2][1];
end if;
F<alpha> := ext < R | f>;
G := GL(2, F);
a := G![z * y,x * y + z, z, y];
a;
b := G![y + x/4 * z, x* y, y * z / 73, z * x + y];
a, b;
G:=sub < G | a, b>;
time f:=IsFinite(G);
f;
IsSolubleByFinite (G);

Q := GF (q);
R<x> := FunctionField(Q);
P<y> := PolynomialRing(R);
f := x * y^2- 3;
F<alpha> := ext < R | f>;
if IsIrreducible (f) eq false then
  facs := Factorisation (f);
  f := facs[2][1];
end if;
Type (F);
G := GL(2, F);
a := G![1,1/x, x, y];
b := G![1-1/x, x* y, 0, 1];
G:=sub < G | a, b>;
G;
time f:=IsFinite(G);
f;
IsSolubleByFinite (G);


R<x> := FunctionField(GF(5));
P<y> := PolynomialRing(R);
F<alpha, beta> := FunctionField([y^2 - 1/x, y^3 + x]);
G := GL(2, F);
a := G![1,1/x, x, y];
b := G![1-1/x, x* y, 0, 1];
G:=sub < G | a, b>;
time f:=IsFinite(G);
f;
IsSolubleByFinite (G);

K := RationalExtensionRepresentation(F);
P := GL(2, K);
P!Eltseq (G.1);
x := P!Eltseq (G.1);
y := P!Eltseq (G.2);
x, y;
G:=sub<GL(2, K) | x, y>;
G;
time f:=IsFinite(G);
f;
IsSolubleByFinite (G);

q := 5;
 F := GF (q);
 R<u> := FunctionField (F);
 v := u; w := -2 * v;
 Px<X> := PolynomialRing (R);
 Py<Y> := PolynomialRing (R);
 f :=  Y^2- 3 * u * X * Y^2  + v * X^3;
 facs := Factorisation (f);
 F:=ext <R | facs[2][1]>;
 n := 3;
 Z := 4 * X * Y;
 MA:= MatrixAlgebra(F,n);
 h1:= Id(MA);
 h1[n][n]:= (X^2+Y+Z+1);
 h1;
 h1[1][n]:= X+1;
 h1[1][n]:= X+1;
 h1[1][1]:=(Z^5-X^2*Z+Z*X*Y);
 h1[2][1]:=1-X*Y*Z;
 h1[2][n]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;
 h2:= Id(MA);
 h2[n][n]:= (X^7+Z^6+1);
 h2[1][n]:= X^2+X+1;
 h2[1][1]:=(Y^3+X^2+X+1);
 h2[2][1]:=1-X^2;
 h2[2][n]:= X^50+Y^35+X^20+X^13+Y^2+1;
 G := sub< GL(n, F) | h1, h2>;
  
time f:=IsFinite(G);
f;
IsSolubleByFinite (G);
