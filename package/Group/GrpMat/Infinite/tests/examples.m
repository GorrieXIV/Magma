
 SetVerbose ("CompositionTree", 0);

SetVerbose ("Infinite", 1);

SetEchoInput (true);

 Q := Rationals ();
 F<t>:= RationalFunctionField (Q);
 M:= MatrixAlgebra (F, 3);
 a:= M![-1, 2*t^2, -2*t^4 - 2*t^3 - 2*t^2, 0, 1, 0, 0, 0, 1];
 b:= M![1, 0, 0, 1/t^2, -1, (2*t^3 - 1)/(t - 1), 0, 0, 1];
 c:= M![t, -t^3 + t^2, t^5 - t^2 - t, t^2, -t^4, (t^8 - t^5 + 1)/(t^2 -
t), (t - 1)/t, -t^2 + t, t^4 - t];
 G:= sub<GL(3,F)|a,b,c>;
time f  := IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

 Q := Rationals ();
 F<t>:= RationalFunctionField (Q);
 M:= MatrixAlgebra (F, 6);
 a:= M![2, 2*t^2, 4, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0,
0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1];
 b:= M![(4*t + 4)/t, 4*t, (t + 1)/t, 0, t, t^2 + t, 0, 4, 0, 0, 0,
1/t, 4/t, t^2 + 4*t, 1/t, 0, 0, 0, 0, 4*t, 0, 0, 0, 0, 0, 0, 4, 4,
0, 0, 0, 0, 0, 4, 0, 0];
 G:= sub<GL(6,F)|a,b>;
time f  := IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
// time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

 R<s>:= QuadraticField(-1);
 F<t>:= FunctionField(R);
 M:= MatrixAlgebra (F, 2);
 a:= M![-s*t^2 + 1, s*t^3, -s*t, s*t^2 + 1];
 b:= M![t^2 - 3*t + 1, 0, 0, t^2 - 3*t + 1];
 G:= sub<GL(2,F)|a,b>;
time f  :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

Q := Rationals ();
F<t>:= RationalFunctionField (Q);
M:=MatrixAlgebra (F, 2);
a := M![t,0,1,t];
b := M![t^2 + t + 1, t, 0, 1];
c:= M![t/(t^2 + t + 1),0,1,1/t];
A := sub <M | a, b, c>;
H := sub <GL(2, F) | a, b, c>;
time f  :=IsFinite (H);
"Finite? ", f;
time IsSolubleByFinite (H);
// time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);

Q := Rationals ();
F<t, u>:= RationalFunctionField (Q, 2);
M:= MatrixAlgebra (F, 2);
a := M![t * u,0,1,t/(t * u + t + 1)];
b := M![t^2 + t + 1, t, 0, 1];
c:= M![t/(u * t^2 + t + u ),0,u,(u * t^2 + t)/t];
A := sub <M | a, b, c>;
H := sub <GL(2, F) | a, b, c>;
time f  :=IsFinite (H);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);


 Q := Rationals ();
d := 8;
F := Q;
K<t>:= RationalFunctionField (F, 1);
S := ScalarMatrix (K, d, t); 
T := ScalarMatrix (K, d, -t); 
G := sub <GL(d, K) | S, T>;
time f  :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

 Q := Rationals ();
d := 2;
F := Q;
K<t>:= RationalFunctionField (F, 1);
G := sub<GL(2, K) |  [1/t, 1/(t+ 1), 1, 1]>;
time f  :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

 Q := Rationals ();
d := 2;
F := Q;
K<t>:= RationalFunctionField (F);
G := sub<GL(2, K) |  [1/t, 1/(t+ 1), 1, 1]>;
time f  :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

 Q := Rationals ();
d := 3;
F := Q;
K<t, u>:= RationalFunctionField (F, 2);
G := sub<GL(3, K) |  [1/t, 0,0, 0, 1/(t+ 1), 0, 0, 0, 1/(t+2)], 
  [1/t, 1/(t+ 1), 1/u, 0, 1, 1/(1+u), 0, 0, 1/(u + 1) ]>;
time f  :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

 R<x> := PolynomialRing(Integers());
 K<y> := NumberField(x^4-420*x^2+40000);

 G := GL (2, K);

 a := G![1,1,0,-1];
 b:= G![1/(2), 1, 0, 1/3];
 H := sub <GL(2, K) | a, b>;
time f  :=IsFinite(H);
"Finite? ", f;
time IsSolubleByFinite (H);
time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);

 a := G![y,1,0,-1];
 b:= G![y/(y + 1), 1, 0, 1/y];
 H := sub <GL(2, K) | a, b>;
time f  :=IsFinite(H);
"Finite? ", f;
time IsSolubleByFinite (H);
time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);

 L<t> := RationalFunctionField (K);
 G := GL (2, L);
 a := G![t,1,0,-1];
 b:= G![t/(t + 1), 1, 0, 1/t];
 H := sub <GL(2, L) | a, b>;
time f  :=IsFinite(H);
"Finite? ", f;
time IsSolubleByFinite (H);
time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);

R<x> := PolynomialRing(Integers());
K<y> := NumberField(x^4-420*x^2+40000);
DB := RationalMatrixGroupDatabase();
G := Group (DB, 4, 2);
H:= ConstructConjugate (G, K);
time f  :=IsFinite(H);
"Finite? ", f;
time IsSolubleByFinite (H);
time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);

R<s>:= QuadraticField(-1);
funt<t>:=FunctionField(R); 
aqo:= GL(2,funt)![1,t*s,0,1];
H:= sub<GL(2,funt)|aqo>;
time f  :=IsFinite(H);
"Finite? ", f;
time IsSolubleByFinite (H);
time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);


Q<z> := QuadraticField(5);
O<w> := sub< MaximalOrder(Q) | 7 >;
G := GL(2, Q);
x := G![1,1+w,0,w];
y:=G![-1/2, 2, 2 + w, 5 + w^2];
H:=sub<G | x, y>;
time f := IsFinite(H);
"Finite? ", f;
time IsSolubleByFinite (H);
// time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);

R<u> := FunctionField (Rationals ());
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
time f  :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

R<u> := FunctionField (Rationals ());
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
time f  :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

G:=CyclotomicExample (3, 4, 5);
time f  :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

Q:= Rationals();
MA:= MatrixAlgebra(Q,3);
e:= Identity(MA);
d:=Zero(MA);
d[3][1]:= 1;
for i in [1..2] do; d[i][i+1]:= 1; end for;
a:=DiagonalMatrix(Q,[1,2,Factorial(2)^-1]);
b:=DiagonalMatrix(Q,[2,1,Factorial(2)^-1]);
G:= sub<GL(3,Q)|a*d, b*d>;
time f :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

R<x> := PolynomialRing(Integers());
K<y> := NumberField(x^4-420*x^2+40000);
K := NumberField([x^3-2, x^2-5]:Abs);
t := K![1,2,3,4,5,6];
t1:=K![0,2,0,5,6,0];
G := GL(2, K);
a := G![t+t1, 2*t1, 3 * t, t1^6-1];
b := G![t^2 + t + 1, t, 0, 1];
H := sub <GL(2, K) | a, b>;
time f :=IsFinite(H);
"Finite? ", f;
time IsSolubleByFinite (H);
// time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);

Q := Rationals ();
R<x> := FunctionField(Q);
P<y> := PolynomialRing(R);
P2<z> := PolynomialRing(R);
f := x * y^2- 3 * x * y^2 * z + 6 * x;
F<alpha> := ext < R | f>;
G := GL(2, F);
a := G![z * y,x * y + z, z, y];
b := G![y + x/4 * z, x* y, y * z / 73, z * x + y];
G := sub < G | a, b>;
G;
time f := IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
// time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

Q := Rationals ();
R<x> := FunctionField(Q);
P<y> := PolynomialRing(R);
f := x * y^2- 3;
F<alpha> := ext < R | f>;
Type (F);
 Basis (F);
G := GL(2, F);
a := G![1,1/x, x, y];
b := G![1-1/x, x* y, 0, 1];
G:=sub < G | a, b>;
G;
time f :=IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
// time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

Q := Rationals ();
R<x> := FunctionField(Q);
P<y> := PolynomialRing(R);
f := x * y^2- 3;
F<alpha> := ext < R | f>;
G := GL(2, F);
a := G![1,1/x, x, y];
b := G![1-1/x, x* y, 0, 1];
G:=sub < G | a, b>;
time f := IsFinite(G);
"Finite? ", f;
time IsSolubleByFinite (G);
// time IsCompletelyReducible (G);
time IsNilpotentByFinite (G);

 Q := Rationals ();
K:= ext<Q|Polynomial(Q, [37693751, 928116, 21536, -249, 1])>;
H:= sub< GL(1, K) | [-1], [ [ 930492355707/1547824452731,
34408370158/1547824452731, -437778961/1547824452731,
   1616652/1547824452731]]>;
time f  :=IsFinite(H);
"Finite? ", f;
time IsSolubleByFinite (H);
time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);

H:= MatrixGroup<1, QuadraticField(-3) | [ [ 1/2, 1/2 ] ] >;
time f  :=IsFinite(H);
"Finite? ", f;
time IsSolubleByFinite (H);
time IsCompletelyReducible (H);
time IsNilpotentByFinite (H);
