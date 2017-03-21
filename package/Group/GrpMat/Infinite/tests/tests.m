SetSeed (1);

// short test file -- takes less than 20 seconds 

SetEchoInput (true);
SetVerbose ("Infinite", 1);

// example 1

q := 5^2;
 L<t> := RationalFunctionField (GF (q));
 G := GL (2, L);
 a := G![t,1,0,-1];
 b:= G![t/(t + 1), 1, 0, 1/t];
 H := sub <GL(2, L) | a, b>;
time f :=IsFinite(H);
f;
time IsSolubleByFinite (H);
time IsCompletelyReducible (H);
// time IsCentralByFinite (H);

// example  2 
Q := GF (5^2);
F<t>:= RationalFunctionField (Q);
M:=MatrixAlgebra (F, 2);
a := M![t,0,1,t];
b := M![t^2 + t + 1, t, 0, 1];
c:= M![t/(t^2 + t + 1),0,1,1/t];
A := sub <M | a, b, c>;
H := sub <GL(2, F) | a, b, c>;
time IsFinite (H);
time IsSolubleByFinite (H);
// time IsCompletelyReducible (H);
time IsCentralByFinite (H);

// example 4
d := 2;
q := 7^3;
F := GF(q);
K<t>:= RationalFunctionField (F, 1);
G := sub<GL(2, K) |  [1/t, 1/(t+ 1), 1, 1]>;
time IsFinite(G);
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
time IsAbelianByFinite (G);
time IsNilpotentByFinite (G);
time IsCentralByFinite (G);

// example 9

G := MatrixGroup<3, IntegerRing() |
    \[ 1, -2, 3, 0, 6, -13, 0, 1, -2 ],
    \[ -8, -1, 1, -8, -2, 3, -1, -1, 2 ] >;
time IsFinite (G);
time IsSolubleByFinite (G);
time IsAbelianByFinite (G);
time IsNilpotentByFinite (G);
time IsCentralByFinite (G);
// time IsCompletelyReducible (G);

// example 10
q := 19;
 L<t> := RationalFunctionField (GF (q));
 G := GL (2, L);
 a := G![t,1,0,-1];
 b:= G![t/(t + 1), 1, 0, 1/t];
 H := sub <GL(2, L) | a, b>;
time IsFinite(H);
time IsSolubleByFinite (H);
// time IsCompletelyReducible (H);

// example 11
G := MatrixGroup<3, IntegerRing() |
    \[ 5608, 711, -711, 6048, 766, -765, 1071, 135, -134 ],
    \[ 1, -2415, 5475, 0, 4471, -10140, 0, 780, -1769 ],
    \[ 5743, -5742, 639, -576, 577, -72, -711, 711, -80 ],
    \[ 526168, -618507, 729315, 621984, -731138, 862125, 274455, -322620, 380419
    ],
    \[ 648226, -4621455, 9226791, 660687, -4710305, 9404184, 85626, -610473,
    1218820 ],
    \[ 32581, -39465, 46350, 53100, -64319, 75540, 24210, -29325, 34441 ] > ;
time IsFinite (G);
time IsSolubleByFinite (G);
time IsCentralByFinite (G);
// time IsCompletelyReducible (G);
time IsAbelianByFinite (G);
time IsNilpotentByFinite (G);

// example 13
K := QuadraticField(2);
G := MatrixGroup<2, K | [K.1,0,0,1], [-1,0,0,-1] >;
time IsFinite(G);
time IsSolubleByFinite (G);
time IsCentralByFinite (G);
time IsCompletelyReducible (G);
time IsAbelianByFinite (G);
time IsNilpotentByFinite (G);

// example 14
 R<s>:= QuadraticField(-1);
 F<t>:= FunctionField(R);
 M:= MatrixAlgebra (F, 2);
 a:= M![-s*t^2 + 1, s*t^3, -s*t, s*t^2 + 1];
 b:= M![t^2 - 3*t + 1, 0, 0, t^2 - 3*t + 1];
 G:= sub<GL(2,F)|a,b>;
time IsFinite(G);
time IsSolubleByFinite (G);
time IsCentralByFinite (G);
time IsCompletelyReducible (G);
time IsAbelianByFinite (G);
time IsNilpotentByFinite (G);

// example 15
Q<z> := QuadraticField(5);
O<w> := sub< MaximalOrder(Q) | 7 >;
G := GL(2, Q);
x := G![1,1+w,0,w];
y:=G![-1/2, 2, 2 + w, 5 + w^2];
H:=sub<G | x, y>;
time IsFinite (H);
time IsSoluble (H);
time IsSolubleByFinite (H);

// example 16
d := 8;
F := GF (5^2);
K<t>:= RationalFunctionField (F, 1);
S := ScalarMatrix (K, d, t); 
T := ScalarMatrix (K, d, -t); 
G := sub <GL(d, K) | S, T>;
time IsFinite(G);
time IsSolubleByFinite (G);
time IsCentralByFinite (G);
// time IsCompletelyReducible (G);
time IsAbelianByFinite (G);
time IsNilpotentByFinite (G);

// example 17
d := 3;
F := GF (5^2);
K<t, u>:= RationalFunctionField (F, 2);
G := sub<GL(3, K) |  [1/t, 0,0, 0, 1/(t+ 1), 0, 0, 0, 1/(t+2)], 
  [1/t, 1/(t+ 1), 1/u, 0, 1, 1/(1+u), 0, 0, 1/(u + 1) ]>;
time IsFinite(G);
time IsSolubleByFinite (G);
// time IsCentralByFinite (G);
// time IsCompletelyReducible (G);
// time IsAbelianByFinite (G);
// time IsNilpotentByFinite (G);


// example 18
 R<x> := PolynomialRing(Integers());
 K<y> := NumberField(x^4-420*x^2+40000);
 G := GL (2, K);
 a := G![1,1,0,-1];
 b:= G![1/(2), 1, 0, 1/3];
 H := sub <GL(2, K) | a, b>;
time IsFinite(H);
time IsSolubleByFinite (H);
time IsCentralByFinite (H);
time IsCompletelyReducible (H);
time IsAbelianByFinite (H);
time IsNilpotentByFinite (H);

// example 19
 R<x> := PolynomialRing(Integers());
 K<y> := NumberField(x^4-420*x^2+40000);
 G := GL (2, K);
 a := G![y,1,0,-1];
 b:= G![y/(y + 1), 1, 0, 1/y];
 H := sub <GL(2, K) | a, b>;
time IsFinite(H);
time IsSolubleByFinite (H);
time IsCentralByFinite (H);
time IsCompletelyReducible (H);
time IsAbelianByFinite (H);
time IsNilpotentByFinite (H);

// example 20 
 R<x> := PolynomialRing(Integers());
 K<y> := NumberField(x^4-420*x^2+40000);
 L<t> := RationalFunctionField (K);
 G := GL (2, L);
 a := G![t,1,0,-1];
 b:= G![t/(t + 1), 1, 0, 1/t];
 H := sub <GL(2, L) | a, b>;
time IsFinite(H);
time IsSolubleByFinite (H);
time IsCentralByFinite (H);
time IsCompletelyReducible (H);
// time IsAbelianByFinite (H);
time IsNilpotentByFinite (H);

// example 22
R<s>:= QuadraticField(-1);
funt<t>:=FunctionField(R); 
aqo:= GL(2,funt)![1,t*s,0,1];
H:= sub<GL(2,funt)|aqo>;
time IsFinite(H);
time IsSolubleByFinite (H);
time IsCentralByFinite (H);
time IsCompletelyReducible (H);
time IsAbelianByFinite (H);
time IsNilpotentByFinite (H);

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
time IsSolubleByFinite (G);
time IsCentralByFinite (G);
time IsCompletelyReducible (G);
time IsAbelianByFinite (G);
time IsNilpotentByFinite (G);

// example 25
Q := GF (5^2);
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
time f, I, tau := IsomorphicCopy (G);
tau;

// example 28
d := 3;
F := GF (3);
K<t, u>:= RationalFunctionField (F, 2);
G := sub<GL(3, K) |  [1/t, 0,0, 0, 1/(t+ 1), 0, 0, 0, 1/(t+2)],
  [1/t, 1/(t+ 1), 1/u, 0, 1, 1/(1+u), 0, 0, 1/(u + 1) ]>;
time IsFinite(G);
time IsSolubleByFinite (G);

// example 30
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
time IsFinite(G);
time IsSolubleByFinite (G);
// time IsAbelianByFinite (G);
// time IsCompletelyReducible (G);
// time IsNilpotentByFinite (G);
// time IsCentralByFinite (G);

// example 38 

 q:=11;

 K<w>:= GF(q);

 R<x,y>:=RationalFunctionField(K,2);

 n:=6;

 d:=Zero(MatrixAlgebra(R,n));

 d[n][1]:= 1;

 for i in [1..n-1] do;
 d[i][i+1]:= 1;  end for;

 y:=x;

 a:=DiagonalMatrix(R,[x*w^-1,4, 3, 2/x, w, w*Factorial(4)^-1]);

 b:=DiagonalMatrix(R,[6*x, w^9+w^3+w*x+1,1/(w^9+w^3+w*x+1),1,1/6/x,
 w]);

 c:=DiagonalMatrix(R,[x*y,1/(x*y),w^2-3,1,-1, w]);

 m:=5;

 den:= GL(m,R)![0,1,0,0,0, 0,0,1,0,0, 0,0,0,1,0, 0,0,0,0,1,
 1,0,0,0,0];

 H:=
 sub<GL(m*n,R)|KroneckerProduct(a*d,den),KroneckerProduct(b*d,den),
 KroneckerProduct(c*d,den),
 KroneckerProduct(d*a,den),KroneckerProduct(d*b,den),
 KroneckerProduct(d*c,den)>;

 gl:= GL(n*m,R);

 r:= 3;

 MA:= MatrixAlgebra(R,n*m);

 h := Id(MA);

 S := [];

 for i in [1..r] do S[i] := h; end for;

 for k in [1..r] do
   for i in [1..n] do       for j in [1..n] do
         if j gt i then S[k][i][j] := x^i + y^k + j;
end if;       end for;    end for;  end for;
 testy:= sub<gl|S,H>;
 time IsFinite(testy);


K<w>:= CyclotomicField(7);

R<x,y>:=RationalFunctionField(K,2);

n:=5;

d:=Zero(MatrixAlgebra(R,n));

d[n][1]:= 1;

for i in [1..n-1] do

d[i][i+1]:= 1;

end for;

y:=x;

a:=DiagonalMatrix(R,[x*w^-1,4, 3, 2/x, w*Factorial(4)^-1]);

b:=DiagonalMatrix(R,[6/x^2,
w^9+w^3+w*x+1,1/(w^9+w^3+w*x+1),x^2,1/6]);

c:=DiagonalMatrix(R,[x,2*y,3/y,4/x,1/24]);

f:=DiagonalMatrix(R,[w^3,w^5,w^7,w^9, w^-24]);

g:=DiagonalMatrix(R,[1+w*y,1-w*y,w/(1-w^2*y^2),1,1]);

h:=DiagonalMatrix(R,[1,x*y^3+2,4/(x*y^3+2),w,1/(4*w)]);

j:=DiagonalMatrix(R,[x+y,1/(x+y),w^3,1/w^3,1]);

k:=DiagonalMatrix(R,[w,y/w,w^3,1/(y*w^3),1]);

m:=5;

/*den:= Identity(MatrixAlgebra(R,m));*/

den:= GL(m,R)![0,1,0,0,0, 0,0,1,0,0, 0,0,0,1,0, 0,0,0,0,1,
1,0,0,0,0];

/*den:= GL(m,R)!den;*/

PreGInfFinGen2:=
sub<GL(m*n,R)|KroneckerProduct(a*d,den),KroneckerProduct(b*d,den),
KroneckerProduct(c*d,den), KroneckerProduct(f*d,den),
KroneckerProduct(g*d,den), KroneckerProduct(h*d,den),
KroneckerProduct(j*d,den), KroneckerProduct(d*a,den),
KroneckerProduct(d*b,den), KroneckerProduct(d*c,den),
KroneckerProduct(d*f,den), KroneckerProduct(d*g,den),
KroneckerProduct(d*h,den), KroneckerProduct(d*j,den),
KroneckerProduct(k*d,den), KroneckerProduct(d*k,den)>;

conj:= Identity(MatrixAlgebra(R,m*n));

conj[1][n*m]:= (y-1)/2;

for i:=2 to n*m do

conj[2][i]:= i*y;

end for;

for i:=3 to n*m do

conj[3][i]:= x^2-i;

end for;

conj:= GL(n*m,R)!conj;

E := [Eltseq (conj*PreGInfFinGen2.i*conj^-1): i in [1..Ngens
(PreGInfFinGen2)]];

G:= sub<GL(m*n,R)|E>;
time IsFinite (G);

// example 39 

F<x> := FunctionField (GF (2));
G := GL(2, F);
a := G![1, 1/x, 0, 1];
b := [1, 1/(x + 1), 0, 1]; 
G := sub<G | a, b>;
time IsFinite (G);
time f, I := IsomorphicCopy (G);
// time IsCompletelyReducible (G);

// example 40 
F := GF(2);
P := PolynomialRing (F);
P<t> := PolynomialRing (F);
F := ext < F | t^2+t+1>;
G := GL (2, FunctionField (F));
a := G![1,1/t, 0, 1];
b := [1,1/(t + 1), 0, 1];
c := [1,1/(t^2 + t + 1), 0, 1];
d := [1,1/(t^2 + t), 0, 1];
G := sub < G | a,b,c,d>;
G;
time IsFinite (G);
time f, I := IsomorphicCopy (G);


// test cases for code supplied by Tobias Rossman 
K<w> := QuadraticField(2);

// reducible
G := MatrixGroup< 8, K |
    [w-1,0,1,1,0,0,0,0,0,-1,0,0,1,1,0,0,2*w-4,0,-w+1,-w+1,0,0,0,1,0,0,0,0,
     0,0,0,-1,0,-2,0,0,1,1,1,-w+1,0,0,0,0,0,0,-1,w-1,0,0,0,w-1,0,1,0,0,0,
     0,0,1,0,0,0,0],
    [0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,-w+1,-w+1,0,-1,-1,0,0,0,-w,1,0,0,0,0,0,
     0,0,0,1,0,0,-1,-1,0,0,0,1,0,0,0,0,0,0,-w+1,-1,0,w-1,0,1,1,0,-1,0,0,1,
     0,0,0,1],
    [1,0,0,-1,0,0,0,-1,0,1,0,0,0,-1,-1,w-1,-w,0,0,w,0,0,0,w-1,-w+2,0,-1,
     -1,0,0,0,-1,0,0,0,0,0,0,-1,w-1,0,2,0,0,-1,-1,-1,w-1,-w+2,0,w-1,0,1,0,
     0,0,w,0,1,0,0,0,0,0]
    >;
G;
IsIrreducibleFiniteNilpotent(G);

// irreducible but (evidently) imprimitive
G := MatrixGroup< 8, K |
    [1/2*w,1/2*w,0,0,0,0,0,0,-1/2*w,1/2*w,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,
     0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,
     0,0,0,1],
    [1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,
     0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1],
    [0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,
    0,0,0,0,1,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
    >;
G;
IsIrreducibleFiniteNilpotent(G);
r, B := IsPrimitiveFiniteNilpotent(G);
r;
#B;

// primitive
G := MatrixGroup< 4, Rationals() |
    [ 0, 1, -1, -1, -1, -1, 1, 0, -1, -1, 0, -1, 1, 0, 1, 1 ],
    [ 0, 0, 0, 1, 0, 0, -1, -1, 0, -1, 0, 0, 1, 1, 0, 0 ] >;
G;
IsIrreducibleFiniteNilpotent(G);
IsPrimitiveFiniteNilpotent(G);

// unipotent check 
 R<x> := PolynomialRing(Integers());
 K<y> := NumberField(x^4-420*x^2+40000);
 G := GL (2, K);
 a := G![1,y,0,1];
 b:= G![1, y/(y + 1), 0, 1];
 H := sub <GL(2, K) | a, b>;
 c:= G![y^2-2, y/(y + 1), y, 1];
 K := H^c;
 flag, cb := IsUnipotent (K);
 K^cb;


// check of function field 
 R<x> := FunctionField(GF(5)); 
 P<y> := PolynomialRing(R);
 F<alpha, beta> := FunctionField([y^2 - 1/x, y^3 + x]);
  a := GL(2, F) ! [1, x, 0,1];
 G  := sub<GL(2, F) | a >;
 f, I := IsomorphicCopy (G);
f, I;

 H := sub<GL(2, F) | >;
 f, I := IsomorphicCopy (H);
f, I;


// type of field construction 
P<x> := PolynomialRing(Rationals());
  F2<i,omega> := NumberField([x^2+1,x^2+x+1] : Abs := false);
  a2 := Matrix(F2,2,2,[
      [              -1,  0],
      [-i - 2*omega - 1,  1]]);
  b2 := Matrix(F2,2,2,[
      [ 1, omega + 1],
      [ 0,     omega]]);
  G := sub<GL(2,F2) | a2,b2>;
  f, I := IsomorphicCopy (G);
  f, I;
  assert #I eq 48;

P<x> := PolynomialRing(Rationals());
  F2<i,omega> := NumberField([x^2+1,x^2+x+1] : Abs := true);
  a2 := Matrix(F2,2,2,[
      [              -1,  0],
      [-i - 2*omega - 1,  1]]);
  b2 := Matrix(F2,2,2,[
      [ 1, omega + 1],
      [ 0,     omega]]);
  G := sub<GL(2,F2) | a2,b2>;
  f, I := IsomorphicCopy (G);
  f, I;
  assert #I eq 48;
  
quit;

