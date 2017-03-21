// test file for recognition paper 

SetVerbose ("CompositionTree", 5);

// AttachSpec ("../infmat.spec");
load "start.m";
SetVerbose ("Infinite", 1);
SetEchoInput (true);

// G_1 

/* 
F<w>:= CyclotomicField(17);

n:=24;

MA:=MatrixAlgebra(F,n);

diag:= Identity(MA);

diag[n][n]:= w;

P:= SymmetricGroup(n);

M := sub<GL(n, F) | [PermutationMatrix (F, P.i): i in [1..Ngens
(P)]]>;

test1:= sub<GL(n,F)|diag, M>;

x:= diag;

x[1][n]:= w/2;

for i:=2 to n do

x[2][i]:= i*w^3/(i+1);

end for;

for i:=n-5 to n do

x[n-5][i]:= (i+w^7)/(w^3*i+2);

end for;

x:= GL(n,F)!x;

G_1:= sub<GL(n,F)|x*test1.1*x^-1,x*test1.2*x^-1,x*test1.3*x^-1>;

SetSeed (1);
time f, o := IsFinite (G_1: UseCongruence := true);
f;
o;
time S := MySylow (G_1, 3);
#S;
time D := MyDerivedGroup (G_1);
#D;


// G_2

/* 
d := 4; e := 2; n := 2; m := 1;
d := 4; e := 2; n := 3; m := 2;
// G := PrimitiveExample (d, e, n, m);
P := PrimitiveGroup (n, m);
DB := RationalMatrixGroupDatabase();
G := Group(DB, d, e);
G := WreathProduct (G, P);
P := CyclotomicField (2);
time G_2 := ConstructConjugate (G, P);
G_2;
Ngens (G_2);

// X := Set (&cat ([Eltseq (x): x in Generators (G_2)]));
// "Size of entries is ", [Ilog (10, Abs (Ceiling (x))) : x in X | x ne 0];    
// D := {Denominator (x): x in X};
// "Denoms are ", {Ilog (10, x): x in D};


SetSeed (1);
time IsFinite (G_2);
time o := Order (G_2);
"Factored Order is ", Factorisation (o);
time Z := MyCentre (G_2);
time F := MyFittingSubgroup (G_2);
time R := MySolvableRadical (G_2);

*/

// G_3 

/* 

R<u> := FunctionField (Rationals ());

Px<X> := PolynomialRing (R);

f := u*X^2-2*X+1;

F:=ext <R | f>;

n := 20;

Y:=X;

Z := 4 * X * Y;

MA:=MatrixAlgebra(F,n);

ide:= Identity(MA);

ide[n][n]:= -1;

P:= SymmetricGroup(n);

M := sub<GL(n, F) | [PermutationMatrix (F, P.i): i in [1..Ngens
(P)]]>;

test1:= sub<GL(n,F)|ide, M>;

test1:=MyDerivedGroup(test1);

h1:= ide;

h1:= Id(MA);

h1[n][n]:= (X^2+Y+Z+1);

h1[1][n]:= X+1;

h1[1][n]:= X+1;

h1[1][1]:=(Z^5-X^2*Z+Z*X*Y);

h1[2][1]:=1-X*Y*Z;

h1[3][6]:=X*Y^2;

h1[5][8]:=X^2-2*X+1;

for i in [6..n] do

h1[6][i]:=X^2-2*i;

end for;

h1[n-1][n]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;

h1:= GL(n,F)!h1;

G_3:=sub<GL(n,F)| [h1*test1.i*h1^-1: i in [1..Ngens (test1)]]>;

SetSeed (1);
time IsFinite (G_3);
time #G_3;
time H := MySylow (G_3, 7);
time MyIsNormal (G_3, H);

// G_4 

K<w>:= CyclotomicField(19);

n:=10;

MA:= MatrixAlgebra(K,n);

d:=Zero(MA);

d[n][1]:= 1;

for i in [1..n-1] do

d[i][i+1]:= 1;

end for;

a:=DiagonalMatrix(K,[w^-1,5*w^-16,w^16,4, 3, 2, 1, 1, 1,
w*Factorial(5)^-1]);

b:=DiagonalMatrix(K,[1, 2, 3, 4, 5, 6,1,
w^9,1/w^9,Factorial(6)^-1]);

c:=DiagonalMatrix(K,[1,2,3,4, 5,6 ,7,8, 9, Factorial(9)^-1]);

f:=DiagonalMatrix(K,[w,w^2,w^3,w^4, w^5,w^6 ,w^7,w^8, w^9,
w^-Factorial(9)]);

g:=DiagonalMatrix(K,[1+w,1-w,1,1, 1,1 ,-1,-1, w, w/(1-w^2)]);

h:=DiagonalMatrix(K,[1,2,3,4, w,1/w ,w,1/w, 1, Factorial(4)^-1]);

j:=DiagonalMatrix(K,[w^2,1/w^2,w^3,1/w^3, w^4,1/w^4 ,1,1, 1, 1]);

m:=10;

den:= Identity(MatrixAlgebra(K,m));

den:= GL(m,K)!den;

G_4:=
sub<GL(m*n,K)|KroneckerProduct(a*d,d),KroneckerProduct(b*d,d),
KroneckerProduct(c*d,den), KroneckerProduct(f*d,den),
KroneckerProduct(g*d,den), KroneckerProduct(h*d,den),
KroneckerProduct(j*d,d), KroneckerProduct(d*a,d),
KroneckerProduct(d*b,d), KroneckerProduct(d*c,d),
KroneckerProduct(d*f,den), KroneckerProduct(d*g,den),
KroneckerProduct(d*h,den), KroneckerProduct(d*j,den)>;

SetSeed (1);
time IsFinite (G_4: UseCongruence := true);

// G_5 


R<u> := FunctionField (Rationals ());

Px<X> := PolynomialRing (R);

f := u*X^3-(u^2+1)*X/(u-1)+3*X^2-4;

F:=ext <R | f>;

n := 5;

Z := X^2-5;

Y:=X+2;

MA:= MatrixAlgebra(F,n);

d:=Zero(MA);

d[n][1]:= 1;

for i in [1..n-1] do

d[i][i+1]:= 1;

end for;

a:=DiagonalMatrix(F,[1,2,3,4,Factorial(4)^-1]);

b:=DiagonalMatrix(F,[1, 432, 1/321, 321, 1/432]);

c:=DiagonalMatrix(F,[1, 432, 1/321, 321, 1/432]);

f:=DiagonalMatrix(F,[-12, -1/12, 32109, -1/32109, -1]);

g:=DiagonalMatrix(F,[1,1,-1,-1,1]);

m:=6;

den:= GL(m,R)![0,1,0,0,0,0, 0,0,1,0,0,0, 0,0,0,1,0,0, 0,0,0,0,1,0,
0,0,0,0,0,1, 1,0,0,0,0,0];

den:= GL(m,F)!den;

PreGInfFinGen3:=
sub<GL(m*n,F)|KroneckerProduct(a*d,den),KroneckerProduct(b*d,den),
KroneckerProduct(c*d,den),KroneckerProduct(f*d,den),KroneckerProduct(g*d,den),
KroneckerProduct(d*a,den),
KroneckerProduct(d*b,den),KroneckerProduct(d*c,den),
KroneckerProduct(d*f,den),KroneckerProduct(d*g,den)>;

h1:= Id(MatrixAlgebra(F,n*m));

h1[n][n]:= (X^2+Y+Z+1);

h1[1][n]:= X+1;

h1[1][n]:= X+1;

h1[1][1]:=(Z^5-X^2*Z+Z*X*Y);

h1[2][1]:=1-X*Y*Z;

for i in [3..n*m] do

h1[3][i]:= 10*i+X^i-i*Z+X^3*Y^7;

end for;

h1[5][8]:=X^2-2*X+1;

h1[n*m-1][n*m]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;

for i in [4..n*m] do

h1[4][i]:= 2^i*Z^i;

end for;

h1:= GL(n*m,F)!h1;

G_5:=sub<GL(n*m,F)|h1*PreGInfFinGen3.1*h1^-1,h1*PreGInfFinGen3.2*h1^-1,
h1*PreGInfFinGen3.3*h1^-1,h1*PreGInfFinGen3.4*h1^-1>;

SetSeed (1);
time IsFinite (G_5);

*/
// G_6 

q := 3^2;
d := 6;
R<x> := FunctionField(GF(q));
 P<y> := PolynomialRing(R);
F<alpha> := FunctionField(y^2 - 1/x);
G := GL(d, q);
n := Degree (G);
   MA := MatrixAlgebra (F, n);
   e := Identity (MA);
   for i in [1..n] do
      for j in [1..n] do
    if i lt j then e[i][j] := y+i*y^0; end if;
      end for;
   end for;
G_6 := sub<GL(n, F) |  [e * MA ! g * e^-1: g in Generators (G)]>;
SetSeed (1);
time f, o := IsFinite (G_6);
"order is ", o;
time U := MyUnipotentRadical (G_6);
time H := MySylow (G_6, 3);
time N := MyNormalClosure (G_6, H);

// G_7 

n:=8; q:=2; dim:=2; are:= 5;

R<u> := FunctionField(GF(q));

Px<X> := PolynomialRing (R);

f := u*X^3-(u^2+1)*X/(u-1)+3*X^2-4*u+5;

F:=ext <R | f>;

H:= GL(n,GF(q));

twid:= TestFF2(H);

unipo:= TestUnipotentFF(dim,q,are);

kraw := KroneckerProductOfLists ([twid.i: i in [1..Ngens (twid)]],
[unipo.i: i in [1..Ngens (unipo)]]);

noncred:= sub<GL(n*dim, F) | kraw>;

Y:=X;

Z := 4 * X * Y;

MA:= MatrixAlgebra(F,n*dim);

h1:= Id(MA);

h1[n][n]:= (X^2+Y+Z+u);

h1[1][n]:= u+1;

h1[1][n]:= u^2-1/u;

h1[1][1]:=(Z^5-X^2/u+Z*u);

h1[2][1]:=1-X*Y*Z;

h1[3][6]:=X*Y^2;

h1[5][8]:=X^2-2*X+1;

for i in [6..n] do

h1[6][i]:=X^2-2*i;

end for;

h1[n-1][n]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;

h1:= GL(n*dim,F)!h1;

G_7:= sub<GL(n*dim,F)|[h1 *g * h1^-1: g in Generators (noncred)]>;

SetSeed (1);
time IsFinite (G_7);
time o := Order (G_7);
"order is ", o;
time H := MyFittingSubgroup (G_7);
time N := MyNormalClosure (G_7, H);


// G_8 
q:=5;

F<x,y> := FunctionField(GF(q),2);

n:=4;

d:=Zero(MatrixAlgebra(F,n));

d[n][1]:= 1;

for i in [1..n-1] do

d[i][i+1]:= 1;

end for;

a:=DiagonalMatrix(F,[x, 3, 1, 2/x]);

b:=DiagonalMatrix(F,[6*x, x, 1, 1/x^2]);

c:=DiagonalMatrix(F,[y^2,1,1,-1/y^2]);

m:=3;

den:= GL(m,F)![0,1,0, 0,0,1, 1,0,0];

gl:= GL(n*m,F);

r:= 2;

MA:= MatrixAlgebra(F,n*m);

h := Id(MA);

S := [];

for i in [1..r] do S[i] := h; end for;

for k in [1..r] do
   for i in [1..n] do
      for j in [1..n] do
         if j gt i then S[k][i][j] := x^i + y^k + j; end if;
      end for;
   end for;
end for;

G_8:=
sub<GL(m*n,F)|KroneckerProduct(a*d,den),KroneckerProduct(b*d,den),
KroneckerProduct(c*d,den),
KroneckerProduct(d*a,den),KroneckerProduct(d*b,den),
KroneckerProduct(d*c,den),S>;

SetSeed (1);
time IsFinite (G_8);

// G_9 

q:=5;

R<u> := FunctionField(GF(q));

Px<x> := PolynomialRing (R);

f := u*x^3-(u^2+1)*x+3*x-4*u+5;

F:=ext <R | f>;

n:=4;

d:=Zero(MatrixAlgebra(F,n));

d[n][1]:= 1;

for i in [1..n-1] do

d[i][i+1]:= 1;

end for;

a:=DiagonalMatrix(R,[u, 3, 1, 2/u]);

b:=DiagonalMatrix(R,[u, u, 1, 1/u^2]);

c:=DiagonalMatrix(R,[u^2,1,1,-1/u^2]);

m:=3;

den:= GL(m,F)![0,1,0, 0,0,1, 1,0,0];

gl:= GL(n*m,F);

r:= 2;

MA:= MatrixAlgebra(F,n*m);

h := Id(MA);

S := [];

for i in [1..r] do S[i] := h; end for;

for k in [1..r] do
   for i in [1..n] do
      for j in [1..n] do
         if j gt i then S[k][i][j] := x^i + u^k + j; end if;
      end for;
   end for;
end for;

G_9:=
sub<GL(m*n,F)|KroneckerProduct(a*d,den),KroneckerProduct(b*d,den),
KroneckerProduct(c*d,den),
KroneckerProduct(d*a,den),KroneckerProduct(d*b,den),
KroneckerProduct(d*c,den),S>;

SetSeed (1);
time IsFinite (G_9);
