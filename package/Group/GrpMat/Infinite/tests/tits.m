// test file for Tits paper 

// AttachSpec ("../infmat.spec");
SetVerbose ("Infinite", 1);
load "construct.m";
load "construct-wreath.m";
load "wreath-examples.m";
load "ff.m";
load "pff.m";
load "paff.m";
load "infmat.m";
SetEchoInput (true);

// example 1 
Q := Rationals ();
F := Q;
n := 7;
G := MonomialGroup (F, n);
d := DiagonalMatrix (F, [i : i in [1..n]]);
H := sub<GL(n, F) | G, d>;
G := ConstructConjugate (H, Q);
time IsSolubleByFinite (G);
time IsCompletelyReducible (G);
SetSeed (1);
time IsAbelianByFinite (G);
"Ngens is ", Ngens (G);
"** Degree is ", Degree (G);

// example 2 

G := MonomialNilpotent (Q, 40);

R<u> := FunctionField (Rationals ());
v := u; w := -2 * v;
Px<X> := PolynomialRing (R);
f :=  X^3- 3 * u * X + v ;
F:=ext <R | f>;
n := Degree (G);
Z := 4 * X; 
Y := -X^2;
MA:= MatrixAlgebra(F,n);
h1:= Id(MA);
h1[1][n]:= X+1;
h1[1][n]:= X+1;
h1[11][1]:=(Z^5-X^2*Z+Z*X*Y);
h1[22][19]:=1-X*Y*Z;
h1[12][n]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;
h1[13][15]:= X^3 - 5 * X + 1;
h1[28][22] := X^4 + X;
h1[n][n]:= (X^2+Y+Z+1);
h2:= Id(MA);
h2[n][n]:= (X^7+Z^6+1);
h2[10][11]:= X^2+X+1;
h2[18][4]:=(Y^3+X^2+X+1);
h2[22][32]:=1-X^2;
h2[13][18]:= X^50+Y^35+X^20+X^13+Y^2+1;
h := h1 * h2 * h1^3 * h2^5;
gens := [MA ! G.i: i in [1..Ngens (G)]];
gens := [h * g * h^-1: g in gens];
F<t>:=BaseRing (MA);
s := ScalarMatrix (Degree (G), t);
G := sub<GL(Degree (G), F) |  gens, s>;
time IsFinite (G);
SetSeed (1);
time IsCentralByFinite (G);
"Ngens is ", Ngens (G);
"** Degree is ", Degree (G);

// example 3
SetVerbose ("Infinite", 1);

G := ReducibleNilpotentQ (4, 2);
H := ShephardTodd (36);
L := KroneckerProductOfLists ([G.i: i in [1..Ngens (G)]], 
[H.i: i in [1..Ngens (H)]]);
U := Universe (L);
G := sub<GL(Degree (U), Q) | L>;
R<u> := FunctionField (Rationals ());
v := u; w := -2 * v;
Px<X> := PolynomialRing (R);
Py<Y> := PolynomialRing (R);
f :=  Y^2- 3 * u * X * Y^2  + v * X^3;
facs := Factorisation (f);
F:=ext <R | facs[2][1]>;
n := Degree (G);
Z := 4 * X * Y;
MA:= MatrixAlgebra(F,n);
h1:= Id(MA);
h1[1][n]:= X+1;
h1[1][n]:= X+1;
h1[11][1]:=(Z^5-X^2*Z+Z*X*Y);
h1[22][19]:=1-X*Y*Z;
h1[12][n]:= X^20+X*Y^15+Y^10+Z^4*Y*X^5+1;
h1[13][15]:= X^3 - 5 * X + 1;
h1[28][22] := X^4 + X;
h1[n][n]:= (X^2+Y+Z+1);
h2:= Id(MA);
h2[n][n]:= (X^7+Z^6+1);
h2[10][11]:= X^2+X+1;
h2[18][4]:=(Y^3+X^2+X+1);
h2[22][32]:=1-X^2;
h2[42][18]:= X^50+Y^35+X^20+X^13+Y^2+1;
h := h1 * h2 * h1^3 * h2^5;
gens := [MA ! G.i: i in [1..Ngens (G)]];
gens := [h * g * h^-1: g in gens];
H := sub<GL(Degree (G), F) | gens >;
time IsFinite (H);
SetSeed (1);
time IsNilpotentByFinite (H);
time IsFinite (H);
time IsCompletelyReducible (H);
time IsFinite (H);
"Ngens is ", Ngens (H);
"** Degree is ", Degree (H);

// example 4
Q := GF (19);
v := PrimitiveElement (Q);
n := 6;
G := Sym (6);
S := Subgroups (G);
X := [x : x in S | IsSoluble(x`subgroup)];
A := X[#X]`subgroup;
M := PermutationModule (A, Q);
A := ActionGroup (M);
B := DiagonalMatrix (Q, [v : i in [1..n]]);
B[2][2] := 1;
G := sub<GL(n, Q) | A, B>;
d := 3;
MA := MatrixAlgebra (Q, d);
A := Identity (MA);
A[1][2] := 1;
B := Identity (MA);
B[2][3] := -1;
H := sub<GL(d, Q) | A, B>;
X := [G.i: i in [1..Ngens (G)]];
Y := [H.i: i in [1..Ngens (H)]];
L := KroneckerProductOfLists (X, Y);
G := sub <GL(d * n, Q) | L>;
G := ConstructConjugate (G, Q);
K:=BaseRing (G);
s :=ScalarMatrix (Degree (G), K.1);
H := sub<GL(Degree (G), K) | G, s>;
time IsFinite (H);
SetSeed (1);
time IsSoluble (H);
"Ngens is ", Ngens (H);
"** Degree is ", Degree (H);

// example 5

load "polenta-examples.m";
P := PolExamples ();
H := P[9];
T := ShephardTodd (30);
F := BaseRing (T);
x := Random (GL(4, Integers ()));
MA := MatrixAlgebra (F, 4);
x := MA!x;
x := Generic (T)!x;
T := T^x;
MA := MatrixAlgebra (F, Degree (H));
Z := Identity (MA);
Z[1][4] := F.1;
Z[2][1] := F.1 + F.1^2;
Z[3][4] := 2 * F.1 + F.1^2;
Z[4][3] := F.1^2;
Z := GL(Degree (H), F) ! Z;
X :=[Z * GL(Degree (H), F)! H.i * Z^-1: i in [1..Ngens (H)]];
H := sub<GL(Degree (H), F) | X>;
K := KroneckerProductOfLists ([H.i: i in [1..Ngens (H)]], [T.i: i in [1..Ngens 
(T)]]);
UU := Universe (K);
G := sub<GL(Degree (UU), F) | K>;
P := RandomProcess (G);
X := &*[Random (P): i in [1..100]];
G := G^X;
// G;
"Ngens is ", Ngens (G);
"** Degree is ", Degree (G);
SetVerbose ("Infinite", 1);
time IsFinite (G);
SetSeed (1);
time IsSolubleByFinite (G);
Degree (G);
"Ngens is ", Ngens (G);
"** Degree is ", Degree (G);

// example 6 

Z := Integers ();
Q := Rationals ();
G := SL(12, Z);
g := Random (G);
G := G^g;
G := ConstructConjugate (G, Q);
SetSeed (1);
time IsSolubleByFinite (G);
"Ngens is ", Ngens (G);
"** Degree is ", Degree (G);

// example 7 

Z := Integers ();
Q := Rationals ();
G := GL (2, Z);
a := G![1,1,0,1];
b := G![1,0,2,1];
G := sub < G | a, b>;
R<x> := PolynomialRing(Integers());
f := x^4 - 420*x^2 + 40000;
K<y> := NumberField(f);
MA := MatrixAlgebra (K, 2);
A := Identity (MA);
A[1][2] := K.1^2 + K.1 + 1;
A[2][1] := 2 * K.1 - 1;
G := sub<GL(2, K) | [A * MA! G.i * A^-1: i in [1..2]]>;

H := ReducibleNilpotent (8, 2, Q);
MA := MatrixAlgebra (K, Degree (H));
A := Identity (MA);
A[1][2] := K.1^3 + 2 * K.1 + 1;
A[2][1] := K.1^2 - K.1 + 5;
A[2][4] := K.1^2 - K.1 + 5;
A[5][7] := 3 * K.1^7 - 1;
A[7][3] := 13 * K.1^4 + 3;
A[8][2] := K.1^14 + 1;

H := sub<GL(Degree (H), K) | [A * MA! H.i * A^-1: i in [1..Ngens (H)]]>;

L := KroneckerProductOfLists ([G.i: i in [1..Ngens (G)]], 
        [H.i : i in [1..Ngens (H)]]);
G := sub< GL(32, K) | L>;
SetVerbose ("Infinite", 1);
IsFinite (G);
IsNilpotent (G);
SetSeed (1);
time IsSolubleByFinite (G);
"Ngens is ", Ngens (G);
"** Degree is ", Degree (G);

quit;
