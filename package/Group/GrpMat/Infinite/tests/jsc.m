SetEchoInput (true);
SetVerbose ("Infinite", 1);
SetVerbose ("CompositionTree", 0);

// examples similar to those used in D & F paper on deciding finiteness

// example 1 
Q := RationalField ();
// F<y>:= RationalFunctionField (Q, 1);
F<y>:= RationalFunctionField (Q);

X := 
[ [ [ 0, y^10, 0, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, y^-10, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, y^-15, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, y^15, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ],
      [ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ],
  [ [ 0, y^8, 0, 0, 0, 0, 0, 0, 0, 0 ], [ y^-8, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, y^-8, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 0, y^8, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ],
  [ [ -1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 ],
      [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 ], [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 ] ] ]
;

X := [&cat (x): x in X];
G11 := sub <GL(10, F) | X >;

"test example 1 1";
time flag := IsFinite(G11);
flag;
time flag := IsSolubleByFinite(G11);
flag;

"test example 1 2";
M := MonomialGroup (Q, 10);
G12 := ConstructConjugate (M,Q: Add := false);
time flag := IsFinite(G12);
flag;
time flag := IsSolubleByFinite(G12);
flag;

/* example 2 */

G22:=MonomialGroup (Q, 20);
MA := MatrixAlgebra (F, 20);
X := [MA ! G22.i: i in [1..Ngens (G22)]];

I := Identity (MA);

I[1][1] := y^30; I[2][2] := y^(-30);
X[1] := X[1] * I;

I[19][19] := y^40; I[20][20] := y^(-40);
X[2] := X[2] * I;

"test example 2 1";
G21 := sub<GL(20, F) | X>;
time flag := IsFinite(G21);
flag;
time flag := IsSolubleByFinite(G21);
flag;

X := [MA ! G22.i: i in [1..Ngens (G22)]];

I := Identity (MA);
I[1][2] := y^20; I[2][3] := y^25;
X[1] := X[1] * I;
X[2] := I * X[2];

"test example 2 2";
G22 := sub<GL(20, F) | X >;
time flag := IsFinite(G22);
flag;
// time flag := IsSolubleByFinite(G22);
// flag;

/* # 3 examples */
Q := RationalField ();
F<y>:= RationalFunctionField (Q, 1);

M := MonomialNilpotent (Q, 36);

MA := MatrixAlgebra (F, 36);
X := [MA ! M.i: i in [1..Ngens (M)]];

I := Identity (MA);
I[1][2] := y;
X :=  [x * I : x in X];

"test example 3 1";
G31 := sub<GL(36, F) | X>;
time flag := IsFinite(G31);
flag;
time flag := IsSolubleByFinite(G31);
flag;

G32 := ConstructConjugate (M,Q: Add := false);
time flag := IsFinite(G32);
time flag := IsSolubleByFinite(G32);
flag;

