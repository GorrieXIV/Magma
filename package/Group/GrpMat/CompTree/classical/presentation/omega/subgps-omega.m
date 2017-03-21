// in Omega+(2n, q) construct Omega+(2n - 2)
Q, R := MyOmegaPlusPres (2*n, q);
  v := Q.8; s1 := Q.4;
  a := v * (s1)^(v^-1);
  H := sub<Q| [Q.i:  i in [1..7]], a>;

// odd q 
// in Omega+(2n,q) construct Omega(2n - 1, q) 
S := Q.1 * Q.4; T := Q.2 * Q.5; Delta := Q.3 * Q.6; V := Q.4 * Q.8;
H := sub< Q | S, T, Delta, V>;

// even q
// in Omega+(2n,q) construct Omega(2n - 1, q) 

/* 
q := 8;
X := ClassicalStandardGenerators ("Omega+", 8, q);        
t := X[2];
V := X[8] * X[4]^(X[8]^-1);     
u := X[4];
v := X[8];
x := X[5];
L:=sub<Universe (X) | [X[i]:  i in [1..6]], 
                      (t*(x^u))^(v^-1), V, (X[1] * X[4])^(X[8]^-1)>;

*/

// even q
// in Omega+(2n,q) construct Omega(2n - 1, q) 
Q, R := MyOmegaPlusPres (2*n, q);
s := Q.1; t := Q.2; v := Q.8; x := Q.5; u := Q.4; 
V := v * u^(v^-1); 

H := sub< Q | [Q.i: i in [1..6]], 
              (t*(x^u))^(v^-1), V, (s * u)^(v^-1)>;

// in Omega-(2n, q) construct Omega(2n - 1, q)

X := ClassicalStandardGenerators ("Omega-", 2*n, q);
Y:= ClassicalStandardGenerators ("Omega+", 2 * n, q);
Z:=X cat Y;
H := sub<Universe (Z) | [Z[i]: i in [1,2,5] cat [6..11]]>;

H := sub<Q | Q.1, Q.2, Q.5, [Q.i: i in [6..11]]>;

// in Omega-(2n, q) construct Omega-(2n - 2, q)
gens := [Q.1, Q.2, Q.3, Q.4^(Q.5^-2)];
H := sub< Q | gens>;

// in Omega-(2n, q) construct Omega+(2n - 2, q)
gens := [Q.4, Q.5, Q.i: i in [6..11]];
H := sub< Q | gens>;

// in Omega(2n+1, q) construct Omega^+(2n, q)
X := MyOGenerators (d, q);
words := ConstructPlus (d, q);
Y:=Evaluate (words, X);
Z := X cat Y;
H:=sub<Universe (X) | [Z[i]: i in [3..11]]>;
LMGCompositionFactors (H);

  Q, R := MyOmegaPres (2 * n + 1, q);
  H := sub<Q | [Q.i: i in [3..11]]>;



