freeze;

SetGlobalTCParameters (:Hard,CosetLimit:=10^8,Print:=10^5);

AttachSpec ("spec");

// Omega+(2n, q) as subgroup of Omega(2n + 1, q) 

d := 7; q := 3;

for d in [3] do 
for q in [3, 5, 7] do 
Q, R := int_StandardPresentationForOmega (d, q: MinGens := false);
Q := SLPToFP (Q, R);
#Q;
end for;
end for;

for d in [5,7] do 
for q in [3,5] do 
Q, R := int_StandardPresentationForOmega (d, q: MinGens := false);
Q := SLPToFP (Q, R);
H := sub<Q | [Q.i: i in [3..11]]>;
I:=CosetImage (Q, H);
RandomSchreier (I);
#I;
CompositionFactors (I);
end for;
end for;

for d in [4] do 
for q in [2,3,4, 5, 7,8,9] do 
Q, R := int_StandardPresentationForOmega (d, q: MinGens := false);
Q := SLPToFP (Q, R);
H:=sub<Q|>;
I:=CosetImage (Q, H);
#Q;
end for;
end for;

// in Omega+(2n,q) construct Omega(2n - 1, q) 
n:=4;
for n in [3] do 
d := 2 * n;
for q in [2,3,4, 5, 9] do 
Q, R := int_StandardPresentationForOmega (d, q: Type := "Omega+", 
MinGens := false);
Q := SLPToFP (Q, R);
s := Q.1; t := Q.2; v := Q.8; x := Q.5; u := Q.4; 
V := v * u^(v^-1); 
H := sub< Q | [Q.i: i in [1..6]], 
              (t*(x^u))^(v^-1), V, (s * u)^(v^-1)>;
I:=CosetImage (Q, H);
RandomSchreier (I);
#I;
#I;
CompositionFactors (I);
end for;
end for;

// in Omega-(2n,q) construct Omega(2n - 1, q) 
n:=3;
d := 2 * n;
for q in [2,3,4, 5, 9] do 
Q, R := int_StandardPresentationForOmega (d, q: Type := "Omega-", 
MinGens := false);
Q := SLPToFP (Q, R);
H := sub<Q | Q.1, Q.2, Q.5, [Q.i: i in [6..11]]>;
I:=CosetImage (Q, H);
RandomSchreier (I);
#I;
CompositionFactors (I);
end for;


// in Omega-(2n, q) construct Omega-(2n - 2, q)
n:=4;
d := 2 * n;
for q in [2,3,4, 5, 9] do 
Q, R := int_StandardPresentationForOmega (d, q: 
         Type := "Omega-", MinGens := false);
Q := SLPToFP (Q, R);
gens := [Q.1, Q.2, Q.3, Q.4^(Q.5^-2)];
H := sub< Q | gens>;
I:=CosetImage (Q, H);
RandomSchreier (I);
#I;
CompositionFactors (I);
end for;


