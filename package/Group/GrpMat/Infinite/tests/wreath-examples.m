
/* 
T := [];
for n in [3..10] do
   G := MaximalRational (n);
"Degree ", Degree (G);
tt := Cputime ();
   time f := IsFiniteMatrixGroup (G);
tt := Cputime (tt);

tt2 := Cputime ();
   time g := IsFinite (G);
tt2 := Cputime (tt2);
Append (~T, [tt, tt2]);
   "=============================";
end for;
*/


/* 
T := [];
for d in [6..10] do 
H := ShephardTodd (d);
for n in [6..10 by 1] do 
for k in PrimeBasis (n) do 
S := SylowSubgroup (Sym (n), k);
G := WreathExample (H, S);
"Degree ", Degree (G);
tt := Cputime ();
   time g := IsFinite (G);
tt := Cputime (tt);

tt2 := Cputime ();
   time f := IsFiniteMatrixGroup (G);
   "=============================";
tt2 := Cputime (tt2);
Append (~T, [d, n, k, tt, tt2]);
end for;

end for;
end for;
*/

/* 
S := Subgroups (Sym (6));
for i in [2..#S] do 
  s := S[i]`subgroup;
for d in [4..10] do 
H := ShephardTodd (d);
G := WreathExample (H, s);
"Degree ", Degree (G);
   time f := IsFiniteMatrixGroup (G);
   time g := IsFinite (G);
   "=============================";
end for;
end for;
*/

/* 
for q in [2..17] do 
if IsPrime (q) then s := PSL(2, q); end if;
for d in [4..10] do 
H := ShephardTodd (d);
G := WreathExample (H, s);
"Degree ", Degree (G);
   time f := IsFiniteMatrixGroup (G);
   time g := IsFinite (G);
   "=============================";
end for;
end for;
*/


/*
for d in [4..36] do 
G := ShephardTodd (d);
for n in [3..7] do 
for m in [1..NumberOfPrimitiveGroups (n)] do 
   P := ReflectionExample (G, n, m: Rational := true);
   d, n, m, Degree (P);
   time f := IsFiniteMatrixGroup (P);
   time g := IsFinite (P);
   "=============================";
end for;
end for;
end for;
*/

/* 
DB := RationalMatrixGroupDatabase();
for d in [4..10] do 
for e in [1..NumberOfGroups (DB, d)] do 
for n in [3..7] do 
for m in [1..NumberOfPrimitiveGroups (n)] do 
   P := PrimitiveExample (d, e, n, m: Rational := true);
   d, e, n, m, Degree (P);
   time f := IsFiniteMatrixGroup (P);
   time g := IsFinite (P);
   "=============================";
end for;
end for;
end for;
end for;
*/


/* 
load m11;
s := G;
for d in [8..10] do 
H := ShephardTodd (d);
G := WreathExample (H, s);
"Degree ", Degree (G);
   time f := IsFiniteMatrixGroup (G);
   time g := IsFinite (G);
   "=============================";
end for;
*/
