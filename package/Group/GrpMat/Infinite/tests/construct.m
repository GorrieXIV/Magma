
MonomialSylow := function (F, p, a)
   S := SylowSubgroup (Sym (p^a), p); 
   return [PermutationMatrix (F, S.i): i in [1..Ngens (S)]];
end function;

KroneckerProductOfLists := function (X, Y)
   return [KroneckerProduct (x, Y[i]): i in [1..#Y], x in X];
end function;

MonomialNilpotent := function (F, n)
   b := PrimeBasis (n);
   L := [* MonomialSylow (F, l, Valuation (n, l)): l in b *];
   X := L[1];
   for i in [2..#L] do X := KroneckerProductOfLists (X, L[i]); end for;
   return sub<GL(n, F) | X >;
end function;

/* reducible but not completely reducible subgroups of GL(m*k, Q); 
   entries chosen from [0..l]  */
  
ReducibleNilpotentQ := function (m, k: l := 1)
   Q := RationalField ();
   M := MonomialNilpotent (Q, k); 
   if m eq 1 then return M; end if;

   L := [];
   MA := MatrixAlgebra (Q, m);

   /* upper triangular matrices */
   for i in [1..m - 1] do
      L[i] := Id (MA);
      L[i][i][m] := Random (Q, l);
   end for;

   X := KroneckerProductOfLists (L, [M.i: i in [1..Ngens (M)]]);

   return sub<GL(m * k, Q) | X>;

end function;

/* construct maximal absolutely irreducible nilpotent 
   subgroup G of GL(n, p^t); return true and G, 
   or return false if such subgroups do not exist.

   GL(n,q) contains absolutely irreducible nilpotent subgroups
   if r|q-1 for each prime divisor r of n;

   Let n = r1^a1...rk^ak be the prime facorization of n. 
   G is a Kronecker product of groups G1,...,Gk, where 
   Gi = Hi \cdot F*, and Hi is Sylow pi-subgroup of GL(ri^ai,F)
*/

MaximalAbsolutelyIrreducibleNilpotentMatrixGroup := function (n, p, t)
   if IsPrime (p) eq false then error p, "must be prime"; end if;
   if t lt 1 then error t, "must be positive"; end if;

   q := p^t;
   factor := Factorisation (n);
   b := [f[1]: f in factor];
   l := [f[2]: f in factor];

   if exists{r : r in b | (q - 1) mod r ne 0} then 
      return false, _; 
   end if;
   
   L := [ClassicalSylow(GL (b[i]^l[i], q), b[i]): i in [1..#b]];
   W := [L[1].i : i in [1..Ngens (L[1])]];
   for i in [2..#b] do 
      W := [KroneckerProduct (w, l): w in W, l in Generators (L[i])];
   end for;

   W := [GL(n, q) | w : w in W];
   F<w> := GF(p, t);
   Append (~W, ScalarMatrix (n, w));

   return true, sub<GL(n, q) | W >;
end function;

/* reducible subgroup of GL(n * k, F) */

ReducibleNilpotentFF := function (n, k, F)

   q := #F;
   flag, p, t := IsPrimePower (q);
   w := PrimitiveElement (F);

   flag, U := MaximalAbsolutelyIrreducibleNilpotentMatrixGroup (k, p, t);
   if not flag then return false; end if;

   MA := MatrixAlgebra (F, n);

   /* upper triangular matrices */
   L := [ MA | ];
   for i in [1..n - 1] do
      L[i] := Id (MA);
      L[i][i][n] := w;
   end for;
   X := [KroneckerProduct (L[j], U.i): i in [1..Ngens (U)], j in [1..#L]];
   return sub<GL(n * k, F) | X >;
end function;

/* return reducible subgroup of GL (n * k, F)
   where F is finite field or Q;
   if latter then matrix entries are in range [1..l] */
 
ReducibleNilpotent := function (n, k, F: l := 1)
   if IsFinite (F) then return ReducibleNilpotentFF (n, k, F); 
   else return ReducibleNilpotentQ (n, k: l := l); end if;
end function;

/* nilpotent subgroup of GL(n, q) having k p-factors */

NilpotentFF := function (n, q, k)
   G := GL(n, q);
   o := #G;
   B := PrimeBasis (o);
   Exclude (~B, Characteristic (BaseRing (G)));
   S := [ClassicalSylow (G, Random (B)): i in [1..k]];
   N := DirectProduct (S);
   return N;
end function;

/* random rational subgroup of GL(n, Q) where entries lie in range [0..k] */

RandomRational := function (n, k)
   Q := RationalField ();
   MA := MatrixAlgebra (Q, n);
   L := [];
   repeat 
      a := [Random (Q, 10): i in [1..n^2]];
      b := MA!a;
      if Determinant (b) ne 0 then Append (~L, b); end if;
   until #L ge k;
   return sub<GL(n, Q) | L>;
end function;

/* nilpotent subgroup of GL(n, q) embedded in rationals */

NilpotentRational := function (n, q, k)
   G := NilpotentFF (n, q, k);
   Q := RationalField ();
   Z := Integers ();
   E := [Eltseq (G.i): i in [1..Ngens (G)]];
   E := [[Z!x: x in e]: e in E];
   return sub <GL(Degree (G), Q) | E >;
end function;

/* G defined over prime field, embed in Q */

FiniteToRational := function (G)
   Q := RationalField ();
   Z := Integers ();
   E := [Eltseq (G.i): i in [1..Ngens (G)]];
   E := [[Z!x: x in e]: e in E];
   return sub <GL(Degree (G), Q) | E >;
end function;

ConstructConjugate := function (G, K: Number := false, 
   Add := false, Uni := true)
   if Number then 
      F<y> := NumberField (K);
   elif Uni then 
      F<y> := RationalFunctionField (K);
   else 
      F<y> := RationalFunctionField (K, 1);
   end if;
   n := Degree (G);
   MA := MatrixAlgebra (F, n);
   e := Identity (MA);
   for i in [1..n] do
      for j in [1..n] do
         if i lt j then e[i][j] := y+i*y^0; end if;
      end for;
   end for;
   if Add then 
      return sub<GL(n, F) | e, [e * MA ! g * e^-1: g in Generators (G)]>;
   else 
      return sub<GL(n, F) | [e * MA ! g * e^-1: g in Generators (G)]>;
   end if;
end function;

/* 
Q := Rationals ();
F<t>:= RationalFunctionField (Q);
M:=MatrixAlgebra (F, 2);
a := M![t,0,1,t];
b := M![t^2 + t + 1, t, 0, 1];
c:= M![t/(t^2 + t + 1),0,1,1/t];
A := sub <M | a, b, c>;
H := sub <GL(2, F) | a, b, c>;

Q := Rationals ();
F<t, u>:= RationalFunctionField (Q, 2);
M:= MatrixAlgebra (F, 2);
a := M![t * u,0,1,t/(t * u + t + 1)];
b := M![t^2 + t + 1, t, 0, 1];
c:= M![t/(u * t^2 + t + u ),0,u,(u * t^2 + t)/t];
A := sub <M | a, b, c>;
H := sub <GL(2, F) | a, b, c>;

*/


TestFF2or3:= function(n,q)
F<X,Y,Z>:= FunctionField(GF(q),3);
G:= GL(n,F);
H:= GL(n,GF(q));
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

TestFF:= function(n,q);

/*n should be greater than 10 to be safe with the
definition of the infinite order matrices*/

F<X>:= FunctionField(GF(q));

G:= GL(n,F);

H:= GL(n,GF(q));

MA:= MatrixAlgebra(F,n);


h1:= Id(MA);

h1[n][n]:= (X^2+1)/(X^5-X^2+X);

h1[1][n]:= X+1;

h1[1][1]:=(X^5-X^2+X)/(X^2+1);

h1[2][1]:=1-X;

h1[2][n]:= X^20+X^15+X^10+X^5+1;


h2:= Id(MA);

h2[n][n]:= (X^7+X^6+1)/(X^3+X^2+X+1);

h2[1][n]:= X^2+X+1;

h2[1][1]:=(X^3+X^2+X+1)/(X^7+X^6+1);

h2[2][1]:=1-X^2;

h2[2][n]:= X^50+X^35+X^20+X^13+X^2+1;


h3:= Id(MA);

h3[n][n]:= (X^17+X^5+111111)/(X^3+X^2+X+1);

h3[1][n]:= X^112+X;

h3[1][1]:=(X^3+X^2+X+1)/(X^17+X^5+111111);

h3[2][1]:=1-X^2;

h3[2][n]:= X^5+X^3+X^2+X+1;


h4:= Id(MA);

h4[n][n]:= (X^7+X^5-X^90)/(X^3+X^2+X+1);

h4[1][n]:= X^112+X^3;

h4[1][1]:=(X^3+X^2+X+1)/(X^7+X^5-X^90);

h4[2][1]:=1-X^230;

h4[2][n]:= X/(X^1000-1);


h5:= Id(MA);

h5[n][n]:= (X^27+X^15-X^9)/(X^3-X^2-X+1);

h5[1][n]:= X^12+X^3+X+29;

h5[1][n-1]:= X^12+X^3+X+29;

h5[1][1]:=(X^3-X^2-X+1)/(X^27+X^15-X^9);

h5[2][1]:=1-X^230;

h5[3][n]:= (X^91-X^7+13)/(X^10-100*X);


h6:= Id(MA);

h6[n][n]:= (X^7+X^5-X^90)/(X^3+X^2+X+1);

h6[1][n]:= X^112+X^3;

h6[1][1]:=(X^3+X^2+X+1)/(X^7+X^5-X^90);

h6[2][1]:=X^7-X^23;

h6[2][n-1]:= X/(X^101-119*X);


h7:= Id(MA);

h7[n][n]:= (X^7+X^5-X^90)/(X^3+X^2+X+1);

h7[1][n]:= X^53+X^35;

h7[1][1]:=(X^3+X^2+X+1)/(X^7+X^5-X^90);

h7[2][1]:=X^67-X^22;

h7[2][n-2]:= X/(X^1000-1);


h8:= Id(MA);

h8[n][n]:= (X^17-X^5+X^90)/(X^3+X^2+X+1);

h8[1][n-1]:= X^2+X^3;

h8[1][1]:=(X^3+X^2+X+1)/(X^17-X^5+X^90);

h8[2][1]:=1-X^230;

h8[2][n]:= X/(X^1000-1);


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

/*This one accepts any input and conjugates it*/

TestFF2:= function(Kr);

n:= Degree(Kr);

E:= BaseRing(Kr);

F<X>:= FunctionField(E);

g:= GL(n,F);

S:= Generators(Kr);

MA:= MatrixAlgebra(F,n);

h:= Id(MA);

h[n][n]:= X^2+1;

h[1][n]:= X+1;

h[1][n-1]:= (X^17-31*X^2+13)/(X^68+5*X^5+3*X^3+10091);

l:= [];

for i in [1..Ngens(Kr)] do;
l:= Append(l,MA!Kr.i);
end for;

lit:= [];

for x in l do;
lit:= Append(lit,h*x*h^-1);
end for;

triu:= sub<g|lit>;

return triu;

end function;

/*Standalone Kroneckering function*/

KroneckerProductOfLists := function (X, Y)
   return [KroneckerProduct (x, Y[i]): i in [1..#Y], x in X];
end function;

/*Standalone Diagonal Joining function*/

DiagonalJoinOfLists := function (X, Y)
   return [DiagonalJoin (x, Y[i]): i in [1..#Y], x in X];
end function;


/*A nilpotent as Kronecker product of Sylows in different dimensions*/

TestNilpotentFF:= function(p,m,r,n,q);

s:= ClassicalSylow(SL(p^m,q),p);

t:= ClassicalSylow(SL(r^n,q),r);

Kroe := KroneckerProductOfLists ([s.i: i in [1..Ngens (s)]], [t.i: i in [1..Ngens (t)]]);

u:= sub<GL((p^m)*(r^n), q) | Kroe>;

ute:= TestFF2(u);

return ute;

end function;

/*A nilpotent as DiagonalJoin of different Sylows in same dimensions*/

TestNilpotentBlockFF:= function(n,p,r,q);

s:= ClassicalSylow(SL(n,q),p);

t:= ClassicalSylow(SL(n,q),r);

Stitch := DiagonalJoinOfLists([s.i: i in [1..Ngens (s)]], [t.i: i in [1..Ngens (t)]]);

ur:= sub<GL(2*n, q) | Stitch>;

bloke:= TestFF2(ur);

return bloke;

end function;

/* TestUnipotentFF constructs a unipotent subgroup of GL(n, GF(q)(x))
i.e. a finite nilpotent reducible but not completely reducible subgroup 
of GL(n, GF(q)(x).*/

TestUnipotentFF := function(n, q, r)

F<X>:= FunctionField(GF(q));

G:= GL(n,F);

MA:= MatrixAlgebra(F,n);

h := Id(MA);

S := [];

for i in [1..r] do S[i] := h; end for;

for k in [1..r] do
   for i in [1..n] do
      for j in [1..n] do
         if j gt i then S[k][i][j] := X^i + X^k + j; end if;
      end for;
   end for;
end for;

uni:= sub<G|S>;

return uni;

end function;

/*Kronecker product of conjugate of GL with unipotent: non-nilpotent,
non-completely reducible. Note the dimension n must be even, ge 6*/

TestNonCredFF:= function(n,q,dim,are: Soluble := false) 

F<X>:= FunctionField(GF(q));

H:= GL(n,GF(q));

if Soluble then 
twid := TestFF2 (ClassicalSylow (H, 2));
else 
twid:= TestFF2(H);
end if;

unipo:= TestUnipotentFF(dim,q,are);

kraw := KroneckerProductOfLists ([twid.i: i in [1..Ngens (twid)]], [unipo.i: i in [1..Ngens (unipo)]]);

noncred:= sub<GL(n*dim, F) | kraw>;

Mat:= MatrixAlgebra(F,n);

Mat2:= MatrixAlgebra(F,dim);

skel:= Id(Mat);

for i in [1..n/2] do
skel[i][i]:= X;
end for;

for i in [(n/2)+1..n] do
skel[i][i]:=1/X;
end for;

/*skel[n][n]:= (X^7+X^5-X^90)/(X^3+X^2+X+1);

skel[1][n]:= X^53+X^27;

skel[1][1]:=(X^3+X^2+X+1)/(X^7+X^5-X^90);

skel[2][n-2]:= X/(X^500-1);*/

skelo:= KroneckerProduct(skel, Id(Mat2));

skel2:= Id(Mat);

for i in [1..n/2] do
skel2[i][i]:= X^10+X^67-8*X^2+1;
end for;

for i in [(n/2)+1..n] do
skel2[i][i]:=1/(X^10+X^67-8*X^2+1);
end for;

skel2[1][2]:= (X^30-87*X^67+X^5+X^4+X^3+X^2)/(59*X^1200-X^12+X+1);

skel2[2][3]:= (X^49-7*X^76+2)/(89*X^106-X^2+X+1);

skel2[2][4]:= (X^91+6*X^243)/(5*X^3-X^2+X+1);

skel2[3][4]:= (X^30-87*X^67+X+X^32+4)/(59*X^99-X^2+X+1);

skelo2:= KroneckerProduct(skel2, Id(Mat2));

skel3:= Id(Mat);

for i in [1..n/2] do
skel3[i][i]:= X^20-71*X^27+89*X^5;
end for;

for i in [(n/2)+1..n] do
skel3[i][i]:=1/(X^20-71*X^27+89*X^5);
end for;

skel3[1][2]:= 5*X^132-2*X^3+X+X^67+X^89+X^389+X^54;

/*skel3[2][3]:= (X^79-X)/(89*X^7-20*X^2+X+1);

skel3[2][4]:= X^123-7*X^376+4;*/

skel3[2][5]:= (71*X^7+X^8-X^9+X^119+X^83)/(2*X^16-100*X^2+X+1);

skel3[3][4]:= X^31+6*X^243-13;

skel3[4][5]:= (X^90-X^472+X+X^32+X^4)/(59*X^10-92*X^2+1);

skelo3:= KroneckerProduct(skel3, Id(Mat2));

noncred2:= sub<GL(n*dim, F) | kraw, skelo, skelo2, skelo3>;

return noncred, noncred2;

end function;


/*Kronecker product of finite nilpotent with unipotent; hence 
nilpotent, reducible and not completely reducible*/

/*TestMixNilFF:= function(p,m,r,n,q,dim,are);*/

TestMixedNilFF:= function(n,p,r,q,dim,are);

F<X>:= FunctionField(GF(q));

Mat:= MatrixAlgebra(F,2*n);

/*cred:= TestNilpotentFF(p,m,r,n,q); Use diagonal join instead
because in adding infinite diagonals need to */

cred:= TestNilpotentBlockFF(n,p,r,q);

unip:= TestUnipotentFF(dim,q,are);

krow := KroneckerProductOfLists ([cred.i: i in [1..Ngens (cred)]], [unip.i: i in [1..Ngens (unip)]]);

mixl:= sub<GL(2*n*dim, F) | krow>;

Mat2:= MatrixAlgebra(F,2*n*dim);

scala:= Id(Mat2);

scala2:= Id(Mat2);

for i in [1..n*dim] do
scala[i][i]:= X;
end for;

for i in [n*dim+1..2*n*dim] do
scala[i][i]:=1/X;
end for;

for i in [1..n*dim] do
scala2[i][i]:= X^10+89*X^5+X^3+1001*X^2-X+2;
end for;

for i in [n*dim+1..2*n*dim] do
scala2[i][i]:=1/(X^10+89*X^5+X^3+1001*X^2-X+2);
end for;

mixl2:= sub<GL(2*n*dim, F) | krow,scala,scala2>;

return mixl, mixl2;

end function;

/*Large degree single element examples. n must be even. N.B. repeating
experiments chooses a different random element, so run in a single 
Magma session*/

TestSingleElementFF:= function(n,m,q);

F<X>:= FunctionField(GF(q));

G:= GL(n*m,F);

unip:= TestUnipotentFF(m,q,1);

repeat 
h1:= Random(GL(n,q));
until IsIdentity (h1) eq false;

if GCD(Order(h1),q) eq 1 then

ah1:= TestFF2(sub<GL(n,q)|h1>);

aah1:= KroneckerProduct(ah1.1,unip.1);

singl:= sub<G|aah1>;

else singl:= sub<G|Id(G)>;

end if;

h2:= Random(GL(n,q));

ah2:= TestFF2(sub<GL(n,q)|h2>);

ah22:= MatrixAlgebra(F,n)!ah2.1;

for i in [1..n/2] do

ah22[i][i]:= X;

end for; 

for i in [(n/2)+1..n] do

ah22[i][i]:= 1/X;

end for;

for i in [1..n] do;

for j in [i+1..n] do;

ah22[i][j]:= 0;

end for;

end for;

aah2:= KroneckerProduct(ah22,unip.1);

singl2:= sub<G|aah2>;

return singl, singl2;

end function;

/*Monomial Example*/

MonomialGroup := function (F, n)

if Type (F) eq RngIntElt then
   q := F; F := GF (q);
   G := SymmetricGroup (n);
   S := [G.i: i in [1..Ngens (G)]];
   L := [PermutationMatrix (GF(q), G.i) : i in [1..Ngens (G)]];
   MA := MatrixAlgebra (GF(q), n);
   e := Identity (MA);
   e[1][1] := PrimitiveElement(F);
   return sub <GL(n, q) | L, e>;
else
   G := SymmetricGroup (n);
   S := [G.i: i in [1..Ngens (G)]];
   L := [PermutationMatrix (F, G.i) : i in [1..Ngens (G)]];
   MA := MatrixAlgebra (F, n);
   e := Identity (MA);
   e[1][1] := -1;
   return sub <GL(n, F) | L, e>;
end if;
end function;

