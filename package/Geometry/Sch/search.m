freeze;

declare verbose PointSearch,2;
Z:=Integers();

function get_points(S,EQ,v,p) d:=Dimension(S);
 if #[x : x in DefiningEquations(S) | x ne 0] eq 0 then
  R:=[Eltseq(x) : x in SetToSequence(Points(AffineSpace(GF(p),d)))];
  return R; end if;
 if d gt 0 then
  vprintf PointSearch,2 : "Local pts v:%o Fp-dimension is %o\n",v,d; end if;
 if d le 0 then return [Eltseq(x) : x in Points(S)]; end if;
 d:=Dimension(Ambient(S)); PTS:=[];
 if d gt 0 then A<[X]>:=AffineSpace(GF(p),d-1); end if;
 for u in GF(p) do
  w:=v cat [u] cat [X[i] : i in [1..(d-1)]];
  GP:=get_points(Scheme(A,[Evaluate(f,w) : f in EQ]),EQ,v cat [u],p);
  PTS cat:=[[u] cat x : x in GP]; end for; return PTS; end function;

function doit(EQ,M,W,h,p,dim)
 for n in [1..h] do V:=[[Evaluate(f,Eltseq(w)) : f in EQ] : w in W];
  V:=[Vector([GF(p)!Integers()!(-u/p^n) : u in v]) : v in V];
  b,S,K:=IsConsistent(M,V);
  if not b or Dimension(K) gt dim then vprintf PointSearch,1 :
                        "Problem at %o\n",ChangeUniverse(Eltseq(W[1]),GF(p));
   return false,_; end if;
  U:=[[0] cat ChangeUniverse(Eltseq(s+Random(K)),Z) : s in S];
  W:=[[W[j][i]+p^n*U[j][i] : i in [1..#U[j]]] : j in [1..#W]]; end for;
 return true,W; end function;

function liftpt(EQ,J,P,p,e,n,h,dim) Zph:=Integers(p^(h+1)); Z:=Integers();
 N:=Matrix(e,n+1,[Evaluate(f,P): f in Eltseq(J)]);
 N:=Submatrix(Transpose(N),2,1,n,e); w:=ChangeUniverse(P,Z);
 Q:=[Vector(w)+
        p*Vector([0] cat [Random(0,p^h) : i in [1..n]]) : j in [1..(2*n)]];
 b,S:=doit(EQ,N,Q,h,p,dim); if not b then return false,_; end if;
 sol:=[ChangeUniverse(s,Zph) : s in S];
 M:=Submatrix(ChangeRing(HermiteForm(Matrix(sol)),Z),1,1,n+1,n+1);
 if M[n+1][n+1] ne 0 then
  vprintf PointSearch,2 : "Done with %o\n",P; return true,M; end if;
 M:=ChangeRing(HermiteForm(ChangeRing(M,Integers(p^h))),Z);
 r:=Rank(M)-1; // rarely called, even if expensive
 vprintf PointSearch,2: "Only have %o lifts with %o\n",r,P;
 while true do R:=r; sz:=Max(2*n,Ilog(p,2^30)); M:=Submatrix(M,1,1,R,n+1);
  Q:=[Vector(w)+
         p*Vector([0] cat [Random(0,p^h) : i in [1..n]]) : j in [1..sz]];
  b,S:=doit(EQ,N,Q,h,p,dim); if not b then return false,_; end if;
  sol:=[ChangeUniverse(s,Zph) : s in S];
  sol:=Matrix([Eltseq(M[i]) : i in [1..NumberOfRows(M)]] cat sol);
  M:=Submatrix(ChangeRing(HermiteForm(Matrix(sol)),Z),1,1,n+1,n+1);
  if M[n+1][n+1] ne 0 then
   vprintf PointSearch,2 : "Done with %o\n",P; return true,M; end if;
  r:=Rank(M)-1; if r eq R then break; end if;
  vprintf PointSearch,2: "Now have %o lifts with %o\n",r,P; end while;
 M:=ChangeRing(HermiteForm(ChangeRing(M,Integers(p^h))),Z);
 ROWS:=[i : i in [1..(n+1)] | Norm(M[i]) eq 0];
 LEFT:=[Min([i : i in [1..(n+1)] | r[i] ne 0]) : r in Rows(M) | Norm(r) ne 0];
 EMPTY:=SetToSequence(Set([1..(n+1)]) diff Set(LEFT)); assert #EMPTY eq #ROWS;
 for i in [1..#ROWS] do M[ROWS[i]][EMPTY[i]]:=p^h; end for;
 assert IsPrimePower(Abs(Determinant(M))); // silly check
 vprintf PointSearch,2 : "done with %o (possible skips?)\n",P;
 return true,M; end function;

function local_points(S,p,d : affine:=false, nonsing:=false)
 n:=Dimension(Ambient(S)); J:=JacobianMatrix(S);
 EQ:=DefiningEquations(S); e:=#EQ; N:=[MatrixAlgebra(Integers(),n+1)|];
 K<[X]>:=AffineSpace(GF(p),n);
 if d eq 1 then h:=n;
 else o:=n; h:=0;
  while o ge 0 do o:=o-Binomial(h+d-1,d-1); h:=h+1; end while; h:=h-1; end if;
 vprintf PointSearch,2 : "liftht:%o schdim:%o projdim:%o eqs:%o\n",h,d,n,e;

 seq:=[1] cat [X[i] : i in [1..n]]; Sp:=Scheme(K,[Evaluate(f,seq) : f in EQ]);
 pts:=get_points(Sp,EQ,[1],p); pts:=[[1] cat x : x in pts];

 for P in pts do b,M:=liftpt(EQ,J,P,p,e,n,h,d);
  if not b and nonsing then return false; end if;
  if b then N cat:=[M]; end if; end for;

 Z:=[A.i : i in [1..n+1]] where A := Ambient(S); v:=Z;
 // if affine then return N; end if;
 for j in [2..(n+1)] do T:=v[j]; v[j]:=v[1]; v[1]:=T;
  vprintf PointSearch,2 : "Swapping variables 1 and %o\n",j;
  Ej:=[Evaluate(f,v): f in EQ]; dd:=Max(d-j+1,0);
  Jj:=Matrix(e,n+1,[[Derivative(f,Z[i]) : i in [1..(n+1)]] : f in Ej]);
  if (n+1) gt j then K<[X]>:=AffineSpace(GF(p),n+1-j);
   seq:=[1] cat [0 : i in [1..(j-1)]] cat [X[i] : i in [1..(n+1-j)]];
   Sp:=Scheme(K,[Evaluate(f,seq) : f in Ej]);
   pts:=get_points(Sp,Ej,[1] cat [0 : i in [1..(j-1)]],p);
   pts:=[[1] cat [0 : i in [1..(j-1)]] cat x : x in pts];
  else seq:=[GF(p)!1] cat [0 : i in [1..n]];
   if #[x: x in [Evaluate(f,seq) : f in Ej] | x ne 0] eq 0 then
    pts:=[seq]; else pts:=[]; end if; end if;
  for P in pts do b,M:=liftpt(Ej,Jj,P,p,e,n,h,d);
   if not b and nonsing then return false; end if;
   if b then N cat:=[SwapColumns(M,1,j)]; end if; end for;
 T:=v[j]; v[j]:=v[1]; v[1]:=T; end for; return N; end function;

function EB(H,d,N) // compute prime for height H and dim d in P^N
 l:=1; e:=0; r:=d-1; m:=0; n:=N+1;
  while n gt 0 do m:=Min(l,n); n:=n-m; e:=e+m*(r-d+1);
   l:=l+Binomial(r,d-2); r:=r+1; end while;
 return Ceiling(H^((N+1)/e)); end function;

function roots(f) if f eq 0 then return {1}; end if;
 return {r[1] : r in Roots(f)}; end function;

function short_vectors(L,B,N,EQ,EQ2) L:=LLL(L : Delta:=0.99999);
 M:=ChangeRing(Matrix(Basis(L)),Rationals()); U:=Transpose(M^(-1)*B);
 v:=[Floor(&+[Abs(x) : x in Eltseq(U[i])]) : i in [1..NumberOfRows(U)]];
// skinny lattices ?
if true then
 if v[1] lt 100 then SV:=[]; for t in ShortVectors(L,N) do x:=t[1]; u:=Vector(x);
  for F in EQ2 do if InnerProduct(u*F, u) ne 0 then continue t; end if; end for;
  for F in EQ do if Evaluate(F, Eltseq(x)) ne 0 then continue t; end if; end for;
  Append(~SV, Eltseq(x)); end for; return SV; end if;
 if &+[v[i] : i in [2..#v]] eq 0 then return [Eltseq(Basis(L)[1])]; end if;
 w:=Remove(v,1); C:=CartesianProduct([Integers(2*x+1) : x in w]);
elif #[j : j in [1..Dimension(L)] | v[j] ne 0] ne 0 then
 n:=Dimension(L); VEC:=[Rows(U)[j] : j in [1..n] | v[j] ne 0];
 _<[W]>:=PolynomialRing(Rationals(),#VEC);
 ev:=[Evaluate(de,[&+[VEC[j][i]*W[j] : j in [1..#VEC]] : i in [1..n]])
	         : de in EQ]; Gcd(ev);
end if;
vprintf PointSearch, 1: "[SKINNY:%o,%o] ", v[1], v[2];
//"SKIPPED SKINNY", v; return [];
// work on this
 Y := PolynomialRing(Rationals()); z := Y.1; M:=ChangeRing(M,Y); E:=[];
 for t in C do u:=Vector([z] cat [Integers()!x : x in t]);
  es:=Eltseq(u*M); ro:=SetToSequence(&meet{roots(Evaluate(e,es)) : e in EQ});
  for r in ro do ES:=[Evaluate(e,r) : e in es]; E cat:=[ES]; end for; end for;
 E:=[x : x in E | Max(x) ne 0 or Min(x) ne 0];
 for i in [1..#E] do L:=LCM([Denominator(x) : x in E[i]]);
  E[i]:=[x*L : x in E[i]]; end for;
 for i in [1..#E] do G:=GCD([Numerator(x) : x in E[i]]);
  E[i]:=[x/G : x in E[i]]; end for; E:=[ChangeUniverse(x,Integers()) : x in E];
 return E; end function;

function rGCD(S) B:=Universe(S);
 d:=LCM([Denominator(Rationals()!x): x in S | x ne 0] cat [1]);
 return B!(GCD([IntegerRing()!(x*d): x in S])/d); end function;

function naive_projective_closure(S) 
 assert IsAffine(S);  
 /*
 Sproj_ideal,homog_map:=Homogenization(Ideal(S));
 // the new variable is first, by default
 Sproj:=Scheme(ProjectiveSpace(Generic(Sproj_ideal)),Sproj_ideal);
 S_to_Sproj := map< S -> Sproj |
               [Sproj.i @@ homog_map : i in [1..Length(Ambient(Sproj))]],
                               : Check:=true >;
 bool, Sproj_to_S := IsInvertible(S_to_Sproj); assert bool; // hopeless
 return Sproj, S_to_Sproj, Sproj_to_S, 1; 
 */
 A := Ambient(S);
 Sproj :=  ProjectiveClosure(S);
 A_to_Aproj := ProjectiveClosureMap(A);
 S_to_Sproj := map< S -> Sproj | DefiningPolynomials(A_to_Aproj), 
                                 InverseDefiningPolynomials(A_to_Aproj) 
                               : Check:=false, CheckInverse:=false >;
 // get patch index
 pt := Eltseq(A_to_Aproj(A![0 : i in [1..Dimension(A)]]));
 inds := [i : i in [1..#pt] | pt[i] ne 0]; assert #inds eq 1;

 return Sproj, S_to_Sproj, Inverse(S_to_Sproj), inds[1];
end function;

// PointSearch previously declared for Sch[FldRat],
// but that stuffs up signature matching 
// for all input types that do not admit extended types.
// Nonsingular flag added March 2010, SRD.
DIM:=Dimension;

intrinsic PointSearch
(S::Sch, H::RngIntElt :
 Primes:=[], Dimension:=0, Nonsingular:=false, OnlyOne:=false)  -> SeqEnum
{Search for rational points of height up to approximately H
 on an affine or projective scheme defined over Q.
 (Uses a lattice-based search method)}

 require Type(BaseRing(S)) eq FldRat : "The scheme must be defined over the rationals.";

 A:=Ambient(S); 
 affine:=IsAffine(A);
 if affine then 
  Saff:=S; 
  S, Saff_to_S, S_to_Saff, patch := naive_projective_closure(Saff); 
 end if;

 A:=Ambient(S);
 require IsProjective(A):
 "Scheme must be in an affine space or a projective space";
 G:=Gradings(S); require #G eq 1: "Scheme can only have one grading";
 require Min(G[1]) eq Max(G[1]): "Scheme cannot be in weighted proj space";
 if not Nonsingular and assigned S`Nonsingular 
  then Nonsingular:=S`Nonsingular; end if;
 n:=DIM(A);
 if Dimension eq 0 then d:=DIM(S); else d:=Dimension; end if;
 require d ne 0: "Scheme must be positive-dimensional";
 vprintf PointSearch,1 : "Dimension is taken to be %o\n",d;
 EQ:=DefiningEquations(S); ANS:=[]; PR:=Primes;
 if #EQ le 2 and d eq 1 then C:=Curve(S);
  if #EQ eq 1 and TotalDegree(EQ[1]) eq 3 and not IsSingular(C)
   then pts:=PointsCubicModel(C,H : OnlyOne:=OnlyOne); end if;
  b,QI:=IsQuadricIntersection(C); // meaning 2 quadrics in P^3 ...
  if b and not IsSingular(C) then
   pts:=PointsQI(C,H : OnlyOne:=OnlyOne); end if;
  if assigned pts and affine then
   return [pt@S_to_Saff : pt in pts | pt[patch] ne 0];
  elif assigned pts then return pts; end if; end if;
 EQ:=[e/rGCD(Coefficients(e)) : e in EQ]; T:=Scheme(A,EQ);
 EQZ:=[PZ!e : e in EQ] where PZ is ChangeRing(Universe(EQ),Z);
 EQ2:=[ChangeRing(2*SymmetricMatrix(F),Z) : F in EQZ
      | IsHomogeneous(F) and TotalDegree(F) eq 2];
 if #PR eq 0 then P:=EB(H,d,n);
  if P lt 100 then PR:=[NextPrime(P)];
  else PR:=[NextPrime(Floor(Sqrt(P)))]; Append(~PR,NextPrime(PR[1])); end if;
 else require #PR le 2 : "At most two primes can be given";
      require &and[IsPrime(p) : p in PR] : "Primes must be prime"; end if;
 if #PR eq 2 then require PR[1] ne PR[2] : "Primes must be distinct"; end if;
 Sort(~PR);

/********* new code ********/
// This is bad: even SingularSubscheme is impractical for curves with 
// many defining equations, and dimension involves doing Groebner.
// Also (TO DO) the singularity check here is not the right one. 
if not Nonsingular then SS:=SingularSubscheme(S);
 SS:=Scheme(T,[e/rGCD(Coefficients(e)) : e in Equations(SS)]);
 if DIM(SS) eq 0 then SP:=Points(SS); end if; p:=PR[1];
  while true do SSp:=SingularSubscheme(ChangeRing(T,GF(p)));
  if DIM(SSp) gt DIM(SS)
   or (DIM(SSp) eq 0 and #Points(SSp) gt #SP) then
  vprintf PointSearch : "The prime %o looks bad -- skipping it\n",p;
  p:=NextPrime(p); else break; end if; end while;
 if #PR eq 2 then q:=PR[2]; if q le p then q:=NextPrime(p); end if;
 while true do SSq:=SingularSubscheme(ChangeRing(T,GF(q)));
  if DIM(SSq) gt DIM(SS)
   or (DIM(SSq) eq 0 and #Points(SSq) gt #SP) then
  vprintf PointSearch : "The prime %o looks bad -- skipping it\n",q;
  q:=NextPrime(q); else break; end if; end while; PR:=[p,q];
 else PR:=[p]; end if;
end if;
/******** end new code *******/

 if #PR eq 1 then p:=PR[1]; vprintf PointSearch: "Prime is %o\n",p;
  repeat ppts:=local_points(T,p,d : affine:=affine, nonsing:=Nonsingular);
   bad:= ppts cmpeq false; if bad then p:=NextPrime(p); 
   vprint PointSearch: "Bad prime, trying again with",p; end if; until not bad;
  pM:=[Lattice(x) : x in ppts];
  vprintf PointSearch,1 : "Have %o lattices from %o\n",#pM,p;
  for i in [1..#pM] do
   for sv in short_vectors(pM[i],H,n*H^2,EQZ,EQ2) do
    if Gcd(sv) ne 1 then continue sv; end if;
    b,pt:=IsCoercible(S,sv); if b then Append(~ANS,pt);
     vprintf PointSearch,1 : "Found %o\n",pt;
     if OnlyOne then break i; end if; end if;
   end for; end for; 

 else p,q:=Explode(Sort(PR));
  vprintf PointSearch: "Primes are %o and %o\n",p,q;
  repeat ppts:=local_points(T,p,d : affine:=affine, nonsing:=Nonsingular);
   bad:= ppts cmpeq false; if bad then p:=NextPrime(p); 
   vprint PointSearch: "Bad prime, trying again with",p; end if; until not bad;
  pM:=[Lattice(x) : x in ppts];
  vprintf PointSearch,1 : "Have %o lattices from %o\n",#pM,p;
  if q le p then q:=NextPrime(p); end if;
  repeat qqts:=local_points(T,q,d : affine:=affine, nonsing:=Nonsingular);
   bad:= qqts cmpeq false; if bad then q:=NextPrime(q); 
   vprint PointSearch: "Bad prime, trying again with",q; end if; until not bad;
  qM:=[Lattice(x) : x in qqts];
  vprintf PointSearch,1 : "Have %o lattices from %o\n",#qM,q;
  for i in [1..#pM] do for qm in qM do //printf ".";
   for sv in short_vectors(pM[i] meet qm,H,n*H^2,EQZ,EQ2) do
    if Gcd(sv) ne 1 then continue sv; end if;
    b,pt:=IsCoercible(S,sv); if b then Append(~ANS,pt);
     vprintf PointSearch,1 : "Found %o\n",pt;
     if OnlyOne then break i; end if; end if; end for; end for;
   vprintf PointSearch,1 : "Done with p-lattice %o\n",i; end for; end if;

 if Nonsingular or DIM(SS) ne 0 then pts:=ANS; 
 else pts:=SetToSequence(Set(ANS) join Points(SS)); end if;

 pts:=SetToSequence(Set(pts));

 if affine then return [pt@S_to_Saff : pt in pts | pt[patch] ne 0];
 else return [S!x : x in pts]; end if; end intrinsic;
