freeze;

// File name : 5coverings.m   
// Written by : T. Fisher
// Original version : December 2006
// This version : September 2014 

declare verbose FiveDescent, 3;
import "ThreeDesc/trivialize1.m" : TraceMatrix;

Z := Integers();
Q := Rationals();
P := PolynomialRing(Q); X := P.1;

// Given T in E(L), where E/Q is an elliptic curve and L = Q(T), 
// finds a polynomial f(x,y) with rational coefficients so that 
// f(x(T),y(T)) = L.1.

function ReversePolynomial(T)
  assert T ne Curve(T)!0;
  R<x,y> := PolynomialRing(Q,2);
  L := Ring(Parent(T));
  d := Degree(L);
  mat := Matrix(1,d,Eltseq(L!1));
  n := 1;
  bb := [R|1];
  while Rank(mat) lt d do
    n +:= 1;
    if n mod 2 eq 0 then 
      b := x^m where m is ExactQuotient(n,2);
    else
      b := x^m*y where m is ExactQuotient(n-3,2);
    end if;
    bb := bb cat [b];
    row := Eltseq(L!Evaluate(b,[T[1],T[2]]));
    mat := VerticalJoin(mat,Matrix(1,d,row));
  end while;
  vec := Vector(d,Eltseq(L.1));
  soln := Solution(mat,vec);
  f := &+[soln[i]*bb[i] : i in [1..#bb]];
  assert Evaluate(f,[T[1],T[2]]) eq L.1;
  return f;
end function;  
 
// Given T in E(L)[n], we match up the conjugates for the field L 
// with the group law on E(C). The answer is given as a function 
// from (Z/nZ)^2 -> [1..n^2-1]. We arrange that complex conjugation  
// act as (a,b) :-> (a,-b). Since we use floating point calculations,
// a tolerance must be set. 

function GroupLawOnEmbeddings(T,tol)
  E := Curve(T[1]);
  assert exists(n){ n : n in [3,5] | n*T[1] eq E!0};
  L := <Ring(Parent(T0)): T0 in T>;
  xTconj := &cat[Conjugates(T0[1]): T0 in T];
  yTconj := &cat[Conjugates(T0[2]): T0 in T];
  IsClose := func<x,y|Maximum([Abs(x[i]-y[i]) : i in [1..2]]) lt tol>;
  V := VectorSpace(GF(n),2);
  rr := [[r,s] : r,s in [0..n-1] | [r,s] ne [0,0]];
  complexpts := [EllipticExponential(E,[r[1]/n,r[2]/n]): r in rr];
  embs := [];
  for i in [1..n^2-1] do
    TT := [xTconj[i],yTconj[i]];
    jj := [j : j in [1..n^2-1] | IsClose(TT,complexpts[j])];
    error if #jj ne 1, "Insufficient precision";
    embs cat:= [V!rr[jj[1]]];
  end for;
  places := [];
  c := 0;
  for i in [1..#T] do
    r,s := Signature(L[i]);
    places cat:= [{c+j}: j in [1..r]]; 
    places cat:= [{c+j,c+j+1}: j in [r+1..r+2*s-1 by 2]];
    c +:= Degree(L[i]);
  end for;
  assert c eq n^2 - 1;
//  places := [{i}: i in [0..n-1]] cat [{i,i+1}: i in [n..(n^2-1) by 2]];
  cc := func<u|[v : v in V | {Position(embs,x): x in [u,v]} in places][1]>;
  tau := Matrix(GF(n),2,2,[cc(x): x in Basis(V)]);
  id := IdentityMatrix(GF(n),2);
  eigenbasis := &cat[Basis(Kernel(tau - lambda*id)): lambda in [1,-1]];
  eigenbasis[2] *:= (1/Determinant(Matrix(eigenbasis)));
  assert Determinant(Matrix(eigenbasis)) eq 1;
  iota := hom<V->V|eigenbasis>;
  return func<x,y|Position(embs,iota(V![x,y]))>;
end function;

// Extracts an nth root of x (for n is odd) making sure
// that if x is real then the answer is real. 

function MyRoot(x,n)
  assert IsOdd(n);
  sgn := IsReal(x) select Sign(Re(x)) else 1;
  return sgn*Root(sgn*x,n);
end function;

// Finds a basis for L that is "minimised and reduced" 
// with respect to alpha.

function GoodBasis(L,alpha,n:factorhint := 1)
  IndentPush();
  vprintf FiveDescent,1 : "Computing conjugates of alpha\n"; 
  vtime FiveDescent,1 : alphaconj := &cat[Conjugates(a): a in alpha];
  vtime FiveDescent,1 : gammaconj := [MyRoot(x,n) : x  in alphaconj];
  vprintf FiveDescent,1 : "Computing ring of integers of L\n";
  vtime FiveDescent,3 : OL := <RingOfIntegers(L0): L0 in L>;
  vprintf FiveDescent,1 : "Factoring ideal generated by alpha\n";
  myid := <ideal<OL[i]|alpha[i]/factorhint[i]^n> : i in [1..#L]>;
  vtime FiveDescent,3 : ff := <Factorization(myid0):myid0 in myid>;
  FracOL := <FieldOfFractions(OL0) : OL0 in OL>;
  rootid := <&*[PowerIdeal(FracOL[i])| f[1]^(-Floor(f[2]/n)): f in ff[i]]: i in [1..#L]>;
  rootid := <rootid[i] * ideal<OL[i]|1/factorhint[i]> : i in [1..#L]>;
  vprintf FiveDescent,1 : "Some preliminary reduction\n";
  d := &+[Degree(L0): L0 in L];
  Lbasis := &cat[[<i eq j select L[i]!x else L[i]!0: i in [1..#L]> 
                              : x in Basis(rootid[j])]: j in [1..#L]];
  for ctr in [1..3] do
    vprint FiveDescent, 1 : "Iteration",ctr;
    M := Matrix(d,d,[&cat[Conjugates(x0): x0 in x]: x in Lbasis]);
    Mconj := Matrix(d,d,[ComplexConjugate(x): x in Eltseq(M)]);
    D := DiagonalMatrix([Abs(x)^2: x in gammaconj]);
    A := M*D*Transpose(Mconj);
    A := Matrix(d,d,[Re(A[i,j]):i,j in [1..d]]);
    A := A + Transpose(A);
    _,cob := LLLGram(A);
    Lbasis := [<&+[cob[i,j]*Lbasis[j][k]: j in [1..d]]: k in [1..#L]>: i in [1..d]];
  end for;
  basL := &cat[[<i eq j select b else L[i]!0: i in [1..#L]> : b in Basis(L[j])]: j in [1..#L]];
  mat := Matrix(Q,d,d,[&+[Trace(b1[i]*b2[i]):i in [1..#L]]: b1 in Lbasis,b2 in basL])^(-1);
  Ldualbasis := [<&+[mat[i,j]*basL[j][k]: j in [1..d]]: k in [1..#L]>: i in [1..d]];
  IndentPop();
  return Lbasis,Ldualbasis,gammaconj;
end function;

// Adjusting choice of gamma = alpha^(1/n), where gamma is
// given by a list of conjugates (in R or C).
// We require that gamma is in L \tensor R, and that it is
// compatible with nu where sigma(alpha) = alpha^2 / nu^n. 
// We are free to multiply gamma by elements of w(E[n](R)).
// For n an odd prime, this leaves n^((n-1)/2) choices.
  
function GammaAdjustments(gamma,nu,emb)
  assert exists(n){n : n in [3,5] | #gamma eq n^2-1};
  C<i> := Universe(gamma);
  pi := Pi(C);
  zeta5 := Exp(2*pi*i/n);
  V := VectorSpace(GF(n),n^2-1);
  v0,v1,v2 := Explode([V|0,0,0]);
  pairs := case<n|
    3 : [[1,1]],
    5 : [[1,1],[2,2],[4,4],[2,1],[4,2],[3,4],[0,1]],
    default : []>;
  for ij in pairs do
    i,j := Explode(ij);
    z := gamma[emb(i,j)]^2/(gamma[emb(2*i,2*j)]*nu[emb(i,j)]);
    t := Re(n*Arg(z)/(2*pi));
    assert Abs(t - Round(t)) lt 0.000001;
    v0[emb(2*i,2*j)] := 2*v0[emb(i,j)] + Round(t);
  end for;
  pairs := case<n|
    3 : [[1,1],[2,2]],
    5 : [[0,1],[0,2],[1,1],[2,2],[3,3],[4,4],[1,3],[2,1],[3,4],[4,2]],
    default : []>;
  for ij in pairs do
    i,j := Explode(ij);
    z := ComplexConjugate(gamma[emb(i,j)])/gamma[emb(i,-j)];
    t := Re(n*Arg(z)/(2*pi));
    assert Abs(t - Round(t)) lt 0.000001;
    v0[emb(i,-j)] := - v0[emb(i,j)] + Round(t);
  end for;
  for i in [1..n-1] do
    v1[emb(0,i)] := i;
    v2[emb(i,i)] := i;
    v2[emb(i,-i)] := n-i;
  end for;
  U := case<n| 3 : sub<V|v1>, 5 : sub<V|v1,v2>, default : 0>;
  return [v0 + v: v in U];
end function;

// Real trivialisation of the obstruction algebra 
// A_1 = (R,+,*_eps) w.r.t. the basis {delta_T : T in E[n]}.
// Here n is odd, and we take eps = e^(1/2).
// Computation of the Weil pairing is left to chance!!!!
 
function HeisenbergMatrices(n,emb,zeta)
  C := Parent(zeta);
  mat1 := Matrix(C,n,n,[<(i mod n)+1,i,1>: i in [1..n]]);
  mat2 := DiagonalMatrix(C,n,[zeta^i: i in [0..n-1]]);
  hmats := [ZeroMatrix(C,n,n): i in [1..24]];
  m := Integers()!((n+1)/2);
  for r,s in [0..n-1] do
    if [r,s] ne [0,0] then 
      hmats[emb(r,s)] := zeta^(m*r*s)*mat1^r*mat2^s;
    end if;
  end for;
  return hmats;
end function;

// Computes log base 10 of the maximum absolute value.

function LogScore(seq,prec)
  m := Maximum([Abs(x): x in seq]);
  return m eq 0 select prec else -Log(m)/Log(10);
end function;

// Computes the structure constants for the obstruction
// algebra, by first computing a trivialisation over the reals.
// Several choices of gamma (where gamma^n = alpha) are
// are tried. We recognise the correct choice by the fact it
// gives integer structure constants.

function ObstructionAlgebra(basis,gamma,heis,loopseq,prec:denom := 1)
  IndentPush();
  assert exists(n){n : n in [3,5] | #gamma eq n^2-1};
  C<i> := Universe(gamma);
  zeta := Exp(2*Pi(C)*i/n);
  idC := IdentityMatrix(C,n);
  vprintf FiveDescent, 2 : "We loop over %o possibilities\n",#loopseq;
  for ctr in [1..#loopseq] do
    v := Vector(Z,n^2-1,Eltseq(loopseq[ctr]));
    vprintf FiveDescent, 2 : "%o\t%o\n",ctr,v;
    mats := [zeta^v[j]*gamma[j]*heis[j]: j in [1..n^2-1]];
    mats := [idC] cat [&+[b[j]*mats[j]: j in [1..n^2-1]]: b in basis];
    mats := [Matrix(n,n,[Re(mat[i,j]): i,j in [1..n]]): mat in mats];
    tempmat := Matrix(n^2,n^2,[Eltseq(mat): mat in mats]);
    try
      bigmat := NumericalInverse(tempmat);
    catch e;
      IndentPop();
      vprint FiveDescent, 1 : "Problem computing numerical inverse";
      return "Increase precision";
    end try; 
// some randomly chosen structure constants
    for j in [1..3] do
      m1 := Random(mats);
      m2 := Random(mats);
      approxsc := Eltseq(denom*Vector(Eltseq(m1*m2))*bigmat);
      diffr := [x - Round(Re(x)): x in approxsc];
      score := LogScore(diffr,prec);
      if score lt 1 then break; end if;
    end for;
// computing all the structure constants
    strconsts := [];
    for m1 in mats do
      if score lt 1 then break; end if;
      approxsc := [denom*Vector(Eltseq(m1*m2))*bigmat: m2 in mats];
      sc := [[Round(Re(x)): x in Eltseq(y)]: y in approxsc];
      diffr := [approxsc[j][k] - sc[j][k]: j,k in [1..n^2]];
      score := Minimum(score,LogScore(diffr,prec));
      strconsts cat:= [[x/denom : x in xx]: xx in sc];
    end for;
    vprint FiveDescent,1 : score;
    if score gt 10 then break; end if;  // replace 10 by prec/2 ??
  end for;
  if score lt 10 then IndentPop(); return "Increase precision"; end if;
  V := VectorSpace(Q,n^2);
  vprint FiveDescent,3 : 
    "denom =",Factorization(Denominator(RationalGCD(&cat strconsts)));
  A := AssociativeAlgebra< V | strconsts : Check := true >;
  IndentPop();
  return A;
end function;

// Function to "minimise and reduce" the rows of a matrix over Q.
 
function MyRowReduce(mat)
  L := PureLattice(Lattice(mat));
  return LLL(Matrix(Q,[Eltseq(x): x in Basis(L)]));
end function;

function MyKernelMatrix(mat)
  return MyRowReduce(KernelMatrix(mat));
end function;

// mat1 represents an inclusion U -> V. 
// mat2 represents an endomorphism of V, known to act on U.
// We compute a matrix that represents the action on U.

function ActionOnSubspace(mat1,mat2)
  K := BaseRing(mat2);
  n1 := Nrows(mat1);
  n2 := Ncols(mat1);
  assert Nrows(mat2) eq n2;
  assert Ncols(mat2) eq n2;
  U := VectorSpace(K,n1);
  V := VectorSpace(K,n2);
  mat1 := ChangeRing(mat1,K);
  map := hom<U->V|mat1>;
  return Matrix(K,n1,n1,[Eltseq((mat1[i]*mat2) @@ map): i in [1..n1]]);
end function;

// A matrix group G with m generators acts on U1 and U2
// via matrices mats1 and mats2 (each sequences of length m).
// We compute a non-zero element of Hom_G(U1,U2). 
// Knowing the dimension of Hom_G(U1,U2) allows us to exit
// the linear algebra calculations early.

function AlgebraHomomorphism(mats1,mats2,dimhom)
  m := #mats1;
  n1 := Nrows(mats1[1]);
  n2 := Nrows(mats2[1]);
  AA := [Matrix(Q,n1,n2,[<i,j,1>]): j in [1..n2],i in [1..n1]];
  bigmat := ZeroMatrix(Q,n1*n2,0);
  for k in [1..m] do
    newmat := Matrix(Q,n1*n2,n1*n2,[Eltseq(mats1[k]*A-A*mats2[k]): A in AA]);
    bigmat := HorizontalJoin(bigmat,newmat);
    if k gt 1 and Rank(bigmat) eq n1*n2-dimhom then break; end if;
  end for;
  km := MyKernelMatrix(bigmat);
  pi := Matrix(Q,n1,n2,Eltseq(km[1]));
  assert forall{i : i in [1..m]| mats1[i]*pi eq pi*mats2[i]};
  return pi;
end function;

// Compute an isomorphism A -> Mat(n,Q), starting from knowledge
// of a zerodivisor x in A.
 
function Trivialisation(A,x)
  IndentPush(); 
  nn := Dimension(A);
  assert exists(n){n : n in [3,5] | n^2 eq nn};
  _, mm := MatrixAlgebra(A);
  MM := [mm(A.i): i in [1..nn]];
  rmat := Matrix(Q,nn,nn,[Eltseq(x*A.i): i in [1..nn]]);
  matA := MyRowReduce(rmat);
  matB := MyKernelMatrix(rmat);
  rank := Integers()!(Nrows(matA)/n);
  vprintf FiveDescent,2 : "Working with a zerodivisor of rank %o\n",rank;
  if rank eq 1 then 
    M := [ActionOnSubspace(matA,m): m in MM];
  elif rank eq n-1 then 
    M := [ActionOnSubspace(matB,m): m in MM];
  end if;
  if n eq 5 and rank in {2,3} then 
    if rank eq 2 then 
      M10 := [ActionOnSubspace(matA,m): m in MM];
      M15 := [ActionOnSubspace(matB,m): m in MM];
    else
      M10 := [ActionOnSubspace(matB,m): m in MM];
      M15 := [ActionOnSubspace(matA,m): m in MM];
    end if;
    pi := AlgebraHomomorphism(M15,M10,6);
    if Rank(pi) eq 10 then 
      mat := MyKernelMatrix(pi);
      M := [ActionOnSubspace(mat,m): m in M15];
    else 
      mat := MyRowReduce(pi);
      M := [ActionOnSubspace(mat,m): m in M10];
    end if;
  end if;
  IndentPop();
  return M;
end function;

// Given an n by n matrix, representing an endomorphism
// alpha : V -> V, computes a n(n-1)/2 by n(n-1)/2 matrix 
// representing \wedge^2 alpha : \wedge^2 V -> \wedge^2 V.

function Alt2Matrix(mat)
  L := BaseRing(mat);
  n := Nrows(mat);
  assert Ncols(mat) eq n;
  nn := Binomial(n,2);
  altmats := [Matrix(L,n,n,[<i,j,1>,<j,i,-1>]): i,j in [1..n]| i lt j];
  return Matrix(L,nn,nn,[[B[i,j]: i,j in [1..n]| i lt j] 
     where B is Transpose(mat)*A*mat : A in altmats]);
end function;

// Given an n by n matrix, representing an endomorphism
// alpha : V -> V, computes a n(n+1)/2 by n(n+1)/2 matrix 
// representing S^2 alpha : S^2 V -> S^2 V.

function Sym2Matrix(mat)
  L := BaseRing(mat);
  n := Nrows(mat);
  assert Ncols(mat) eq n;
  nn := Binomial(n+1,2);
  symmats := [Matrix(L,n,n,[<i,j,1>,<j,i,1>]): i,j in [1..n]| i le j];
  return Matrix(L,nn,nn,[[B[i,j]: i,j in [1..n]| i le j] 
     where B is Transpose(mat)*A*mat : A in symmats]);
end function;

// Converts a matrix MW in GL(n,L), whose conjugates generate the 
// Heisenberg group, to a (proper) transformation tr of genus one models.
// If n = 3 then tr = <1/alpha,MW>, where MW^3 = alpha I3.
// If n = 5 then tr = <MV,(1/alpha)*MW> where MW^5 = alpha I5, and
// MV^5 = alpha^2 I5. Here V and W are irreducible representations
// of the Heisenberg group, and the central character of V is the
// square of that for W.
 
function MatrixToTransformation(MW)
  IndentPush();
  n := Nrows(MW);
  assert n in {3,5};
  alpha := Determinant(MW);
  if n eq 3 then 
    tr := <1/alpha,MW>;
  else
    vprint FiveDescent, 1 : "Computing action on W10 = Alt(2,W)";
    vtime FiveDescent, 2 : M10 := Alt2Matrix(MW); 
    vprint FiveDescent, 1 : "Computing action on W15 = Sym(2,W)";
    vtime FiveDescent, 2 : M15 := Sym2Matrix(MW); 
    vprint FiveDescent, 1 : "Computing an element pi of Hom(W15,W10)";
    d := Degree(BaseRing(MW));
    mats1 := [Matrix(Q,10,10,[M10[i,j][k]: i,j in [1..10]]): k in [1..d]];
    mats2 := [Matrix(Q,15,15,[M15[i,j][k]: i,j in [1..15]]): k in [1..d]];
    vtime FiveDescent, 2 : pi := AlgebraHomomorphism(mats2,mats1,6);
    vprint FiveDescent, 1 : pi;
    vprint FiveDescent, 1 : "Computing action on V = Kernel(pi)";
    if Rank(pi) eq 10 then 
      mat := MyKernelMatrix(pi);
      mats := [ActionOnSubspace(mat,m): m in mats2];
    else 
      mat := MyRowReduce(pi);
      mats := [ActionOnSubspace(mat,m): m in mats1];
    end if;
    L := BaseRing(MW);
    MV := &+[ChangeRing(mats[i],L)*Basis(L)[i]: i in [1..d]];
    assert Determinant(MV) eq alpha^2;
    tr := <MV,(1/alpha)*MW>; 
  end if;
  IndentPop();
  return tr;
end function;

function FixedPencil(n,tr)
  IndentPush();
  M := tr[2];
  L := BaseRing(M);
  N := Integers()!(10*n/(6-n));
  vprint FiveDescent, 1 : "Computing the Heisenberg invariant models";
  I := IdentityMatrix(L,N);
  basis := [GenusOneModel(n,Eltseq(I[i])): i in [1..N]];
  ans := [];
  bigmat := ZeroMatrix(Q,N,0);
  if n eq 5 then 
    _,tr1 := IsTransformation(5,<Transpose(tr[1]),Transpose(tr[2])>);
  else 
    _,tr1 := IsTransformation(3,<tr[1],Transpose(tr[2])>); 
  end if;
  for k in [1..N] do
    vprint FiveDescent,2 : "k =",k;
    vtime FiveDescent,2 : 
      vv := Vector(ModelToSequence(tr1*basis[k]))-I[k];
    vtime FiveDescent,2 : 
      newmat := Matrix(Q,N,Degree(L),[Eltseq(x): x in Eltseq(vv)]);
    vtime FiveDescent,2 : bigmat := HorizontalJoin(bigmat,newmat);
    vtime FiveDescent,2 : rk := Rank(bigmat);
    vprint FiveDescent,2 : "rk =",rk;
    if k gt 1 and rk eq N-2 then break; end if;
  end for;
  mat := KernelMatrix(bigmat);
  mat := MyRowReduce(mat);
  assert Nrows(mat) eq 2;
  if n eq 3 then 
    mat := mat*DiagonalMatrix(Q,[1,1,1,3,3,3,3,3,3,6]);
  end if;
  pencil := [GenusOneModel(n,Eltseq(mat[i])): i in [1..2]];
  IndentPop();
  return pencil;
end function;

function FindInHessePencil(E,model)
  n := Degree(model);
  c4,c6,Delta := Invariants(model);
  DD,cc4,cc6 := HessePolynomials(n,1,[c4,c6]);
  ff := cc4^3-jInvariant(E)*Delta*DD^n;
  f := Evaluate(ff,[X,1]);
  newmodels := [];
  if Degree(f) lt TotalDegree(ff) then 
    rt := [1,0];
    Append(~newmodels,model);
  else
    for rt in Roots(f) do
      Append(~newmodels,rt[1]*model + Hessian(model));
    end for;
  end if;
  newmodels := [(1/RationalGCD(Eltseq(m1)))*m1 : m1 in newmodels];
  return newmodels;
end function;

// IsTrivialisation := func<A,mats| forall{ [i,j] : i,j in [1..n] | 
//   mats[i]*mats[j] eq &+[Eltseq(A.i*A.j)[k]*mats[k]: k in [1..n]] }
//   where n is Dimension(A) >;

function GetFiveCovering(E,T,alpha:prec := 200,factorhint := 1,NthRoot := 0) 

  assert exists(n){n : n in [3,5] | n*T[1] eq E!0};
  vprintf FiveDescent, 1 : " n = %o\n",n;

  L := <Ring(Parent(T0)): T0 in T>;
  f := <ReversePolynomial(T0): T0 in T>;
  uu := <Evaluate(f[i],[Eltseq(2*T[i])[j] : j in [1,2]]): i in [1..#T]>;
  sigma := <hom<L[i]->L[i]|uu[i]>: i in [1..#T]>;

  vprintf FiveDescent, 1 : "Computing group law on embeddings L -> C\n";

  for L0 in L do SetKantPrecision(L0,prec); end for;

  vtime FiveDescent, 1 : 
    embnos := GroupLawOnEmbeddings(T,10^(-5));

  vprintf FiveDescent, 1 : "Computing a convenient basis for L\n";

  OL := <RingOfIntegers(L0):L0 in L>; 
  for OL0 in OL do SetKantPrecision(OL0,prec); end for;
  F := <FieldOfFractions(OL0): OL0 in OL>;
  for F0 in F do SetKantPrecision(F0,prec); end for;

  if factorhint cmpeq 1 then
    factorhint := <L0!1 : L0 in L>;
  end if;

  vtime FiveDescent, 1 : 
    B,Bdual,gammaconj := GoodBasis(L,alpha,n:factorhint:=factorhint);
  if exists{c : c in gammaconj | Abs(c) lt 10^(-prec)} then
    return "Increase precision";
  end if;

  vprintf FiveDescent, 1 : "Computing fifth root of alpha^2/sigma(alpha)\n";
  if NthRoot cmpeq 0 then 
    vtime FiveDescent, 1 : nu := <Root(alpha[i]^2/sigma[i](alpha[i]),n) : i in [1..#L]>;
  else
    nu := NthRoot;
    for i in [1..#L] do 
      vtime FiveDescent, 1 : assert nu[i]^n eq alpha[i]^2/sigma[i](alpha[i]);
    end for;
  end if;

  vprintf FiveDescent, 1 : "Adjusting choice of gamma = alpha^(1/n)\n";
  loopseq := GammaAdjustments(gammaconj,&cat[Conjugates(nu0): nu0 in nu],embnos);

  vprintf FiveDescent, 1 : "Computing the obstruction algebra\n";
  C<i> := Universe(gammaconj);

  zeta := Exp(2*Pi(C)*i/n);
  heis := HeisenbergMatrices(n,embnos,zeta);
  Bconj := [&cat[Conjugates(x0): x0 in x]: x in B];  

  vtime FiveDescent, 1 : 
     A := ObstructionAlgebra(Bconj,gammaconj,heis,loopseq,prec);

  if A cmpeq "Increase precision"
    then return A;
  end if;

  a := A!0;
  bas := Basis(A); 

  for ctr in [1..3] do
    vprintf FiveDescent, 1 : "Basis elements have minimal polynomials\n";
    IndentPush();
    a := A!0;
    size := 0;
    for b in bas do
      mp := P!MinimalPolynomial(b);
      size := Maximum(size,Maximum([Abs(x): x in Coefficients(mp)]));
      vprint FiveDescent, 1 : mp; 
      if not IsIrreducible(mp) then
        f := Factorization(mp)[1][1];
        vprint FiveDescent, 1 : " Factor: ",f; 
        a := Evaluate(f,b);
        break;
      end if;
    end for;
    IndentPop();
    if a ne 0 then break; end if; 
    vprint FiveDescent,1 : "Max coefficient size =",size;
    if size gt 10^20 then 
      vprint FiveDescent,1 : 
        "That looks too big - try again with more precision";
      return "Increase precision";
    end if;

    if ctr eq 1 then
      vprint FiveDescent,1 : "Computing maximal order";
      vtime FiveDescent,1 : bb := MaximalOrder(A);
      bb := Basis(bb);
      cob := LLL(Matrix(Q,n^2,n^2,[Eltseq(b): b in bb]));
      bas := [A!cob[i] : i in [1..n^2]];
    end if;

    if ctr eq 2 then 
      trmat := TraceMatrix(A,bas);
      discr := Abs(Determinant(trmat));
      vprint FiveDescent, 1 : "Discriminant of maximal order =",discr;
      if discr ne 1 then 
        vprint FiveDescent, 1 : Factorization(Integers()!discr);
        return 0; 
      end if;
      bb := TrivializeNew(A,bas:JustBasis,UseTraceForm,AdHocReduce);
      bas := bb;
    end if;
  end for;
  
  vprintf FiveDescent, 1 : "Computing trivialisation\n";
  mats := Trivialisation(A,a);
  M := <&+[Bdual[i][k]*mats[i+1]: i in [1..n^2-1]]: k in [1..#L]>;
  if n eq 3 then M := Transpose(M); end if;

  vprintf FiveDescent, 1 : "Computing Heisenberg invariant pencil\n"; 
  assert #T eq 1; 
  tr := MatrixToTransformation(M[1]);
  pencil := FixedPencil(n,tr);
  models := FindInHessePencil(E,pencil[1]);
  mm := [ m : m in models | IsIsomorphic(Jacobian(m),E)];
  vprintf FiveDescent, 1 : "We are left with %o models\n",#mm;
  assert #mm eq 1;
  return mm[1]; 

end function;

intrinsic FiveDescentCoveringCurve(E::CrvEll,alpha::Tup: 
	   prec := 200, factorhint := 1 , fifthroot := 0) -> ModelG1 
{Given an elliptic curve E/Q and a 5-Selmer element alpha in L^*/(L^*)^5, where Spec(L) = E[5] - \{0\}, computes the 5-covering curve corresponding to alpha. This has only been implemented in the case L is a field, i.e. Galois acts transitiviely on E[5] - \{0\}. A zero model is returned if the 5-covering has non-trivial obstruction.}

  T := FiveTorsionPoints(E);
  require #T eq 1 : "Only implemented in the case Galois acts transitively on E[5] - \{0\}.";
  done := false;
  repeat 
    vprint FiveDescent, 1 : "Calling FiveDescent with prec =",prec;
    vtime FiveDescent, 1 :
    ans := GetFiveCovering(E,T,alpha:
             prec := prec,factorhint := factorhint,NthRoot := fifthroot);      
    if Type(ans) eq MonStgElt then
      assert ans eq "Increase precision";
      prec *:= 2;
      vprint FiveDescent,1 : "Increasing precision to",prec;
    else
      done := true;
    end if;
  until done or prec gt 10000;
  if ans cmpeq 0 then // i.e. 5-covering has non-trivial obstruction
    model := GenusOneModel(Rationals(),5,[0: i in [1..50]]);
  else
    vprint FiveDescent,1 : "Minimising";
    model := Minimise(ans);
    vprint FiveDescent,1 : "Reducing";
    model := Reduce(model);
  end if;
  return model;
end intrinsic;
