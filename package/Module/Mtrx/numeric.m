freeze;

/* added 20 Jul 2010 MW */

intrinsic NumericalEigenvectors(M::Mtrx, e::FldComElt) -> SeqEnum
{ Given a numerical approximation to an eigenvalue of a square matrix
  (coercible into C), attempt to find eigenvectors corresponding to it.
  The usual concerns about numerical linear algebra should apply.
  This function is for cases that are numerically nice. }

 d:=Degree(Parent(M)); MA:=MatrixAlgebra(Parent(e),d);
 require IsCoercible(MA,M): "Matrix must coerce into the complexes";
 require NumberOfRows(M) eq NumberOfColumns(M): "Matrix must be square";
 return Rows(NumericalKernel(MA!M-e*MA!1)); /* 2014 Apr 30, use NumericalK */

 d:=Degree(Parent(M)); MA:=MatrixAlgebra(Parent(e),d);
 require IsCoercible(MA,M): "Matrix must coerce into the complexes";
 M:=MA!M-e*MA!1; prec:=Precision(Parent(e)); C:=ComplexField(prec);
 S:=Vector([C!0 : i in [1..d]]); ANS:=[Parent(S)|]; T:=MA!1;
 for e in [1..d] do v:=M[e];
  for f in [1..e-1] do S[f]:=C!0; c:=0;
   for w in [1..d] do // get pivot, 2014 Apr 19 fix, for zero columns
    if Abs(Norm(M[f][w])) lt 10^(-prec) then continue; end if; c:=w; end for;
   if c eq 0 then continue; end if;
   S[f]:=M[e][c]/M[f][c]; M[e]-:=S[f]*M[f]; T[e]-:=S[f]*T[f]; end for;
  if Abs(Norm(M[e])) lt 10^(-prec) then S[e]:=-1;
   v:=Vector([C!0 : i in [1..d]]); v[e]:=1; ANS cat:=[v*T]; end if; end for;
 return ANS; end intrinsic;

/*
> n:=10; M:=Matrix(C,n,n,[Random([-100..100]) : i in [1..n^2]]); // random
> for i in [1..n] do M[i][1]:=0; end for; M; // make 1st column zero
> for i in [1..n] do M[i][8]:=0; end for; M; // make 8th column zero
> ANS:=NumericalEigenvectors(M,C!0);
> v1:=ANS[1]; Norm(v1*M); // 2.59068606588359389290436530285E-54
> v2:=ANS[2]; Norm(v2*M); // 4.94495729215513186789764475467E-54
> ev:=SetToSequence(Eigenvalues(M))[1][1];
> v:=NumericalEigenvectors(M,C!ev)[1];
> Norm(v*M-ev*v); // 3.67471815839021900970903178658E-53
> M[1][1]:=0; M[10][1]:=1000;
> ANS:=NumericalEigenvectors(M,C!0);
> v1:=ANS[1]; Norm(v1*M); // 2.59068606588359389290436530285E-54
> ev:=SetToSequence(Eigenvalues(M))[1][1];
> v:=NumericalEigenvectors(M,C!ev)[1];
> Norm(v*M-ev*v); // 3.67471815839021900970903178658E-53
*/

intrinsic DiagonalisingMatrix(M::Mtrx) -> Mtrx
{ Given a square matrix M coercible into C, numerically find a matrix T for
  which TMT^(-1) is diagonal. Fails if Jordan form is not diagonal, or
  numerical difficulties arise }
 require NumberOfRows(M) eq NumberOfColumns(M): "Matrix must be square";
 if Type(BaseRing(Parent(M))) eq FldCom then C:=BaseRing(Parent(M));
 elif Type(BaseRing(Parent(M))) eq FldRe
  then C:=ComplexField(BaseRing(Parent(M)));
 else C:=ComplexField(Precision(0.5)); end if;
 d:=Degree(Parent(M)); MA:=MatrixAlgebra(C,d);
 require IsCoercible(MA,M): "Matrix must coerce into the complexes";
 M:=MA!M; ev:=Eigenvalues(M); V:=&cat[NumericalEigenvectors(M,e[1]) : e in ev];
 require #V eq d: "Numerically unstable, or Jordan form is not diagonal";
 return Matrix(V); end intrinsic;

/* Test code
> d:=10; M:=Matrix(d,d,[Random([-d^2..d^2]) : i in [1..d^2]]);
> M:=ChangeRing(M,ComplexField(30)); T:=DiagonalisingMatrix(M);
> A:=T*M*T^(-1); B:=A-DiagonalMatrix(Diagonal(A));
> Max([Abs(Norm(b)) : b in Eltseq(B)]); // should be small
*/

  /************************************************************************/

// 
// uses stable iterative methods from numerical recipies. I forgot which I
// used...
// (But the names should be the same as in the book)
//
//NumercialRecipies: Chapter 11.2: Householder Transforms
//
tred2 := function(a, trafo)
  n := NumberOfRows(a);
  R := Parent(a[1][1]);
//  eps := 10^-(Precision(R) div 2);
  e := [R!0: x in [1..n]];
  d := [R!0: x in [1..n]];
  
  for i in [n..2 by -1] do
    l := i-1;
    scale := R!0;
    h := scale;
    if l gt 1 then
      for k in [1..l] do
        scale +:= Abs(a[i][k]);
      end for;
      if scale eq R!0 then
//      if scale le eps then
        e[i] := a[i][l];
      else 
        for k in [1..l] do
          a[i][k] /:= scale;
          h +:= a[i][k] * a[i][k];
        end for;
        f := a[i][l];
        if f gt 0 then
          g := -Sqrt(h);
        else
          g := Sqrt(h);
        end if;

        e[i] := scale * g;
        h -:= f*g;
        a[i][l] := f-g;
        f := R!0;

        for j in [1..l] do
          if trafo then
            a[j][i] := a[i][j] / h;
          end if;  
          g := R!0;
          for k in [1..j] do
            g +:= a[j][k] * a[i][k];
          end for;
          for k in [j+1..l] do
            g +:= a[k][j] * a[i][k];
          end for;
          e[j] := g/h;
          f +:= e[j]*a[i][j];
        end for;
        hh := f/(h+h);
        for j in [1..l] do
          f := a[i][j];
          g := e[j]  - hh*f;
          e[j] := g;
          for k in [1..j] do
            a[j][k] -:= (f*e[k] + g*a[i][k]);
          end for;
        end for;
      end if;
    else
      e[i] := a[i][l];
    end if;
    d[i] := h;
  end for;  

  d[1] := R!0;
  e[1] := R!0;
  for i in [1..n] do
    if trafo then
      l := i-1;
      if d[i] ne 0 then
        for j in [1..l] do
          g := R!0;
          for k in [1..l] do
            g+:= a[i][k] * a[k][j];
          end for;
          for k in [1..l] do
            a[k][j] -:= g*a[k][i];
          end for;
        end for;  
      end if;
      d[i] := a[i][i];
      a[i][i] := R!1;
      for j in [1..l] do
        a[j][i] := R!0;
        a[i][j] := R!0;
      end for;
    else  
      d[i] := a[i][i];
    end if;  
  end for;

  if trafo then
    return d, e, a;
  else  
    return d, e;
  end if;

end function;

sign := function(a,b)
  if b lt 0 then
    return -Abs(a);
  else
    return Abs(a);
  end if;
end function;  

// Numercial Recipies: Chapter 11.3: QL decomposition of a symmetric 
// tridiagonal matrix (d is the diagonal, e represents both off diagonal
// parts)
tqli := function(d,e,trafo,z)
  n := #d;
  R := Parent(d[1]);
//  eps := 10^-(Precision(R) div 4);

  for i in [2..n] do e[i-1] := e[i]; end for;
  e[n] := R!0;

  for l in [1..n] do
    iter := 0;
    repeat
      br := false;
      mm := l;
      while mm le n-1 do
        dd := Abs(d[mm]) + Abs(d[mm+1]);
        if Abs(e[mm]) + dd eq dd then 
//        if Abs(e[mm]) le eps then 
//        if Abs(Abs(e[mm]) + dd - dd) le eps then 
           e[mm] := R!0;
           br := true; 
           break; 
         end if;
        mm +:= 1;  
      end while;

      if mm ne l then
        iter +:=1;
        if iter eq 30 then 
          print "Error: too many iterations";
          return false;
        end if;
        g := (d[l+1] - d[l])/((R!2)*e[l]);
        r := Sqrt(g*g+1);
        g := d[mm] - d[l] + e[l] / (g + sign(r, g));
        c := R!1;
        s := c;
        p := R!0;
        for i in [mm-1..l by -1] do
          f := s*e[i];
          b := c*e[i];
          if Abs(f) ge Abs(g) then
            c := g/f;
            r := Sqrt(c*c+1);
            e[i+1] := f*r;
            s := 1/r;
            c *:= s;
          else
            s := f/g;
            r := Sqrt(s*s+1);
            e[i+1] := g*r;
            c := 1/r;
            s *:= c;
          end if;
          g := d[i+1] - p;
          r := (d[i] - g)*s+2*c*b;
          p := s*r;
          d[i+1] := g+p;
          g := c*r-b;
          if trafo then
            for k in [1..n] do
              f := z[k][i+1];
              z[k][i+1] := s*z[k][i]+c*f;
              z[k][i] := c*z[k][i] - s*f;
            end for;  
          end if;  
        end for;
        d[l] := d[l] - p;
        e[l] := g;
        e[mm] := R!0;
      end if;
    until mm eq l;
  end for;

  if trafo then
    return d, z;
  else  
    return d;
  end if;  
end function;  
   

intrinsic ConditionNumber(M::Mtrx) -> RngElt
  {The condition number of M, ie. the largest eigenvalue of M^t*M times 
    1/ the smallest. This is a measure for the stability of linear algebra.}
  d,e := tred2(Transpose(M)*M, false);
  l := tqli(d,e, false, false);

  return Sqrt(Minimum(l)^-1*Maximum(l));
end intrinsic;

intrinsic SpectralRadius(M::Mtrx) -> RngElt, RngElt
  {The square root of then largest (and of the smallest) eigenvalue of M^t * M, ie. the smallest
    admissible operator norm for M wrt to L_2.}

  d,e := tred2(Transpose(M)*M, false);
  l := tqli(d,e, false, false);

  return Sqrt(Maximum(l)), Sqrt(Minimum(l));
end intrinsic;

intrinsic SchurNorm(M::Mtrx) -> RngElt
  {The Schur norm, ie. the sqrt of the sum of the squares of all entries}
  return Sqrt(&+ [ x^2 : x in Eltseq(M)]);
end intrinsic;

intrinsic MaximumNorm(M::Mtrx) -> RngElt
  {The maximal entry of M}
  return Maximum([Abs(x) : x in Eltseq(M)]);
end intrinsic;

intrinsic OperatorNorm(M::Mtrx:Norm := 2) -> RngElt
  {The subordinate matrix norm of M wrt to the L_norm norm}
  if Norm cmpeq 2 then
    return SpectralRadius(M);
  elif Norm cmpeq Infty or Type(Norm) eq Infty then
    return Maximum([&+ [ Abs(x) : x in Eltseq(M[i])] : i in [1..Nrows(M)]]);
  else
    error "Currently only Infty and 2-norms are supported";
  end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//////// NumericalKernel and QRDecomposition -- MW 31 May 2012 /////////
////////////////////////////////////////////////////////////////////////

/* Moved to C code, Apr 2014 */

function ElementaryVector(R,n,i)
 v:=[R!0 : i in [1..n]]; v[i]:=1; return Vector(v); end function;

function HouseholderReflector(x : only_last:=false)
 BR:=BaseRing(x); real:=Type(BR) eq FldRe; // only_last is last row of Q*
 sz:=#Eltseq(x); n:=Sqrt(Norm(x)); // can Norm(x) be zero?
 if real then alpha:=x[sz] ge 0 select -n else n; // u bad when [0,...0,z] ?
 else alpha:=-Exp((BR.1)*Arg(x[sz]))*n; end if; // can Norm(u) be 0 below ?
 Z:=ElementaryVector(BR,sz,sz); u:=x+alpha*Z; v:=u/Sqrt(Norm(u)); V:=Matrix(v);
// hmm, that should be x-alpha*Z ?
 if only_last then if real then return Z-2*v[sz]*v,v; end if;
  e:=(v,x); a:=e/Conjugate(e); // can e be 0 ?
  return Z-(1+a)*Conjugate(v[sz])*v,v; end if; // new Conjugate(vector)
 I:=IdentityMatrix(BR,sz);
 if real then Q:=I-2*Transpose(V)*V; // this code (full mat) never used now!
 else VC:=ConjugateTranspose(V); Q:=I-(1+(v,x)/(x,v))*(VC*V); end if;
 return Q,v; end function;
// should check if Norm(u) is zero, and if so, just take v arbitrary?

function FasterHQR(M) // BR:=BaseRing(M); r:=Type(BR) eq FldRe;
 prec:=Precision(BaseRing(M));
 nr:=Nrows(M); nc:=Ncols(M); assert nc eq nr; QA:=[* *];
 for k in [nr..2 by -1] do A:=Submatrix(M,1,1,k,k);
  x:=A[k]; QA cat:=[* x *]; pad:=[0 : i in [1..nr-k]];
  qk,v:=HouseholderReflector(x : only_last); // bad when Norm(x) is zero ?
  v:=Vector(Eltseq(v) cat pad); qk:=Vector(Eltseq(qk) cat pad);
  if Norm(v[k]) lt 10^(-2*prec+3) then continue; end if;
  for u in [1..k-1] do M[u]-:=v*(M[u][k]-(M[u],qk))/v[k]; end for;
  M[k]-:=2*(v,M[k])*v; end for; return M,QA; end function; // M is upp triang

intrinsic NumericalKernel_old(M::Mtrx : Epsilon:=0)
 -> SeqEnum[ModTupFldElt],SeqEnum[FldReElt]
{Given a real or complex matrix, compute its numerical kernel.
 Also returns singular value approximations as a measure of stability.}
 BR:=BaseRing(Parent(M)); real:=Type(BR) eq FldRe; prec:=Precision(BR);
 require real or Type(BR) eq FldCom: "Base Ring must be real or complex";
 require Nrows(M) eq Ncols(M): "Sigh, matrix must be square for now";
 R,S:=FasterHQR(Transpose(M)); d:=Degree(Parent(M)); // M^T Q = R, R upptri
 if Epsilon eq 0 then Epsilon:=1/10^(Precision(BR)/2); end if; K:=[];
 if real then ev:=[Norm(x) : x in Diagonal(R)];
 else ev:=[Sqrt(Real(Norm(x))) : x in Diagonal(R)]; end if;
 k:=#[u : u in ev | u lt Epsilon]; K:=[ElementaryVector(BR,d,j) : j in [1..k]];
 for s in Reverse(S) do e:=#Eltseq(s);
  qk,V:=HouseholderReflector(s : only_last); pad:=[0: i  in [1..d-e]];
  if not real then V:=Conjugate(V); end if; // new Conjugate(vector)
  if Norm(V[e]) lt 10^(-2*prec+3) then continue; end if;
  for j in [1..k] do ip:=&+[K[j][i]*qk[i] : i in [1..e]];
   K[j]-:=Vector(Eltseq(V*(K[j][e]-ip)/V[e]) cat pad); end for; end for;
  return K,ev; end intrinsic;

intrinsic QLDecomposition_old(M::Mtrx) -> Mtrx, Mtrx
{Given a real/complex matrix, return a QL decomposition.
 Here Q is orthogonal/unitary and L is *lower* triangular.}
 BR:=BaseRing(Parent(M)); real:=Type(BR) eq FldRe; prec:=Precision(BR);
 require real or Type(BR) eq FldCom: "Base Ring must be real or complex";
 require Nrows(M) eq Ncols(M): "Sigh, matrix must be square for now";
 R,S:=FasterHQR(Transpose(M)); d:=Degree(Parent(M)); Q:=IdentityMatrix(BR,d);
 for s in Reverse(S) do e:=#Eltseq(s);
  qk,V:=HouseholderReflector(s : only_last); pad:=[0: i  in [1..d-e]];
  if not real then V:=Conjugate(V); end if; // new Conjugate(vector)
  if Norm(V[e]) lt 10^(-2*prec+3) then continue; end if;
  for j in [1..d] do ip:=&+[Q[j][i]*qk[i] : i in [1..e]];
   Q[j]-:=Vector(Eltseq(V*(Q[j][e]-ip)/V[e]) cat pad); end for; end for;
 if real then return Transpose(Q),Transpose(R); // have QN=R^T
 else return ConjugateTranspose(Q),Transpose(R); end if; end intrinsic;

intrinsic QLDecomposition(M::Mtrx) -> AlgMatElt, Mtrx // see above
{Given a real/complex matrix, return a QL decomposition.
 Here Q is orthogonal/unitary of determinant 1 and L is *lower* triangular.}
 require Type(BaseRing(Parent(M))) in {FldCom,FldRe}:
  "Base ring must be real or complex";
 R,Q:=RQDecomposition(Transpose(M)); /* now internal */
 return Transpose(Q),Transpose(R); end intrinsic;

intrinsic NumericalPseudoinverse(M::Mtrx : Epsilon:=-1.0) -> Mtrx
{Given a real/complex matrix, return the pseudoinverse.}
 RING:=BaseRing(Parent(M)); is_real:=Type(RING) eq FldRe; nr:=Nrows(M);
 require Type(RING) in {FldCom,FldRe}: "Base ring must be real or complex";
 require Type(Epsilon) in {FldReElt}: "Epsilon must be real"; nc:=Ncols(M);
 Q,L,C,rk:=QLCDecomposition(M : Epsilon:=RealField(Precision(RING))!Epsilon);
 if rk eq 0 then return Parent(Transpose(M))!0; end if;
 k:=Nrows(L)-rk; A:=Matrix(Rows(L)[k+1..Nrows(L)]);
 if rk lt Ncols(M) then // recurse if not full column rank
  B:=Transpose(NumericalPseudoinverse(Transpose(A) : Epsilon:=Epsilon));
 else B:=NumericalInverse(A : Epsilon:=0.0); end if; // not the swiftest, but
 if is_real then QT:=Transpose(Q); else QT:=ConjugateTranspose(Q); end if;
 if is_real then CT:=Transpose(C); else CT:=ConjugateTranspose(C); end if;
 H:=HorizontalJoin(Matrix(RING,Nrows(B),k,[RING!0 : i in [1..k*Nrows(B)]]),B);
 return CT*H*QT; end intrinsic;

////////////////////////////////////////////////////////////////////////

/*
u:=60; C:=ComplexField(u); d:=80; k:=7;
M:=Matrix(d,d+k,
  [C![Random(-10^u,10^u)/10^u,Random(-10^u,10^u)/10^u] : i in [1..d^2+k*d]]);
N:=MatrixAlgebra(C,d+k)!0;
for i in [1..d] do N[i]:=M[i]; end for;
for i in [1..k] do N[d+k]:=M[Random(1,d)]; end for;
T:=IdentityMatrix(C,d+k);
for i in [1..d+k] do for j in [i+1..d+k] do
 T[i,j]:=C![Random(-10^u,10^u)/10^u,Random(-10^u,10^u)/10^u]; end for; end for;
N:=T*N; T:=IdentityMatrix(C,d+k);
for i in [1..d+k] do for j in [i+1..d+k] do
 T[j,i]:=C![Random(-10^u,10^u)/10^u,Random(-10^u,10^u)/10^u]; end for; end for;
N:=T*N; T:=IdentityMatrix(C,d+k);
for i in [1..d+k] do for j in [i+1..d+k] do
 T[i,j]:=C![Random(-10^u,10^u)/10^u,Random(-10^u,10^u)/10^u]; end for; end for;
N:=N*T; T:=IdentityMatrix(C,d+k);
for i in [1..d+k] do for j in [i+1..d+k] do
 T[j,i]:=C![Random(-10^u,10^u)/10^u,Random(-10^u,10^u)/10^u]; end for; end for;
N:=N*T;
time K,ev:=NumericalKernel(N); [Sqrt(Norm(k*N)) : k in K];
time Q,R:=QRDecomposition(N); Max([Real(Norm(x)) : x in Rows(Q*R-N)]);

////////////////////////////////////////////////////////////////////////

u:=60; R:=RealField(u); d:=80; k:=7;
M:=Matrix(d,d+k,[R!(Random(-10^u,10^u)/10^u) : i in [1..d^2+k*d]]);
N:=MatrixAlgebra(R,d+k)!0;
for i in [1..d] do N[i]:=M[i]; end for;
for i in [1..k] do N[d+k]:=M[Random(1,d)]; end for;
T:=IdentityMatrix(R,d+k);
for i in [1..d+k] do for j in [i+1..d+k] do
 T[i,j]:=R!(Random(-10^u,10^u)/10^u);  end for; end for;
N:=T*N; T:=IdentityMatrix(R,d+k);
for i in [1..d+k] do for j in [i+1..d+k] do
 T[j,i]:=R!(Random(-10^u,10^u)/10^u);  end for; end for;
N:=T*N; T:=IdentityMatrix(R,d+k);
for i in [1..d+k] do for j in [i+1..d+k] do
 T[i,j]:=R!(Random(-10^u,10^u)/10^u);  end for; end for;
N:=N*T; T:=IdentityMatrix(R,d+k);
for i in [1..d+k] do for j in [i+1..d+k] do
 T[j,i]:=R!(Random(-10^u,10^u)/10^u);  end for; end for;
N:=N*T;
time K,ev:=NumericalKernel(N); [Sqrt(Norm(k*N)) : k in K];
time Q,R:=QRDecomposition(N); Max([Sqrt(Norm(x)) : x in Rows(Q*R-N)]);
*/

/************************************************************************/

intrinsic Subdiagonal(M::Mtrx) -> SeqEnum
{Given a square matrix, return its subdiagonal elements}
 sz:=Max(Nrows(M)-1,Ncols(M));
 return [M[i+1][i] : i in [1..sz]]; end intrinsic;

// NumericalSchurForm: MW Jan/Feb 2016

intrinsic NumericalSchurForm(M::Mtrx : Transform:=true) -> Mtrx, Mtrx
{Given a real/complex square matrix, compute its Schur form S
 and an orthogonal/unitary matrix Q such that QMQ^T is equal to S}
 require Nrows(M) eq Ncols(M): "Matrix must be square";
 require Type(BaseRing(M)) in {FldRe,FldCom}: "Matrix must be real/complex";
 if Nrows(M) le 1 then return M,IdentityMatrix(BaseRing(M),Nrows(M)); end if;
 SYM:=(Type(BaseRing(M)) eq FldRe)
      select IsSymmetric(M) else (M eq ConjugateTranspose(M));
 if SYM and not Transform then H:=NumericalHessenbergForm(M);
  S:=InternalNumericalSymmetricFrancisQR(H); return S,_; end if;
 if Transform then
  H,T:=NumericalHessenbergForm(M); b,S,Q:=InternalNumericalFrancisQR_Step(H,T);
  while not b do b,S,Q:=InternalNumericalFrancisQR_Step(S,Q); end while;
  return S,Q;
 else H:=NumericalHessenbergForm(M); b,S:=InternalNumericalFrancisQR_Step(H);
      while not b do b,S:=InternalNumericalFrancisQR_Step(S); end while;
 end if; return S,_; end intrinsic;

function parlett_reinsch_balance(M) // needs to handle cn*rn=0 case!
 MD:=DiagonalMatrix(Diagonal(M)); A:=M-MD;
 k:=1; n:=Nrows(M); change:=false; D:=[BaseRing(MD)!1 : i in [1..n]];
 while true do rn:=Abs(Sqrt(Norm(A[k]))); cn:=Abs(Sqrt(Norm(Transpose(A)[k])));
  if rn ne 0 and cn ne 0 then s:=Floor(Log(rn/cn)/Log(4)+0.5); f:=2^s;
   if (cn*f)^2+(rn/f)^2 lt 0.999*(cn^2+rn^2) then;
    for i in [1..n] do A[k][i]:=A[k][i]/f; A[i][k]:=A[i][k]*f; end for;
     D[k]:=D[k]/f; change:=true; end if; end if; k:=k+1;
  if k gt n then if not change then break; end if; change:=false; k:=1; end if;
  end while; return A+MD,DiagonalMatrix(D); end function;

intrinsic ParlettReinschBalancing(M::Mtrx[RngReCom]) -> Mtrx,Mtrx
{Given a real/complex square matrix, return its Parlett-Reinsch balancing,
 that is, a matrix P such that P=DMD^(-1) for some (diagonal) matrix D, so
 that M and P have the same eigenvalues, with P numerically more suitable
 to computations. Also returns D as a second argument}
 require Nrows(M) eq Ncols(M): "Matrix must be square";
 require Type(BaseRing(M)) in {FldRe,FldCom}: "Matrix must be real or complex";
 if Nrows(M) le 1 then return M,Parent(M)!1; end if;
 return parlett_reinsch_balance(M); end intrinsic;
 
intrinsic NumericalEigenvalues(M::Mtrx[RngReCom] : Balance:=true) -> SeqEnum
{Given a real/complex square matrix, compute approximations to its eigenvalues}
 require Nrows(M) eq Ncols(M): "Matrix must be square";
 require Type(BaseRing(M)) in {FldRe,FldCom}: "Matrix must be real or complex";
 if Nrows(M) eq 0 then return [BaseRing(M)|]; end if;
 if Nrows(M) eq 1 then return [M[1][1]]; end if;
 function f(x,y)
  if Type(x) eq FldReElt and Type(y) ne FldReElt then return -1; end if;
  if Type(y) eq FldReElt and Type(x) ne FldReElt then return 1; end if;
  if Type(x) eq FldReElt and Type(y) eq FldReElt then return x-y; end if;
  if Real(x) eq Real(y) then return Imaginary(x)-Imaginary(y); end if;
  return Real(x)-Real(y); end function;
 if Balance then M:=parlett_reinsch_balance(M); end if;
 S:=NumericalSchurForm(M : Transform:=false); j:=1; C:=BaseRing(M); EV:=[C|];
 if Type(C) eq FldRe then C:=ComplexField(BaseRing(M)); end if;
 while j le Nrows(S) do
  if j eq Nrows(S) then EV cat:=[S[j][j]]; j:=j+1; continue; end if;
  if S[j+1][j] eq 0 then EV cat:=[S[j][j]]; j:=j+1; continue; end if;
  SUB:=Submatrix(S,j,j,2,2); t:=Trace(SUB); d:=Determinant(SUB);
  s:=Sqrt(C!t^2-4*d); EV cat:=[(t+s)/2,(t-s)/2]; j:=j+2; end while;
 ANS:=Sort(EV,f); return ANS; end intrinsic;

intrinsic NumericalBidiagonalForm(M::Mtrx[RngReCom]) -> Mtrx,Mtrx,Mtrx
{Given a real/complex matrix M, return B,U,V with B upper bidiagonal
 and M=UBV* when rows<=cols, and B lower bidiagonal in the alternative case.
 In the complex case, B still has real entries (all imag parts 0).}
 require Type(BaseRing(M)) in {FldRe,FldCom}: "Matrix must be real or complex";
 TRANS:=(Type(BaseRing(M)) eq FldRe) select Transpose else ConjugateTranspose;
 I:=IdentityMatrix(BaseRing(M),Min(Ncols(M),Nrows(M)));
 if Nrows(M) gt Ncols(M) then X:=TRANS(M); R,Q:=RQDecomposition(TRANS(M));
  B,U,V:=InternalNumericalBidiagonalForm(I,R,Q); return TRANS(B),V,U; end if;
 R,Q:=RQDecomposition(M); B,U,V:=InternalNumericalBidiagonalForm(I,R,Q);
 return B,U,V; end intrinsic;

intrinsic
NumericalSingularValueDecomposition(M::Mtrx[RngReCom]) -> Mtrx,Mtrx,Mtrx
{Given a real/complex matrix M, return S,U,V with UMV* = S, where S is the
 singular value matrix (diagonal), with entries the C-norms of eigenvalues}
 R:=BaseRing(M); require Type(R) in {FldRe,FldCom}: "Matrix not real/complex";
 B,U1,V1:=NumericalBidiagonalForm(M);
 if Type(R) eq FldCom then RR:=RealField(R); B:=ChangeRing(B,RR);
  Im:=IdentityMatrix(RR,Nrows(M)); In:=IdentityMatrix(RR,Ncols(M));
 else Im:=IdentityMatrix(R,Nrows(M)); In:=IdentityMatrix(R,Ncols(M)); end if;
 S,U2,V2:=InternalNumericalSVD_fromBidiagonal(Im,B,In); /* Im/In bad over C */
 if Type(R) eq FldRe then return S,U2*U1,V2*V1; end if; /* sloppy mult */
 return ChangeRing(S,R),ChangeRing(U2,R)*U1,ChangeRing(V2,R)*V1; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Pseudoinverse(M::Mtrx[RngReCom] : Epsilon:=0) -> Mtrx
{Abbreviation for NumericalPseudoinverse}
 return NumericalPseudoinverse(M : Epsilon:=Epsilon); end intrinsic;

intrinsic SchurForm(M::Mtrx[RngReCom] : Transform:=true) -> Mtrx, Mtrx
{Abbreviation for NumericalSchurForm}
 return NumericalSchurForm(M : Transform:=true); end intrinsic;

intrinsic Eigenvalues(M::Mtrx[RngReCom] : Balance:=true) -> SeqEnum
{Abbreviation for NumericalEigenvalues, though for backwards compatibility
 the return type is a sequence of <eigenvalues,multiplicities> rather than
 just eigenvalues. The "multiplicities" should not be taken too seriously,
 due to numerical constraints. Also, only real eigenvalues are returned
 for a real input}
 E:=Multiset(NumericalEigenvalues(M : Balance:=Balance)); BR:=BaseRing(M);
 if Type(BR) eq FldRe then p:=Precision(BR);
  E:=[BR!Real(e) : e in E | Abs(Imaginary(e)/e) lt 10^(-p+1)*Nrows(M)]; end if;
 return [<r,Multiplicity(E,r)> : r in Set(E)];  end intrinsic;

intrinsic BidiagonalForm(M::Mtrx[RngReCom]) -> Mtrx,Mtrx,Mtrx
{Abbreviation for NumericalBidiagonalForm}
 return NumericalBidiagonalForm(M); end intrinsic;

intrinsic SingularValueDecomposition(M::Mtrx[RngReCom]) -> Mtrx,Mtrx,Mtrx
{Abbreviation for NumericalSingularValueDecomposition}
 return NumericalSingularValueDecomposition(M); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic HessenbergForm(M::Mtrx[RngReCom]) -> Mtrx,Mtrx
{Abbreviation for NumericalHessenbergForm} // not same as internal method
 return NumericalHessenbergForm(M); end intrinsic; 

intrinsic Signature(M::Mtrx[RngReCom]) -> RngIntElt, RngIntElt
{Abbreviation for NumericalSignature.					 
 Given a real symmetric matrix, determine its signature.
 May fail if numerically unstable.}
 require Nrows(M) eq Ncols(M): "Must have same number of rows and columns";
 return NumericalSignature(M); end intrinsic;

intrinsic Inverse(M::Mtrx[RngReCom] : Epsilon:=0) -> Mtrx
{Abbreviation for NumericalInverse} // unneeded sig: convenient for Epsilon
 if Epsilon eq 0 then return NumericalInverse(M); end if;
 require Type(Epsilon) eq FldReElt: "Epsilon must be real";
 require Epsilon gt 0: "Epsilon must be positive";
 return NumericalInverse(M : Epsilon:=Epsilon); end intrinsic;

/*
// I don't see a reason for anything below, as internally it all goes to numer
intrinsic Rank(M::Mtrx[RngReCom] : Epsilon:=0) -> RngIntElt
{Abbreviation for NumericalRank}
 if Epsilon eq 0 then return NumericalRank(M); end if;
 require Type(Epsilon) eq FldReElt: "Epsilon must be real";
 require Epsilon gt 0: "Epsilon must be positive";
 return NumericalRank(M : Epsilon:=Epsilon); end intrinsic;

intrinsic IsConsistent // sadly gives ambiguity if deleted
(M::Mtrx[RngReCom],w::ModTupFldElt[RngReCom] : Epsilon:=0) ->
 BoolElt, ModTupFldElt, ModTupFld
{Abbreviation for NumericalIsConsistent,
 but the third return value is a space, not a matrix}
 if Epsilon eq 0 then b,S,K:=NumericalIsConsistent(M,w);
 else require Type(Epsilon) eq FldReElt: "Epsilon must be real";
       require Epsilon gt 0: "Epsilon must be positive";
       b,S,K:=NumericalIsConsistent(M,w : Epsilon:=Epsilon); end if;
 SK:=sub<RSpace(BaseRing(M),Nrows(M))|[Eltseq(e) : e in Rows(K)]>;
 return b,S,SK; end intrinsic;

intrinsic IsConsistent(M::Mtrx[RngReCom],w::Mtrx[RngReCom] : Epsilon:=0) ->
 BoolElt, ModMatFldElt, ModTupFld {"}//"
 if Epsilon eq 0 then b,S,K:=NumericalIsConsistent(M,w);
 else require Type(Epsilon) eq FldReElt: "Epsilon must be real";
       require Epsilon gt 0: "Epsilon must be positive";
       b,S,K:=NumericalIsConsistent(M,w : Epsilon:=Epsilon); end if;
 SK:=sub<RSpace(BaseRing(M),Nrows(M))|[Eltseq(e) : e in Rows(K)]>;
 return b,S,SK; end intrinsic;

// similarly, this gives an ambiguity if Mtrx[RngReCom]
intrinsic Nullspace(M::ModMatFldElt[RngReCom] : Epsilon:=0) -> ModTupFld
{Abbreviation for NumericalKernel, but returns a space, not a matrix}
 if Epsilon eq 0 then K:=NumericalKernel(M);
 else require Type(Epsilon) eq FldReElt: "Epsilon must be real";
      require Epsilon gt 0: "Epsilon must be positive";
      K:=NumericalKernel(M : Epsilon:=Epsilon); end if;
 S:=sub<RSpace(BaseRing(M),Nrows(M))|[Eltseq(e) : e in Rows(K)]>;
 return S; end intrinsic;

// similarly, this gives an ambiguity if Mtrx[RngReCom]
intrinsic Kernel(M::ModMatFldElt[RngReCom] : Epsilon:=0) -> ModTupFld
{Abbreviation for NumericalKernel, but returns a space, not a matrix}
 if Epsilon eq 0 then K:=NumericalKernel(M);
 else require Type(Epsilon) eq FldReElt: "Epsilon must be real";
      require Epsilon gt 0: "Epsilon must be positive";
      K:=NumericalKernel(M : Epsilon:=Epsilon); end if;
 S:=sub<RSpace(BaseRing(M),Nrows(M))|[Eltseq(e) : e in Rows(K)]>;
 return S; end intrinsic;

intrinsic Solution(M::Mtrx[RngReCom],w::ModTupFldElt[RngReCom] : Epsilon:=0) ->
 ModTupFldElt, ModMatFld // necessary for ambiguity resolution
{Abbreviation for NumericalSolution,
 though the second return value is a space rather than a matrix}
 if Epsilon eq 0 then s,K:=NumericalSolution(M,w);
 else require Type(Epsilon) eq FldReElt: "Epsilon must be real";
      require Epsilon gt 0: "Epsilon must be positive";
      s,K:=NumericalSolution(M,w : Epsilon:=Epsilon); end if;
 S:=sub<RSpace(BaseRing(M),Nrows(M))|[Eltseq(e) : e in Rows(K)]>;
 return s,S; end intrinsic;

intrinsic Solution(M::Mtrx[RngReCom],w::Mtrx[RngReCom] : Epsilon:=0) ->
 ModTupFldElt, ModMatFld {"}//"
 if Epsilon eq 0 then s,K:=NumericalSolution(M,w);
 else require Type(Epsilon) eq FldReElt: "Epsilon must be real";
      require Epsilon gt 0: "Epsilon must be positive";
      s,K:=NumericalSolution(M,w : Epsilon:=Epsilon); end if;
 S:=sub<RSpace(BaseRing(M),Nrows(M))|[Eltseq(e) : e in Rows(K)]>;
 return s,S; end intrinsic;
*/
