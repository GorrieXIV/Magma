
freeze;

/* 
This package provides basic operations for Phi modules over a field of power series with
coefficients in a finite field of characteristic p.

Add documentation...
*/

import "skewpoly.m":
 RandomSkewPolynomial, FindFactorSS, SkewFactorization_list;

//*************************************
// Basic creation functions
//*************************************

declare type PhiModElt: ModMatFldElt;
declare attributes PhiModElt: Parent,Vector;

declare type PhiMod [PhiModElt]: ModMatFld;
declare attributes PhiMod: Space, Phi, r, Frobenius;

intrinsic Dimension(D::PhiMod) -> RngIntElt
  {Return the dimension of the phi-module D}
  return Dimension(D`Space);
end intrinsic;

intrinsic BaseRing(D::PhiMod) -> Rng
  {Return the coefficient ring of the phi-module D}
  return CoefficientRing(D`Space);
end intrinsic;

intrinsic FrobeniusMatrix(D::PhiMod) -> ModMatFldElt
  {Return the matrix of the Frobenius action on D}
  return D`Phi;
end intrinsic;

intrinsic Print(x::PhiModElt)
  {Print an element of a phi-module}
  printf "Element of a phi-module of dimension %o over %o with Frobenius %o", Dimension(x`Parent), CoefficientRing(x`Vector),
  (x`Parent)`Frobenius;
end intrinsic;
  
intrinsic Print(D::PhiMod)
  {Print a phi-module}
  printf "Phi-module of dimension %o over %o with matrix\n%o and Frobenius %o", Dimension(D), CoefficientRing(D), D`Phi, D`Frobenius;
end intrinsic;
  
//*************************************
// Compute the Frobenius on S1
//*************************************

_FrobS1 := function(x,b,s)
  S1:=Parent(x);
  u1:=S1.1;
  v:=Valuation(x);
  apr:=AbsolutePrecision(x);
  if apr le v then 
     return S1!0;
  else
  y:=S1!0;
  z:=x;
  while Valuation(z) lt apr do
    v:=Valuation(z);
    y:=y+Frobenius(Coefficient(x,v),s)*u1^(b*v);
    z:=z-Coefficient(x,v)*u1^v;
    apr:=AbsolutePrecision(z);
  end while;
  return y;
  end if;
end function;

FrobS1 := function(x)
  p:=Characteristic(Parent(x));
  return _FrobS1(x,p,1);
end function;

//****************************************************
// Compute the Frobenius on Matrices with coeffs in S1
//****************************************************

_FrobS1Mat := function(M,b,s)
  n:=Nrows(M);
  m:=Ncols(M);
  S1:=Parent(M[1,1]);
  FM:=ZeroMatrix(S1,n,m);
  for i in [1..n] do
    for j in [1..m] do
      FM[i,j]:=_FrobS1(M[i,j],b,s);
    end for;
  end for;
  return FM;
end function;

FrobS1Mat := function(M)
  n:=Nrows(M);
  m:=Ncols(M);
  S1:=Parent(M[1,1]);
  FM:=ZeroMatrix(S1,n,m);
  for i in [1..n] do
    for j in [1..m] do
      FM[i,j]:=FrobS1(M[i,j]);
    end for;
  end for;
  return FM;
end function;

tr:=function(x,S,u)
  v:=Ceiling(Valuation(x));
  apr:=Ceiling(AbsolutePrecision(x))-1;
    if (v eq Infinity()) or (apr lt v) then return 0;
    else y:=&+[Coefficient(x,i)*u^i : i in [v..apr]];
        return y;
    end if;
end function;

RandomMatrix:=function(S,d,r)
  pr:=Precision(S);
  u:=UniformizingElement(S);
  K:=CoefficientRing(S);
  G:=ZeroMatrix(S,d,d);
  for i in [1..d] do
    for j in [1..d] do
      G[i,j]:=u^Random(r)*&+[Random(K)*u^i : i in [0..pr]];
    end for;
  end for;
  return G;
end function;
  

//*************************************************
// Compute the Smith and Hermite normal forms on S1
//*************************************************

_SmithOverS1:=function(M,prec)
  m:=Ncols(M);              
  n:=Nrows(M);
  S1:=Parent(M[1,1]);
  u:=UniformizingElement(S1);
  P:=IdentityMatrix(S1,n);
  Pinv:=IdentityMatrix(S1,n);
  Q:=IdentityMatrix(S1,m);
  N:=M;
    for j in [1..m] do
      i:=j;
      t:=j;
      val:=Infinity();
      for r in [j..n] do
        for s in [j..m] do
          if val gt Valuation(N[r,s]) then
            val:=Valuation(N[r,s]);
            i:=r;
            t:=s;
          end if;
        end for;
      end for;
      if val ge prec then return P,Pinv,N;
      else
        SwapRows(~N,i,j);
        SwapRows(~P,i,j);
        SwapColumns(~Pinv,i,j);
        SwapColumns(~N,t,j);
        SwapColumns(~Q,t,j);
        c:=1/N[j,j];
        for s in [j+1..n] do
          cst:=-N[s,j];
          AddRow(~N, cst*c, j,s);
          AddRow(~P, cst*c, j,s);
          AddColumn(~Pinv,-cst*c,s,j);
        end for;
      end if;
    end for;
  return P,Pinv,N;
end function;          
  
SmithOverS1:=function(M)
  S1:=Parent(M[1,1]);
  return _SmithOverS1(M,Precision(S1));
end function;

_HermiteOverS1:=function(M,prec)
  m:=Ncols(M);          
  n:=Nrows(M);
  S1:=CoefficientRing(M);
  u:=UniformizingElement(S1);
  P:=IdentityMatrix(S1,n);
  Pinv:=IdentityMatrix(S1,n);
  Q:=IdentityMatrix(S1,m);
  N:=M;
  for j in [1..m] do
    i:=j;
    t:=j;
    val:=Infinity();
    for r in [j..n] do
      for s in [j..m] do
        if val gt Valuation(N[r,s]) then
          val:=Valuation(N[r,s]);
          i:=r;
          t:=s;
        end if;
      end for;
    end for;
    if val ge prec then
      return P,Pinv,Q,N;
    else
      SwapRows(~N,i,j);
      SwapRows(~P,i,j);
      SwapColumns(~Pinv,i,j);
      SwapColumns(~N,t,j);
      SwapColumns(~Q,t,j);
      c:=1/N[j,j];
      for s in [j+1..n] do
        cst:=-N[s,j];
        AddRow(~N, cst*c, j,s);
        AddRow(~P, cst*c, j,s);
        AddColumn(~Pinv,-cst*c,s,j);
      end for;
      for s in [j+1..m] do
        cst:=-N[j,s];
        AddColumn(~N,cst*c,j,s);
        AddColumn(~Q,cst*c,j,s);
      end for;
      MultiplyColumn(~N,u^(-Valuation(c))*c,j);
      MultiplyColumn(~Q,u^(-Valuation(c))*c,j);
    end if;
  end for;
  return P,Pinv,Q,N;
end function;

HermiteOverS1:=function(M)
  S1:=Parent(M[1,1]);
  return _HermiteOverS1(M,Precision(S1));
end function;  

LargestInvFactorVal:=function(M)
  P,Pinv,N:=SmithOverS1(M);
  n:=Ncols(M);
  return Valuation(N[n,n]);
end function;


//******************************************
// Functions for etale Phi-modules over S1
//******************************************

// An etale Phi-module D over S1 is a S1-vector space of finite dimension, with attributes:
// - the Frobenius action on the coefficients of D, given as a couple [s,b], the action being given by F(a) = a^(p^s) when a lies in
// the base field, and F(u) = u^b. The integer s may be 0. The integer b must be > 1.
// - the matrix of the map Phi in a basis of D
// - an integer r such that u^rD lies inside the submodule generated by the image of Phi.

intrinsic IsEtale(D::PhiMod) -> BoolElt
  {Say whether a phi-module is etale}
  return D`r lt Precision(CoefficientRing(D));
end intrinsic;

RandomPhiModule:=function(S,d,r,Frob)
  G:=RandomMatrix(S,d,r);
  r0:=LargestInvFactorVal(G);
  while r0 ge Precision(S) do
    G:=RandomMatrix(S,d,r);
    r0:=LargestInvFactorVal(G);
  end while;
  PhM:=New(PhiMod);
  PhM`Space:=VectorSpace(S,d);
  PhM`r:=r0;
  PhM`Phi:=G;
  PhM`Frobenius:=Frob;
  return PhM;
end function;

intrinsic PhiModule
(G::AlgMatElt:F:=[1,Characteristic(Parent(G))]) -> PhiMod
  {Create a phi-module out of its matrix G.
The optional argument F describes the action of the Frobenius on the coefficients by a couple [s,b], the action on the residue field is given by a -> a^(p^s) and the action on the variable u is given by u-> u^b. The default value is such that the Frobenius is the classical x -> x^p map.
  }
  r0:=LargestInvFactorVal(G);
  assert r0 lt Precision(CoefficientRing(G));
  PhM:=New(PhiMod);
  PhM`Space:=VectorSpace(CoefficientRing(G),Ncols(G));
  PhM`Phi:=G;
  PhM`r:=r0;
  PhM`Frobenius:=F;
  return PhM;
end intrinsic;

intrinsic PhiModuleElement(x::ModMatFldElt,D::PhiMod) -> PhiModElt
  {Create an element of a phi-module D out of a vector x. The vector should have dimension d x 1 (where dim D = d) and the same coefficient ring as D.}
  require CoefficientRing(x) eq CoefficientRing(D`Space):"Vector must be in the underlying vector space";
  v:=New(PhiModElt);
  v`Parent:=D;
  v`Vector:=x;
  return v;
end intrinsic;

intrinsic ChangePrecision(~D::PhiMod,pr::RngIntElt)
  {Change the precision of a phi-module D to the precision pr}
  S:=CoefficientRing(D`Space);
  ChangePrecision(~S,pr);
  d:=Dimension(D);
  D`Space:=VectorSpace(S,d);
  G:=ZeroMatrix(S,d,d);
  for i in [1..d] do
    for j in [1..d] do
      G[i,j]:=S!(D`Phi[i,j]);
    end for;
  end for;
  D`Phi:=G;
end intrinsic;

intrinsic ElementaryPhiModule
(S::RngSerLaur,d::RngIntElt,s::RngIntElt:F:=[1,Characteristic(S)]) -> PhiMod
  {Create an elementary phi-module D(d,s) over the ring S. The optional argument F describes the action of the Frobenius on the coefficients}
  u:=UniformizingElement(S);
  G:=ZeroMatrix(S,d,d);
  for i in [1..d-1] do
    G[i+1,i] := 1;
  end for;
  G[1,d]:=u^s;
  PhM:=New(PhiMod);
  PhM`Phi:=G;
  PhM`Space := VectorSpace(S,d);
  PhM`r:=s;
  PhM`Frobenius:=F;
  return PhM;
end intrinsic;

intrinsic DirectSum(Phi1::PhiMod,Phi2::PhiMod) -> PhiMod
{Return the phi-module obtained by direct sum of the phi-modules Phi1 and Phi2}
  G1:=Phi1`Phi;
  G2:=Phi2`Phi;
  r1:=Phi1`r;
  r2:=Phi2`r;
  S:=CoefficientRing(G1);
  assert S eq CoefficientRing(G2);
  d1:=Ncols(G1);
  d2:=Ncols(G2);
  G:=ZeroMatrix(S,d1+d2,d1+d2);
  InsertBlock(~G,G1,1,1);
  InsertBlock(~G,G2,1+d1,1+d1);
  PhM:=New(PhiMod);
  PhM`Space:=VectorSpace(CoefficientRing(Phi1),d1+d2);
  PhM`Phi:=G;
  PhM`r:=Maximum(r1,r2);
  PhM`Frobenius:=Phi1`Frobenius;
  return PhM;
end intrinsic;

intrinsic BaseChange(~D::PhiMod,P::AlgMatElt)
  {Change the basis in which the matrix of the Frobenius action on the phi-module D is written. The base change matrix is P.}
  assert Valuation(Determinant(P)) eq 0;
  b:=D`Frobenius[2];
  s:=D`Frobenius[1];
  FrobS1:=function(x)
    return _FrobS1(x,b,s);
  end function;
  FrobMatS1:=function(M)
    return _FrobS1Mat(M,b,s);
  end function;
  D`Phi:=P^(-1)*(D`Phi)*FrobMatS1(P);
end intrinsic;

intrinsic RandomBaseChange(~D::PhiMod)
  {Randomly change the basis in which the matrix of the Frobenius action on the phi-module D is written.}
  S:=CoefficientRing(D`Phi);
  d:=Dimension(D);
  while true do
    P:=RandomMatrix(S,d,0);
    if Valuation(Determinant(P)) eq 0 then
      BaseChange(~D,P);
      break;
    end if;
  end while;
end intrinsic;

intrinsic Phi(D::PhiMod,x::PhiModElt) -> PhiModElt
  {Apply the map phi on the phi-module D to an element x of D}
  G:=D`Phi;
  s:=D`Frobenius[1];
  b:=D`Frobenius[2];
  v:=x`Vector;
  return PhiModuleElement(G*_FrobS1Mat(v,b,s),D);
end intrinsic;

RequestedPrecision:=function(D) // Precision the algorithm needs on coeffs to work
  G:=D`Phi;
  r:=D`r;
  b:=D`Frobenius[2];
  d:=Ncols(G);
  c:=Floor(r/(b-1)+1);
  prec:= (b+2 + d)*c ;
  return prec;
end function;

MatrixMod:=function(M,prec) // Computes M mod u^prec
  m:=Ncols(M);
  n:=Nrows(M);
  S1:=Parent(M[1,1]);
  u:=UniformizingElement(S1);
  M0:=ZeroMatrix(S1,n,m);
  for i in [1..n] do
    for j in [1..m] do
      if Valuation(M[i,j]) ge prec then
        M0[i,j]:=0;
      else
        M0[i,j]:=&+[Coefficient(M[i,j],t)*u^t : t in [Valuation(M[i,j])..prec]];
      end if;
    end for;
  end for;
  return M0;
end function;


Relations:=function(G,r,b,FrobS1,FrobMatS1,x)
  d:=Ncols(G);
  c:=Floor(r/(b-1))+2; //Attention, c'est +2 en fait. Je mets +1 pour un test
  vec:=x;
  nilist:=[];
  S1:=CoefficientRing(G);
  K:=CoefficientRing(S1);
  u1:=UniformizingElement(S1);
  X:=ZeroMatrix(S1,d,d*c+1);
  InsertBlock(~X,vec,1,1);
  isfree:=true;
  i:=2;
  Q:=IdentityMatrix(K,d*c);
  P:=IdentityMatrix(K,d*c);
  family:=ZeroMatrix(K,d*c,1);
  for j in [1..d] do
    for r in [1..c] do
      family[(j-1)*c+r,1]:=Coefficient(vec[j,1],r-1);
    end for;
  end for;
  while isfree do                                     
    v0:=G*FrobMatS1(vec);								
    n:=Minimum([Valuation(v0[j,1]) : j in [1..d]]);
    vec:=((1/u1)^n)*v0;
    Append(~nilist,n);
    InsertBlock(~X,vec,1,i);
    vec2:=ZeroMatrix(K,d*c,1);
    for j in [1..d] do
      for r in [1..c] do
        vec2[(j-1)*c+r,1]:=Coefficient(vec[j,1],r-1);
      end for;
    end for;
    vec2:=Q*vec2;
    Mat:=ZeroMatrix(K,d*c,i);
    InsertBlock(~Mat,family,1,1);
    InsertBlock(~Mat,vec2,1,i);
    m:=i;
    while m le d*c and Mat[m,i] eq 0 do
      m:=m+1;
    end while;
    if m eq d*c+1 then
      isfree:=false;   
      rel:=vec2;           
    else
      SwapRows(~Mat,i,m);
      SwapRows(~Q,i,m);
      MultiplyRow(~Q,1/Mat[i,i],i);
      MultiplyRow(~Mat,1/Mat[i,i],i);
      for j in [1..i-1] do
        coef:=-Mat[j,i];
        AddRow(~Mat,coef,i,j);
        AddRow(~Q,coef,i,j);
      end for;
      for j in [i+1..d*c] do
        coef:=-Mat[j,i];
        AddRow(~Mat,coef,i,j);
        AddRow(~Q,coef,i,j);
      end for;
      i:=i+1;
    end if;
    family:=Mat;
  end while;
  t:=1;
  while rel[t,1] eq 0 do
    t:=t+1;
  end while;
  return nilist[t..i-1],Submatrix(X,1,t,d,i-t),Submatrix(rel,t,1,i-t,1);
end function;

Relevexi:=function(G,nilist,X,rel,S1,FrobS1,FrobMatS1,prec);   // Relever une famille li\ufffde mod u^c en une li\ufffde mod u^prec
  Y:=X;
  u:=UniformizingElement(S1);
  d:=Ncols(G);
  N:=Ncols(X);
  x:=Submatrix(X,1,1,d,1);
  y:=rel[1,1]^(-1)*(u^(-nilist[N])*G*FrobMatS1(Submatrix(X,1,N,d,1)) - &+[rel[i,1]*Submatrix(X,1,i,d,1) : i in [1..N]]);
  v:=Minimum([Valuation(y[j,1]) : j in [1..d]]);  // Les calculs sont justifi\ufffds dans l'article
  while (v lt prec) do
    if x eq (x + y) then
	  break;
    end if;
    x:=x+y;
    z:=x;
    for j in [1..N] do
      InsertBlock(~Y,z,1,j);
      z:=u^(-nilist[j])*G*FrobMatS1(z);
    end for;
    y:=rel[1,1]^(-1)*(u^(-nilist[N])*G*FrobMatS1(Submatrix(Y,1,N,d,1)) -&+[rel[i,1]*Submatrix(Y,1,i,d,1) : i in [1..N]]);
    v:=Minimum([Valuation(y[j,1]) : j in [1..d]]);
  end while;
  return nilist,Y,rel;
end function;

Iteratex:=function(G,x, S1, FrobS1,FrobMatS1)
  d:=Ncols(G);
  H:=G;
  u1:=UniformizingElement(S1);
  y:=Submatrix(x,1,1,d,1);
  M:=ZeroMatrix(S1,d,d);
  nilist:=[];
  for i in [1..d] do
    InsertBlock(~M,y,1,i);
    y:=H*FrobMatS1(y);
    n:=Minimum([Valuation(y[j,1]) : j in [1..d]]);
    y:=u1^(-n)*y;
    Append(~nilist,n);
  end for;
  return M;
end function;

SimplifySlope:=function(j,s,b)
  r:=s/(b^j-1);
  t:=Denominator(r);
  i:=1;
  while ((b^i -1) mod t) ne 0 do
    i:=i+1;
  end while;
  j0:=i;
  s0:=s div ((b^j -1) div (b^j0 -1));
  return j0,s0;
end function;

SolvePuiseux:=function(list,vec,t,S1,b,si,FrobS,FrobMatS)
  k:=CoefficientRing(S1);
  S<u>:=PuiseuxSeriesRing(k,Precision(S1));
  function PFrobS(x,j)
    if j eq 0 then
      return x;
    else
      return FrobS(PFrobS(x,j-1));
    end if;
  end function;
  function PFrobMatS(M,j)
    if j eq 0 then
      return M;
    else
      return FrobMatS(PFrobMatS(M,j-1));
    end if;
  end function;
  function Psigma(a,j)
    return Frobenius(a,si*j);
  end function;
  N:=#list;
  if N eq 1 then
    return Matrix(S,1,1,[1]),[1,Valuation(S!vec[1,1])+list[1]],[-Coefficient(S!vec[1,1],Valuation(S!vec[1,1])),1];
  else
    J:=[0];
    vv:=(Valuation(S!vec[N,1])+list[N])/(b-1);
    for i in [1..N-1] do
      cst:=(b^i*Valuation(S!vec[N-i,1]) + b^i*list[N]+ &+[b^(j-1)*list[N - j] : j in [1..i]])/(b^(i+1)-1);
      if cst lt vv then
        vv:=cst;
        J:=[i];
      else
	    if cst eq vv then
            Append(~J,i);
        end if;
      end if;
    end for;
    j0:=Minimum(J)+1;
    n:=Maximum(J)+1;
    s:=IntegerRing()!(vv*(b^(j0) -1));
    vn:=Valuation(S!vec[N-n+1,1]);
    aninv:=1/Psigma(Coefficient(S!vec[N-(n-1),1],vn),n-1);
	listcoeff:=[-aninv];
	for i in [0..n-2] do
	  if (i in J) then
	    vj:=Valuation(S!vec[N-i ,1]);
	    Append(~listcoeff, aninv*Psigma(Coefficient(S!vec[N-i,1],vj),i));
      end if;
    end for;
	Append(~listcoeff,1);
	j1,s1:=SimplifySlope(j0,s,b);
	listcoeff2:=[];
	for i in [1..#listcoeff -1] do
	  Append(~listcoeff2,listcoeff[i]);
	  for j in [1..(j0 div j1) - 1] do
	    Append(~listcoeff2,0);
	  end for;
    end for;
	Append(~listcoeff2, listcoeff[#listcoeff]);
//        print listcoeff2, si,j1;
	listfac:=SkewFactorization_list(listcoeff2,si*j1);
//        print listfac;
	list1:=listfac[#listfac];
	n1:=(#list1-1);
	M:=ZeroMatrix(S,j1*n1,j1*n1);	
	for i in [1..j1*n1-1] do
      M[i+1,i]:=1;
      if (((i-1) mod j1) eq 0) then
        M[i,j1*n1]:=-list1[n1 - ((i-1) div j1)];
      end if;
    end for;
	M[1,j1*n1]:=-list1[1];
    xi:=ZeroMatrix(S,n1*j1,N);
    for i in [1..Minimum(n1*j1,N)] do
       xi[i,i]:=1;
    end for;
    xi0:=Submatrix(M,1,n1*j1,n1*j1,1);
    for i in [n1*j0+1..N] do
      InsertBlock(~xi,xi0,1,i);
      for j in [1..n1*j1] do
        xi0[j,1]:=FrobS(xi0[j,1]);
      end for;
      xi0:=M*xi0;
    end for;
    Mi:=[M];
    M0:=M;
    for i in [1..N-1] do
      M0:=M*FrobMatS(M0);
      Append(~Mi,M0);
    end for;
    mui:=ZeroMatrix(S,N,1);
    lambda0i:=ZeroMatrix(S,N,1);
    lambdai:=ZeroMatrix(S,N,1);
    for j in [0..N-1] do
      if j in J then
        val:=Valuation(S!vec[N-j,1]);
        lam:=u^(-val)*(S!vec[N-j,1]);
        lamp:=PFrobS(lam,j);
        lambda0i[j+1,1]:=lamp;
        mui[j+1,1]:=lamp-Coefficient(lamp,0);
	  else
        lambdai[j+1,1]:=PFrobS(u^(-b*vv+list[N])*vec[N-j,1],j)*u^vv;
      end if;
    end for;
    Y1:=&+[(mui[j,1] + lambdai[j,1])*Submatrix(xi,1,j,n1*j1,1) : j in [1..N]];
    Y:=Y1;
    prc:=1;
    while prc lt t do
      prc:=b*prc;
      Y:=Y1 + &+[(lambda0i[j,1] + u^(list[N])*lambdai[j,1])*M*PFrobMatS(Y,j): j in [1..N]];
    end while;
	xsol:=ZeroMatrix(S,n1*j1,N);
    unFxN:=u^(list[N])*M*FrobMatS(u^(-vv)*(Submatrix(xi,1,1,n1*j1,1) + Y));
    InsertBlock(~xsol, u^(-vv)*(Submatrix(xi,1,1,n1*j1,1) + Y), 1,N);
	//InsertBlock(~xsol, vec[1,1]*unFxN,1,1);
    InsertBlock(~xsol, u^list[N]*vec[1,1]*M*FrobMatS(Submatrix(xsol, 1,N, n1*j1,1)),1,1);
    for i in [2..N-1] do
      InsertBlock(~xsol,u^(list[i-1])*M*FrobMatS(Submatrix(xsol, 1,i-1, n1*j1,1)) + vec[i,1]*unFxN, 1, i) ;
    end for;
    vecsol:=ZeroMatrix(S,N,1);
    for i in [1..N] do
      vecsol[i,1]:=tr((u^vv)*xsol[1,i],S1,UniformizingElement(S1));
    end for;
    return vecsol, [j1,s1], listcoeff2;  // Le vecteur cherch\ufffd et la pente du sous-module associ\ufffd.
  end if;
end function;

UnbuildMatrix:=function(M)
  listc:=[];
  listv:=[];
  n:=Nrows(M);
  m:=Ncols(M);
  Pol:=Eltseq(DefiningPolynomial(CoefficientRing(CoefficientRing(M))));
  for i in [1..n] do
    for j in [1..m] do
      listcoeff,val:=Eltseq(M[i,j]);
      Append(~listc,[Eltseq(listcoeff[i]) : i in [1.. #listcoeff]]);
      Append(~listv, val);
    end for;
  end for; 
  return listc, listv, Pol;
end function;

BuildMatrix:=function(S,n,m,listc,listv)
  L:=CoefficientRing(S);
  M := ZeroMatrix(ChangeRing(S,L),n,m);
  for i in [1..n] do
    for j in [1..m] do
      M[i,j]:= S.1^listv[m * (i-1) + j]*S![L!listc[m*(i-1) + j][t]  : t in [1..#listc[m*(i-1) + j]]];
    end for;
  end for;
  return M;
end function;

SolvePuiseux_0:=function(list,vec,t,S1,b,si,FrobS,FrobMatS)
  k:=CoefficientRing(S1);
  S<u>:=PuiseuxSeriesRing(k,Precision(S1));
  function PFrobS(x,j)
    if j eq 0 then
      return x;
    else
      return FrobS(PFrobS(x,j-1));
    end if;
  end function;
  function PFrobS(x,j)
    if j eq 0 then
      return x;
    else
      return FrobS(PFrobS(x,j-1));
    end if;
  end function;
  function PFrobMatS(M,j)
    if j eq 0 then
      return M;
    else
      return FrobMatS(PFrobMatS(M,j-1));
    end if;
  end function;
  function Psigma(a,j)
    return a;
  end function;
  N:=#list;
  if N eq 1 then
    return Matrix(S,1,1,[1]),[1,Valuation(S!vec[1,1])+list[1]], k, [-Coefficient(S!vec[1,1,Valuation(S!vec[1,1])]),1];
  else
    J:=[0];
    vv:=(Valuation(S!vec[N,1])+list[N])/(b-1);
    for i in [1..N-1] do
      cst:=(b^i*Valuation(S!vec[N-i,1]) + b^i*list[N]+ &+[b^(j-1)*list[N - j] : j in [1..i]])/(b^(i+1)-1);
      if cst lt vv then
        vv:=cst;
        J:=[i];
      else
	if cst eq vv then
          Append(~J,i);
        end if;
      end if;
    end for;
    j0:=Minimum(J)+1;
    n:=Maximum(J)+1;
    s:=IntegerRing()!(vv*(b^(j0) -1));
    vn:=Valuation(S!vec[N-n+1,1]);
    listcoeff:=[-k!1];
    for i in [0..n-1] do
      if (i in J) then
	vj:=Valuation(S!vec[N-i ,1]);
	Append(~listcoeff, Coefficient(S!vec[N-i,1],vj));
      else
        Append(~listcoeff,k!0);
      end if;
    end for;
    listfac:=Factorization(PolynomialRing(k)!Reverse(listcoeff));
    Pol:=listfac[1][1];
    if Degree(Pol) eq 1 then
      L:=k;
      mu:= - Coefficient(Pol,0);
    else
      L<mu>:=ext<k|listfac[1][1]>;
    end if;
    S2:=ChangeRing(S,L);
    mui:=ZeroMatrix(S2,N,1);
    lambda0i:=ZeroMatrix(S2,N,1);
    lambdai:=ZeroMatrix(S2,N,1);
    for j in [0..N-1] do
      if j in J then
        val:=Valuation(S!vec[N-j,1]);
        lam:=u^(-val)*(S!vec[N-j,1]);
        lambda0i[j+1,1]:=lam;
        mui[j+1,1]:=lam-Coefficient(lam,0);
      else
        lambdai[j+1,1]:= u^(-(b-1)*vv+list[N])*S2!vec[N-j,1];
      end if;
    end for;
	Y1:=&+[mu^(j+1)*(mui[j,1] + lambdai[j,1]) : j in [1..N]];
    Y:=Y1;
    prc:=1;
    while prc lt t do
      prc:=b*prc;
      Y:=Y1 + &+[mu^(j+1)*(lambda0i[j,1] + u^(list[N])*lambdai[j,1])*PFrobS(Y,N - j): j in [1..N]];
    end while;
    unFxN:=u^(list[N])*u^(-b*vv)*FrobS(1 + Y);
    xsol:=ZeroMatrix(S2,N,1);
    xsol[1,1]:= mu^(-1)*vec[1,1]*unFxN;
    for i in [2..N-1] do
      xsol[i,1] := mu^(-1)*(u^list[i-1] *FrobS(xsol[i-1,1]) + vec[i,1]*unFxN);
    end for;
    xsol[N,1]:=u^(-vv)*(1+Y);
    S3:=ChangeRing(S,L);
    vecsol:=ZeroMatrix(S3,N,1);
    for i in [1..N] do
      vecsol[i,1]:=tr((u^vv)*xsol[i,1],S3,UniformizingElement(S3));
    end for;
    return vecsol, [j0,s], L, Eltseq(mu);  // Le vecteur cherche et la pente du sous-module associe.
  end if;
end function;

Cyclicvector:=function(G,r,b,sigma,FrobS1,FrobMatS1)
  d:=Ncols(G);
  S:=Parent(G[1,1]);
  u:=UniformizingElement(S);
  l:=[S!0 : j in [2..d]];
  Insert(~l,1,S!1);
  n:=Floor(r/(b-1))+1;
  vec:=Matrix(S,d,1,l);
  list,X,vec:=Relations(G,r,b,FrobS1,FrobMatS1,vec);
  N:=#list;
  while n gt r/(b-1) do
    vecsol, couple,pol:=SolvePuiseux(list,vec,(b+2)*r,S,b,sigma,FrobS1,FrobMatS1);
    valpha:=Minimum([Valuation(vecsol[i,1]) : i in [1..Nrows(vecsol)]]);
    Pr2:=Floor((b+2)*r/(b-1)) +1 - Minimum([valpha,0]) ;
    list,X,vec:=Relevexi(G,list,X,vec, S,FrobS1,FrobMatS1, Pr2);
    sol:=&+[vecsol[i,1]*Submatrix(X,1,i,d,1) : i in [1..N]];
    n:=Minimum([Valuation(sol[i,1]) : i in [1..d]]);
    sol:=u^(-n)*sol;
    l:=[];
    N:=N-1;
    X:=Submatrix(X,1,1,d,N);
    vec:=ZeroMatrix(S,N,1);
    for i in [1..N] do
      vec[i,1]:= -vecsol[i,1]/vecsol[N+1,1];
    end for;
    Prune(~list);
  end while;
  return sol, couple, n, pol;
end function;

Cyclicvector_0:=function(G,r,b,sigma, FrobS1, FrobMatS1)
  d:=Ncols(G);
  S:=Parent(G[1,1]);
  k:=CoefficientRing(S);
  u:=UniformizingElement(S);
  l:=[S!0 : j in [2..d]];
  Insert(~l,1,S!1);
  n:=Floor(r/(b-1))+1;
  vec:=Matrix(S,d,1,l);
  list,X,vec:=Relations(G,r,b,FrobS1,FrobMatS1,vec);
  N:=#list;
  while n gt r/(b-1) do
    vecsol, couple, L, mu:=SolvePuiseux_0(list,vec,(b+2)*r,S,b,sigma,FrobS1,FrobMatS1);
    Embed(k,L);
    S1:=ChangeRing(S,L);
    G1:=ChangeRing(G, S1);
    valpha:=Minimum([Valuation(vecsol[i,1]) : i in [1..Nrows(vecsol)]]);
    Pr2:=Floor((b+2)*r/(b-1)) +1 - Minimum([valpha,0]) ;
    list,X,vec:=Relevexi(G1,list,ChangeRing(X,S1),ChangeRing(vec,S1), S1,FrobS1,FrobMatS1, Pr2);
    sol:=&+[vecsol[i,1]*Submatrix(X,1,i,d,1) : i in [1..N]];
    n:=Minimum([Valuation(sol[i,1]) : i in [1..d]]);
    sol:=u^(-n)*sol;
    l:=[];
    N:=N-1;
    X:=Submatrix(X,1,1,d,N);
    vec:=ZeroMatrix(S1,N,1);
    for i in [1..N] do
      vec[i,1]:= -vecsol[i,1]/vecsol[N+1,1];
    end for;
    Prune(~list);
  end while;
  return sol, couple, n, L, L!mu;
end function;

SemisimpleDecomposition_0:= function(D)
  G0:=D`Phi;
  r:=D`r;
  si:=D`Frobenius[1];
  b:=D`Frobenius[2];
  S1:=CoefficientRing(G0);
  d:=Ncols(G0);
  prec:=RequestedPrecision(D);
  S<u>:=ChangePrecision(S1,prec);
  FrobS1:=function(x)
    return _FrobS1(x,b,si);
  end function;
  FrobMatS1:=function(M)
    return _FrobS1Mat(M,b,si);
  end function;
  G:=ZeroMatrix(S,d,d);
  for i in [1..d] do
    for j in [1..d] do
      G[i,j]:=ChangePrecision(G0[i,j],prec);
    end for;
  end for;
  delta0:=0;
  Q:=IdentityMatrix(S,d);
  Q2:=IdentityMatrix(S,d);
  slopes:=[];
  dims:=[];
  mus:=[];
  H:=G;
  while d gt delta0 do
    H:=Submatrix(H,delta0+1,delta0+1,d-delta0,d-delta0);
    x ,couple,n,L,mu:=Cyclicvector_0(H,r,b,si,FrobS1,FrobMatS1);
    S:=ChangeRing(S,L);
    H:=ChangeRing(H,S);
    G:=ChangeRing(G,S);
    list,mat,vec:=Relations(H,r,b,FrobS1,FrobMatS1,x);
    j:=1;
    while vec[j,1] eq S!0 do
      j:=j+1;
      x:=u^(-list[j-1])*H*FrobMatS1(x);
    end while;
    M:=Iteratex(H,x,S,FrobS1,FrobMatS1);
    T,Tinv,P:= _SmithOverS1(M,1+Ceiling((b+2)*r/(b-1)));
    i:=1;
    while (i le d-delta0) and (Valuation(P[i,i]) le r/(b-1)) do
      i:=i+1;
    end while;
    i:=i-1;
    Q0:=ZeroMatrix(S,d,d);
    Q1:=ZeroMatrix(S,d,d);
    InsertBlock(~Q0,IdentityMatrix(S,delta0),1,1);
    InsertBlock(~Q1,IdentityMatrix(S,delta0),1,1);
    InsertBlock(~Q0,T,delta0+1,delta0+1);
    InsertBlock(~Q1,Tinv,delta0+1,delta0+1);
    delta0:=delta0+i;
    Q:=Q0*Q;
    Q2:=Q2*Q1;
    H:=MatrixMod(Q*G*FrobMatS1(Q2), Floor(b*r/(b-1))+1 );
    Append(~slopes,couple);
    Append(~dims,i);
    mus:=[L|mus[i] : i in [1..mus]];
    Append(~mus,L!mu);
  end while;
  L0:=GF(Characteristic(S),Degree(L));
  Embed(L,L0);
  mus:=[L0|mus[i] : i in [1..mus]];
  S0:=ChangeRing(S,L0);
return ChangeRing(H,S0),ChangeRing(MatrixMod(Q,Floor(b*r/(b-1))+1 ),S0),slopes,dims, mus, L0;
end function;

SemisimpleDecomposition_step:= function(D)
  if D`Frobenius[1] eq 0 then
    return SemisimpleDecomposition_0(D);
  end if;
  G0:=D`Phi;
  r:=D`r;
  si:=D`Frobenius[1];
  b:=D`Frobenius[2];
  S1:=CoefficientRing(G0);
  d:=Ncols(G0);
  prec:=RequestedPrecision(D);
  S<u>:=ChangePrecision(S1,prec);
  k:=CoefficientRing(S);
  FrobS1:=function(x)
    return _FrobS1(x,b,si);
  end function;
  FrobMatS1:=function(M)
    return _FrobS1Mat(M,b,si);
  end function;
  G:=ZeroMatrix(S,d,d);
  for i in [1..d] do
    for j in [1..d] do
      G[i,j]:=ChangePrecision(G0[i,j],prec);
    end for;
  end for;
  delta0:=0;
  Q:=IdentityMatrix(S,d);
  Q2:=IdentityMatrix(S,d);
  slopes:=[];
  dims:=[];
  pols:=[PolynomialRing(k)|];
  H:=G;
  while d gt delta0 do
    H:=Submatrix(H,delta0+1,delta0+1,d-delta0,d-delta0);
    x,couple,n,pol:=Cyclicvector(H,r,b,si,FrobS1,FrobMatS1);
    list,mat,vec:=Relations(H,r,b,FrobS1,FrobMatS1,x);
    j:=1;
    while vec[j,1] eq S!0 do
      j:=j+1;
      x:=u^(-list[j-1])*H*FrobMatS1(x);
    end while;
    M:=Iteratex(H,x,S,FrobS1,FrobMatS1);
    T,Tinv,P:= _SmithOverS1(M,1+Ceiling((b+2)*r/(b-1)));
    i:=1;
    while (i le d-delta0) and (Valuation(P[i,i]) le r/(b-1)) do
      i:=i+1;
    end while;
    i:=i-1;
    Q0:=ZeroMatrix(S,d,d);
    Q1:=ZeroMatrix(S,d,d);
    InsertBlock(~Q0,IdentityMatrix(S,delta0),1,1);
    InsertBlock(~Q1,IdentityMatrix(S,delta0),1,1);
    InsertBlock(~Q0,T,delta0+1,delta0+1);
    InsertBlock(~Q1,Tinv,delta0+1,delta0+1);
    delta0:=delta0+i;
    Q:=Q0*Q;
    Q2:=Q2*Q1;
    H:=MatrixMod(Q*G*FrobMatS1(Q2), Floor(b*r/(b-1))+1 );
    Append(~slopes,couple);
    d2:=couple[1];
    Append(~dims,i);
    Append(~pols,Norm(SkewPolynomialRing(k,d2*si)!pol));
  end while;
return H,MatrixMod(Q,Floor(b*r/(b-1))+1 ),slopes,dims,pols;
end function;

intrinsic SemisimpleDecomposition(D::PhiMod) -> AlgMatElt,AlgMatElt,SeqEnum, SeqEnum
  {Return a Jordan-Holder decomposition of a phi-module D. The result is given as:
- the matrix of the Frobenius in a basis corresponding to a Jordan-Holder sequence
- the matrix of the new basis
- the list of slopes of the phi-module
- the list of dimensions of the Jordan-Holder blocks
- the list of polynomials describing (together with the slopes) the composition factors}
  H,P:=SemisimpleDecomposition_step(D);
  Phi1:=PhiModule(H:F:=D`Frobenius);
  H1,P1,slopes,dims,pols := SemisimpleDecomposition_step(Phi1);
  return H1, P*P1,slopes,dims,pols;
end intrinsic;

SemiSimplify:=function(Phi)
  H,Q,slopes,dims:=SemisimpleDecomposition(Phi);
  nbfac:=#dims;
  d:=0;
  facts:=[];
  for i in [1..nbfac] do
    M:=Submatrix(H,d+1,d+1,dims[i],dims[i]);
	Append(~facts,[M]);
	d:=d+dims[i];
  end for;
  return facts;
end function;


intrinsic Slopes(D::PhiMod) -> SeqEnum
  {Return the slopes of a phi-module}
  H,Q,slopes,dims:=SemisimpleDecomposition(D);
  b:=D`Frobenius[2];
  newslopes:=[];
  for sl in slopes do
    d:=sl[1];
	s:=sl[2];
	if s ne 0 then
	  while (s mod b) eq 0 do
	    s:= s div b;
	  end while;
	end if;
	Append(~newslopes, [d,s]);
	end for;
  return Reverse(newslopes);
end intrinsic;

//Quotient:= function(PhiMod)
//return _;
//end function;

//Intersection:= funtion(PhiMod)
//  return _;
//end function;

//Induction:= funtion(PhiMod)
//  return _;
//end function;

//Restriction:= funtion(PhiMod)
//  return _;
//end function;
