freeze;

/*
**********************************************************************
 *    ClassicalSylow.m :  ClassicalSylow package - construction code
 *
 *    File      : ClassicalSylow.m
 *    Author    : Mark Stather
 *    Date : 19/12/05
 *
 ********************************************************************
 *	This package will construct and conjugate Sylow subgroups of the
 * classical groups and compute a PC presentaion of a given Sylow p-subgroup.
 * We are also able to compute the normalisers in the GL,Sp,GO,GO+,GO-,GU cases.
 * Changed by Derek Holt, 6/10/09 to eliminate second parameter. It is computed
 * from G by the function ClassicalType.
 * We change the inconsistently named function SylowConjClassical
 * to ClassicalSylowConjugation
 * We also eliminate the final parameter, specifying the prime,
 * from all functions except for ClassicalSylow
Eg.
  G:=GOPlus(8,17);
  P:=ClassicalSylow(G,3);
  S:=P^Random(G);
  g:=SylowConjClassical(G,P,S,3);
  Pc,PtoPc,PctoP:=ClassicalSylowToPC(P,"GO+",3);
  N:=ClassicalSylowNormaliser(G,P); 
*/

ClassicalType := function(G)
/* G should be a classical group in its natural representation and one of:
 * GL, SL, Sp, GO, GO+, GO-, SO, SO+, SO-, Omega, Omega+, Omega-, GU, SU
 * Identify which and return appropriate string
 */
  local cfs, q, gens, type, x, w, S, rq, form;
  if not IsAbsolutelyIrreducible(G) then
     error "G is not absolutely irreducible";
  end if;
  if not RecognizeClassical(G:NumberOfElements:=100) then
     error "G is not a classical group in its natural representation";
  end if;
  cfs := ClassicalForms(G);
  type := cfs`formType;
  if Dimension(G) eq 2 and type eq "symplectic" then //don't want symplectic
       type := "linear";
  end if;
  q := #BaseRing(G);
  gens := Generators(G);
  if type eq "linear" then
    if forall{g : g in gens | Determinant(g) eq 1 } then
      return "SL";
    else A<x> := AbelianGroup([q-1]);
      w := PrimitiveElement(GF(q));
      S := sub< A | [ Log(w, Determinant(g)) * x : g in gens ] >;
      if S eq A then
        return "GL";
      else error "In linear case, input group must be SL or GL";
      end if;
    end if;
  elif type eq "unitary" then
    if forall{g : g in gens | Determinant(g) eq 1 } then
      return "SU";
    else _, rq := IsSquare(q);
      A<x> := AbelianGroup([rq+1]);
      w := PrimitiveElement(GF(q));
      assert forall{g : g in gens | Log(w, Determinant(g)) mod (rq-1) eq 0 };
      S := sub< A | [ (Log(w, Determinant(g)) div (rq-1)) * x : g in gens ] >;
      if S eq A then
        return "GU";
      else error "In unitary case, input group must be SU or GU";
      end if;
    end if;
  elif type eq "symplectic" then
    return "Sp";
  elif type eq "orthogonalcircle" then
    if forall{g : g in gens | SpinorNorm(g, cfs`bilinearForm) eq 0 } then
       return "Omega";
    else return "SO";
    end if;
  elif type eq "orthogonalplus" then
    if forall{g : g in gens | SpinorNorm(g, cfs`bilinearForm) eq 0 } then
       return "Omega+";
    elif forall{g : g in gens | Determinant(g) eq 1 } then
       return "SO+";
    else return "GO+";
    end if;
  elif type eq "orthogonalminus" then
    if forall{g : g in gens | SpinorNorm(g, cfs`bilinearForm) eq 0 } then
       return "Omega-";
    elif forall{g : g in gens | Determinant(g) eq 1 } then
       return "SO-";
    else return "GO-";
    end if;
  end if;
end function;
import "../Forms/form.m" : ClassicalForms_QuadraticForm2;

UT := function(mat)
    n:=Nrows(mat); assert n eq Ncols(mat);
    K:=BaseRing(mat);
    nmat := MatrixAlgebra(K,n)!mat;
    for i in [2..n] do for j in [1..i-1] do
       nmat[j][i] +:=  nmat[i][j];  nmat[i][j]:=0;
    end for; end for;
    return nmat;
end function;


function pPart(n,p)
// returns k st n=p^k.m with HCF(m,p) eq 1
  return Valuation(n,p);
end function;

EmbedMat := function(m,k,q,n)
//Construct and return  image of m in GL(k,q^n) under embedding
// GL(k,q^n) ->  GL(nk,q)
  if Type(m) eq FldFinElt then
    m:=GL(k,q^n)![m];
  end if;
  im:=MatrixAlgebra(GF(q),n*k)!0;
  F:=GF(q^n);
  B:=Basis(F,GF(q));
  V,v:=VectorSpace(F,GF(q));
  for r in [1..k] do for c in [1..k] do
    //find image of x in GF(q^n) in GF(n,q)
       M:=[];
      for i in [1..#B] do
        M:=M cat Eltseq(v(m[r][c]*B[i]));
      end for;
      M:=MatrixAlgebra(GF(q),n)!M;
      InsertBlock(~im,M,n*(r-1)+1,n*(c-1)+1);
  end for; end for;
  return GL(n*k,q)!im;
end function;

QuadraticToBilinear:=function(J)
  n:=NumberOfRows(J);
  q:=#CoefficientRing(J);
  I:=MatrixAlgebra(GF(q),n)!0;
  V:=VectorSpace(GF(q),n);
  for i in [1..n] do
    for j in [1..n] do
      x:=InnerProduct((V.i+V.j)*J,(V.i+V.j));
      y:=InnerProduct(V.i*J,V.i);
      z:=InnerProduct(V.j*J,V.j);
      I[i][j]:=x-y-z;
    end for;
  end for;
  return I;
end function;
     
BilinearToQuadratic:=function(G,J)
  F:=CoefficientRing(J);
  if IsOdd(#F) then
     H := 0*J;
     for i in [1..NumberOfRows(J)] do
         H[i,i] := J[i,i]/2;
         for j in [i+1..NumberOfRows(J)] do
             H[i,j] := J[i,j];
         end for;
     end for;
     return H;
  end if;
  gens:=[G.i : i in [1..Ngens(G)] ];
  scalars:=[1 : i in [1..Ngens(G)] ];
  return ClassicalForms_QuadraticForm2(F,J,gens,scalars);
end function;

CyclicSylow:=function(type,n,q,r)
// Reurns a cyclic sylow subgroup along with its centraliser
// Uses Lemma 3.1 of M.I.M. AlAli 
  if type cmpeq "linear" then
    x:=GL(1,q^n)![PrimitiveElement(GF(q^n))];
    g:=EmbedMat(x,1,q,n);
    o:=pPart(q^n-1,r);
    h:=g^IntegerRing()!((q^n-1)/r^o);
    return sub<GL(n,q) | h>,sub<GL(n,q) | g>,MatrixAlgebra(GF(q),n)!0;
  elif type eq "symplectic" then
    m:=IntegerRing()!(n/2);
    I:=GL(2,q^m)![0,1,-1,0];
    x:=GL(1,q^n)![(PrimitiveElement(GF(q^n)))^(q^m-1)];
    x:=EmbedMat(x,1,q^m,2);
    L:=GF(q^m); K:=GF(q);
    V:=VectorSpace(L,2); W:=VectorSpace(K,n);
    B:=Basis(L,K);
    phi:=function(w)
      v1:=L!0; v2:=L!0;
      for i in [1..m] do
        v1:=v1+w[i]*B[i];
      end for;
      for i in [1..m] do
        v2:=v2+w[m+i]*B[i];
      end for;
      return V![v1,v2];
    end function;
    J:=MatrixAlgebra(K,n)!0;
    for i in [1..n] do
      for j in [1..n] do
        J[i][j]:=Trace(InnerProduct(phi(W.i)*I,phi(W.j)),K);
      end for;
    end for;
    g:=EmbedMat(x,2,q,m);
    o:=pPart(q^m+1,r);
    h:=g^IntegerRing()!((q^m+1)/r^o);
    return sub<GL(n,q) | h>,sub<GL(n,q) | g>,J;
  elif type cmpeq "orth-" and IsEven(q) then
    m:=IntegerRing()!(n/2);
    X:=GOMinus(2,q^m);
    flag,tp,I:=OrthogonalForm(X);
    I:=BilinearToQuadratic(X,I);
    x:=X.2;
    L:=GF(q^m); K:=GF(q);
    V:=VectorSpace(L,2); W:=VectorSpace(K,n);
    B:=Basis(L,K);
    phi:=function(w)
      v1:=L!0; v2:=L!0;
      for i in [1..m] do
        v1:=v1+w[i]*B[i];
      end for;
      for i in [1..m] do
        v2:=v2+w[m+i]*B[i];
      end for;
      return V![v1,v2];
    end function;
    E:=[];
    for i in [1..n] do
      for j in [i..n] do
        if i eq j then
          Append(~E,W.i);
        else
          Append(~E,W.i+W.j);
        end if;
      end for;
    end for;
    M:=[]; w:=[];
    for k in [1..#E] do
      v:=Coordinates(W,E[k]);
      for i in [1..n] do
        for j in [i..n] do
          M:=M cat [v[i]*v[j]];
        end for;
      end for;
      w:=w cat [Trace(InnerProduct(phi(E[k])*I,phi(E[k])),K)];
    end for;
    M:=Matrix(K,#E,#E,M);
    w:=VectorSpace(K,#E)!w;
    s:=Solution(Transpose(M),w);
    count:=1; J:=MatrixAlgebra(K,n)!0;
    for i in [1..n] do
      for j in [i..n] do
        J[i][j]:=s[count];
        count:=count+1;
      end for;
    end for;
    g:=EmbedMat(x,2,q,m);        
    o:=pPart(q^m+1,r);
    h:=g^IntegerRing()!((q^m+1)/r^o);
    return sub<GL(n,q) | h>,sub<GL(n,q) | g>,J;
  elif type cmpeq "unitary" then
// Can't make lemma 3.1 work.  
// Am using Kantor - Sylow's thm in poly time Prop 15.2
    x:=GL(1,q^n)![PrimitiveElement(GF(q^n))];
    x:=EmbedMat(x,1,q,n);
    p:=IntegerRing()!(q^(n/2));
    x:=x^(p-1);
    E:=MatrixRing<GF(q),n | x>;
    B:=Basis(E);
    J:=E!0;
    for i in [1..n] do
      for j in [1..n] do
        J[i][j]:=Trace(B[i]*(B[j]^(p)));
      end for;
    end for;
    o:=pPart(p+1,r);
    g:=x^IntegerRing()!((p+1)/r^o);
    return sub<GL(n,q) | g>,sub<GL(n,q) | x>,J;
  elif type cmpeq "orth-" and IsOdd(q) then
    x:=GL(1,q^n)![PrimitiveElement(GF(q^n))];
    x:=EmbedMat(x,1,q,n);
    p:=IntegerRing()!(q^(n/2));
    x:=x^(p-1);
    E:=MatrixRing<GF(q),n | x>;
    B:=Basis(E);
    J:=E!0;
    for i in [1..n] do
      for j in [1..n] do
        J[i][j]:=Trace(B[i]*(B[j]^(p))+(B[i]^p)*B[j]);
      end for;
    end for;
    o:=pPart(p+1,r);
    g:=x^IntegerRing()!((p+1)/r^o);
    return sub<GL(n,q) | g>,sub<GL(n,q) | x>,J;
  end if;
  error "Error in Classical type";
end function;     

StandardForm:=function(type,n,q)
//  returns "my" standard forms
  if n eq 0 then return ZeroMatrix(GF(q),0,0); end if;
  if type cmpeq "linear" then
    return MatrixAlgebra(GF(q),n)!0;
  elif type cmpeq "symplectic" then
    m:=IntegerRing()!(n/2);
    A:=MatrixAlgebra(GF(q),m);
    J:=VerticalJoin(HorizontalJoin(A!0,A!1),HorizontalJoin(-A!1,A!0));
  elif type cmpeq "orth+" and IsOdd(q) then
    m:=IntegerRing()!(n/2);
    A:=MatrixAlgebra(GF(q),m);
    J:=VerticalJoin(HorizontalJoin(A!0,A!1),HorizontalJoin(A!1,A!0));
  elif type cmpeq "orth-" and IsOdd(q) then
    m:=IntegerRing()!((n-2)/2);
    A:=MatrixAlgebra(GF(q),m);
    J1:=VerticalJoin(HorizontalJoin(A!0,A!1),HorizontalJoin(A!1,A!0));
    k:=PrimitiveElement(GF(q));
    J2:=Matrix(GF(q),2,2,[1,0,0,-k]);
    J:=DiagonalJoin(J1,J2);
  elif type cmpeq "orth" then
    m:=IntegerRing()!((n-1)/2);
    A:=MatrixAlgebra(GF(q),m);
    J1:=VerticalJoin(HorizontalJoin(A!0,A!1),HorizontalJoin(A!1,A!0));
    k:=PrimitiveElement(GF(q));
    J2:=Matrix(GF(q),1,1,[1]);
    J:=DiagonalJoin(J1,J2);
  elif type cmpeq "orth+" and IsEven(q) then
    m:=n div 2;
    A:=MatrixAlgebra(GF(q),m);
    J:=VerticalJoin(HorizontalJoin(A!0,A!1),HorizontalJoin(A!0,A!0));
  elif type cmpeq "orth-" and IsEven(q) then
    _,J:=QuadraticForm(GOMinus(n,q));
  elif type cmpeq "unitary" then
    J:=GL(n,q)!1;
  end if;
  return J;
end function;

sigma:=function(x)
// Applies the field auto to the matrix x or module x or vector x
  if Type(x) eq ModGrp then
     G := Group(x);
     q:=#CoefficientRing(G);
     return GModule(G,[ $$(m): m in [ActionGenerator(x,i): i in [1..Ngens(G)]]]);
  end if;
  if Type(x) eq ModGrpElt or Type(x) eq ModTupFldElt then
    q:=#CoefficientRing(x);
    P:=Parent(x);
    v:=Eltseq(x);
    p:=Truncate(SquareRoot(q));
    return P![v[i]^p : i in [1..#v] ];
  end if;
  F:=CoefficientRing(x);
  if Type(CoefficientRing(x)) eq FldFunRat then
    q:=#CoefficientRing(CoefficientRing(x));
  else
    q:=#CoefficientRing(x);
  end if;
  n:=NumberOfRows(x);
  im:=ZeroMatrix(F,n,n);
  p:=Truncate(SquareRoot(q));
  for i in [1..n] do
    for j in [1..n] do
      im[i][j]:=x[i][j]^p;
    end for;
  end for;
  return GL(n,F)!im;
end function;

import "../Forms/form.m" : ClassicalForms_Signum, ClassicalForms_Signum2;

function ClassicalGroup(type,Phi)
// Returns a classical group satisfying form Phi
  n:=NumberOfRows(Phi); q:=#CoefficientRing(Phi);
  if type eq "linear" then T:=GL(n,q); return [T.i : i in [1..Ngens(T)] ]; 
  elif type eq "symplectic" then
    T:=Sp(n,q);
    _,Psi:=SymplecticForm(T);
  elif type in {"orth","orth+","orth-"} then
    if n eq 1 then return [GL(1,q)![-1]]; end if;
    if IsOdd(n) then ftype:=0;
    elif IsOdd(q) then
      ftype:=ClassicalForms_Signum(GF(q),Phi);
    elif IsEven(q) then
      ftype:=ClassicalForms_Signum2(GF(q),QuadraticToBilinear(Phi), Phi);
    end if;
    if ftype eq 0 then ftype:="orth";
      T:=GO(n,q);
    elif ftype eq 1 then ftype:="orth+";
      T:=GOPlus(n,q);
    elif ftype eq -1 then ftype:="orth-";
      T:=GOMinus(n,q);
    end if;
    //Derek Holt correction for small OPlus
    if n eq 2 and q le 3 and ftype eq "orth+" then
      Psi := MatrixAlgebra(GF(q),2)![0,1,1,0];
    else _,_,Psi:=OrthogonalForm(T);
    end if;
    if IsEven(q) then Psi:=BilinearToQuadratic(T,Psi); end if;
    type:=ftype;
  elif type eq "unitary" then
    _,p:=IsSquare(q);
    T:=GU(n,p);  
    _,Psi:=UnitaryForm(T);
  end if;
  m1:=CorrectForm(Psi,n,q,type); m2:=CorrectForm(Phi,n,q,type);
  T:=T^(m1*m2^-1);
  return [GL(n,q) | T.i : i in [1..Ngens(T)] ];
end function; 


function ClassicalSylow1(G,type,r,Psi)
  assert r ne 2;
  n:=Dimension(G); q:=#BaseRing(G);
  assert GCD(q,r) eq 1;
  if type eq "unitary" then
    flag,p:=IsSquare(q);
    if not flag then error "q is not a square in unitary type"; end if;
    d:=Order(Integers(r)!(q+r));
    e:=Order(Integers(r)!(p+r));
    n_0:=n div d;
    n_1:=n-n_0*d;
  else
    d:=Order(Integers(r)!(q+r));
    n_0:=n div d;
    n_1:=n-n_0*d;
  end if;
  if type eq "orth+" and IsEven(d) and n_1 eq 0 and IsOdd(n_0) then
    n_1:=d; n_0:=n_0-1;
  elif type eq "orth-" and IsEven(d) and n_1 eq 0 and IsEven(n_0) then
    n_1:=d; n_0:=n_0-1;
  end if;
  if n_0 eq 0 then return sub<GL(n,q) | >,G; end if;
  if type eq "linear" or (type eq "symplectic" and IsEven(d)) or (type eq "orth" and IsEven(d)) or (type eq "orth+" and IsEven(d)) or (type eq "orth-" and IsEven(d)) or (type eq "unitary" and e mod 4 eq 2) then
    if type notin {"orth","orth+"} then
      C,_,Phi_0:=CyclicSylow(type,d,q,r);   
    else
      C,_,Phi_0:=CyclicSylow("orth-",d,q,r);   
    end if;
    T_n0:=Sylow(Sym(n_0),r);
    R_1:=WreathProduct(C,T_n0);    
    Phi_0:=DiagonalJoin([Phi_0 : i in [1..n_0] ]);
  else
    n_0:=2*(n div (2*d)); n_1:=n-n_0*d;
/* dfh 24/10/07 derek Holt again
    if type eq "orth-" then
      n_1:=n_1+2;
    elif type eq "orth" then
      n_1:=n_1+1;
    end if;
*/
    if type eq "orth-" and n_1 eq 0 then
      n_1:=n_1+2;
    end if;

    m:=(n-n_1) div 2;
    if m le 0 then return sub<GL(n,q) | >,G; end if;
    P:=$$(GL(m,q),"linear",r,ZeroMatrix(GF(q),m,m));
    if type ne "unitary" then
      R_1:=sub<GL(2*m,q) | [GL(2*m,q)!DiagonalJoin(P.i,Transpose(P.i)^-1) : i in [1..Ngens(P)] ]>;
    else
      R_1:=sub<GL(2*m,q) | [GL(2*m,q)!DiagonalJoin(P.i,Transpose(sigma(P.i))^-1) : i in [1..Ngens(P)] ]>;
    end if;
    I:=IdentityMatrix(GF(q),m);  
    O:=ZeroMatrix(GF(q),m,m);
    if type eq "linear" then
      Phi_0:=ZeroMatrix(GF(q),2*m,2*m);
    elif type eq "symplectic" then
      Phi_0:=VerticalJoin(HorizontalJoin(O,I),HorizontalJoin(-I,O));
    elif type in {"orth","orth+","orth-"} then
      if IsOdd(q) then
        Phi_0:=VerticalJoin(HorizontalJoin(O,I),HorizontalJoin(I,O));
      else
        Phi_0:=VerticalJoin(HorizontalJoin(O,I),HorizontalJoin(O,O));
      end if;
    elif type eq "unitary" then
      Phi_0:=VerticalJoin(HorizontalJoin(O,I),HorizontalJoin(I,O));
    end if;
  end if;
  I:=IdentityMatrix(GF(q),n_1);
  if Dimension(R_1) ne n then
    alpha:=func<x | GL(n,q)!DiagonalJoin(x,I)>;
    P:=sub<GL(n,q) | {alpha(x) : x in Generators(R_1)}>;
  else
    P:=R_1;
  end if;
  if type eq "linear" then 
    return P;
  end if;
  if Dimension(R_1) ne n then
    if type notin {"orth+","orth-"} or IsOdd(d) then
      Phi_1:=StandardForm(type,n_1,q);
    elif type in {"orth+"} then
      if IsEven(n_0) then
        Phi_1:=StandardForm("orth+",n_1,q);
      else
        Phi_1:=StandardForm("orth-",n_1,q);
      end if;
    else
      if IsEven(n_0) then
        Phi_1:=StandardForm("orth-",n_1,q);
      else
        Phi_1:=StandardForm("orth+",n_1,q);
      end if;
    end if;
    Phi:=DiagonalJoin(Phi_0,Phi_1);
  else
    Phi:=Phi_0;
  end if;

  t:=CorrectForm(Phi,n,q,type)*CorrectForm(Psi,n,q,type)^-1;
  return P^t;
end function;

ClassicalSylow2Dim2:=function(type,q)
/* Returns Sylow 2 subgroups of classical groups of dimension 2
*/
  if type cmpeq "linear" then
    if q mod 4 eq 1 then
      o:=pPart(q-1,2);
      e:=(PrimitiveElement(GF(q)))^(IntegerRing()!((q-1)/2^o));
      S:=WreathProduct(sub<GL(1,q) | GL(1,q)![e]>,Sym(2));
    else
      o:=pPart(q^2-1,2);
      e:=(PrimitiveElement(GF(q^2)))^(IntegerRing()!((q^2-1)/2^o));
      X:=GL(2,q)![0,1,1,e+e^q];
      Y:=GL(2,q)![0,1,-1,0];
      S:=sub<GL(2,q) | X,Y>;
    end if;
    z:=PrimitiveElement(GF(q));
    Z:=sub<GL(2,q) | GL(2,q)![z,0,0,z]>;
    return S,MatrixAlgebra(GF(q),2)!0,Z;
  elif type cmpeq "symplectic" then
    if q mod 4 eq 1 then
      o:=pPart(q-1,2);
      e:=(PrimitiveElement(GF(q)))^(IntegerRing()!((q-1)/2^o));
      X:=GL(2,q)![e,0,0,e^-1];
      Y:=GL(2,q)![0,1,-1,0];
      S:=sub<GL(2,q) | X,Y>;
    else
      o:=pPart(q^2-1,2);
      e:=(PrimitiveElement(GF(q^2)))^(IntegerRing()!((q^2-1)/2^o));
      X:=GL(2,q)![0,1,1,e+e^q];
      Y:=GL(2,q)![0,1,-1,0];
      S:=sub<GL(2,q) | X^2,Y>;
    end if;
    J:=GL(2,q)![0,-1,1,0];
    Z:=sub<GL(2,q) | GL(2,q)![-1,0,0,-1]>;
    return S,J,Z;
  elif type cmpeq "unitary" then
    _,q:=IsSquare(q);
    if q mod 4 eq 3 then
      o:=pPart(q+1,2);
      e:=(PrimitiveElement(GF(q^2)))^(IntegerRing()!((q^2-1)/(2^o)));
      S:=WreathProduct(sub<GL(1,q^2) | GL(1,q^2)![e]>,Sym(2));
      J:=GL(2,q^2)!1;
    else
      o:=pPart(q^2-1,2);
      e:=(PrimitiveElement(GF(q^2)))^(IntegerRing()!((q^2-1)/2^o));
/*      gamma:=(e+e^-1)/2;
      delta:=(e-e^-1)/2;
      flag:=exists(A){<alpha,beta> : alpha,beta in GF(q) | alpha^2+beta^2 eq GF(q)!(gamma^2)};      
      alpha:=GF(q^2)!A[1]; beta:=GF(q^2)!A[2];
      X:=GL(2,q^2)![alpha+delta,beta,beta,-alpha+delta];
      Y:=GL(2,q^2)![0,-1,1,0];
*/
// Use my own ideas here
      X := GL(2,q^2)![e,0,0,-e^-1];
      Y := GL(2,q^2)![0,1,1,0];
      J := GL(2,q^2)![0,1,1,0];
      S:=sub<GL(2,q^2) | X,Y>;
    end if;
    z:=PrimitiveElement(GF(q^2))^(q-1);
    Z:=sub<GL(2,q^2) | GL(2,q^2)![z,0,0,z]>;
    return S,J,Z;
  elif type cmpeq "orth+" then
    if q mod 4 eq 1 then
      o:=pPart(q-1,2);
      e:=(PrimitiveElement(GF(q)))^(IntegerRing()!((q-1)/2^o));
      X:=GL(2,q)![e,0,0,e^-1];
      Y:=GL(2,q)![0,1,1,0];
      S:=sub<GL(2,q) | X,Y>;
      J:=StandardForm("orth+",2,q);
    else
      e:=-GF(q)!1;
      X:=sub<GL(1,q) | GL(1,q)![e]>;
      S:=DirectProduct(X,X);
      J:=GL(2,q)![1,0,0,-1];
    end if;
    Z:=sub<GL(2,q) | GL(2,q)![-1,0,0,-1]>;
    return S,J,Z;
  elif type cmpeq "orth-" then
    if q mod 4 eq 1 then
      e:=-GF(q)!1;
      X:=sub<GL(1,q) | GL(1,q)![e]>;
      S:=DirectProduct(X,X);
      J:=StandardForm("orth-",2,q);
    else
      epsilon:=PrimitiveElement(GF(q^2));
      a:=GF(q)!((epsilon+epsilon^q)/2);
      _,b := IsSquare(GF(q)!(epsilon*epsilon^q)-a^2);
      X:=GL(2,q)![a,b,-b,a]; X:=X^(q-1);
      o:=pPart(q+1,2);
      J:=GL(2,q)!1;
      X := X^((q+1) div 2^o);
      Y:=GL(2,q)![0,1,1,0];
      S:=sub<GL(2,q) | X,Y>;
    end if;
    Z:=sub<GL(2,q) | GL(2,q)![-1,0,0,-1]>;
    return S,J,Z;
  else
    error "Error in classical type";
  end if;
end function;

function ClassicalSylow2(G,type,Psi)
  n:=Dimension(G); q:=#BaseRing(G);
  assert IsOdd(q);
  if n eq 2 then
    W,Phi:=ClassicalSylow2Dim2(type,q);
    if type cmpeq "linear" then return W; end if;
    g:=CorrectForm(Phi,2,q,type)*CorrectForm(Psi,2,q,type)^-1;
    return W^g;
  end if;
  case type:
    when "linear":
      W:=ClassicalSylow2Dim2(type,q);
      m:=n div 2; T_m:=Sylow(Sym(m),2);
      R:=WreathProduct(W,T_m);
      if IsEven(n) then return R; end if;
      z:=PrimitiveElement(GF(q))^((q-1) div 2^pPart(q-1,2));
      alpha:=sub<GL(1,q) | GL(1,q)![z]>;
      R:=DirectProduct(alpha,R);
      return R;

    when "symplectic":
      W,Phi_0:=ClassicalSylow2Dim2(type,q);
      m:=n div 2; T_m:=Sylow(Sym(m),2);
      R:=WreathProduct(W,T_m);
      Phi:=DiagonalJoin([Phi_0 : i in [1..m] ]);
      t:=CorrectForm(Phi,n,q,type)*CorrectForm(Psi,n,q,type)^-1;
      return R^t;
 
    when "orth":
      if q mod 4 eq 1 then
        W,Phi_0:=ClassicalSylow2Dim2("orth+",q);
      else
        W,Phi_0:=ClassicalSylow2Dim2("orth-",q);
      end if;
      m:=(n-1) div 2; T_m:=Sylow(Sym(m),2);
      R:=WreathProduct(W,T_m);
      Phi:=DiagonalJoin([Phi_0 : i in [1..m] ]);
      alpha:=sub<GL(1,q) | GL(1,q)![-1]>;
      R:=DirectProduct(alpha,R);

      Phi:=DiagonalJoin(IdentityMatrix(GF(q),1),Phi);      
      t:=CorrectForm(Phi,n,q,type)*CorrectForm(Psi,n,q,type)^-1;
      return R^t;
 
    when "orth+":
      if n mod 4 eq 0 and q mod 4 eq 3 then
        W_0,Phi_0:=ClassicalSylow2Dim2("orth-",q);
        m:=n div 2;
      elif n mod 4 ne 0 and q mod 4 eq 3 then
        W_0,Phi_0:=ClassicalSylow2Dim2("orth-",q);
        W_1,Phi_1:=ClassicalSylow2Dim2("orth+",q);
        m:=(n div 2) - 1;
      else
        W_0,Phi_0:=ClassicalSylow2Dim2("orth+",q);
        m:=n div 2;
      end if;
      T_m:=Sylow(Sym(m),2);
      R:=WreathProduct(W_0,T_m);
      Phi:=DiagonalJoin([Phi_0 : i in [1..m] ]);
      if q mod 4 eq 3 and n mod 4 ne 0 then
        R:=DirectProduct(R,W_1);
        Phi:=DiagonalJoin(Phi,Phi_1);
      end if;
      t:=CorrectForm(Phi,n,q,type)*CorrectForm(Psi,n,q,type)^-1;
      return R^t;

    when "orth-":
      if n mod 4 ne 0 and q mod 4 eq 3 then
        W_0,Phi_0:=ClassicalSylow2Dim2("orth-",q);
        m:=n div 2;
      elif n mod 4 eq 0 and q mod 4 eq 3 then
        W_0,Phi_0:=ClassicalSylow2Dim2("orth-",q);
        W_1,Phi_1:=ClassicalSylow2Dim2("orth+",q);
        m:=(n div 2) - 1;
      else
        W_0,Phi_0:=ClassicalSylow2Dim2("orth+",q);
        m:=n div 2;
        W_1,Phi_1:=ClassicalSylow2Dim2("orth-",q);
        m:=(n div 2) - 1;
      end if;
      T_m:=Sylow(Sym(m),2);
      R:=WreathProduct(W_0,T_m);
      Phi:=DiagonalJoin([Phi_0 : i in [1..m] ]);
      if q mod 4 eq 3 and n mod 4 eq 0 or q mod 4 eq 1 then
        R:=DirectProduct(R,W_1);
        Phi:=DiagonalJoin(Phi,Phi_1);
      end if;
      t:=CorrectForm(Phi,n,q,type)*CorrectForm(Psi,n,q,type)^-1;
      return R^t;

    when "unitary":
      W_0,Phi_0:=ClassicalSylow2Dim2(type,q);
      m:=n div 2;
      T_m:=Sylow(Sym(m),2);
      R:=WreathProduct(W_0,T_m);
      Phi:=DiagonalJoin([Phi_0 : i in [1..m] ]);
      p:=Truncate(SquareRoot(q));
      if IsOdd(n) then
        z:=PrimitiveElement(GF(q))^((q-1) div (p+1));
        z1:=z^((p+1) div 2^pPart(p+1,2));
        alpha:=sub<GL(1,q) | GL(1,q)![z1]>;
        R:=DirectProduct(alpha,R);
        Phi:=DiagonalJoin(IdentityMatrix(GF(q),1),Phi);      
      end if;
      t:=CorrectForm(Phi,n,q,type)*CorrectForm(Psi,n,q,type)^-1;
      return R^t;
         
  end case;
end function;
        

function ClassicalSylow3(G,type,Psi)
// Returns a Sylow p subgroup of type where p = char (GF(q)) 
  n:=Dimension(G); q:=#BaseRing(G);
  if type cmpeq "linear" then
// return a sylow p subgroup of SL(n,q) 
    B:=Basis(GF(q));
    I:=GL(n,q)!1;
    gens:=[];
    for i in [1..n] do
      for j in [(i+1)..n] do
        for x in B do
          g:=InsertBlock(I,GL(1,q)![x],i,j);
          Append(~gens,GL(n,q)!g);
        end for;
      end for;
    end for;
    P:=sub<GL(n,q) | gens>;
// Now the normaliser
    z:=PrimitiveElement(GF(q));
    for i in [1..n] do
       Append(~gens,InsertBlock(I,GL(1,q)![z],i,i));
    end for;    
    N:=sub<GL(n,q) | gens>;
    return P,N;

  elif type cmpeq "symplectic" then
    n:=n div 2;
// returns a sylow p subgroup of Sp(2*n,q) 
    B:=Basis(GF(q));
    A:=MatrixAlgebra(GF(q),n);
    Phi:=VerticalJoin(HorizontalJoin(A!0,A!1),HorizontalJoin(-A!1,A!0));
    I:=GL(2*n,q)!1;
    gens:=[];
    for i in [1..n] do
      for x in B do
        for j in [(i+1)..n] do
          g1:=InsertBlock(I,GL(1,q)![x],i,j);
          g1:=InsertBlock(g1,GL(1,q)![-x],n+j,n+i);
          Append(~gens,GL(2*n,q)!g1);
          g2:=InsertBlock(I,GL(1,q)![x],i,n+j);
          g2:=InsertBlock(g2,GL(1,q)![x],j,n+i);
          Append(~gens,GL(2*n,q)!g2);
        end for;
        g4:=InsertBlock(I,GL(1,q)![x],i,n+i);
        Append(~gens,GL(2*n,q)!g4);
      end for;
    end for;
    P:=sub<GL(2*n,q) | gens>;
// Now the normaliser
    z:=PrimitiveElement(GF(q));
    X:=IdentityMatrix(GF(q),n);
    for i in [1..n] do
      temp1:=InsertBlock(I,GL(1,q)![z],i,i);
      temp2:=InsertBlock(temp1,GL(1,q)![z^-1],n+i,n+i);        
      Append(~gens,temp2);
    end for;
    N:=sub<GL(2*n,q) | gens>;
    t:=CorrectForm(Phi,2*n,q,type)*CorrectForm(Psi,2*n,q,type)^-1;
    return P^t,N^t;


 elif type cmpeq "orth" then
// Returns a sylow p subgroup of GO(2*n+1,q) 
    assert IsOdd(q);
    n:=(n-1) div 2;
    B:=Basis(GF(q));
    A:=MatrixAlgebra(GF(q),n);
    Phi:=VerticalJoin(HorizontalJoin(A!0,A!1),HorizontalJoin(A!1,A!0));
    Phi:=DiagonalJoin(GL(1,q)![2^-1],Phi);
    I:=GL(2*n+1,q)!1;
    gens:=[];
    for i in [1..n] do
      for x in B do
        for j in [(i+1)..n] do
          g1:=InsertBlock(I,GL(1,q)![x],i+1,j+1);
          g1:=InsertBlock(g1,GL(1,q)![-x],n+j+1,n+i+1);
          Append(~gens,GL(2*n+1,q)!g1);
          g2:=InsertBlock(I,GL(1,q)![x],i+1,n+j+1);
          g2:=InsertBlock(g2,GL(1,q)![-x],j+1,n+i+1);
          Append(~gens,GL(2*n+1,q)!g2);
        end for;
        g3:=InsertBlock(I,GL(1,q)![x],1,n+i+1);
        g3:=InsertBlock(g3,GL(1,q)![-2*x],i+1,1);
        g3:=InsertBlock(g3,GL(1,q)![-x^2],i+1,n+i+1);
        Append(~gens,GL(2*n+1,q)!g3);
      end for;
    end for;
    //forall{g : g in gens | g*Phi*Transpose(g) eq Phi};    
    P:=sub<GL(2*n+1,q) | gens>;
    g:=GL(2*n+1,q)!PermutationMatrix(GF(q),Sym(2*n+1)!(n+1,2*n+1));
// Now the normaliser
    Append(~gens,InsertBlock(I,GL(1,q)![-1],1,1));
    z:=PrimitiveElement(GF(q));
    for i in [1..n] do
      temp:=InsertBlock(I,GL(1,q)![z],i+1,i+1);
      temp:=InsertBlock(temp,GL(1,q)![z^-1],n+i+1,n+i+1);
      Append(~gens,GL(2*n+1,q)!temp);  
    end for;
    N:=sub<GL(2*n+1,q) | gens>;
    t:=CorrectForm(Phi,2*n+1,q,type)*CorrectForm(Psi,2*n+1,q,type)^-1;
    return P^t,N^t;

  elif type cmpeq "orth+" then
// returns a sylow p subgroup of GO+(2*n,q)
    n:=n div 2;
    B:=Basis(GF(q));
    A:=MatrixAlgebra(GF(q),n);
    if IsOdd(q) then
      Phi:=VerticalJoin(HorizontalJoin(A!0,A!1),HorizontalJoin(A!1,A!0));
    else
      Phi:=VerticalJoin(HorizontalJoin(A!0,A!1),HorizontalJoin(A!0,A!0));
    end if;    
    I:=GL(2*n,q)!1;
    gens:=[];
    for i in [1..n] do
      for x in B do
        for j in [(i+1)..n] do
          g1:=InsertBlock(I,GL(1,q)![x],i,j);
          g1:=InsertBlock(g1,GL(1,q)![-x],n+j,n+i);
          Append(~gens,GL(2*n,q)!g1);
          g2:=InsertBlock(I,GL(1,q)![x],i,n+j);
          g2:=InsertBlock(g2,GL(1,q)![-x],j,n+i);
          Append(~gens,GL(2*n,q)!g2);
        end for;
       end for;
    end for;
    
    P:=sub<GL(2*n,q) | gens>;
    g:=GL(2*n,q)!PermutationMatrix(GF(q),Sym(2*n)!(n,2*n));
    if IsEven(q) then
      P:=sub<GL(2*n,q) | Generators(P) join {GL(2*n,q)!g}>;
    end if;
// Now the normaliser
    z:=PrimitiveElement(GF(q));
    Append(~gens,g);
    for i in [1..n] do
      temp:=InsertBlock(I,GL(1,q)![z],i,i);
      temp:=InsertBlock(temp,GL(1,q)![z^-1],n+i,n+i);
      Append(~gens,GL(2*n,q)!temp);  
    end for;
    N:=sub<GL(2*n,q) | gens>;
    t:=CorrectForm(Phi,2*n,q,type)*CorrectForm(Psi,2*n,q,type)^-1;
    return P^t,N^t;


  elif type cmpeq "orth-" then
    n:=n div 2;
// Returns a sylow p subgroup of GO-(2*n,2^l) 
    B1:=Basis(GF(q)); 
    A:=MatrixAlgebra(GF(q^2),n);
    I:=GL(2*n,q^2)!1;
    gens:=[];
    B2:=Basis(GF(q^2));
    for x in B1 do
      for i in [1..(n-2)] do
        for j in [(i+1)..(n-1)] do
          g:=InsertBlock(I,GL(1,q^2)![x],i,j);
          g:=InsertBlock(g,GL(1,q^2)![-x],n+j,n+i);
          h:=InsertBlock(I,GL(1,q^2)![x],i,n+j);
          h:=InsertBlock(h,GL(1,q^2)![-x],j,n+i);
          gens:=gens cat [GL(2*n,q^2)!g,GL(2*n,q^2)!h];
        end for;
      end for;
    end for; 
    for x in B2 do
      for i in [1..(n-1)] do
        g:=InsertBlock(I,GL(1,q^2)![x],i,n);
        g:=InsertBlock(g,GL(1,q^2)![-x],2*n,n+i);
        h:=InsertBlock(I,GL(1,q^2)![x^q],i,2*n);
        h:=InsertBlock(h,GL(1,q^2)![-x^q],n,n+i);
        gens:=gens cat [GL(2*n,q^2)!(g*h)];
      end for;
    end for;
    if IsEven(q) then
      g:=PermutationMatrix(GF(q^2),Sym(2*n)!(n,2*n));
      Append(~gens,GL(2*n,q^2)!g);
    end if;
    P:=sub<GL(2*n,q^2) | gens>;   
    z:=PrimitiveElement(GF(q));
    for i in [1..(n-1)] do
      g:=InsertBlock(I,GL(1,q^2)![z],i,i);
      g:=InsertBlock(g,GL(1,q^2)![z^(-1)],n+i,n+i);
      Append(~gens,GL(2*n,q^2)!g);
    end for; 
    z:=PrimitiveElement(GF(q^2));
    g:=InsertBlock(I,GL(1,q^2)![z^(q-1)],n,n);
    g:=InsertBlock(g,GL(1,q^2)![z^((q*(q-1)))],2*n,2*n);
    Append(~gens,GL(2*n,q^2)!g);
    g:=PermutationMatrix(GF(q^2),Sym(2*n)!(n,2*n));
    Append(~gens,GL(2*n,q^2)!g);
    N:=sub<GL(2*n,q^2) | gens>;

    perm:=Sym(2*n)!([1..(n-1)] cat [2*n-1] cat [n..(2*n-2)] cat [2*n]);
    permmat:=GL(2*n,q^2)!PermutationMatrix(GF(q^2),perm);
    P:=P^permmat; N:=N^permmat;
    A1:=MatrixAlgebra(GF(q^2),n-1);
    if IsOdd(q) then
      Phi:=VerticalJoin(HorizontalJoin(A1!0,A1!1),HorizontalJoin(A1!1,A1!0));
      Phi:=DiagonalJoin(Phi,GL(2,q^2)![0,1,1,0]);
    else
      Phi:=VerticalJoin(HorizontalJoin(A1!0,A1!1),HorizontalJoin(A1!0,A1!0));
      Phi:=DiagonalJoin(Phi,Matrix(GF(q^2),2,2,[0,1,0,0]));
    end if;      
    alpha:=Generator(GF(q^2),GF(q));
    S0:=GL(2,q^2)![1,-alpha,1,-alpha^q];
    S:=DiagonalJoin(GL(2*n-2,q^2)!1,S0);    
    if IsOdd(q) then
      Phi:=Transpose(S)*Phi*S;
    else
      Phi:=UT(Transpose(S)*Phi*S);
    end if;
    
    P:=sub<GL(2*n,q) | [GL(2*n,q)!Transpose(S^-1*P.i*S) : i in [1..Ngens(P)] ]>;
    N:=sub<GL(2*n,q) | [GL(2*n,q)!Transpose(S^-1*N.i*S) : i in [1..Ngens(N)] ]>;
    Phi:=Matrix(GF(q),2*n,2*n,[GF(q)!Eltseq(Phi)[i] : i in [1..(2*n)^2] ]);
    t:=CorrectForm(Phi,2*n,q,type)*CorrectForm(Psi,2*n,q,type)^-1;
    return P^t,N^t;

  elif type cmpeq "unitary" then
    q:=IntegerRing()!(q^(1/2));
    B1:=Basis(GF(q^2));
    B2:=Basis(GF(q));
    gens:=[];
    A:=MatrixAlgebra(GF(q^2),n);
    Phi:=A!0; I:=A!1;
    if IsOdd(n) then
      for i in [1..n] do
        Phi[i][n-i+1]:=(-1)^(i+1);
      end for;
    else
      flag:=exists(epsilon){x : x in  GF(q^2) | x ne 0 and x+x^q eq 0};      
      for i in [1..n] do
        Phi[i][n-i+1]:=epsilon*(-1)^(i+1);
      end for;
    end if;
    if IsOdd(n) then 
       m:=Truncate(n/2)+1;
    else
       m:=Truncate(n/2);
    end if;
    for i in [1..(m-1)] do
      for j in [(i+1)..(n-i+1)] do
        if (IsOdd(n) and j ne m) or (IsEven(n) and i ne n-j+1) then
          for x in B1 do
            g:=InsertBlock(I,GL(1,q^2)![x],i,j);
            h:=InsertBlock(I,GL(1,q^2)![x^q*(-1)^(i+j+1)],n-j+1,n-i+1);
            if g*h ne A!1 then
              Append(~gens,g*h);
            end if;
          end for;
        elif IsOdd(n) then
          for x in B1 do
            flag:=exists(z){z : z in GF(q^2) | z+z^q eq (-1)^(m+1-i)*x^(q+1)};
            g1:=InsertBlock(I,GL(1,q^2)![x],i,m);
            g2:=InsertBlock(g1,GL(1,q^2)![(-1)^(m+1-i)*x^q],m,n-i+1);
            g3:=InsertBlock(g2,GL(1,q^2)![z],i,n-i+1);
            Append(~gens,GL(n,q^2)!g3);
          end for;
        else
          for x in B2 do
            g:=InsertBlock(I,GL(1,q^2)![x],i,j);
            Append(~gens,GL(n,q^2)!g);                 
          end for;
        end if;
      end for;
    end for;       
    if IsEven(n) then
      for x in B2 do
        g:=InsertBlock(I,GL(1,q^2)![x],m,n-m+1);
        Append(~gens,GL(n,q^2)!g);                 
      end for;
    end if;
    P:=sub<GL(n,q^2) | gens>;
    k:=PrimitiveElement(GF(q^2));
    for i in [1..Truncate(n/2)] do
      g:=InsertBlock(I,GL(1,q^2)![k],i,i);
      h:=InsertBlock(A!0,GL(1,q^2)![k^(-q)-1],n-i+1,n-i+1);
      gens:=gens cat [GL(n,q^2)!(g+h)];
    end for;
    if IsOdd(n) then
      flag:=exists(l){l : l in [2..q^2] | (k^l)^(q+1) eq 1};
      m:=(n div 2)+1;
      g:=InsertBlock(I,GL(1,q^2)![k^l],m,m);
      gens:=gens cat [GL(n,q^2)!g];
    end if;
    N:=sub<GL(n,q^2) | gens>;

    t:=CorrectForm(Phi,n,q^2,type)*CorrectForm(Psi,n,q^2,type)^-1;
    return P^t,N^t;
  end if;
end function;

SchreierGeneratorsIndex2 := function (G: Known := [])
   index := [1..Ngens (G)];
   M := [x : x in index | not (x in Known)];
   /* G.m is not in H */
   m := Minimum (M);
   g := G.m;
   S := [G.i : i in Known] cat [g * G.i * g^-1: i in Known]
        cat [g * G.i: i in M] cat [g * G.i^-1: i in M | i ne m];
   return S;
end function;

function SpinorNorm(g, form)
    d:= NumberOfRows(g);
    q:= #BaseRing(g);

    m:= MatrixAlgebra(GF(q), d);
    i:= Identity(m);

    //test from Dye paper.
    if IsEven(q) then
      r:= Rank(g - i);
      return IsEven(r) select 0 else 1;
    end if;

    assert IsOdd(q);
    a:= g + i;
    cp<x>:= CharacteristicPolynomial(a: Proof:= false);

 //find the highest power of x that divides the CP. the nullspace of a to that power is the space //M(-1, \sigma) in the Zassenhaus paper
    exponent:= 0;
    while Coefficient(cp, exponent) eq 0 do
      exponent:= exponent+1;
    end while;

    if exponent gt 0 then
      cp:= ExactQuotient(cp, x^exponent);
      ns1:= Nullspace(a^exponent);
      basis1:= Basis(ns1);
      b1:= #basis1;

    //this should be the form restricted to the nullspace
      list:= &cat[[Matrix(basis1[i])*form*Transpose(Matrix(basis1
 [j])) : j in [1..b1]]: i in [1..b1]];
      newform:= MatrixAlgebra(GF(q), b1)![x[1][1]: x in list];
      det1:= Determinant(newform);
    else det1:= GF(q)!1;
    end if;

 //the nullspace of the remaining term in the CP is the space M^hat (-1, \sigma) in the Zassenhaus paper
    if Degree(cp) gt 0 then
      ns2:= Nullspace(Evaluate(cp, a));
// This methods seems to be faster
/*      ecp := Eltseq(cp);
      ns2 := ecp[1]*i; tmp := a;
        for j in [2..#ecp] do
        ns2 +:= ecp[j]*tmp;
        if j ne #ecp then tmp *:= a; end if;
      end for;
      ns2 := NullSpace(ns2); */
      basis2:= Basis(ns2);
      b2:= #basis2;
      newelt:= ScalarMatrix(d, GF(q)!2^(-1)) * a;

 //this should be the matrix of 1/2(1+a) restricted to the subspace.
      newmat:= MatrixAlgebra(GF(q), b2)!&cat[Coordinates(ns2, basis2[i]
 *newelt) : i in [1..b2]];
      det2:= Determinant(newmat);
    else det2:= GF(q)!1;
    end if;

    return IsSquare(det1*det2) select 0 else 1;

end function;

function SpinorNormMap(G,P,type,Psi)
// Returns the kernel of the spinor norm map restricted to P
  KnownP:=[i : i in [1..Ngens(P)] | SpinorNorm(P.i,Psi) eq 0 ];
  KP:=sub<Generic(P) | SchreierGeneratorsIndex2(P : Known:=KnownP)>;
  return KP;
end function;

/*function SpinorNormMap(G,P,type,Psi)
// Returns the spinor norm map of G=GL(2m,2^e)
  n:=Dimension(G); q:=#BaseRing(G);
  if type eq "orth+" then
    K:=OmegaPlus(n,q);
  elif type eq "orth-" then
    K:=OmegaMinus(n,q);
  else
    K:=Omega(n,q);
  end if;
  _,_,Phi:=OrthogonalForm(K);
  if IsOdd(q) then
    CF_Psi:=CorrectForm(Psi,n,q,type);
    CF_Phi:=CorrectForm(Phi,n,q,type);
  else
    CF_Psi:=CorrectForm(BilinearToQuadratic(G,Psi),n,q,type);
    CF_Phi:=CorrectForm(BilinearToQuadratic(K,Phi),n,q,type);
  end if;
  K:=K^(CF_Phi*CF_Psi^-1);
  C:=CyclicGroup(2);
  ki:=function(g)
    j:=RelativeOrder(g,K);
    if j eq 1 then return C!1;
    else return C.1;
    end if;
  end function;  
  KnownP:=[i : i in [1..Ngens(P)] | IsId(ki(P.i)) ];
  KP:=sub<GL(n,q) | SchreierGeneratorsIndex2(P : Known:=KnownP)>;
  return KP;
end function;

function RelativeOrder(g,K)
  O:=[]; L:=[]; i:=1;
  repeat
    k:=Random(K);
    o:=Order(g*k);
    Append(~O,o);
    Append(~L,GCD(O));
    if L[i] eq 1 then return 1; end if;
    if i gt 20 and #Seqset([L[i-j] : j in [20..0 by -1] ]) eq 1 then return L[#L]; end if;
    i+:=1;
  until i eq 10000;
  error "Failure in Relative Order";
end function;


*/

KernelOfHomtoCyclic := function (G, E, phi)

   q := #BaseRing (G); 

//#E eq 1 case put in by dfh, 23/10/07
   image := #E eq 1 select [0: i in [1..Ngens (G)]]
    else  [IntegerRing()!(Eltseq(phi(G.i))[1]) : i in [1..Ngens(G)] ];
   e := #E;
   n, a := XGCD (image cat [e]);

   g := &*[G.i^a[i] : i in [1..Ngens (G)]];

   /* generators of kernel as normal subgroup */
   H := sub < G | [G.i * g^(-image[i] div n) : i in [1..Ngens(G)]]>;

   /* add in conjugates to generate kernel as subgroup */
   Kgens := {Generic(G) |  g^(e div n)} join  
               {H.i^(g^u) : i in [1..Ngens (H)], u in [0..e - 1]};
   return Kgens;

end function;

intrinsic ClassicalSylow(G::GrpMat,p::RngIntElt)->GrpMat
{ Computes a Sylow p subgroup of G where G is one of GL,SL,Sp,GO,SO,Omega,GO+,SO+,Omega+,GO-,SO-,Omega-,GU,SU in its natural representation. }
  require IsPrime(p) : "p is not prime";
  type := ClassicalType(G);
  n:=Dimension(G); q:=#BaseRing(G);  
// Check orders
  if type in {"SL","GL"} then type2:="linear";
  elif type in {"Sp"} then type2:="symplectic";
  elif type in {"SO","GO","Omega"} then type2:="orth";
  elif type in {"SO+","GO+","Omega+"} then type2:="orth+";
  elif type in {"SO-","GO-","Omega-"} then type2:="orth-";
  elif type in {"SU","GU"} then type2:="unitary";
  else type2:=type;
  end if;

  case type2:
    when "linear":
      Psi:=ZeroMatrix(GF(q),n,n);
    when "symplectic":
      flag,Psi:=SymplecticForm(G);
      if not flag then
        error "Error in computing symplectic form";
      end if;
    when "orth":
      flag,_,Psi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
    when "orth+":
      flag,_,Psi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
      if IsEven(q) then Psi:=BilinearToQuadratic(G,Psi); end if;
    when "orth-":
      flag,_,Psi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
      if IsEven(q) then Psi:=BilinearToQuadratic(G,Psi); end if;
    when "unitary":
      r:=Truncate(SquareRoot(q));
      flag,Psi:=UnitaryForm(G);
      if not flag then
        error "Error in computing unitaryform form";
      end if;
  end case;

  if IsDivisibleBy(q,p) then
    P:=ClassicalSylow3(G,type2,Psi);
  elif p eq 2 then
    P:=ClassicalSylow2(G,type2,Psi);
  else
//DFH - bypass orthogonal cases that are not working
if type2 in {"orth+", "orth-"} and IsEven(q) then
  return Sylow(G,p);
end if;
    P:=ClassicalSylow1(G,type2,p,Psi);
  end if;
  if IsDivisibleBy(q-1,p) and type in {"SL","SO","Omega","SO+","Omega+","SO-","Omega-","SU"} then
// Compute the intersection
    M,mu:=MultiplicativeGroup(GF(q));
    A,inc:=sub<M | {Determinant(g)@@mu : g in Generators(P)} >;
   det:=func<x | Determinant(x) @@ mu @@ inc>;
    Kgens := KernelOfHomtoCyclic(P,A,det);
    P := sub<GL(n,q) | Kgens>;
  end if; 
  if p eq 2 and type in {"Omega","Omega+","Omega-"} then
     P:=SpinorNormMap(G,P,type2,Psi);
  end if;
  return P;
end intrinsic;
