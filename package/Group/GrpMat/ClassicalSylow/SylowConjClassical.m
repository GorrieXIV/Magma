freeze;

/*
**********************************************************************
 *    SylowConjClassical.m :  ClassicalSylow package - conjugation code
 *
 *    File      : SylowConjClassical.m
 *    Author    : Mark Stather
 *    Date : 19/12/05
 *
 ********************************************************************
  *	This package will construct and conjugate Sylow subgroups of the classical groups and compute a PC presentaion of a given Sylow p-subgroup.  We are also able to compute the normalisers in the GL,Sp,GO,GO+,GO-,GU cases.
 * type and prime parameters eliminated by Derek Holt, 6/10/09
Eg.
  G:=GOPlus(8,17);
  P:=ClassicalSylow(G,"GO+",3);
  S:=P^Random(G);
  g:=SylowConjClassical(G,P,S,"GO+",3);
  Pc,PtoPc,PctoP:=ClassicalSylowToPC(P,"GO+",3);
  N:=elassicalSylowNormaliser(G,P,"orth+",3); 
*/

import "../Forms/form.m" : ClassicalForms_QuadraticForm2, ClassicalForms_Signum, ClassicalForms_Signum2, MatToQ;
import "ClassicalSylow.m" : ClassicalGroup, CyclicSylow, ClassicalSylow2Dim2, BilinearToQuadratic, QuadraticToBilinear, sigma, pPart, EmbedMat, StandardForm, SpinorNorm,UT;
import "Syl2Dim2.m" : Dim2ConjGL, Dim2ConjSp, Dim2ConjGOPlus, Dim2ConjGOMinus, Dim2ConjGU, Dim2ConjSU;
import "ClassicalSylow.m": ClassicalType;

forward SylowConjImprimitive, Sylow2Dim2Conj;

function IspGroup(G)
  repeat
    g:=Random(G);
  until not IsId(g); 
  f:=Factorization(Order(g));
  if #f gt 1 then return false,_; end if;
  p:=f[1][1];
  for i in [1..100] do
    g:=Random(G);
    if not IsId(g) then
      f:=Factorization(Order(g));
      if #f gt 1 then return false,_; end if;
      if f[1][1] ne p then return false,_; end if;
    end if;
  end for;
  return true,p;
end function;


function IsBlockDiagonal(x,d)
  n:=NumberOfRows(x); m:=n div d;
  for i in [1..m] do
    for j in [1..m] do
      if i ne j and not IsZero(ExtractBlock(x,(i-1)*d+1,(j-1)*d+1,d,d)) then
        return false;
      end if;
    end for;
  end for;
  return true;
end function;

IrredEltConj:=function(x,y,type,J)
// Finds g such that x^g eq y and g satisfies J
// Based on correspondance with Scott Murray
//  assert IsIrreducible(GModule([x]));
//  assert IsIrreducible(GModule([y]));
//x:Magma; y:Magma; type:Magma; J:Magma;
  q:=#CoefficientRing(x);
  if type in {"orth+","orth-","orth"} and IsEven(q) then
    QJ:=J;
    J:=QuadraticToBilinear(J);
  end if;
  n:=NumberOfRows(x);
//"Here",n,type;

  flag,g := IsSimilar(y,x);
  if not flag then return false,_; end if;
  g := GL(n,q)!g;

  A:=MatrixAlgebra(GF(q),n);
  S:=sub<A | A!x>;
//"Constructing centraliser";
  C := Centraliser(A,S);
//"Constructed centraliser";
// Find a normal basis for C
//"Finding normal basis";
  repeat
    repeat
      c:=Random(C);
    until not IsZero(c) and Order(c) eq q^n-1;
    cpwrs := [A!1];
    for i in [1..(n-1)] do
      Append(~cpwrs,cpwrs[i]*c);
    end for;
//"Computing COB matrix";
    mat := A!&cat[Coordinates(C,cpwrs[i]) : i in [1..n] ];
  until Determinant(mat) ne 0;
//"Found normal basis";

// Next bit is bug fix from Derek Holt. Mark seemed to forget the linear case
// had J = 0, which crashed when inverted below.
  if type eq "linear" then
    //need element of C with determinant equal to det(g)
    d := Determinant(c);
    pow := Log(d,Determinant(g));
    g := c^(-pow) * g;
    assert Determinant(g) eq 1;
    return true, g;
  end if;

  if type eq "unitary" then //brute force for moment
    fac := Factorisation(q);
    rq := fac[1][1]^(fac[1][2] div 2);
  end if;
/*
    d := Determinant(c);
    pow := Log(d,Determinant(g));
    g := c^(-pow) * g;
    assert Determinant(g) eq 1;
    d := c^Order(d);
    tJ := g * J * Transpose(MatToQ(g,rq));   
    e := 1;
    td := Transpose(MatToQ(d,rq));
    ct:=0;
    while tJ ne J do 
      ct +:=1;
      J := d * J * td;
    end while;
ct;
    return true, d^ct * g;
  end if;
*/
// end of Derek Holt's fix

  mat:=GL(n,q)!mat^-1;
  mc := MinimalPolynomial(c);
  E := ext<GF(q) | mc>;
  V := VectorSpace(GF(q),n);
  BE := Basis(E);
  CtoE := function(e)
   v := V!Coordinates(C,e);
   v := Eltseq(v*mat);
   return &+[BE[i]*v[i] : i in [1..n] ];
  end function;

  EtoC := func<z | &+[e[i]*c^(i-1) where e := Eltseq(z) : i in [1..n] ]>;  
  z := PrimitiveElement(E);
//unitary cases below by Derek Holt
  K := type eq "unitary" select sub<E | z^(rq^n + 1) > 
       else sub<E | z^(q^(n div 2)+1)>;    
  t:= type eq "unitary" select J*Transpose(MatToQ(g,rq))^-1*J^-1*g^-1
      else J*Transpose(g)^-1*J^-1*g^-1;
  t1 := K!CtoE(C!t);
 // Solve the norm equation
 //  h^(q^m+1) = t1

  U := PolynomialRing(K);
  repeat
   repeat
    delta := Random(K);
    poly := U.1^2+delta*U.1+U!t1; 
   until IsIrreducible(poly);
   flag,gamma := HasRoot(poly,E);
   e := n gt 1 select Eltseq(gamma) else [gamma];
   h := &+[cpwrs[i]*e[i] : i in [1..n] ];
  until Determinant(h) ne 0;
  if n eq 1 and IsOdd(q) and
 (h*g) * J * Transpose(MatToQ(h*g,rq)) *J^-1 eq -IdentityMatrix(GF(q),1) then
    //don't know why I need this!
    h *:= Matrix(GF(q),1,1,[z^((rq-1) div 2)])
                                   where z := PrimitiveElement(GF(q)); 
  end if;
//(h*g) * J * Transpose(MatToQ(h*g,rq)) *J^-1;
  return true,GL(n,q)!(h*g);
end function;


SylowConjCyclic:=function(P,Q,r,type,Psi)
  q:=#BaseRing(P); n:=Dimension(P);
  flag,x:=IsCyclic(P); 
  if not flag then error "P is not cyclic"; end if;
  flag,y:=IsCyclic(Q); 
// Using Bill Kantor's method to find x2 and y with x2 in P and x2 and y similar
  if IsSimilar(x,y) then
    x2 := x;
  else
    m := MinimalPolynomial(x);
    E := ext <GF(q) | m>;
    mm := MinimalPolynomial(y);
    flag,root := HasRoot(mm,E);
    //another Derek Holt fix - hope line below is right!
    e := E eq GF(q) select [root] else Eltseq(root);
    x2 := ZeroMatrix(GF(q),n,n);
    temp := IdentityMatrix(GF(q),n);
    for i in [1..#e] do
      x2 := x2 + e[i]*temp;
      temp := temp * x;
    end for;
    x2 := Generic(P)!x2;
  end if;
  flag,g:=IrredEltConj(x2,y,type,Psi);

/*if not flag then error "Q is not cyclic"; end if;
  S:={i : i in [1..Order(x)] | GCD(Order(x),i) eq 1};
  for i in S do
    if IsSimilar(x^i,y) then
      flag,g:=IrredEltConj(x^i,y,type,Psi);
      if flag eq true then
        break;
      end if;
    end if;
  end for;
*/
  return g;
end function;


function CorrectBlocks(E,r,type,Phi)
  M:=&+E;
  n:=Dimension(M); q:=#BaseRing(M);
  mat:=Matrix(&cat[[M!E[i].j : j in [1..Dimension(E[i])] ] : i in [1..#E] ]);
  if type eq "linear" then return GL(n,q)!(mat^-1); end if;

/*  dims:=Setseq({Dimension(E[i]) : i in [1..#E] });
  Sort(~dims);  

  FormCorrections:=[**];
  count:=1;
  for j in [1..#dims] do
    dim:=dims[j];
    form:=ExtractBlock(Phi,count,count,dim,dim);
    if type in {"orth","orth-","orth+"} and IsEven(q) then
      formsign:=ClassicalForms_Signum2(GF(q),QuadraticToBilinear(form),form);
      if formsign cmpeq [0] then 
        ftype:="orth";
      elif formsign cmpeq 1 then
        ftype:="orth+";
      else
        ftype:="orth-";
      end if;
    elif type in {"orth","orth-","orth+"} and IsOdd(q) then
      formsign:=ClassicalForms_Signum(GF(q),form);
      if formsign cmpeq [0] then 
        ftype:="orth";
      elif formsign cmpeq 1 then
        ftype:="orth+";
      else
        ftype:="orth-";
      end if;
    else
      ftype:=type;
    end if;
    Append(~FormCorrections,<dim,ftype,CorrectForm(form,dim,q,ftype)>);
    count+:=dim*#[i : i in E | Dimension(i) eq dim];
  end for;
*/
  if type eq "unitary" then  
    X:=mat*Phi*Transpose(sigma(mat));
  elif type in {"orth+","orth-","orth"} and IsEven(q) then
    X:=UT(mat*Phi*Transpose(mat));
  else
    X:=mat*Phi*Transpose(mat);
  end if;

  c:=ZeroMatrix(GF(q),n,n);
  count:=1;
  for i in [1..#E] do
    dim:=Dimension(E[i]);
    t:=ExtractBlock(X,count,count,dim,dim);
    form:=ExtractBlock(Phi,count,count,dim,dim);
    if type in {"orth","orth-","orth+"} and IsEven(q) then
      formsign:=ClassicalForms_Signum2(GF(q),QuadraticToBilinear(form),form);
      if formsign cmpeq [0] then 
        ftype:="orth";
      elif formsign cmpeq 1 then
        ftype:="orth+";
      else
        ftype:="orth-";
      end if;
    elif type in {"orth","orth-","orth+"} and IsOdd(q) then
      formsign:=ClassicalForms_Signum(GF(q),form);
      if formsign cmpeq [0] then 
        ftype:="orth";
      elif formsign cmpeq 1 then
        ftype:="orth+";
      else
        ftype:="orth-";
      end if;
    else
      ftype:=type;
    end if;    
    InsertBlock(~c,CorrectForm(form,dim,q,ftype)*CorrectForm(t,dim,q,ftype)^-1,count,count);
    count+:=dim;
  end for;
  mat:=GL(n,q)!(c*mat)^-1;

  return mat;
end function;
  

function SylowConjReducible(P,S,r,type,Phi)
  n:=Dimension(P); q:=#BaseRing(P);
  d:=Order(Integers(r)!(q+r));
  n_0:=n div d;
  Phi_0:=ExtractBlock(Phi,1,1,d,d);

  MP:=GModule(P); MS:=GModule(S);
  EP:=IndecomposableSummands(MP);
  ES:=IndecomposableSummands(MS);
  Sort(~EP,func<x,y | Dimension(x)-Dimension(y)>);
  Sort(~ES,func<x,y | Dimension(x)-Dimension(y)>);
  gp1:=CorrectBlocks(EP,r,type,Phi);
  gs1:=CorrectBlocks(ES,r,type,Phi);
  P:=P^gp1; S:=S^gs1;

  c:=IdentityMatrix(GF(q),n);
  count:=1;
  for i in [1..#EP] do
    dim:=Dimension(EP[i]);
    Pblock:=sub<GL(dim,q) | {ExtractBlock(g,count,count,dim,dim) : g in Generators(P)}>;
    Sblock:=sub<GL(dim,q) | {ExtractBlock(g,count,count,dim,dim) : g in Generators(S)}>;
    if dim eq d then
      if r eq 2 then
// Sylow 2 subgroup of dim 2
        if type notin {"orth+","orth","orth-"} then
          InsertBlock(~c,Sylow2Dim2Conj(Pblock,Sblock,type,Phi_0),count,count);
        else
          btype:=ClassicalForms_Signum(GF(q),Phi_0);
          if btype eq 1 then
            InsertBlock(~c,Sylow2Dim2Conj(Pblock,Sblock,"orth+",Phi_0),count,count);
          else
            InsertBlock(~c,Sylow2Dim2Conj(Pblock,Sblock,"orth-",Phi_0),count,count);
          end if;
        end if;
      else        
// Pblock & Sblock are cyclic
        if type notin {"orth+","orth-","orth"} then
          InsertBlock(~c,SylowConjCyclic(Pblock,Sblock,r,type,Phi_0),count,count);
        else
          InsertBlock(~c,SylowConjCyclic(Pblock,Sblock,r,"orth-",Phi_0),count,count);
        end if;
      end if;
    else
// Pblock & Sblock are imprimitive
      blockPhi:=DiagonalJoin([Phi_0 : i in [1..(dim div d)] ]);
      if type notin {"orth+","orth-","orth"} then
        InsertBlock(~c,SylowConjImprimitive(Pblock,Sblock,r,type,blockPhi),count,count);
      else
        if IsOdd(q) then
          btype:=ClassicalForms_Signum(GF(q),blockPhi);
        else
          //Derek Holt correction btype:=ClassicalForms_Signum(GF(q),blockPhi);
          btype :=
           ClassicalForms_Signum2(GF(q),QuadraticToBilinear(blockPhi),blockPhi);
        end if;
        if btype eq 1 then
          InsertBlock(~c,SylowConjImprimitive(Pblock,Sblock,r,"orth+",blockPhi),count,count);
          else
        InsertBlock(~c,SylowConjImprimitive(Pblock,Sblock,r,"orth-",blockPhi),count,count);
        end if;
      end if;
    end if;
    count+:=dim;
  end for;
  c:=GL(n,q)!c;

  return gp1*c*gs1^-1;
end function;
      

function ElementFromDerivedGroup(P,n)
// Returns a non-scalar elt from the n'th derived group of P
  elts:=[Random(P) : i in [1..2^(n-1)]];
  old:=elts[1];
  for i in [(n-1)..1 by -1] do
    old:=elts[1];
    elts:=[Generic(P) | (elts[j],elts[j+1]) : j in [1..#elts by 2] ];
  end for;
  if IsScalar(elts[1]) then e:=old; 
  else e:=elts[1];
  end if;
  return e;
end function;


function MyImprimitiveAction(P,r)
  n:=Dimension(P); q:=#BaseRing(P);
  A,ki:=AbsoluteRepresentation(P);
  nA:=Dimension(A); qA:=#BaseRing(A);
  d:=Order(Integers(r)!(r+q));
  k:=Valuation(q^d-1,r);
// amount of itteration in wreath product is given by
  wr:=Truncate(Log(r,nA));
  repeat
    relt:=ElementFromDerivedGroup(A,wr+1);
    //flag:=int_SearchForDecomposition(A,[relt] : Report:=false);
    flag:=SearchForDecomposition(A,[relt] : Report:=false);
    if flag then
      X:=BlocksImage(A);
    end if;
  until flag and Type(X) ne MonStgElt and Degree(X) eq Dimension(A);
  assert Degree(X) eq Dimension(A);
  BA:=Blocks(A);
  mat:=GL(nA,qA)!(Matrix(&cat[[BA[i].j : j in [1..Dimension(BA[i])] ] : i in [1..#BA] ])^-1);
  preims:=[GL(n,q) | EmbedMat(A.i,nA,q,d) : i in [1..Ngens(A)] ];
  _,t:=IsIsomorphic(GModule(preims),GModule(P));
  t:=GL(n,q)!t;
  VP:=VectorSpace(P);
  VA:=VectorSpace(A);
  _,alpha:=VectorSpace(GF(q^d),GF(q));
  phi:=map<VA->VP | x:->VP!&cat[Eltseq(alpha(x[i])) : i in [1..nA] ]>;
  BF:=Basis(GF(q^d),GF(q));
// Blocks for P
  BP:=[ sub<VP | [phi(BF[i]*BA[j].1)*t : i in [1..d] ]> : j in [1..#BA] ];
  theta:=func<g | ExtractBlock(g^mat,1,1,1,1)>;
  XtoA:=hom<X->A | [A.i : i in [1..Ngens(A)] ]>;
  XtoP:=hom<X->P | [P.i : i in [1..Ngens(P)] ]>;
  repeat
    g:=Random(P);
    kig:=GL(nA,qA)!ki(g);
    im:=ImprimitiveAction(A,kig);
    Aelt:=kig*XtoA(im)^-1;
  until Order(theta(Aelt)) eq r^k;
  g:=g*XtoP(im)^-1;
  gens:=[GL(n,q) | g];
  reps:=[GL(n,q) | GL(n,q)!1];
  for i in [2..Degree(X)] do
    _,t:=IsConjugate(X,1,i);
    Append(~reps,XtoP(t));
    Append(~gens,g^reps[i]);
  end for;
  K:=sub<GL(n,q) | gens>;
  M:=GModule(K);
  EP:=[sub<M | BP[i]> : i in [1..#BP] ];
  return func<g | ImprimitiveAction(A,GL(nA,qA)!ki(g))>,X,K,EP,reps;
end function;

function CorrectIteratedWreath(X)
// Corrects the iterated wreath product group X to a nice copy
  if IsCyclic(X) then
    _,t:=IsConjugate(Generic(X),X,CyclicGroup(#X));
    return t;
  end if;
  B:=MaximalPartition(X);
  
  rho,IX,KX:=BlocksAction(X,B);
// First correct the kernel
  n:=Degree(X); d:=#Rep(B); m:=n div d;
  B:=Setseq(B);
  g:=Sym(n)!&cat[Setseq(B[i]) : i in [1..#B] ];
  g:=g^-1;
  Y:=X^g; KY:=KX^g;
  newB:=[SetToIndexedSet({((i-1)*d+1)..i*d}) : i in [1..#B] ];
  kelt:=[];
  for i in [1..m] do
    A:=OrbitImage(KY,newB[i]);
    t:=CorrectIteratedWreath(A);
    t:=Eltseq(t);
    kelt:=kelt cat [t[j]+(i-1)*d : j in [1..#t] ];
  end for;
  kelt:=Sym(n)!kelt;

// Now match up the image
  Z:=Y^kelt;
  theta:=func<g | Sym(m)![((Rep(newB[i])^g)-1) div d + 1 : i in [1..#newB] ]>;
  _:=exists(z){z : z in Generators(Z) | Order(theta(z)) eq m};
  _,t:=IsConjugate(Sym(m),theta(z),CyclicGroup(m).1);
  t:=Eltseq(t);
  ielt:=[];
  for i in [1..m] do
    ielt:=ielt cat [(t[i]-1)*d + k : k in [1..d] ];
  end for;
  ielt:=Sym(n)!ielt;

  Z2:=Z^ielt;
  z:=z^ielt;
  
  trickelts:=[[] : i in [1..m] ];
  for i in [1..m] do
    for j in [1..d] do
      im:=((i-1)*d+j)^z mod d;
      if im eq 0 then im:=d;
      else im:=IntegerRing()!im;
      end if;
      Append(~trickelts[i],im);
    end for;
  end for;
  trickelts:=[Sym(d)!trickelts[i] : i in [1..m] ];

  trickelt:=[1..d];
  for i in [2..m] do
    im:=&*[trickelts[j] : j in [i..m] ];
    im:=Eltseq(im);
    trickelt:=trickelt cat [(i-1)*d+im[j] : j in [1..#im] ];
  end for;

  trickelt:=Sym(n)!trickelt;

  return g*kelt*ielt*trickelt;
end function;
      
function SylowConjImprimitive(P,S,r,type,Phi)
  n:=Dimension(P); q:=#BaseRing(P);
  d:=Order(Integers(r)!(q+r));
  n_0:=n div d;
  wr:=Truncate(Log(r,n_0));
  if type eq "unitary" then
    _,p:=IsSquare(q);
  end if;
  if type notin {"orth","orth-","orth+"} then
    Y,_,Psi_0:=CyclicSylow(type,d,q,r);
  else
    Y,_,Psi_0:=CyclicSylow("orth-",d,q,r);
  end if; 
  Phi_0:=ExtractBlock(Phi,1,1,d,d);
  if type ne "linear" then
      Phi:=DiagonalJoin([Phi_0 : i in [1..n_0] ]);
    if type ne "orth" then
      CFPsi_0:=CorrectForm(Psi_0,d,q,type);
      CFPhi_0:=CorrectForm(Phi_0,d,q,type);
    else
      CFPsi:=CorrectForm(Psi_0,d,q,"orth-");
      CFPhi:=CorrectForm(Phi_0,d,q,"orth-");
    end if;
    w:=CFPsi_0*CFPhi_0^-1;
    Y:=Y^w;
  else
    w:=GL(n,q)!1;
  end if;
  thetaP,XP,KP,EP,repsP:=MyImprimitiveAction(P,r);
  thetaS,XS,KS,ES,repsS:=MyImprimitiveAction(S,r);
  gp1:=CorrectBlocks(EP,r,type,Phi);
  gs1:=CorrectBlocks(ES,r,type,Phi);
  KP:=KP^gp1; KS:=KS^gs1;
  repsP:=[repsP[i]^gp1 : i in [1..#repsP] ];
  repsS:=[repsS[i]^gs1 : i in [1..#repsS] ];  

  I:=IdentityMatrix(GF(q),n);
  PBlock:=sub<GL(d,q) | {ExtractBlock(g,1,1,d,d) : g in Generators(KP)}>;
  SBlock:=sub<GL(d,q) | {ExtractBlock(g,1,1,d,d) : g in Generators(KS)}>;
  xp:=SylowConjCyclic(PBlock,Y,r,type,Phi_0);
  xs:=SylowConjCyclic(SBlock,Y,r,type,Phi_0);
  gp2:=IdentityMatrix(GF(q),n);
  gs2:=IdentityMatrix(GF(q),n);
  for i in [1..n_0] do
    x:=ExtractBlock(repsP[i]^-1,(i-1)*d+1,1,d,d)*xp;
    InsertBlock(~gp2,x,(i-1)*d+1,(i-1)*d+1);
    x:=ExtractBlock(repsS[i]^-1,(i-1)*d+1,1,d,d)*xs;
    InsertBlock(~gs2,x,(i-1)*d+1,(i-1)*d+1);
  end for;
  gp2:=GL(n,q)!gp2; gs2:=GL(n,q)!gs2;
  P:=P^(gp1*gp2); S:=S^(gs1*gs2);
  V:=VectorSpace(GF(q),n);
  Vsubs:=[sub<V | [V.((i-1)*d+j) : j in [1..d] ]> : i in [1..n_0] ];
  theta:=function(g)
    im:=[];
    for i in [1..n_0] do
      v:=Vsubs[i].1*g;
      _:=exists(j){j : j in [1..n_0] | v in Vsubs[j]};
      Append(~im,j);
    end for;
    return Sym(n_0)!im;
  end function;

  W:=WreathProduct([CyclicGroup(r) : i in [1..wr] ]);
  XP:=sub<Sym(r^wr) | [theta(P.i) : i in [1..Ngens(P)] ]>;
  XS:=sub<Sym(r^wr) | [theta(S.i) : i in [1..Ngens(S)] ]>;
  xp:=CorrectIteratedWreath(XP);
  xs:=CorrectIteratedWreath(XS);
  xpmat:=ZeroMatrix(GF(q),n,n); xsmat:=ZeroMatrix(GF(q),n,n);
  I:=IdentityMatrix(GF(q),d);
  xp:=Eltseq(xp); xs:=Eltseq(xs);
  for i in [1..n_0] do
    InsertBlock(~xpmat,I,(i-1)*d+1,(xp[i]-1)*d+1);
    InsertBlock(~xsmat,I,(i-1)*d+1,(xs[i]-1)*d+1);  
  end for;
  xpmat:=GL(n,q)!xpmat;
  xsmat:=GL(n,q)!xsmat;
  B:=Blocks(P);

  P:=P^xpmat; S:=S^xsmat;

  Wgens:=[W.i : i in [1..Ngens(W)]  | not IsId(W.i)];
  Sort(~Wgens,func<x,y | #Fix(y)-#Fix(x)>);

  trickP:=Id(P); trickS:=Id(S);
  I:=IdentityMatrix(GF(q),n);
  alphaP:=Homomorphism(W,GL(n,q),[theta(P.i) : i in [1..Ngens(P)] ],[P.i : i in [1..Ngens(P)] ]);
  alphaS:=Homomorphism(W,GL(n,q),[theta(S.i) : i in [1..Ngens(S)] ],[S.i : i in [1..Ngens(S)] ]);
  for i in [1..wr] do
    x:=alphaP(Wgens[i])^trickP;
    y:=alphaS(Wgens[i])^trickS;
    dim:=d*r^(i-1);
    Pblocks:=[MatrixAlgebra(GF(q),dim) | ];
    Sblocks:=[MatrixAlgebra(GF(q),dim) | ];
    Pblocks[r]:=ExtractBlock(x,dim*(r-1)+1,1,dim,dim);
    Sblocks[r]:=ExtractBlock(y,dim*(r-1)+1,1,dim,dim);
    for j in [(r-1)..2 by -1] do
      Pblocks[j]:=ExtractBlock(x,dim*(j-1)+1,dim*j+1,dim,dim)*Pblocks[j+1];
      Sblocks[j]:=ExtractBlock(y,dim*(j-1)+1,dim*j+1,dim,dim)*Sblocks[j+1];
    end for;
    Pblocks[1]:=IdentityMatrix(GF(q),dim);
    Sblocks[1]:=IdentityMatrix(GF(q),dim);
    trickP:=trickP*GL(n,q)!DiagonalJoin(DiagonalJoin(Pblocks),IdentityMatrix(GF(q),n-r*dim));    
    trickS:=trickS*GL(n,q)!DiagonalJoin(DiagonalJoin(Sblocks),IdentityMatrix(GF(q),n-r*dim));    
  end for;

  return gp1*gp2*xpmat*trickP*trickS^-1*xsmat^-1*gs2^-1*gs1^-1;

end function;
    

function SylowConjClassical1(G,P,S,type,r)
  assert r ne 2;
  n:=Dimension(G); q:=#BaseRing(G);
  assert GCD(q,r) eq 1;
  case type:
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
      if IsEven(q) then
        Psi:=BilinearToQuadratic(G,Psi);
      end if; 
    when "orth+":
      flag,_,Psi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
      if IsEven(q) then
        Psi:=BilinearToQuadratic(G,Psi);
      end if; 
    when "orth-":
      flag,_,Psi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
      if IsEven(q) then
        Psi:=BilinearToQuadratic(G,Psi);
      end if; 
    when "unitary":
      flag,p:=IsSquare(q);
      if not flag then error "q is not a square in unitary type"; end if;
      flag,Psi:=UnitaryForm(G);
      if not flag then
        error "Error in computing unitaryform form";
      end if;
  end case;
  if type eq "unitary" then
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
  if type eq "linear" or (type eq "symplectic" and IsEven(d)) or (type eq "orth" and IsEven(d)) or (type eq "orth+" and IsEven(d)) or (type eq "orth-" and IsEven(d)) or (type eq "unitary" and e mod 4 eq 2) then
// In Case A
   if type notin {"orth+","orth-"} then
      Phi_0:=StandardForm(type,n_1,q);
    elif type eq "orth+" then
      if IsOdd(n_0) then
        Phi_0:=StandardForm("orth-",n_1,q);
      else
        Phi_0:=StandardForm("orth+",n_1,q);
      end if;
    elif type eq "orth-" then
      if IsOdd(n_0) then
        Phi_0:=StandardForm("orth+",n_1,q);
      else
        Phi_0:=StandardForm("orth-",n_1,q);
      end if;
    end if;
    if type notin {"orth+","orth-","orth"} then
      blockPhi:=StandardForm(type,d,q);
    else
      blockPhi:=StandardForm("orth-",d,q);
    end if;
    Phi_1:=DiagonalJoin([blockPhi : i in [1..n_0] ]);
    Phi:=DiagonalJoin(Phi_0,Phi_1);
    if type ne "linear" then
      CFPsi:=CorrectForm(Psi,n,q,type);
      CFPhi:=CorrectForm(Phi,n,q,type);
      g1:=CFPsi*CFPhi^-1;
      P:=P^g1; S:=S^g1;
    else
      g1:=GL(n,q)!1;
    end if;
    MP:=GModule(P); MS:=GModule(S);
    FixP:=Fix(MP); FixS:=Fix(MS);
    if Dimension(FixP) ne 0 then
      _,EP:=IsDirectSummand(MP,FixP);
      _,ES:=IsDirectSummand(MS,FixS);  
      gp1:=CorrectBlocks([FixP,EP],r,type,Phi);
      gs1:=CorrectBlocks([FixS,ES],r,type,Phi);
      P:=P^gp1; S:=S^gs1;
    else
      EP:=MP; ES:=MS;
      gp1:=GL(n,q)!1; gs1:=GL(n,q)!1;
    end if;

    P1:=sub<GL(d*n_0,q) | {GL(d*n_0,q)!ExtractBlock(g,n_1+1,n_1+1,d*n_0,d*n_0) : g in Generators(P)}>;
    S1:=sub<GL(d*n_0,q) | {GL(d*n_0,q)!ExtractBlock(g,n_1+1,n_1+1,d*n_0,d*n_0) : g in Generators(S)}>;
    if type notin {"orth+","orth-","orth"} then
      type2:=type;
    else
      if IsEven(n_0) then
        type2:="orth+";
      else
        type2:="orth-";
      end if;
    end if;
    if n_0 eq 1 then
// P1 and S1 are cyclic
      g:=SylowConjCyclic(P1,S1,r,type2,Phi_1);
    else
      flag,t:=IsPower(n_0);
      if (flag and t eq r) or n_0 eq r then
// P1 and S1 are imprimitive
        g:=SylowConjImprimitive(P1,S1,r,type2,Phi_1);
      else
// P1 and S1 are reducible
        g:=SylowConjReducible(P1,S1,r,type2,Phi_1);
//Phi_1; g * Phi_1 * Transpose(MatToQ(g,p));
      end if;
    end if;
    g:=GL(n,q)!DiagonalJoin(IdentityMatrix(GF(q),n_1),g);

    return g1*gp1*g*gs1^-1*g1^-1;

  else
// Case B
    n_0:=2*(n div (2*d));
    n_1:=n-n_0*d;    
    if type eq "orth-" and n_1 eq 0 then //Derek Holt correction
      n_1:=n_1+2;
//    elif type eq "orth" then
//      n_1:=n_1+1;
    end if;
    m:=(n-n_1) div 2;
    if type notin {"orth+","orth-"} then
      Phi_0:=StandardForm(type,n_1,q);
    elif type eq "orth+" then
      if IsOdd(n_0) then
        Phi_0:=StandardForm("orth-",n_1,q);
      else
        Phi_0:=StandardForm("orth+",n_1,q);
      end if;
    elif type eq "orth-" then
      if IsOdd(n_0) then
        Phi_0:=StandardForm("orth+",n_1,q);
      else
        Phi_0:=StandardForm("orth-",n_1,q);
      end if;
    end if;
    I:=IdentityMatrix(GF(q),m);
    O:=ZeroMatrix(GF(q),m,m);
    if type eq "linear" then
      Phi_1:=ZeroMatrix(GF(q),2*m,2*m);
    elif type eq "symplectic" then
      Phi_1:=VerticalJoin(HorizontalJoin(O,I),HorizontalJoin(-I,O));
    elif type in {"orth","orth+","orth-"} then
      if IsOdd(q) then
        Phi_1:=VerticalJoin(HorizontalJoin(O,I),HorizontalJoin(I,O));
      else
        Phi_1:=VerticalJoin(HorizontalJoin(O,I),HorizontalJoin(O,O));
      end if;
    elif type eq "unitary" then
      Phi_1:=VerticalJoin(HorizontalJoin(O,I),HorizontalJoin(I,O));
    end if;
    Phi:=DiagonalJoin(Phi_0,Phi_1);
    CFPsi:=CorrectForm(Psi,n,q,type);
    CFPhi:=CorrectForm(Phi,n,q,type);
    
    g1:=CFPsi*CFPhi^-1;
    P:=P^g1; S:=S^g1;

    MP:=GModule(P); MS:=GModule(S);
    FixP:=Fix(MP); FixS:=Fix(MS);
    if Dimension(FixP) ne 0 then
      _,EP:=IsDirectSummand(MP,FixP);
      _,ES:=IsDirectSummand(MS,FixS);  
      gp1:=CorrectBlocks([FixP,EP],r,type,Phi);
      gs1:=CorrectBlocks([FixS,ES],r,type,Phi);
    else
      EP:=MP; ES:=MS;
      gp1:=GL(n,q)!1; gs1:=GL(n,q)!1;
    end if;
     

    P:=P^gp1; S:=S^gs1;
    n_1:=Dimension(FixP); n_0:=Dimension(EP) div d;
  
    P1:=sub<GL(d*n_0,q) | {GL(d*n_0,q)!ExtractBlock(g,n_1+1,n_1+1,d*n_0,d*n_0) : g in Generators(P)}>;
    S1:=sub<GL(d*n_0,q) | {GL(d*n_0,q)!ExtractBlock(g,n_1+1,n_1+1,d*n_0,d*n_0) : g in Generators(S)}>;
    MP:=GModule(P1); MS:=GModule(S1);
    EP:=IndecomposableSummands(MP);
    ES:=IndecomposableSummands(MS);
    Sort(~EP,func<x,y | Dimension(x)-Dimension(y)>);
    Sort(~ES,func<x,y | Dimension(x)-Dimension(y)>);
    LP:=sub<MP | >; RP:=sub<MP | >;
    LS:=sub<MS | >; RS:=sub<MS | >;

// Split modules
    repeat
      mp:=EP[1]; ms:=ES[1];
      Remove(~EP,1); Remove(~ES,1);
      if type cmpne "unitary" then
        _:=exists(jp){j : j in [1..#EP] | IsIsomorphic(mp,Dual(EP[j]))};    
        mpdual:=EP[jp]; Remove(~EP,jp);
        LP:=LP+mp; RP:=RP+mpdual;
        _:=exists(js){j : j in [1..#ES] | IsIsomorphic(ms,Dual(ES[j]))};    
        msdual:=ES[js]; Remove(~ES,js);
        LS:=LS+ms; RS:=RS+msdual;

      else 
        _:=exists(jp){j : j in [1..#EP] | IsIsomorphic(mp,Dual(sigma(EP[j])))};    
        mpdual:=EP[jp]; Remove(~EP,jp);
        LP:=LP+mp; RP:=RP+mpdual;
        _:=exists(js){j : j in [1..#ES] | IsIsomorphic(ms,Dual(sigma(ES[j])))};    
        msdual:=ES[js]; Remove(~ES,js);
        LS:=LS+ms; RS:=RS+msdual;
      end if;
    until #EP eq 0;
    if type cmpne "unitary" then
      _,tp:=IsIsomorphic(LP,Dual(RP));
      _,ts:=IsIsomorphic(LS,Dual(RS));
    else
      _,tp:=IsIsomorphic(LP,Dual(sigma(RP)));
      _,ts:=IsIsomorphic(LS,Dual(sigma(RS)));
    end if;

    gp2:=GL(2*m,q)!(DiagonalJoin(tp^-1,IdentityMatrix(GF(q),m))*Matrix([MP!LP.i : i in [1..m] ] cat [MP!RP.i : i in [1..m] ]));
    gs2:=GL(2*m,q)!(DiagonalJoin(ts^-1,IdentityMatrix(GF(q),m))*Matrix([MS!LS.i : i in [1..m] ] cat [MS!RS.i : i in [1..m] ]));
    if type in {"orth+","orth-","orth"} and IsEven(q) then
      IP:=UT(gp2*Phi_1*Transpose(gp2));
      IS:=UT(gs2*Phi_1*Transpose(gs2));
    elif type ne "unitary" then
      IP:=gp2*Phi_1*Transpose(gp2);
      IS:=gs2*Phi_1*Transpose(gs2);
    else
      IP:=gp2*Phi_1*Transpose(sigma(gp2));
      IS:=gs2*Phi_1*Transpose(sigma(gs2));
    end if;
    xp:=GL(2*m,q)!DiagonalJoin(ExtractBlock(IP,1,m+1,m,m)^-1,IdentityMatrix(GF(q),m));
    xs:=GL(2*m,q)!DiagonalJoin(ExtractBlock(IS,1,m+1,m,m)^-1,IdentityMatrix(GF(q),m));
    gp2:=xp*gp2; gp2:=gp2^-1;
    gs2:=xs*gs2; gs2:=gs2^-1;
    P1:=P1^gp2; S1:=S1^gs2;

    A:=sub<GL(m,q) | [GL(m,q)!ExtractBlock(p,1,1,m,m) : p in Generators(P1) ]>;
    B:=sub<GL(m,q) | [GL(m,q)!ExtractBlock(p,1,1,m,m) : p in Generators(S1) ]>;
    h:=$$(GL(m,q),A,B,"linear",r);
    if type ne "unitary" then
      h:=GL(2*m,q)!DiagonalJoin(h,Transpose(h)^-1);
    else
      h:=GL(2*m,q)!DiagonalJoin(h,Transpose(sigma(h))^-1);
    end if;
    h:=DiagonalJoin(IdentityMatrix(GF(q),n_1),h);
    gp2:=DiagonalJoin(IdentityMatrix(GF(q),n_1),gp2);
    gs2:=DiagonalJoin(IdentityMatrix(GF(q),n_1),gs2);
    return GL(n,q)!(g1*gp1*gp2*h*gs2^-1*gs1^-1*g1^-1);
  
  end if;
end function;



function Dim2EltConj(x,y,type,Phi : Projective:=false)
  if Projective then
    IdTest:=IsScalar;
  else
    IdTest:=IsOne;
  end if;
  Mx:=GModule([x]);
  if IsIrreducible(Mx) then
    if type notin {"linear","symplectic"} then return IrredEltConj(x,y,type,Phi); 
    elif type eq "symplectic" then
      q:=#CoefficientRing(x);
      z:=PrimitiveElement(GF(q));
      z:=z^((q-1) div GCD(q-1,2));
      z:=GL(2,q)!ScalarMatrix(2,z);
      for i in [0..Order(z)] do
        flag,t:=IrredEltConj(x*z^i,y,type,Phi); 
        if flag then
          return true,t;
        end if;
      end for;
      return false,_;
    else
      q:=#CoefficientRing(x);
      z:=ScalarMatrix(2,PrimitiveElement(GF(q)));
      for i in [0..Order(z)] do
        flag,t:=IsSimilar(x*z^i,y);
        if flag then
          t:=GL(2,q)!(t^-1);
          return true,t;
        end if;
      end for;
      return false,_;
    end if;
  end if;

  My:=GModule([y]);
  q:=#CoefficientRing(x);
  Ex:=IndecomposableSummands(Mx);
  Ey:=IndecomposableSummands(My);  
  xmat:=Matrix([Mx!Ex[1].1,Mx!Ex[2].1]);
  ymat:=Matrix([My!Ey[1].1,My!Ey[2].1]);
  xmat:=(GL(2,q)!xmat)^-1;
  ymat:=(GL(2,q)!ymat)^-1;
  pmat:=GL(2,q)![0,1,1,0];
  z1:=x^xmat*(y^ymat)^-1;
  z2:=x^(xmat*pmat)*(y^ymat)^-1;
  if type eq "linear" then
    if IdTest(z1) then return true,xmat*ymat^-1; 
    elif IdTest(z2) then return true,xmat*pmat*ymat^-1; 
    else return false,_;
    end if;
  elif type eq "unitary" then
    if IdTest(z1) and z1*Phi*Transpose(sigma(z1)) eq Phi then c:=xmat*ymat^-1;
    elif IdTest(z2) and z2*Phi*Transpose(sigma(z2)) eq Phi then c:=xmat*pmat*ymat^-1;
    else
      return false,_;
    end if;
  else
    if IdTest(z1) and z1*Phi*Transpose(z1) eq Phi then c:=xmat*ymat^-1;
    elif IdTest(z2) and z2*Phi*Transpose(z2) eq Phi then c:=xmat*pmat*ymat^-1;
    else
      return false,_;
    end if; 
  end if;
  A:=AutomorphismGroup(Mx);
  MA:=GModule(A);
  E:=[sub<MA | MA!Eltseq(Mx!Ex[1].1)>,sub<MA | MA!Eltseq(Mx!Ex[2].1)>];
  mat:=Matrix([MA!E[1].1,MA!E[2].1]);
  mat:=GL(2,q)!(mat^-1);
  phi1:=func<g | ExtractBlock(mat^-1*g*mat,1,1,1,1)[1][1]>;
  phi2:=func<g | ExtractBlock(mat^-1*g*mat,2,2,1,1)[1][1]>;
  if IsOne(phi1(A.1)) then
    a1:=A.2; a2:=A.1;
  else
    a1:=A.1; a2:=A.2;
  end if;
  if type ne "unitary" then
    t:=Phi*Transpose(c)^-1*Phi^-1*c^-1;
  else
    t:=Phi*Transpose(sigma(c))^-1*Phi^-1*c^-1;
  end if;
  if type ne "unitary" then
    star:=func<g | Phi*Transpose(g)*Phi^-1>;
  else
    star:=func<g | Phi*Transpose(sigma(g))*Phi^-1>;
  end if;
  k11:=Log(phi1(a1),phi1(star(a1)));
  k12:=Log(phi2(a2),phi2(star(a1)));
  k21:=Log(phi1(a1),phi1(star(a2)));
  k22:=Log(phi2(a2),phi2(star(a2)));
// now star(a1)=a1^k11*a2*k12 and star(a2)=a1^k21*a2^k22
  t1:=Log(phi1(a1),phi1(t));
  t2:=Log(phi2(a2),phi2(t));  
// t=a1^t1*a2^t2;
  I:=IntegerRing(q-1);
  mat:=Matrix(I,2,2,[k11+1,k12,k21,k22+1]); 
  vec:=Vector(I,[t1,t2]);
  flag,s:=IsConsistent(mat,vec);
  if flag eq false then
    return false,_;
  end if;
  n1:=IntegerRing()!s[1];
  n2:=IntegerRing()!s[2];
  a:=a1^n1*a2^n2;
  assert star(a)*a eq t;
  g:=a1^n1*a2^n2*c;
  return true,g;
end function;


function Sylow2Dim2Conj(P,S,type,Phi)
// Conjugates Sylow 2 subgroups in dimension 2
  if type eq "linear" then
    if forall{x : x in Generators(P) | Determinant(x) eq 1} then
      return Dim2ConjSp(P,S);
    else
      return Dim2ConjGL(P,S);
    end if;
  elif type eq "symplectic" then
    return Dim2ConjSp(P,S);
  elif type eq "orth+" then
    return Dim2ConjGOPlus(P,S);
  elif type eq "orth-" then 
    return Dim2ConjGOMinus(P,S);
  elif type eq "unitary" then
    if forall{x : x in Generators(P) | Determinant(x) eq 1} then
      return Dim2ConjSU(P,S,Phi);
    else
      G := sub<Generic(P) | ClassicalGroup("unitary",Phi)>;
      return Dim2ConjGU(G,P,S);
    end if;
  else
    error "Error in classical type";
  end if;
end function;

/*
function Sylow2Dim2Conj(P,S,type,Phi)
// Conjugates Sylow-2 subgroups of dim 2, note that the Sylow-2 subgroup of GL,Sp and GU in dim 2 are projectively dihedral, GO+ and GO- are dihedral 
  q:=#BaseRing(P);
  if IsTrivial(P) then return GL(2,q)!1; end if;
  if forall{x : x in Generators(P) | IsScalar(x)} then return GL(2,q)!1; end if;
  if type eq "linear" and forall{x : x in Generators(P) | Determinant(x) eq 1} then type:="symplectic"; Phi:=Generic(P)![0,1,-1,0];end if;
// Fist compute the order / projective order of the cyclic group
  case type:
    when "linear":
      O:=ProjectiveOrder;
      if q mod 4 eq 1 then m:=2^pPart(q-1,2); 
      else m:=2^pPart(q+1,2);
      end if;
      IdTest:=IsScalar;
    when "symplectic":
      O:=ProjectiveOrder;
      if q mod 4 eq 1 then m:=2^(pPart(q-1,2)-1); 
      else m:=2^(pPart(q+1,2)-1);
      end if;
      IdTest:=IsScalar;
    when "unitary":
      O:=ProjectiveOrder;
      _,p:=IsSquare(q);
      if p mod 4 eq 1 then m:=2^pPart(p-1,2); 
      else m:=2^pPart(p+1,2);
      end if;
      if forall{x : x in Generators(P) | Determinant(x) eq 1} then m:=m div 2; end if;
      IdTest:=IsScalar;
    when "orth+":
      O:=Order;
      if q mod 4 eq 1 then m:=2^pPart(q-1,2); 
      else m:=2;
      end if;
      IdTest:=IsId;
    when "orth-":
      O:=Order;
      if q mod 4 eq 3 then m:=2^pPart(q+1,2); 
      else m:=2;
      end if;
      IdTest:=IsId;
  end case;

// Deal with the SO+, SO-, Omega+, Omega- case
  if IsCyclic(P) then
    _,p1:=IsCyclic(P); _,s1:=IsCyclic(S);
    o:=Order(p1);
    T:={i : i in [1..(o-1)] | GCD(i,o) eq 1};
    for i in T do
      flag,g1:=Dim2EltConj(p1^i,s1,type,Phi);
      if flag then return g1; end if;
    end for;
  end if;

  if (type eq "orth+" or type eq "orth-") and m eq 2 then
// Find non-scalar elts and conjugate then  
    repeat
      p1:=Random(P);
    until not IsScalar(p1);
    repeat
      s1:=Random(S);
    until not IsScalar(s1);
    flag,g:=Dim2EltConj(p1,s1,type,Phi);
    if not flag then
      repeat
        z:=Random(S);
      until not IsId(z) and IsScalar(z);
      flag,g:=Dim2EltConj(p1,s1*z,type,Phi);
    end if;
    return g;
  end if;

// First find elements of order m
  repeat
    p1:=Random(P);
  until O(p1) eq m;
  repeat
    s1:=Random(S);
  until O(s1) eq m and Order(s1) eq Order(p1);
  for i in [j : j in [1..m] | GCD(m,j) eq 1] do
    if type in {"orth+","orth-"} then
      flag,g1:=Dim2EltConj(p1^i,s1,type,Phi);
    else
      flag,g1:=Dim2EltConj(p1^i,s1,type,Phi : Projective:=true);
    end if;
    if flag then break; end if;
  end for;

// Find element an element outisde <p1> and <s1>
  if m ne 2 then
    repeat
      p2:=Random(P);
    until not IdTest((p1,p2));
    repeat
      s2:=Random(S);
    until not IdTest((s1,s2));
  else
    repeat
      p2:=Random(P);
    until not IdTest(p2) and not IdTest(p1*p2);
    repeat
      s2:=Random(S);
    until not IdTest(s2) and not IdTest(s1*s2);
  end if;
  k:=O(p2^g1*s2);
  k:=k div 2^pPart(k,2);
  g2:=(s2*p2^g1)^(k div 2);    
  
  return g1*g2;
end function;      
*/

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

function MyImprimitiveAction2(P)
// Finds the imprimitive action for the case r=2
  n:=Dimension(P); q:=#BaseRing(P);
  assert not IsPrimitive(P);

  X:=BlocksImage(P);
  rho:=func<g | ImprimitiveAction(P,g)>;
  B:=Blocks(P);
  V:=VectorSpace(P);
  if Degree(X) ne 2 then
    BX:=MaximalPartition(X);
    rhoX:=BlocksAction(X,BX);
    rho:=func<g | rhoX(rho(g))>;
    X:=sub<Sym(2) | [rho(P.i) : i in [1..Ngens(P)] ]>;
    B:=[sub<V | &+[B[j] : j in b]> : b in BX];        
  end if;
// Now we have a map from P->C_2
  Known:=[i : i in [1..Ngens(P)] | IsId(rho(P.i))];
  Kgens := SchreierGeneratorsIndex2 (P : Known:=Known);
  K:=sub<GL(n,q) | Kgens>;
  if n eq 4 then
    M:=GModule(K);
    EP:=[sub<M | B[i]> : i in [1..#B] ];
    XtoP:=Homomorphism(X,GL(n,q),[X.i : i in [1..Ngens(X)]],[P.i : i in [1..Ngens(P)] ]);
    reps:=[GL(n,q) | GL(n,q)!1];
    for i in [2..Degree(X)] do
      _,t:=IsConjugate(X,1,i);
      Append(~reps,XtoP(t));
    end for;

    return rho,X,K,EP,reps;
  end if;

  m:=n div 2;
  mat:=GL(n,q)!(Matrix([B[1].j : j in [1..m] ] cat [B[2].j : j in [1..m] ]))^-1;;
  K1:=sub<GL(m,q) | {ExtractBlock(g^mat,1,1,m,m) : g in Generators(K)}>;
  K2:=sub<GL(m,q) | {ExtractBlock(g^mat,m+1,m+1,m,m) : g in Generators(K)}>; 
  rho1,X1,K1,EP1,_:=$$(K1);
  rho2,X2,K2,EP2,_:=$$(K2);
  K:=DirectProduct(K1,K2)^(mat^-1);    
  Vm:=VectorSpace(GF(q),m);
  M1:=GModule(K1);
  M2:=GModule(K2);
  VmtoV1:=hom<Vm->V | [V.i : i in [1..m] ]>;
  VmtoV2:=hom<Vm->V | [V.(m+i) : i in [1..m] ]>;
  B:=[];
  for i in [1..#EP1] do
    B:=B cat [sub<V |
    VmtoV1((Vm!M1!EP1[i].1))*mat^-1,(VmtoV1(Vm!M1!EP1[i].2))*mat^-1>];
  end for;  
  for i in [1..#EP2] do
    B:=B cat [sub<V |
    VmtoV2((Vm!M2!EP2[i].1))*mat^-1,(VmtoV2(Vm!M2!EP2[i].2))*mat^-1>];
  end for;  
  M:=GModule(K);
  EP:=[sub<M | B[i]> : i in [1..#B] ];
  rho:=function(g)
    im:=[];
    for i in [1..#B] do
      x:=B[i].1*g;
      _:=exists(j){j : j in [1..#B] | x in B[j]};
      Append(~im,j);
    end for;
    return Sym(#im)!im;
  end function;
  X:=sub<Sym(m) | [rho(P.i) : i in [1..Ngens(P)] ]>;
  XtoP:=Homomorphism(X,GL(n,q),[X.i : i in [1..Ngens(X)]],[P.i : i in [1..Ngens(P)] ]);
  reps:=[GL(n,q) | GL(n,q)!1];
  for i in [2..Degree(X)] do
    _,t:=IsConjugate(X,1,i);
    Append(~reps,XtoP(t));
  end for;
  return rho,X,K,EP,reps;
end function;


function SylowConjImprimitive2(P,S,type,Phi)
// conjugates imprimitive sylow 2 subgroups
  n:=Dimension(P); q:=#BaseRing(P);
  d:=2;
  n_0:=n div d;
  wr:=Truncate(Log(2,n_0));
  if type eq "unitary" then
    _,p:=IsSquare(q);
  end if;
  Y,Psi_0:=ClassicalSylow2Dim2(type,q);
  Phi_0:=ExtractBlock(Phi,1,1,d,d);
  if type ne "linear" then
      Phi:=DiagonalJoin([Phi_0 : i in [1..n_0] ]);
    if type ne "orth" then
      CFPsi_0:=CorrectForm(Psi_0,d,q,type);
      CFPhi_0:=CorrectForm(Phi_0,d,q,type);
    else
      CFPsi:=CorrectForm(Psi_0,d,q,"orth-");
      CFPhi:=CorrectForm(Phi_0,d,q,"orth-");
    end if;
    w:=CFPsi_0*CFPhi_0^-1;
    Y:=Y^w;
  else
    w:=GL(n,q)!1;
  end if;
  thetaP,XP,KP,EP,repsP:=MyImprimitiveAction2(P);
  thetaS,XS,KS,ES,repsS:=MyImprimitiveAction2(S);
  gp1:=CorrectBlocks(EP,2,type,Phi);
  gs1:=CorrectBlocks(ES,2,type,Phi);
  KP:=KP^gp1; KS:=KS^gs1;
  repsP:=[repsP[i]^gp1 : i in [1..#repsP] ];
  repsS:=[repsS[i]^gs1 : i in [1..#repsS] ];  

  I:=IdentityMatrix(GF(q),n);
  PBlock:=sub<GL(d,q) | {ExtractBlock(g,1,1,d,d) : g in Generators(KP)}>;
  SBlock:=sub<GL(d,q) | {ExtractBlock(g,1,1,d,d) : g in Generators(KS)}>;
  xp:=Sylow2Dim2Conj(PBlock,Y,type,Phi_0);
  xs:=Sylow2Dim2Conj(SBlock,Y,type,Phi_0);
  gp2:=IdentityMatrix(GF(q),n);
  gs2:=IdentityMatrix(GF(q),n);
  for i in [1..n_0] do
    x:=ExtractBlock(repsP[i]^-1,(i-1)*d+1,1,d,d)*xp;
    InsertBlock(~gp2,x,(i-1)*d+1,(i-1)*d+1);
    x:=ExtractBlock(repsS[i]^-1,(i-1)*d+1,1,d,d)*xs;
    InsertBlock(~gs2,x,(i-1)*d+1,(i-1)*d+1);
  end for;
  gp2:=GL(n,q)!gp2; gs2:=GL(n,q)!gs2;
  

  P:=P^(gp1*gp2); S:=S^(gs1*gs2);
  V:=VectorSpace(GF(q),n);
  Vsubs:=[sub<V | [V.((i-1)*d+j) : j in [1..d] ]> : i in [1..n_0] ];
  theta:=function(g)
    im:=[];
    for i in [1..n_0] do
      v:=Vsubs[i].1*g;
      _:=exists(j){j : j in [1..n_0] | v in Vsubs[j]};
      Append(~im,j);
    end for;
    return Sym(n_0)!im;
  end function;

  W:=WreathProduct([CyclicGroup(2) : i in [1..wr] ]);
  XP:=sub<Sym(2^wr) | [theta(P.i) : i in [1..Ngens(P)] ]>;
  XS:=sub<Sym(2^wr) | [theta(S.i) : i in [1..Ngens(S)] ]>;
  xp:=CorrectIteratedWreath(XP);
  xs:=CorrectIteratedWreath(XS);
  xpmat:=ZeroMatrix(GF(q),n,n); xsmat:=ZeroMatrix(GF(q),n,n);
  I:=IdentityMatrix(GF(q),d);
  xp:=Eltseq(xp); xs:=Eltseq(xs);
  for i in [1..n_0] do
    InsertBlock(~xpmat,I,(i-1)*d+1,(xp[i]-1)*d+1);
    InsertBlock(~xsmat,I,(i-1)*d+1,(xs[i]-1)*d+1);  
  end for;
  xpmat:=GL(n,q)!xpmat;
  xsmat:=GL(n,q)!xsmat;
  

  P:=P^xpmat; S:=S^xsmat;

  Wgens:=[W.i : i in [1..Ngens(W)]  | not IsId(W.i)];
  Sort(~Wgens,func<x,y | #Fix(y)-#Fix(x)>);

  trickP:=Id(P); trickS:=Id(S);
  I:=IdentityMatrix(GF(q),n);
  alphaP:=Homomorphism(W,GL(n,q),[theta(P.i) : i in [1..Ngens(P)] ],[P.i : i in [1..Ngens(P)] ]);
  alphaS:=Homomorphism(W,GL(n,q),[theta(S.i) : i in [1..Ngens(S)] ],[S.i : i in [1..Ngens(S)] ]);
  for i in [1..wr] do
    x:=alphaP(Wgens[i])^trickP;
    y:=alphaS(Wgens[i])^trickS;
    dim:=d*2^(i-1);
    Pblocks:=[MatrixAlgebra(GF(q),dim) | ];
    Sblocks:=[MatrixAlgebra(GF(q),dim) | ];
    Pblocks[2]:=ExtractBlock(x,dim+1,1,dim,dim);
    Sblocks[2]:=ExtractBlock(y,dim+1,1,dim,dim);
    Pblocks[1]:=IdentityMatrix(GF(q),dim);
    Sblocks[1]:=IdentityMatrix(GF(q),dim);
trickP:=trickP*GL(n,q)!DiagonalJoin(DiagonalJoin(Pblocks),IdentityMatrix(GF(q),n-2*dim));    
   
trickS:=trickS*GL(n,q)!DiagonalJoin(DiagonalJoin(Sblocks),IdentityMatrix(GF(q),n-2*dim));    
  end for;

  return gp1*gp2*xpmat*trickP*trickS^-1*xsmat^-1*gs2^-1*gs1^-1;

end function;


function SylowConjClassical2(G,P,S,type)
  n:=Dimension(G); q:=#BaseRing(G);
  assert IsOdd(q);
  case type:
    when "linear":
      Psi:=ZeroMatrix(GF(q),n,n);
      Phi:=Psi;
    when "symplectic":
      flag,Psi:=SymplecticForm(G);
      if not flag then
        error "Error in computing symplectic form";
      end if;
      Phi_0:=StandardForm(type,2,q);
      Phi:=DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]);
      btype:="symplectic";
    when "orth":
      flag,_,Psi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
      if IsEven(q) then
        Psi:=BilinearToQuadratic(G,Psi);
      end if; 
      if q mod 4 eq 1 then
        Phi_0:=StandardForm("orth+",2,q);
        Phi:=DiagonalJoin(GL(1,q)!1,DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]));
        btype:="orth+";
      elif q mod 4 eq 3 then
        Phi_0:=StandardForm("orth-",2,q);
        Phi:=DiagonalJoin(GL(1,q)!1,DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]));
        btype:="orth-";
      end if;
         
    when "orth+":
      flag,_,Psi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
      if IsEven(q) then
        Psi:=BilinearToQuadratic(G,Psi);
      end if;
      if n mod 4 eq 0 and q mod 4 eq 3 then
        Phi_0:=StandardForm("orth-",2,q);
        Phi:=DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]);
        btype:="orth-";
      elif n mod 4 ne 0 and q mod 4 eq 3 then
        Phi_0:=StandardForm("orth-",2,q);
        Phi_1:=StandardForm("orth+",2,q);
	if n ne 2 then
          Phi:=DiagonalJoin(Phi_1,DiagonalJoin([Phi_0 : i in [1..((n div 2)-1)] ]));
	else
	  Phi:=Phi_1;
	end if;
        btype:="orth+";
      else
        Phi_0:=StandardForm("orth+",2,q);
        Phi:=DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]);
        btype:="orth+";
      end if;
 
    when "orth-":
      flag,_,Psi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
      if IsEven(q) then
        Psi:=BilinearToQuadratic(G,Psi);
      end if; 
      if n mod 4 ne 0 and q mod 4 eq 3 then
        Phi_0:=StandardForm("orth-",2,q);
        Phi:=DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]);
        btype:="orth-";
      elif n mod 4 eq 0 and q mod 4 eq 3 then
        Phi_0:=StandardForm("orth-",2,q);
        Phi_1:=StandardForm("orth+",2,q);
        Phi:=DiagonalJoin(Phi_1,DiagonalJoin([Phi_0 : i in [1..((n div 2)-1)] ]));
        btype:="orth+";
      else
        Phi_0:=StandardForm("orth+",2,q);
        Phi_1:=StandardForm("orth-",2,q);
        Phi:=DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]);
	if n ne 2 then
          Phi:=DiagonalJoin(Phi_1,DiagonalJoin([Phi_0 : i in [1..((n div 2)-1)] ]));
	else
	  Phi:=Phi_1;
	end if;
        btype:="orth+";
      end if;

    when "unitary":
      flag,p:=IsSquare(q);
      if not flag then error "q is not a square in unitary type"; end if;
      flag,Psi:=UnitaryForm(G);
      if not flag then
        error "Error in computing unitaryform form";
      end if;
      Phi_0:=StandardForm(type,2,q);
      Phi:=DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]);
      if IsOdd(n) then
        Phi:=DiagonalJoin(GL(1,q)!1,Phi);
      end if;
  end case;

  if n eq 2 then return Sylow2Dim2Conj(P,S,type,Psi); end if;
  if type ne "linear" then
    CF_Psi:=CorrectForm(Psi,n,q,type);
    CF_Phi:=CorrectForm(Phi,n,q,type);
    g1:=CF_Psi*CF_Phi^-1;
    P:=P^g1; S:=S^g1;
  else
    g1:=GL(n,q)!1; 
  end if;

  MP:=GModule(P); EP:=IndecomposableSummands(MP);
  Sort(~EP,func<x,y | Dimension(x)-Dimension(y)>);
  MS:=GModule(S); ES:=IndecomposableSummands(MS);
  Sort(~ES,func<x,y | Dimension(x)-Dimension(y)>);
  if Dimension(EP[1]) eq 1 and Dimension(EP[2]) eq 1 then
    EP:=[EP[1]+EP[2]] cat [EP[i] : i in [3..#EP] ];
    ES:=[ES[1]+ES[2]] cat [ES[i] : i in [3..#ES] ];
  end if;
  gp1:=CorrectBlocks(EP,2,type,Phi);
  gs1:=CorrectBlocks(ES,2,type,Phi);
  P:=P^gp1; S:=S^gs1;
  count:=1;
  x:=IdentityMatrix(GF(q),n);
  for i in [1..#EP] do
    dim:=Dimension(EP[i]);
    Pblock:=sub<GL(dim,q) | [ExtractBlock(g,count,count,dim,dim) : g in Generators(P)]>;
    Sblock:=sub<GL(dim,q) | [ExtractBlock(g,count,count,dim,dim) : g in Generators(S)]>;
    if dim eq 2 then
      blockPhi:=ExtractBlock(Phi,count,count,2,2);
      if type notin {"orth+","orth-","orth"} then
        InsertBlock(~x,Sylow2Dim2Conj(Pblock,Sblock,type,blockPhi),count,count);
      else  
        btype:=ClassicalForms_Signum(GF(q),blockPhi);
        if btype eq 1 then        
          InsertBlock(~x,Sylow2Dim2Conj(Pblock,Sblock,"orth+",blockPhi),count,count);
        else  
          InsertBlock(~x,Sylow2Dim2Conj(Pblock,Sblock,"orth-",blockPhi),count,count);
        end if;
      end if;
    elif dim ne 1 then
      blockPhi:=ExtractBlock(Phi,count,count,dim,dim);
      dim2Phi:=ExtractBlock(Phi,count,count,2,2);
      if type notin {"orth+","orth-","orth"} then
        InsertBlock(~x,SylowConjImprimitive2(Pblock,Sblock,type,blockPhi),count,count);
      else  
        btype:=ClassicalForms_Signum(GF(q),dim2Phi);
        if btype eq 1 then        
          InsertBlock(~x,SylowConjImprimitive2(Pblock,Sblock,"orth+",blockPhi),count,count);
        else  
          InsertBlock(~x,SylowConjImprimitive2(Pblock,Sblock,"orth-",blockPhi),count,count);
        end if;
      end if;
    end if;
    count+:=dim;
  end for;
  x:=GL(n,q)!x;
  return GL(n,q)!(g1*gp1*x*gs1^-1*g1^-1);
end function;      
    
function CompositionSeriesToMatrix(E)
// Goes from a composition series to a matrix that exhibits such a series
  n:=#E; q:=#BaseRing(E[1]);
  M:=E[n];
  V:=VectorSpace(M);
  x:=V!M!E[1].1;
  m:=[x];    
  for i in [2..n] do
    x:=ExtendBasis(m,sub<V | [V!M!E[i].j : j in [1..i] ]>)[i];
    Append(~m,x);
  end for;  
  m:=Matrix(m);
  m[1]:=m[1]/Determinant(m);
  m:=GL(n,q)!m;
  return m;
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


function SpinorNormMap(G,P,S,type,Psi)
// Returns the spinor norm map of G=GL(2m,2^e)
  n:=Dimension(G); q:=#BaseRing(G);
  if type eq "orth+" then
    K:=OmegaPlus(n,q);
  else
    K:=OmegaMinus(n,q);
  end if;
  _,_,Phi:=OrthogonalForm(K);
  CF_Psi:=CorrectForm(BilinearToQuadratic(G,Psi),n,q,type);
  CF_Phi:=CorrectForm(BilinearToQuadratic(K,Phi),n,q,type);
  K:=K^(CF_Phi*CF_Psi^-1);
  C:=CyclicGroup(2);
  ki:=function(g)
    j:=RelativeOrder(g,K);
    if j eq 1 then return C!1;
    else return C.1;
    end if;
  end function;  
  KnownP:=[i : i in [1..Ngens(P)] | IsId(ki(P.i)) ];
  if #KnownP eq Ngens(P) then
    KP:=P; pelt:=P!1;
  else
    KP:=sub<GL(n,q) | SchreierGeneratorsIndex2(P : Known:=KnownP)>;
    pelt:=P.(Random({1..Ngens(P)} diff Seqset(KnownP)));
  end if;
  KnownS:=[i : i in [1..Ngens(S)] | IsId(ki(S.i)) ];
  if #KnownS eq Ngens(S) then
    KS:=S; selt:=S!1;
  else
    KS:=sub<GL(n,q) | SchreierGeneratorsIndex2(S : Known:=KnownS)>;
    selt:=S.(Random({1..Ngens(S)} diff Seqset(KnownS))); 
  end if;
  return ki,KP,pelt,KS,selt;
end function;


function SolvePolynomials(p)
// Finds solutions to polynomials in p with x_n ne 0
  P:=Parent(p[1]);
  n:=Rank(P);
  F:=CoefficientRing(P);
  flag:=false;
  for i in [1..n] do
    bool,_,k:=IsUnivariate(p[i]);
    if bool and k eq n then flag:=true; pnum:=i; break;
    end if;
  end for;
  if flag then
    r:=UnivariatePolynomial(p[pnum]);
    sol:=[];
    flag:=exists(x){x : x in Roots(r) | x[1] ne 0};
    if not flag then
      error "No non zero solution";
    end if;
    sol[n]:=x[1];
    p:=[Evaluate(p[i],n,sol[n]) : i in [1..(n-1)] ];
    A:=ZeroMatrix(F,n-1,n-1);
    for i in [1..(n-1)] do
      for j in [1..(n-1)] do  
        A[i][j]:=Coefficient(p[j],i,1);
      end for;
    end for;
    vec:=[];
    for i in [1..(n-1)] do
      vec[i]:=-p[i]+&+[A[j][i]*P.j : j in [1..(n-1)] ];
    end for;
    vec:=Matrix(F,1,n-1,vec);
    sol1:=Solution(A,vec)[1];
    sol:=Eltseq(sol1) cat [sol[n]];
    return sol;
  end if;

// First construct matrix A and vector v
  A:=ZeroMatrix(P,n-1,n-1);
  for i in [1..(n-1)] do
    for j in [1..(n-1)] do  
      A[i][j]:=Coefficient(p[j],i,1);
    end for;
  end for;
  vec:=[];
  for i in [1..(n-1)] do
    vec[i]:=-p[i]+&+[A[j][i]*P.j : j in [1..(n-1)] ];
  end for;
  vec:=Matrix(P,1,n-1,vec);
  sol1:=Solution(A,vec)[1];
// Substitute these variables into the last equation and solve
  subs:=[P.i-sol1[i] : i in [1..(n-1)] ];
  r:=p[n];
  for i in [1..(n-1)] do
    r:=Resultant(r,subs[i],i);
  end for;
  r:=UnivariatePolynomial(r);
  sol:=[];
  if IsZero(r) then
    sol[n]:=1;
  else
    flag,k:=HasRoot(r);
    if not flag then
      error "No solution";
    end if;
    if k eq 0 then
      flag,k:=HasRoot(r div Parent(r).1);
      if not flag then
        error "No non zero solution";
      end if;
    end if; 
    sol[n]:=k;
  end if;
// Now use this to get solution for x_1,...,x_(n-1)
  for i in [1..(n-1)] do
    r:=UnivariatePolynomial(Evaluate(subs[i],n,sol[n]));
    _,sol[i]:=HasRoot(r);
  end for;
  return sol;
end function;


function MakeSatisfyBilinearForm(X,Y,Phi)
// Alter X such that XPhiX^T=YPhiY^T without altering the module
  YPhi:=Y*Phi*Transpose(Y);
  X:=Matrix(X);
  n:=NumberOfRows(X); q:=#CoefficientRing(X);
  dot:=function(u,v)
    return InnerProduct(u*Phi,v);
  end function;
  for i in [2..n] do
    F:=PolynomialRing(GF(q),i);
    p:=[];
    for j in [1..(i-1)] do
      p[j]:=YPhi[j][i]-&+[F.k*YPhi[j][k] : k in [1..(i-1)]] - F.i*dot(X[j],X[i]);
    end for;
    Append(~p,YPhi[i][i] - (&+[F.j*(&+[F.k*YPhi[j][k] : k in [1..(i-1)] ] + F.i*dot(X[j],X[i]))  : j in [1..(i-1)] ] + F.i*(&+[F.j*dot(X[i],X[j]) : j in [1..i] ])));
    w:=SolvePolynomials(p);
    X[i]:=&+[w[j]*X[j] : j in [1..i] ];
  end for;
  return GL(n,q)!X;
end function;    

function MakeSatisfyHermitianForm(X,Y,Phi)
// Alter X such that XPhisigma(X)^T=YPhisigma(Y)^T without altering the module
 
  YPhi:=Y*Phi*Transpose(sigma(Y));
  X:=Matrix(X);
  n:=NumberOfRows(X); q:=#CoefficientRing(X);
  dot:=function(u,v)
    return InnerProduct(u*Phi,sigma(v));
  end function;
  for i in [2..n] do
    F:=PolynomialRing(GF(q),i);
    p:=[];
    for j in [1..(i-1)] do
      p[j]:=YPhi[j][i]-&+[F.k*YPhi[j][k] : k in [1..(i-1)]] - F.i*dot(X[j],X[i]);
    end for;
    Append(~p,YPhi[i][i] - (&+[F.j*(&+[F.k*YPhi[j][k] : k in [1..(i-1)] ] + F.i*dot(X[j],X[i]))  : j in [1..(i-1)] ] + F.i*(&+[F.j*dot(X[i],X[j]) : j in [1..i] ])));
    w:=SolvePolynomials(p);
    X[i]:=&+[w[j]*X[j] : j in [1..i] ];
  end for;
  return GL(n,q)!X;
end function;    

function MakeSatisfyQuadraticForm(X,Y,Phi)
// Alter X such that UT(XPhiX^T)=UT(YPhiY^T) without altering the module
 
  YPhi:=UT(Y*Phi*Transpose(Y));
  X:=Matrix(X);
  n:=NumberOfRows(X); q:=#CoefficientRing(X);
  dot:=function(u,v)
    return InnerProduct(u*Phi,v);
  end function;
  for i in [2..n] do
    F:=PolynomialRing(GF(q),i);
    p:=[];
    for j in [1..(i-1)] do
      if i ne 2 then
        p[j]:=YPhi[j][i]-&+[F.k*YPhi[j][k] : k in {1..(i-1)} diff {j}] - F.i*(dot(X[j],X[i])+dot(X[i],X[j]));
      else
        p[j]:=YPhi[j][i]-F.i*(dot(X[j],X[i])+dot(X[j],X[i]));
      end if;
    end for;
    p1:=F!0;
    for j in [1..(i-1)] do
      for k in [j..(i-1)] do
        p1:=p1+F.j*F.k*YPhi[j][k];
      end for;
      p1:=p1+F.j*F.i*(dot(X[j],X[i])+dot(X[j],X[i]));
    end for;
    p1:=p1 + F.i^2*dot(X[i],X[i]);
    Append(~p,YPhi[i][i] - p1);
    w:=SolvePolynomials(p);
    X[i]:=&+[w[j]*X[j] : j in [1..i] ];
  end for;
  assert UT(X*Y*Phi*Transpose(X*Y)) eq Phi;
  return GL(n,q)!X;
end function; 



function SylowConjClassical3(G,P,S,type)
  n:=Dimension(G); q:=#BaseRing(G);
  case type:
    when "linear":
      Phi:=ZeroMatrix(GF(q),n,n);
    when "symplectic":
      flag,Phi:=SymplecticForm(G);
      if not flag then
        error "Error in computing symplectic form";
      end if;
    when "orth":
      flag,_,Phi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
    when "orth+":
      flag,_,Phi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
      if IsEven(q) then
        QPhi:=BilinearToQuadratic(G,Phi);
      end if;
 
    when "orth-":
      flag,_,Phi:=OrthogonalForm(G);
      if not flag then
        error "Error in computing orthogonal form";
      end if;
      if IsEven (q) then
        QPhi:=BilinearToQuadratic(G,Phi);
      end if;
        
    when "unitary":
      flag,p:=IsSquare(q);
      if not flag then error "q is not a square in unitary type"; end if;
      flag,Phi:=UnitaryForm(G);
      if not flag then
        error "Error in computing unitaryform form";
      end if;
  end case;  
  if type in {"orth+","orth-"} and IsEven(q) then
    SpNmap,P,pelt,S,selt:=SpinorNormMap(G,P,S,type,Phi);
  end if;

  MP:=GModule(P); MS:=GModule(S);
  if type in {"orth-","orth+"} then
// must choose the correct submodule of dimension n/2
    m:=n div 2;
    Psubmods:=[smod : smod in Submodules(MP) | Dimension(smod) eq m];    
    EPtemp,_,mat:=CompositionSeries(MP);
    EP:=[EPtemp : i in [1..#Psubmods] ];
    gp1:=[GL(n,q) | ];
    for i in [1..#Psubmods] do
      EP[i][m]:=Psubmods[i];
      gp1[i]:=CompositionSeriesToMatrix(EP[i]);
    end for;
    Ssubmods:=[smod : smod in Submodules(MS) | Dimension(smod) eq m];    
    EStemp,_,mat:=CompositionSeries(MS);
    ES:=[EStemp : i in [1..#Ssubmods] ];
    gs1:=[GL(n,q) | ];
    for i in [1..#Ssubmods] do
      ES[i][m]:=Ssubmods[i];
      gs1[i]:=CompositionSeriesToMatrix(ES[i]);
    end for;
    for i in [1..#Psubmods] do for j in [1..#Ssubmods] do
      if IsOdd(q) then
        if forall{g : g in Generators(P) | g^(gp1[i]^-1*gs1[j])*Phi*Transpose(g^(gp1[i]^-1*gs1[j])) eq Phi} then
          gp1:=gp1[i]; gs1:=gs1[j];  
          break;
        end if;
      else 
        if forall{g : g in Generators(P) | UT(g^(gp1[i]^-1*gs1[j])*QPhi*Transpose(g^(gp1[i]^-1*gs1[j]))) eq QPhi} then          
          gp1:=gp1[i]; gs1:=gs1[j];  
          break;
        end if;
      end if;
    end for; 
    if Type(gp1) ne SeqEnum then break; end if; end for;
    if Type(gp1) eq SeqEnum then
      error "Failed to compute correct composition series";
    end if;  
  else
    EP:=CompositionSeries(MP);
    ES:=CompositionSeries(MS);
    gp1:=CompositionSeriesToMatrix(EP);
    gs1:=CompositionSeriesToMatrix(ES);
  end if;

  if type eq "linear" then return gp1^-1*gs1; end if;
  if type in {"orth+","orth-"} and IsEven(q) then
    gp1:=MakeSatisfyQuadraticForm(gp1,gs1,QPhi);
    g2:=gp1^-1*gs1;
    assert UT(g2*QPhi*Transpose(g2)) eq QPhi;
    if IsId(pelt) or IsId(selt) then return g2; end if;
    pelt:=pelt^g2; 
    o:=Order(pelt*selt);
    o:=o div 2^pPart(o,2);
    g3:=(selt*pelt)^((o-1) div 2);
    return g2*g3;
  elif type eq "unitary" then
    gp1:=MakeSatisfyHermitianForm(gp1,gs1,Phi);
    g2:=gp1^-1*gs1;
    assert g2*Phi*Transpose(sigma(g2)) eq Phi;
    return g2;
  else
    gp1:=MakeSatisfyBilinearForm(gp1,gs1,Phi);
    g2:=gp1^-1*gs1;
    assert g2*Phi*Transpose(g2) eq Phi;
    return g2;
  end if;

end function;


intrinsic ClassicalSylowConjugation(G::GrpMat,P::GrpMat,S::GrpMat : type:="")
               ->GrpMatElt
{
  For P and S Sylow-p subgroups of a classical group G.  Find g in G with P^g eq S. G must be one of GL,SL,Sp,GO,SO,Omega,GO+,SO+,Omega+,GO-,SO-,Omega-,GU,SU in its natural representation.
}
  local N;
  if forall{g : g in Generators(P) | g eq Id(G)} then return Id(G); end if;
  _, p := IspGroup(P);
  if type eq "" then
    type := ClassicalType(G);
  end if;
  n:=Dimension(G); q:=#BaseRing(G);  
  if type in {"SL","GL"} then type2:="linear";
  elif type in {"Sp"} then type2:="symplectic";
  elif type in {"SO","GO","Omega"} then type2:="orth";
  elif type in {"SO+","GO+","Omega+"} then type2:="orth+";
  elif type in {"SO-","GO-","Omega-"} then type2:="orth-";
  elif type in {"SU","GU"} then type2:="unitary";
  else type2:=type;
  end if;

  if IsTrivial(P) then return G!1; end if;
  q:=#BaseRing(G);
  q0:=#PrimeField(BaseRing(G));
  if p eq q0 then 
//    "Prime is characteristic of field";
    if type eq "orth" and IsEven(q) then
      require IsOdd(q) : "Unable to do the even q Orthogonal case";
    end if;
    g:=SylowConjClassical3(G,P,S,type2);
  elif p eq 2 then 
//    "Prime is 2";
    g:=SylowConjClassical2(G,P,S,type2);
  else 
//    "Prime is neither 2 nor the characteristic of the field";
if type2 in {"orth+","orth-"} and IsEven(q) then
//DFH - bypass orthogonal cases that are not working
  isc,g := IsConjugate(G,P,S); assert isc;
  return g;
end if;
    g:=SylowConjClassical1(G,P,S,type2,p);
  end if;

  if type in {"SL","SO","SO+","SO-","SU","Omega+","Omega","Omega-"} and Determinant(g) ne 1 then
    N:=ClassicalSylowNormaliser(G,P);
//[Order(Determinant(t)):t in Generators(N)], Order(Determinant(g));
    M,mu:=MultiplicativeGroup(GF(q));
    ims:=[Determinant(N.i)@@mu : i in [1..Ngens(N)]];
    A,inc:=sub<M | ims>;
    alpha:=Homomorphism(A,GL(n,q),[ims[i]@@inc : i in [1..#ims] ],[N.i : i in [1..Ngens(N)] ]);
    h:=alpha(Determinant(g^-1)@@mu@@inc);
    g:=h*g;
  end if; //another Derek Holt bugfix!
  if type in {"Omega","Omega+","Omega-"} then
    if not assigned N then N:=ClassicalSylowNormaliser(G,P); end if;
    KnownN:=[i : i in [1..Ngens(N)] | Determinant(N.i) eq 1];
/* Bug fix by Derek Holt - deal with case when all generators known */
    if Ngens(N) ne #KnownN then
      N:=sub<GL(n,q) | SchreierGeneratorsIndex2(N : Known:=KnownN)>;
    end if;
    _,_,Psi:=OrthogonalForm(G);
    repeat
      n := Random(N);
    until SpinorNorm(n*g,Psi) eq 0;
    g := n*g;
  end if;
  return g;

end intrinsic;
