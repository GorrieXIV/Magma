freeze;

/*
**********************************************************************
 *    ClSylowNorm.m :  ClassicalSylow package - normaliser code
 *
 *    File      : ClSylowNorm.m
 *    Author    : Mark Stather
 *    Date : 19/12/05
 *
 ********************************************************************
 *	This package will construct and conjugate Sylow subgroups of the classical groups and compute a PC presentaion of a given Sylow p-subgroup.  We are also able to compute the normalisers in the GL,Sp,GO,GO+,GO-,GU cases.
 * Changed by Derek Holt 6/10/09 to eliminate type and prime paramters.
Eg.
  G:=GOPlus(8,17);
  P:=ClassicalSylow(G,"GO+",3);
  S:=P^Random(G);
  g:=SylowConjClassical(G,P,S,"GO+",3);
  Pc,PtoPc,PctoP:=ClassicalSylowToPC(P,"GO+",3);
  N:=ClassicalSylowNormaliser(G,P,"orth+",3); 
*/


function CyclicSylowExtraGens(X,r)
// X is a cyclic Sylow-r subgroup of Sym(r)
  r:=#X;
  _:=exists(x){x : x in Generators(X) | Order(x) eq r};
  e1:=[1^(x^n) : n in [0..(r-1)] ]; 
  e2:=[1^(x^(2*n)) : n in [0..(r-1)] ]; 
  if r ne 3 then
    e3:=[1^(x^(3*n)) : n in [0..(r-1)] ]; 
  end if;
  g:=[]; h:=[];
  for i in [1..r] do
    g[e1[i]]:=e2[i];
    if r ne 3 then
      h[e1[i]]:=e3[i];
    end if;
  end for;
  g:=Sym(r)!g;
  if r eq 3 then
    return [g];
  end if;
  h:=Sym(r)!h;
  return [g,h];
end function;

function PermActingOnSets(p,S)
// Given a permutation p of degree n return the action of p on the n sets of S a a permuation of degree #S[1]*n
  im:=[]; n:=Degree(Parent(p));
  list:=S;
  for i in [1..n] do
    j:=i^p;
    for k in [1..#list[1]] do
      im[list[i][k]]:=list[j][k];
    end for;
  end for;
  return Sym(#im)!im;
end function;

function MoveandFix(p,M,F)
// make p act on the sequence M and make it fix F
  n:=Degree(Parent(p)); m:=#M+#F;
  assert n eq #M;
  im:=[];
  for i in [1..m] do
    if i in M then
      Append(~im,M[Position(M,i)^p]);
    else
      Append(~im,i);
    end if;
  end for;
  return Sym(m)!im;
end function;
  
function SymSylowNormaliserExtraGens(X,r)
// X is a Sylow-r subgroup of Sym(r^k)
  n:=Degree(X);
  if n eq r then return CyclicSylowExtraGens(X,r); end if;
  B:=Setseq(MinimalPartition(X));
  Sort(~B,func<x,y | Minimum(x)-Minimum(y)>);
  rho,I,K:=BlocksAction(X,B);
  reps:=[Id(X)];
  for i in [2..#B] do
    _,t:=IsConjugate(I,1,i);
    Append(~reps,t@@rho);
  end for;
  _:=exists(z){z : z in Generators(K) | Order(OrbitAction(K,B[1])(z)) eq r};
  newB:=[ [] : i in [1..#B] ];
  newB[1]:=[1^(z^i) : i in [0..(r-1)] ];
  for i in [1..#B[1]] do
    for j in [2..#B] do 
      Append(~newB[j],newB[1][i]^reps[j]);
    end for;
  end for; 
  B:=newB;
  Blk:=OrbitImage(K,B[1]);
  EBlkgens:=CyclicSylowExtraGens(Blk,r);
  EBlkgens:=[MoveandFix(EBlkgens[i],B[1],&cat[B[j] : j in [2..#B] ]) : i in [1..#EBlkgens] ];  
  Egens:=[&*[EBlkgens[i]^reps[j] : j in [1..#B] ] : i in [1..#EBlkgens] ];  
  EIgens:=SymSylowNormaliserExtraGens(I,r);
  Egens:=Egens cat [PermActingOnSets(EIgens[i],B) : i in [1..#EIgens] ];  
  return Egens;
end function;

import "ClassicalSylow.m" : StandardForm, ClassicalType;
import "SylowConjClassical.m" : MyImprimitiveAction,IrredEltConj, SylowConjCyclic, CorrectBlocks;
import "SylowConjClassical.m" : SylowConjImprimitive, IspGroup;

function SymSylowNormaliser(X,r)
// Returns N_Sym(p^r)(P) with P and Sylow-p subgroup of Sym(p^r)
  Egens:=SymSylowNormaliserExtraGens(X,r);
  N:=sub<Sym(Degree(X)) | [X.i : i in [1..Ngens(X)] ] cat Egens>;
  return N;
end function;

function CyclicSylowNorm(P,Phi,type,r)
// returns extra generators for the Normalisers of P
  n:=Dimension(P); q:=#BaseRing(P);
  flag,x:=IsCyclic(P);
  C:=AutomorphismGroup(GModule([x]));
  c:=C.1;
  if type notin {"linear","unitary"} then
    m:=n div 2;
    c:=c^(q^m-1);
  elif type eq "unitary" then
    _,p:=IsSquare(q);
    c:=c^(p^n-1); //Derek Holt replaced c:=c^(p-1);
  end if;
  flag,y:=IrredEltConj(x,x^q,type,Phi);
  return [GL(n,q) | c,y];
end function;

function ImprimitiveSylowNorm(P,Phi,type,r)
  n:=Dimension(P); q:=#BaseRing(P);
  d:=Order(Integers(r)!(q+r));
  n_0:=n div d;
  wr:=Truncate(Log(r,n_0));
  if type eq "unitary" then
    _,p:=IsSquare(q);
  end if;
  Phi_0:=ExtractBlock(Phi,1,1,d,d);
  theta,X,K,E,reps:=MyImprimitiveAction(P,r);
  g1:=CorrectBlocks(E,r,type,Phi);
  P:=P^g1; K:=K^g1; reps:=[reps[i]^g1 : i in [1..#reps] ];
  B:=sub<GL(d,q) | {ExtractBlock(g,1,1,d,d) : g in Generators(K)}>;
  NBEgens:=CyclicSylowNorm(B,Phi_0,type,r);
  I:=IdentityMatrix(GF(q),n);
  NBEgens:=[GL(n,q)!InsertBlock(I,NBEgens[i],1,1) : i in [1..#NBEgens] ];
  NEgens:=[&*[NBEgens[i]^(reps[j]) : j in [1..#reps] ] : i in [1..#NBEgens] ];
  NEgens:=NEgens cat [GL(n,q)!InsertBlock(I,B.i,1,1) : i in [1..Ngens(B)] ];
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
  W:=sub<Sym(n_0) | {theta(g) : g in Generators(P)}>;
  WEgens:=SymSylowNormaliserExtraGens(W,r);
  conjelts:=[GL(d,q)!ExtractBlock(reps[i],1,(i-1)*d+1,d,d) : i in [1..#reps] ];
  for w in WEgens do
// Construct perm matrix
    p:=ZeroMatrix(GF(q),n,n); I:=IdentityMatrix(GF(q),d);
    for i in [1..Degree(W)] do
      InsertBlock(~p,I,(i-1)*d+1,(i^w-1)*d+1);
    end for;    
    z:=DiagonalJoin([conjelts[i]^-1*conjelts[i^w] : i in [1..#conjelts] ]);
    x:=GL(n,q)!(z*p);
    Append(~NEgens,x);
  end for;
  return [NEgens[i]^(g1^-1) : i in [1..#NEgens] ];
end function;
  
function ReducibleSylowNorm(P,Phi,type,r,d)
  n:=Dimension(P); q:=#BaseRing(P);
  d:=Dimension(IndecomposableSummands(GModule(P))[1]);
  n_0:=n div d;
  B:=[sub<GL(d,q) | {ExtractBlock(g,(i-1)*d+1,(i-1)*d+1,d,d) : g in Generators(P)}> : i in [1..n_0] ];
  conjelts:=[GL(d,q)!1];
  Phi_0:=ExtractBlock(Phi,1,1,d,d);
  if IsCyclic(B[1]) then cyc:=true; else cyc:=false; end if;
  for i in [2..n_0] do
    if cyc then
      Append(~conjelts,SylowConjCyclic(B[1],B[i],r,type,Phi_0));
    else
      Append(~conjelts,SylowConjImprimitive(B[1],B[i],r,type,Phi_0));
    end if;
  end for;
  if cyc then
    NBEgens:=CyclicSylowNorm(B[1],Phi_0,type,r);
  else
    NBEgens:=ImprimitiveSylowNorm(B[1],Phi_0,type,r);
  end if;
  NEgens:=[GL(n,q) | GL(n,q)!InsertBlock(GL(n,q)!1,x,1,1) : x in NBEgens];
  W:=Sym(n_0);
  for w in Generators(W) do
// Construct perm matrix
    p:=ZeroMatrix(GF(q),n,n); I:=IdentityMatrix(GF(q),d);
    for i in [1..Degree(W)] do
      InsertBlock(~p,I,(i-1)*d+1,(i^w-1)*d+1);
    end for;    
    z:=DiagonalJoin([conjelts[i]^-1*conjelts[i^w] : i in [1..#conjelts] ]);
    x:=GL(n,q)!(z*p);
    Append(~NEgens,x);
  end for;
  return NEgens;
end function;

import "ClassicalSylow.m" : BilinearToQuadratic, QuadraticToBilinear,sigma,UT,ClassicalGroup;
import "../Forms/form.m" : ClassicalForms_Signum;


function ExhibitBlockStructure(A,r)
// Exhibits the block structure of the reducible / imprimitive group
  n:=Dimension(A); q:=#BaseRing(A);
  d:=Order(Integers(r)!(q+r));
  M:=GModule(A);
  E:=IndecomposableSummands(M);
  g:=Matrix(&cat[[M!E[i].j : j in [1..Dimension(E[i])] ] : i in [1..#E] ]);
  g:=GL(n,q)!(g^-1);
  h:=IdentityMatrix(GF(q),n);
  count:=1;
  K:=[];
  for i in [1..#E] do
    B:=sub<GL(Dimension(E[i]),q) | {ExtractBlock(x^g,count,count,Dimension(E[i]),Dimension(E[i])) : x in Generators(A)}>;
    if Dimension(E[i]) ne d then
      _,_,K[i],EB:=MyImprimitiveAction(B,r);
      MB:=&+EB;
      x:=Matrix(&cat[[MB!EB[i].j : j in [1..Dimension(EB[i])] ] : i in [1..#EB] ]);
      x:=GL(Dimension(E[i]),q)!x;
      K[i]:=K[i]^(x^-1);      
      InsertBlock(~h,x,count,count);
    else
      K[i]:=B;
    end if;
    count+:=Dimension(E[i]);
  end for;
  h:=GL(n,q)!h;
  K:=DirectProduct(K);
  return g*h^-1,K;      
end function;


function ClassicalSylowNormaliser1(G,P,type,r)
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
  if IsTrivial(P) then
    return G;
  end if;
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
      P:=P^g1; 
    else
      g1:=GL(n,q)!1;
    end if;
    MP:=GModule(P);
    FixP:=Fix(MP); 
    if Dimension(FixP) ne 0 then
      _,EP:=IsDirectSummand(MP,FixP);
    else
      EP:=MP;
    end if;
    dimfixP:=Dimension(FixP);
    CP:=IndecomposableSummands(EP);
    Sort(~CP,func<x,y | Dimension(x)-Dimension(y)>);
    if dimfixP gt 0 then
      E:=[FixP] cat [sub<MP | [MP!x : x in Generators(CP[i])] > : i in [1..#CP] ];    
    else
      E:=[sub<MP | [MP!x : x in Generators(CP[i])] > : i in [1..#CP] ];    
    end if;
    g2:=CorrectBlocks(E,r,type,Phi);
    P:=P^g2;
    blocks:=Setseq({Dimension(CP[i]) : i in [1..#CP] });
    Sort(~blocks);
    blocks2:=[dimfixP];
    for i in [1..#blocks] do
      Append(~blocks2,blocks[i]*#[x : x in CP | Dimension(x) eq blocks[i] ]);
    end for;
    blocks:=blocks2;
    count:=0;
    N:=[GL(n,q) | ];
    I:=IdentityMatrix(GF(q),n);
    if blocks[1] ne 0 then
      temp:=ClassicalGroup(type,Phi_0);
      N:=N cat [GL(n,q)!InsertBlock(I,temp[i],1,1) : i in [1..#temp] ];
    end if;
    count:=blocks[1];
    for i in [2..#blocks] do
      B:=sub<GL(blocks[i],q) | {ExtractBlock(g,count+1,count+1,blocks
[i],blocks[i]) : g in Generators(P)}>;
      blockPhi:=ExtractBlock(Phi,count+1,count+1,blocks[i],blocks[i]);
      if Dimension(B) eq d then
        temp:=CyclicSylowNorm(B,blockPhi,type,r);
      elif IsIrreducible(B) then
        temp:=ImprimitiveSylowNorm(B,blockPhi,type,r);
      else
        temp:=ReducibleSylowNorm(B,blockPhi,type,r,d);
      end if;
      N:=N cat [GL(n,q)!InsertBlock(I,temp[i],count+1,count+1) : i in [1..#temp] ];
      count+:=blocks[i];
    end for;
    N:=sub<GL(n,q) | P,N>;
    N:=N^(g2^-1*g1^-1);
    return N;
 
  else
    // Case B
    n_0:=2*(n div (2*d));
    n_1:=n-n_0*d;    
    if type eq "orth-" and n_1 eq 0 then
      n_1:=n_1+2;
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
    P:=P^g1; 
    MP:=GModule(P);
    FixP:=Fix(MP); 
    
    if Dimension(FixP) ne 0 then
      _,EP:=IsDirectSummand(MP,FixP);
      gp1:=CorrectBlocks([FixP,EP],r,type,Phi);
    else
      EP:=MP;
      gp1:=GL(n,q)!1;
    end if;
    P:=P^gp1;
    n_1:=Dimension(FixP); n_0:=Dimension(EP) div d;
    P1:=sub<GL(d*n_0,q) | {GL(d*n_0,q)!ExtractBlock(g,n_1+1,n_1+1,d*n_0,d*n_0) : g in Generators(P)}>;
    EP:=GModule(P1);
    dimfixP:=Dimension(FixP);
    CP:=IndecomposableSummands(EP);
    Sort(~CP,func<x,y | Dimension(x)-Dimension(y)>);
    LP:=sub<EP | >;    RP:=sub<EP | >;
    // Split modules
    repeat
      mp:=CP[1];
      Remove(~CP,1);
      if type cmpne "unitary" then
        _:=exists(jp){j : j in [1..#CP] | IsIsomorphic(mp,Dual(CP[j]))};    
        mpdual:=CP[jp]; Remove(~CP,jp);
        LP:=LP+mp; RP:=RP+mpdual;

      else 
        _:=exists(jp){j : j in [1..#CP] | IsIsomorphic(mp,Dual(sigma(CP[j])))};    
        mpdual:=CP[jp]; Remove(~CP,jp);
        LP:=LP+mp; RP:=RP+mpdual;
      end if;
    until #CP eq 0;
    if type cmpne "unitary" then
      _,tp:=IsIsomorphic(LP,Dual(RP));
    else
      _,tp:=IsIsomorphic(LP,Dual(sigma(RP)));
    end if;
    g2:=GL(2*m,q)!(DiagonalJoin(tp^-1,IdentityMatrix(GF(q),m))*Matrix([EP!LP.i : i in [1..m] ] cat [EP!RP.i : i in [1..m] ]));
    if type in {"orth+","orth-","orth"} and IsEven(q) then
      IP:=UT(g2*Phi_1*Transpose(g2));
    elif type ne "unitary" then
      IP:=g2*Phi_1*Transpose(g2);
    else
      IP:=g2*Phi_1*Transpose(sigma(g2));
    end if;
    xp:=GL(2*m,q)!DiagonalJoin(ExtractBlock(IP,1,m+1,m,m)^-1,IdentityMatrix(GF(q),m));
    g2:=xp*g2; g2:=g2^-1;
    P1:=P1^g2;
    A:=sub<GL(m,q) | {ExtractBlock(g,1,1,m,m) : g in Generators(P1)}>;
    h,K:=ExhibitBlockStructure(A,r);
    if type ne "unitary" then
      h:=GL(2*m,q)!DiagonalJoin(h,Transpose(h)^-1);
    else
      h:=GL(2*m,q)!DiagonalJoin(h,Transpose(sigma(h))^-1);
    end if; 
    P1:=P1^h;
    A:=sub<GL(m,q) | {ExtractBlock(g,1,1,m,m) : g in Generators(P1)}>;
    NA:=$$(GL(m,q),A,"linear",r);
    if type ne "unitary" then
      gens:=[GL(2*m,q)!DiagonalJoin(x,Transpose(x)^-1) : x in Generators(NA)];
    else
      gens:=[GL(2*m,q)!DiagonalJoin(x,Transpose(sigma(x))^-1) : x in Generators(NA)];
    end if;
    I:=IdentityMatrix(GF(q),d);
    CL:=IndecomposableSummands(LP);
    count:=1;
    for i in [1..#CL] do
      dimCL:=Dimension(CL[i]);
      blk:=sub<GL(dimCL,q) | {ExtractBlock(x,count,count,dimCL,dimCL) : x in Generators(A)} >;
      if type eq "symplectic" then
        blkT:=sub<GL(dimCL,q) | {Transpose(ExtractBlock(x,count,count,dimCL,dimCL)^-1) : x in Generators(A)} >;
      elif type eq "unitary" then
        blkT:=sub<GL(dimCL,q) | {Transpose(sigma(ExtractBlock(x,count,count,dimCL,dimCL))^-1) : x in Generators(A)} >;
      else
        blkT:=sub<GL(dimCL,q) | {Transpose(ExtractBlock(x,count,count,dimCL,dimCL)^-1) : x in Generators(A)} >;
      end if;
      c:=ClassicalSylowConjugation(GL(dimCL,q),blkT,blk : type:="linear" );
      mat:=IdentityMatrix(GF(q),2*m);
      if type eq "symplectic" then
        InsertBlock(~mat,-Transpose(c^-1),count,m+count);
        InsertBlock(~mat,c,m+count,count);
      elif type eq "unitary" then
        InsertBlock(~mat,Transpose(sigma(c)^-1),count,m+count);
        InsertBlock(~mat,c,m+count,count);
      else
        InsertBlock(~mat,Transpose(c^-1),count,m+count);
        InsertBlock(~mat,c,m+count,count);
      end if;
      InsertBlock(~mat,ZeroMatrix(GF(q),dimCL,dimCL),count,count);
      InsertBlock(~mat,ZeroMatrix(GF(q),dimCL,dimCL),m+count,m+count);
      mat:=GL(2*m,q)!mat;
      Append(~gens,mat);
      count+:=dimCL;
    end for;             
    N1:=sub<GL(2*m,q) | gens>; 
    N1:=N1^(h^-1*g2^-1);
    if dimfixP gt 0 then
      cgens:=ClassicalGroup(type,Phi_0);           
      N2:=sub<GL(dimfixP,q) | cgens>;
      N:=DirectProduct(N2,N1);
    else
      N:=N1;
    end if;
    N:=N^(gp1^-1*g1^-1);
    return N;
  end if;
end function;

import "ClassicalSylow.m" : pPart;
import "SylowConjClassical.m" : Dim2EltConj;


function Sylow2Dim2Norm(P,type,Phi)
// Computes the normaliser of a Sylow 2-subgroup in dimension 2 as given in Carter/Fong 1964     
  q:=#BaseRing(P); 
// Deal with the SO,SO-,Omega+,Omega- cases first
  if type in {"orth+","orth-"} and forall{x : x in Generators(P) | Determinant(x) eq 1} then
    if IsTrivial(P) then o:=1; 
    else
      flag,x:=IsCyclic(P);
      o:=Order(x);
    end if;
    if type eq "orth+" and q mod 4 eq 1 then
      if o eq 2^pPart(q-1,2) then type2:="SO+";
      else type2:="Omega+";
      end if;
    elif type eq "orth+" and q mod 4 eq 3 then
      if o eq 2 then type2:="SO+"; 
      else type2:="Omega+";
      end if;
    elif type eq "orth-" and q mod 4 eq 1 then
      if o eq 2 then type2:="SO-"; 
      else type2:="Omega-";
      end if;
    elif type eq "orth-" and q mod 4 eq 3 then
      if o eq 2^pPart(q+1,2) then type2:="SO+";
      else type2:="Omega+";
      end if;
    end if;
    if type2 eq "SO+" then H:=GOPlus(2,q);
    elif type2 eq "SO-" then H:=GOMinus(2,q);
    elif type2 eq "Omega+" then H:=GOPlus(2,q);
    elif type2 eq "Omega-" then H:=GOMinus(2,q);
    end if;
    _,_,Psi:=OrthogonalForm(H);
    t:=CorrectForm(Psi,2,q,type)*CorrectForm(Phi,2,q,type)^-1;
    return [GL(2,q) | H.i^t : i in [1..Ngens(H)] ];
  end if;
    
  Egens:=[GL(2,q) | ];
  z:=PrimitiveElement(GF(q));
  if type cmpeq "linear" then
    Z:=GL(2,q)!(ScalarMatrix(2,z));
  elif type in {"symplectic","orth+","orth-"} then
    Z:=GL(2,q)!(ScalarMatrix(2,-1));
  elif type eq "unitary" then
    _,p:=IsSquare(q);
    Z:=GL(2,q)!(ScalarMatrix(2,z^(p-1)));
  end if;
  Append(~Egens,Z);
  if type eq "symplectic" and q mod 8 in {3,5} then
    repeat
      p1:=Random(P);
    until ProjectiveOrder(p1) eq 2;
    repeat
      p2:=Random(P);
    until not IsScalar(p2) and not IsScalar(p1*p2);
// Find an element of order 3 that conjugates p1 to p2
    w:=p1[1][1]; x:=p1[1][2]; y:=p1[2][1]; z:=p1[2][2];
    F<a,b,c,d>:=PolynomialRing(GF(q),4);
    polys:=[ a*d-b*c-1, a^3 + 2*a*b*c + b*c*d - 1 ,  a^2*b + a*b*d + b^2*c + b*d^2, a^2*c + a*c*d + b*c^2 + c*d^2,  a*b*c + 2*b*c*d + d^3 - 1,-a*b*y + a*d*w - b*c*z + c*d*x -p2[1][1], -b^2*y + b*d*w - b*d*z + d^2*x - p2[1][2], a^2*y - a*c*w + a*c*z - c^2*x - p2[2][1] , a*b*y + a*d*z - b*c*w - c*d*x - p2[2][2] ];
    W:=Variety(Ideal(polys));
    g:=GL(2,q)![W[1][1],W[1][2],W[1][3],W[1][4]];
    Egens:=Egens cat [GL(2,q)!g];
  end if;
  return Egens;
end function;    

import "SylowConjClassical.m" : MyImprimitiveAction2;

function ImprimitiveSylowNorm2(P,Phi,type)
  n:=Dimension(P); q:=#BaseRing(P);
  d:=2;
  n_0:=n div d;
  wr:=Truncate(Log(2,n_0));
  if type eq "unitary" then
    _,p:=IsSquare(q);
  end if;
  Phi_0:=ExtractBlock(Phi,1,1,d,d);
  theta,X,K,E,reps:=MyImprimitiveAction2(P);
  g1:=CorrectBlocks(E,2,type,Phi);
  P:=P^g1; K:=K^g1; reps:=[reps[i]^g1 : i in [1..#reps] ];
  B:=sub<GL(d,q) | {ExtractBlock(g,1,1,d,d) : g in Generators(K)}>;
  if type in {"orth+","orth-","orth"} then
    s:=ClassicalForms_Signum(GF(q),Phi_0);
    if s eq 1 then btype:="orth+";
    elif s eq -1 then btype:="orth-";
    else btype:="orth";
    end if;
  else
    btype:=type;
  end if;
  NBEgens:=Sylow2Dim2Norm(B,btype,Phi_0);
  I:=IdentityMatrix(GF(q),n);
  NBEgens:=[GL(n,q)!InsertBlock(I,NBEgens[i],1,1) : i in [1..#NBEgens] ];
  NEgens:=[&*[NBEgens[i]^(reps[j]) : j in [1..#reps] ] : i in [1..#NBEgens] ];
  NEgens:=NEgens cat [GL(n,q)!InsertBlock(I,B.i,1,1) : i in [1..Ngens(B)] ];
  return [NEgens[i]^(g1^-1) : i in [1..#NEgens] ];
end function;


function ClassicalSylowNormaliser2(G,P,type)
  n:=Dimension(G); q:=#BaseRing(G);
  assert IsOdd(q);
  case type:
    when "linear":
      Psi:=ZeroMatrix(GF(q),n,n);
      Phi:=Psi;
      if IsOdd(n) then
        d1:=1; d2:=n-1; type1:="linear"; type2:="linear";
      else
        d1:=0; d2:=n; type1:=0; type2:="linear";
      end if;
    when "symplectic":
      flag,Psi:=SymplecticForm(G);
      if not flag then
        error "Error in computing symplectic form";
      end if;
      Phi_0:=StandardForm(type,2,q);
      Phi:=DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]);
      d1:=0; d2:=n; type1:=0; type2:="symplectic";
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
        d1:=1; d2:=n-1; type1:=1; type2:="orth+";
      elif q mod 4 eq 3 then
        Phi_0:=StandardForm("orth-",2,q);
        Phi:=DiagonalJoin(GL(1,q)!1,DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]));
        d1:=1; d2:=n-1; type1:=1; type2:="orth-";
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
        d1:=0; d2:=n; type1:=0; type2:="orth-";
        btype:="orth-";
      elif n mod 4 ne 0 and q mod 4 eq 3 then
        Phi_0:=StandardForm("orth-",2,q);
        Phi_1:=StandardForm("orth+",2,q);
	if n ne 2 then
          Phi:=DiagonalJoin(Phi_1,DiagonalJoin([Phi_0 : i in [1..((n div 2)-1)] ]));
	else
	  Phi:=Phi_1;
	end if;
        d1:=2; d2:=n-2; type1:="orth+"; type2:="orth-";
      else
        Phi_0:=StandardForm("orth+",2,q);
        Phi:=DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]);
        btype:="orth+";
        d1:=0; d2:=n; type1:=0; type2:="orth+";
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
        d1:=0; d2:=n; type1:=0; type2:="orth-";
      elif n mod 4 eq 0 and q mod 4 eq 3 then
        Phi_0:=StandardForm("orth-",2,q);
        Phi_1:=StandardForm("orth+",2,q);
        Phi:=DiagonalJoin(Phi_1,DiagonalJoin([Phi_0 : i in [1..((n div 2)-1)] ]));
        d1:=2; d2:=n-2; type1:="orth+"; type2:="orth-";
      else
        Phi_0:=StandardForm("orth+",2,q);
        Phi_1:=StandardForm("orth-",2,q);
        Phi:=DiagonalJoin([Phi_0 : i in [1..(n div 2)] ]);
	if n ne 2 then
          Phi:=DiagonalJoin(Phi_1,DiagonalJoin([Phi_0 : i in [1..((n div 2)-1)] ]));
	else
	  Phi:=Phi_1;
	end if;
        d1:=2; d2:=n-2; type1:="orth-"; type2:="orth+";
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
        d1:=1; d2:=n-1; type1:=0; type2:="unitary";
      else
        d1:=0; d2:=n; type1:=0; type2:="unitary";
      end if;
  end case;

  if n eq 2 then Egens:=Sylow2Dim2Norm(P,type,Psi); 
    N:=sub<GL(2,q) | P,Egens>;
    return N;
  end if;
  if type ne "linear" then
    CF_Psi:=CorrectForm(Psi,n,q,type);
    CF_Phi:=CorrectForm(Phi,n,q,type);
    g1:=CF_Psi*CF_Phi^-1;
    P:=P^g1; 
  else
    g1:=GL(n,q)!1; 
  end if;

  MP:=GModule(P); EP:=IndecomposableSummands(MP);
  Sort(~EP,func<x,y | Dimension(x)-Dimension(y)>);
  if Dimension(EP[1]) eq 1 and Dimension(EP[2]) eq 1 then
    EP:=[EP[1]+EP[2]] cat [EP[i] : i in [3..#EP] ];
  end if;
  g2:=CorrectBlocks(EP,2,type,Phi);
  P:=P^g2;
  Egens:=[GL(n,q) | ];
  I:=IdentityMatrix(GF(q),n);
  start:=1;
  if d1 ge 1 then
    if d1 eq 1 and type cmpeq "linear" then
      z:=PrimitiveElement(GF(q));
      Append(~Egens,GL(n,q)!InsertBlock(I,GL(1,q)![z],1,1));
    elif d1 eq 1 and type cmpeq "unitary" then         
      z:=PrimitiveElement(GF(q))^(p-1);
      Append(~Egens,GL(n,q)!InsertBlock(I,GL(1,q)![z],1,1));
    elif d1 eq 1 and type cmpeq "orth" then
      Append(~Egens,GL(n,q)!InsertBlock(I,GL(1,q)![-1],1,1));
    else
      B:=sub<GL(2,q) | {ExtractBlock(g,1,1,2,2) : g in Generators(P)}>;
      EBgens:=Sylow2Dim2Norm(B,type1,Phi_1);
      for i in [1..#EBgens] do
        Append(~Egens,GL(n,q)!InsertBlock(I,EBgens[i],1,1));
      end for;
    end if;
    start:=2; 
  end if;
  count:=d1+1;
  for i in [start..#EP] do
    blockdim:=Dimension(EP[i]);
    blockPhi:=ExtractBlock(Phi,count,count,blockdim,blockdim);
    if type in {"orth+","orth-","orth"} then
      s:=ClassicalForms_Signum(GF(q),blockPhi);
      if s eq 1 then btype:="orth+";
      elif s eq -1 then btype:="orth-";
      else btype:="orth";
      end if;
    else
      btype:=type2;
    end if;
    B:=sub<GL(blockdim,q) | {ExtractBlock(g,count,count,blockdim,blockdim) : g in Generators(P)}>;    
    if blockdim eq 2 then
      EBgens:=Sylow2Dim2Norm(B,btype,blockPhi);
    else
      EBgens:=ImprimitiveSylowNorm2(B,blockPhi,btype);
    end if;
    for x in EBgens do
      Append(~Egens,GL(n,q)!InsertBlock(I,x,count,count));
    end for;
    for x in Generators(B) do
      Append(~Egens,GL(n,q)!InsertBlock(I,x,count,count));
    end for;
    count+:=blockdim;
  end for;
  N:=sub<GL(n,q) | P,Egens>;
  N:=N^(g2^-1*g1^-1);
  return N;
end function;

import "ClassicalSylow.m" : ClassicalSylow3;

function ClassicalSylowNormaliser3(G,P,type)
  n:=Dimension(G); q:=#BaseRing(G);
  if type eq "linear" then
      Psi:=ZeroMatrix(GF(q),n,n);
  elif type eq "symplectic" then
     _,Psi:=SymplecticForm(G);
  elif type in {"orth","orth+","orth-"} then
      _,_,Psi:=OrthogonalForm(G);
     if IsEven(q) then
       Psi:=BilinearToQuadratic(G,Psi);
     end if;
  elif type eq "unitary" then
      _,p:=IsSquare(q);
      _,Psi:=UnitaryForm(G);
  end if;
  S,NS:=ClassicalSylow3(G,type,Psi);
  _,r:=IsPrimePower(q);
  g:=ClassicalSylowConjugation(G,S,P : type:=type );
  N:=NS^g;
  return N;
end function;  

intrinsic ClassicalSylowNormaliser(G::GrpMat, P::GrpMat)->GrpMat
{ Computes the normaliser of the Sylow p-subgroup P of a classical group G.
G must be one of GL,Sp,GO,GO+,GO-,GU.}
  type := ClassicalType(G);
  if forall{g : g in Generators(P) | g eq Id(G)} then return G; end if;
  _, p := IspGroup(P);
  if type eq "SL" then type:="GL";
  elif type eq "SU" then type:="GU";
  elif type in {"Omega","SO"} then type:="GO";
  elif type in {"Omega+","SO+"} then type:="GO+";
  elif type in {"Omega-","SO-"} then type:="GO-";
  end if;

  if type eq "GL" then type:="linear";
  elif type eq "Sp" then type:="symplectic";
  elif type eq "GO" then type:="orth";
  elif type eq "GO+" then type:="orth+";
  elif type eq "GO-" then type:="orth-";
  elif type eq "GU" then type:="unitary";
  end if;
  q:=#BaseRing(G);
  if IsDivisibleBy(q,p) then
    return ClassicalSylowNormaliser3(G,P,type);
  elif p eq 2 then
    return ClassicalSylowNormaliser2(G,P,type);
  else
    return ClassicalSylowNormaliser1(G,P,type,p);
  end if;
end intrinsic;
