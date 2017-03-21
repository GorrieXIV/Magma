freeze;

/*
**********************************************************************
 *    ClassicalSylowPC.m :  ClassicalSylow package - PC presentation code
 *
 *    File      : ClassicalSylowPC.m
 *    Author    : Mark Stather
 *    Date : 19/12/05
 *
 ********************************************************************
 *	This package will construct and conjugate Sylow subgroups of the classical groups and compute a PC presentaion of a given Sylow p-subgroup.  We are also able to compute the normalisers in the GL,Sp,GO,GO+,GO-,GU cases.
 * Derek Holt 7/10/09 changed calling parameters
Eg.
  G:=GOPlus(8,17);
  P:=ClassicalSylow(G,"GO+",3);
  S:=P^Random(G);
  g:=SylowConjClassical(G,P,S,"GO+",3);
  Pc,PtoPc,PctoP:=ClassicalSylowToPC(P,"GO+",3);
  N:=ClassicalSylowNormaliser(G,P,"orth+",3); 
*/


import "ClassicalSylow.m" : pPart, sigma, ClassicalType;
import "SylowConjClassical.m" : ElementFromDerivedGroup,
  SchreierGeneratorsIndex2,  MyImprimitiveAction2, IspGroup;

function PCPresOfComposite(G1,G1toP1,P1toG1,P1,G2,G2toP2,P2toG2,P2)
// Computes a map from G with Kernel Ker(phi2)
  gens1:=[P1toG1(P1.i) : i in [1..NPCgens(P1)] ];
  gens2:=[P2toG2(P2.i) : i in [1..NPCgens(P2)] ]; 
  ng1:=NPCgens(P1);
  ng2:=NPCgens(P2);
  n:=ng1+ng2;
  if n eq 0 then
    Pc:=PCGroup(AbelianGroup([1]));
    G1toPc:=func<g | Pc!1>;
    PctoG1:=hom<Pc->Generic(G1) | >;
    return Pc,G1toPc,PctoG1;
  end if;
  F:=FreeGroup(n);
  F1:=FPGroup(P1); 
  F1toF:=hom<F1->F | [F.i : i in [1..ng1] ]>;
  P1toF:=hom<P1->F | [F.i : i in [1..ng1] ] : Check:=false >;
  F2:=FPGroup(P2);
  F2toF := hom< F2->F | [F.(ng1+j) : j in [1..ng2]] >;
  P2toF := hom<P2->F|x:->&*[F.(ng1+j)^e[j]:j in [1..ng2]] where e := Eltseq(x)>;
  elts:={<gens1[i],F.i> : i in [1..ng1] } join {<gens2[i],F.(ng1+i)> : i in [1..ng2]} join {<G1!1,F!1>};

  rels:=[];
  if ng2 ne 0 then
    rels:=[r @ F2toF : r in Relations(F2)];
  end if;
  if ng1 gt 0 then
    F1toG1:=hom<F1->Generic(G1) | gens1>;
  end if;
  if ng1 gt 0 and ng2 gt 0 then
    for j in [1..ng1] do for k in [1..ng2] do
      g:=gens2[k]^gens1[j];
      if exists(x){x : x in elts | x[1] eq g} then
        w:=x[2];
      else
        w := g @ G2toP2 @ P2toF;
        Include(~elts,<g,w>);
      end if;
      Append(~rels,F.(ng1+k)^F.j = w );
    end for; end for;
  end if;
  if ng1 gt 0 then
    for r in Relations(F1) do
      if ng2 gt 0 then
        g := (RHS(r)^-1 * LHS(r)) @ F1toG1;
        if exists(x){x : x in elts | x[1] eq g} then
          w:=x[2];
        else
          w := g @ G2toP2 @ P2toF;
          Include(~elts,<g,w>);
        end if;
      else w := Id(F);
      end if;
      Append(~rels, LHS(r) @ F1toF = (RHS(r) @ F1toF) * w);
    end for;
  end if;
  Pc, FtoPc := quo<GrpPC: F | rels: Check := false >;

//time  Pc,GPctoPc:=PCGroup(GPc);
  thetainv:=Homomorphism(Pc,Generic(G1),[Pc.j : j in [1..n] ], gens1 cat gens2); 

  // GtoP is slightly trickier!
  P1toG1 := hom< P1->Generic(G1) | gens1 : Check:=false  >;
  GtoPfun := function(g)
    if ng1 eq 0 then
      return  g @ G2toP2 @ P2toF @ FtoPc;
    end if;
    gi := G1toP1(g);
    if gi cmpeq false then return false; end if;
    if ng2 eq 0 then
      return  gi @ P1toF @ FtoPc;
    end if;
    wr := gi @ P1toF;
    wl :=  ( (gi @ P1toG1)^-1 * g) @ G2toP2;
    if wl cmpeq false then return false; end if;
    wl := wl @ P2toF;
    return (wr*wl) @ FtoPc;
  end function;
  theta:=func<g | GtoPfun(g)>;
  return Pc,theta,thetainv;	
end function;
    

function pExpansion(t,r)
// returns a sequence E with t=E[1]+E[2]r+...+E[n]^r^(n-1) 0 leq E[i] <p
  if t eq 0 then return [0]; end if;
  max:=Truncate(Log(r,t));
  E:=[];
  for i in [max..0 by -1] do
    E[i+1]:=t div r^i;
    t:=t-E[i+1]*r^i;
  end for;
  return E;
end function;


function ClassicalSylowtoPC1(P,type,r)
  assert r ne 2;
  n:=Dimension(P); q:=#BaseRing(P);
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
  M:=GModule(P);
  F:=Fix(M);
  if Dimension(F) ne 0 then
    _,E:=IsDirectSummand(M,F);
  else
    E:=M;
  end if;
  mat:=Matrix([M!E.i : i in [1..Dimension(E)] ] cat [M!F.i : i in [1..Dimension(F)] ]);
  mat:=GL(n,q)!(mat^-1);
  dE:=Dimension(E);
  phi1:=func<g | ExtractBlock(g^mat,1,1,dE,dE)>;
  P1:=sub<GL(dE,q) | {phi1(g) : g in Generators(P)}>;
  M:=GModule(P1);
  E:=IndecomposableSummands(M);


//Case A
  if type eq "linear" or (type eq "symplectic" and IsEven(d)) or (type eq "orth" and IsEven(d)) or (type eq "orth+" and IsEven(d)) or (type eq "orth-" and IsEven(d)) or (type eq "unitary" and e mod 4 eq 2) then

// Construct map onto absolutely irreducible image  
    mat2:=Matrix(&cat[ [M!E[i].j : j in [1..Dimension(E[i])] ] : i in [1..#E] ]);
    mat2:=GL(dE,q)!mat2^-1;
    theta:=[**]; B:=[**]; psi:=[**]; A:=[**]; 
    count:=1;
    for i in [1..#E] do
      theta[i]:=func<g | ExtractBlock(g^mat2,count,count,Dimension(E[i]),Dimension(E[i]))>;
      B[i]:=sub<GL(Dimension(E[i]),q) | {theta[i](g) : g in Generators(P1)}>;
      A[i],psi[i]:=AbsoluteRepresentation(B[i]);
      if Dimension(A[i]) ne 1 then
        if IsPrime(Dimension(A[i])) then wr:=1;
        else
          _,_,wr:=IsPower(Dimension(A[i]));
        end if;
        repeat
          flag:=SearchForDecomposition(A[i],[ElementFromDerivedGroup(A[i],wr+1)] : Report:=false);
          BA:=Blocks(A[i]);          
        until flag and Type(BA) ne MonStgElt;
        mat3:=GL(Dimension(A[i]),#BaseRing(A[i]))!(Matrix(&cat[[BA[i].j : j in [1..Dimension(BA[i])] ] : i in [1..#BA] ])^-1);
        psi[i]:=func<g | mat3^-1*psi[i](g)*mat3>;
      end if;  
      count+:=Dimension(E[i]);
    end for;
    F:=BaseRing(A[1]);
    m:=&+[Dimension(A[i]) : i in [1..#A] ];
    zeta:=function(g)
      im1:=phi1(g);
      if Determinant(im1) eq 0 then return false; end if;
      im1:=GL(dE,q)!im1;
      im2:=IdentityMatrix(F,m);
      count:=1;
      for i in [1..#A] do
        t:=theta[i](im1);
        if Determinant(t) eq 0 then return false; end if;
        t:=GL(NumberOfRows(t),CoefficientRing(t))!t;
        InsertBlock(~im2,psi[i](t),count,count);
        count+:=Dimension(A[i]);
      end for;
      return GL(m,F)!im2;
    end function;

    H:=sub<GL(m,F) | {zeta(g) : g in Generators(P)}>;

  // Construct map of imprimitivity  
    V:=VectorSpace(F,m);
    B:=[sub<V | V.i> : i in [1..m] ];
    rho:=function(g)
      list:=[Position(B,B[i]^g) : i in [1..m] ];
      if #Seqset(list) ne m then return false; end if;
      return Sym(m)!list;
    end function;

  // Construct Kernel
    d:=Order(Integers(r)!(q+r));
    x:=Valuation(q^d-1,r);
    z:=PrimitiveElement(F);
    z:=z^((#F-1) div r^x); 
    K:=DirectProduct([sub<GL(1,F) | [z]> : i in [1..m] ]);

  // Construct map from kernel
    X:=FreeGroup(m*x);  rels:=[];
    for i in [1..m*x by x] do
      for j in [0..(x-2)] do
        Append(~rels,X.(i+j)^r=X.(i+j+1));
      end for;
      Append(~rels,X.(i+x-1)^r=1);
    end for;
    A,qu:=quo<GrpPC : X | rels : Check:=false>;
    eta:=function(g)
      if not IsDiagonal(g) then return false; end if;
      elt:=[];
      for i in [1..m] do
        t:=Log(z,g[i][i]);
        if t eq -1 then return false; end if;
  // Expand t as a_1+a_2*r+a_3*r^2 etc..
        E:=pExpansion(t,r);
        E:=E cat [0 : j in [(#E+1)..x] ];
        elt:=elt cat E;
      end for;
      return A!elt;
    end function;         
    etainv:=Homomorphism(A,GL(m,F),[eta(K.i) : i in [1..Ngens(K)] ],[K.i : i in [1..Ngens(K)] ]);

  // Glue together image and kernel
    Ip:=sub<Sym(m) | [rho(H.i) : i in [1..Ngens(H)] ]>;
    I,ItoPc:=PCGroup(Ip);  
    rho:=func<g | ItoPc(rho(g))>;
    gens:=[H.i : i in [1..Ngens(H)] ];
    Igens:=[ItoPc(Ip.i) : i in [1..Ngens(H)] ];
    rhoinv:=Homomorphism(I,GL(m,F),Igens,gens);  
    Pc,HtoPc,PctoH:=PCPresOfComposite(H,rho,rhoinv,I,K,eta,etainv,A);
    PtoPc:=function(g)
      h:=zeta(g); n:=Dimension(P); q:=#BaseRing(P);
      if h cmpeq false then return false; end if;
      return HtoPc(h);
    end function;
    Pc,inc:=sub<Pc | {PtoPc(x) : x in Generators(P)}>;
    PtoPc:=func<g | PtoPc(g)@@inc>;   
    PctoP:=Homomorphism(Pc,GL(n,q),[PtoPc(P.i) : i in [1..Ngens(P)] ],[P.i : i in [1..Ngens(P)] ]);
    return Pc,PtoPc,PctoP;

  else

    // Split modules
    Sort(~E,func<x,y | Dimension(x)-Dimension(y)>);
    L:=sub<M | >; R:=sub<M | >;

    repeat
      m:=E[1];
      Remove(~E,1); 
      if type cmpne "unitary" then
        _:=exists(j){j : j in [1..#E] | IsIsomorphic(m,Dual(E[j]))};    
        mdual:=E[j]; Remove(~E,j);
        L:=L+m; R:=R+mdual;
      else 
        _:=exists(j){j : j in [1..#E] | IsIsomorphic(m,Dual(sigma(E[j])))};    
        mdual:=E[j]; Remove(~E,j); 
        L:=L+m; R:=R+mdual;
      end if;
    until #E eq 0;
    n:=Dimension(P1);
    mat2:=GL(Dimension(P1),q)!(Matrix([M!L.i : i in [1..Dimension(L)] ] cat [M!R.i : i in [1..Dimension(R)] ])^-1);
    P1toA:=func<g | GL(n div 2,q)!ExtractBlock(mat2^-1*g*mat2,1,1,n div 2,n div 2)>;
    A:=sub<GL(n div 2,q) | {P1toA(g) : g in Generators(P1)}>;
    Pc,AtoPc,PctoA:=$$(A,"linear",r);
    PtoPc:=func<g | g @ phi1 @ P1toA @ AtoPc>;
    PctoP:=Homomorphism(Pc,GL(Dimension(P),q),[PtoPc(P.i) : i in [1..Ngens(P)] ],[P.i : i in [1..Ngens(P)] ]);
    return Pc,PtoPc,PctoP;
  end if;
end function;
      
// Constructs a map from the largest unipotent subgroup of GL to a PC
// presentation of it.
// Returns PC and GtoPC

function UnipotPC(d,q)
// Set up gens
// Number of gens
tm:=Cputime();
  K:=GF(q); p:=Characteristic(K); e:=Degree(K,GF(p));
  n:=((d*(d-1)) div 2)*e; 
  X:=FreeGroup(n);
  count:=1;
  gens:=[ [ [X | ] : j in [1..(i-1)] ] : i in [1..d] ];
  matgens:=[ [ [GL(d,q) | ] : j in [1..(i-1)] ] : i in [1..d] ];
  z:=PrimitiveElement(K);
  M,mu:=AdditiveGroup(K);
  for i in [2..d] do
    for j in [1..(i-1)] do
      for k in [1..e] do
        gens[i][j][k]:=X.count;
        matgens[i][j][k]:=InsertBlock(IdentityMatrix(GF(q),d),GL(1,q)![z^(k-1)],i,j);
        count+:=1;
      end for;
    end for;
  end for;

  rels:=[];
// power rels
  for i in [2..d] do
    for j in [1..(i-1)] do
      for k in [1..e] do
        Append(~rels,gens[i][j][k]^p=Id(X));
        assert IsOne(matgens[i][j][k]^p);
      end for;
    end for;
  end for;

// Conjugation relations

  for i in [2..(d-1)] do for j in [1..(i-1)] do
    for i2 in [(i+1)..d] do
    for k1 in [1..e] do for k2 in [1..e] do
      t:=Eltseq((z^(k1+k2-2))@@mu);
      g:=gens[i2][i][k1]^gens[i][j][k2];
      c:=&*[gens[i2][j][l]^t[l] : l in [1..#t] ]*gens[i2][i][k1];
      gm:=matgens[i2][i][k1]^matgens[i][j][k2];
      cm:=&*[matgens[i2][j][l]^t[l] : l in [1..#t] ]*matgens[i2][i][k1];      
      Append(~rels,g=c);
assert gm eq cm;
    end for; end for;
    end for;
  end for; end for;
//"Computed all relations in ",RealField(5)!Cputime(tm)," seconds";
  Pc,XtoPc:=quo<GrpPC : X | rels : Check:=false>;
  theta:=function(g)
    im:=Pc!1;
    for i in [2..d] do
      for j in [1..(i-1)] do
        t:=g[i][j]@@mu;
        t:=Eltseq(t);
        im:=im*&*[XtoPc(gens[i][j][l]^t[l]) : l in [1..#t] ];
      end for;
    end for;
    return im;
  end function;
  return Pc,theta;
end function;


function ClassicalSylowtoPC3(P)
// Computes a PC presentation of the Unipotent subgroup
  n:=Dimension(P); q:=#BaseRing(P);
  M:=GModule(P); 
  _,_,mat:=CompositionSeries(M);
  mat:=GL(n,q)!(mat^-1);
  Pc,theta:=UnipotPC(n,q);
  PtoPc:=func<g | theta(g^mat)>;
  subgens:=[PtoPc(P.i) : i in [1..Ngens(P)] ];
  PcSub,inc:=sub<Pc | subgens>;
  PtoPcSub:=func<g | PtoPc(g)@@inc>;
  PcSubtoP:=Homomorphism(PcSub,P,[PtoPcSub(P.i) : i in [1..Ngens(P)] ],[P.i : i in [1..Ngens(P)] ]);
  return PcSub,PtoPcSub,PcSubtoP;
end function;

function Sylow2Dim2toPC(P,type)
  q:=#BaseRing(P);
// Fist compute the order / projective order of the cyclic group
  if type eq "linear" and forall{x : x in Generators(P) | Determinant(x) eq 1} then type:="symplectic"; end if;
  case type:
    when "linear":
      O:=ProjectiveOrder;
      IdTest:=IsScalar;
      if q mod 4 eq 1 then m:=2^pPart(q-1,2); 
      else m:=2^pPart(q+1,2);
      end if;
    when "symplectic":
      O:=ProjectiveOrder;
      IdTest:=IsScalar;
      if q mod 4 eq 1 then m:=2^(pPart(q-1,2)-1); 
      else m:=2^(pPart(q+1,2)-1);
      end if;
    when "unitary":
      O:=ProjectiveOrder;
      IdTest:=IsScalar;
      _,p:=IsSquare(q);
      if p mod 4 eq 1 then m:=2^pPart(p-1,2); 
      else m:=2^pPart(q+1,2);
      end if;
      if forall{x : x in Generators(P) | Determinant(x) eq 1} then m:=m div 2; end if;
    when "orth+":
      O:=Order;
      IdTest:=IsId;
      if IsIrreducible(P) and q mod 4 eq 1 then m:=2^pPart(q-1,2); 
      elif IsIrreducible(P) and q mod 4 eq 3 then m:=2^pPart(q+1,2);
      else m:=2;
      end if;
    when "orth-":
      O:=Order;
      IdTest:=IsId;
      if IsIrreducible(P) and q mod 4 eq 1 then m:=2^pPart(q-1,2); 
      elif IsIrreducible(P) and q mod 4 eq 3 then m:=2^pPart(q+1,2);
      else m:=2;
      end if;
    when "orth":
      O:=Order;
      IdTest:=IsId;
      if IsIrreducible(P) and q mod 4 eq 1 then m:=2^pPart(q-1,2); 
      elif IsIrreducible(P) and q mod 4 eq 3 then m:=2^pPart(q+1,2);
      else m:=2;
      end if;
  end case;

// Is P cyclic?
  flag,x:=IsCyclic(P);
  if flag then
    Pc,PtoPc:=PCGroup(P);
    PctoP:=Inverse(PtoPc);
    return Pc,PtoPc,PctoP;
  end if;

// First find element of order m
  repeat
    x:=Random(P);
  until O(x) eq m;
// Construct map onto C_2
  C2:=PolycyclicGroup<a | a^2>;
  if m gt 2 then
    alpha:=function(g)
      if IdTest((g,x)) eq false then return C2.1;
      else return C2!1;
      end if;
    end function;
  else
    alpha:=function(g)
      if IdTest(g) eq true or IdTest(g*x^-1) then return C2!1; 
      else return C2.1;
      end if;
    end function;
  end if;
  Known:=[i : i in [1..Ngens(P)] | IsId(alpha(P.i))];
  alphainv:=hom<C2->GL(2,q) | P.(Random({1..Ngens(P)} diff Seqset(Known)))>;
  K:=SchreierGeneratorsIndex2(P : Known:=Known);
  K:=sub<GL(2,q) | K>;
  if #IndecomposableSummands(GModule(K)) eq 2 then
    M:=GModule(K);
    E:=IndecomposableSummands(M);
    mat:=GL(2,q)!(Matrix([M!E[1].1] cat [M!E[2].1])^-1);
    M,mu:=MultiplicativeGroup(GF(q));
    beta:=func<g | ((g^mat)[1][1]/(g^mat)[2][2])@@mu>; 
    A,inc:=sub<M | {beta(g) : g in Generators(K)}>;
    P1,AtoP1:=PCGroup(A);
    beta:=func<g | beta(g)@@inc@AtoP1>;
    betainv:=Homomorphism(P1,GL(2,q),[beta(K.i) : i in [1..Ngens(K)] ],[K.i : i in [1..Ngens(K)] ]);
    gamma:=func<g | (g^mat)[1][1]@@mu>;
    z:=PrimitiveElement(GF(q))^((q-1) div 2^pPart(q-1,2));
    z:=GL(2,q)!ScalarMatrix(GF(q),2,z);
    Z:=sub<GL(2,q) | z>;
    B,inc2:=sub<M | gamma(z)>;
    P2,BtoP2:=PCGroup(B);
    gamma:=func<g | gamma(g)@@inc2@BtoP2>;
    gammainv:=Homomorphism(P2,GL(2,q),[gamma(z)],[z]);
    Pc,KtoPc,PctoK:=PCPresOfComposite(K,beta,betainv,P1,Z,gamma,gammainv,P2);
    Pc,inc3:=sub<Pc | [KtoPc(K.i) : i in [1..Ngens(K)] ]>;
    KtoPc:=func<g | KtoPc(g)@@inc3>;
    PctoK:=Homomorphism(Pc,GL(2,q),[KtoPc(K.i) : i in [1..Ngens(K)] ],[K.i : i in [1..Ngens(K)] ]);
    Pc,PtoPc,PctoP:=PCPresOfComposite(P,alpha,alphainv,C2,K,KtoPc,PctoK,Pc);
  elif IsCyclic(K) then
    _,g:=IsCyclic(K); og:=Order(g);
    A,rho:=AbsoluteRepresentation(K);
    M,mu:=MultiplicativeGroup(GF(q^2));
    rho:=func<g | (rho(g))[1][1]@@mu>;
    ims:=[rho(K.i) : i in [1..Ngens(K)] ];
    A,inc:=sub<M | ims>;
    P1,AtoP:=PCGroup(A);
    beta:=func<g | rho(g)@@inc@AtoP>;
    betainv:=Homomorphism(P1,GL(2,q),[AtoP(ims[i]@@inc) : i in [1..Ngens(K)] ],[K.i : i in [1..Ngens(K)] ]);
    Pc,PtoPc,PctoP:=PCPresOfComposite(P,alpha,alphainv,C2,K,beta,betainv,P1);
  elif not IsPrimitive(K) then
    P1,S2toP1:=PCGroup(Sym(2));
    beta:=func<g | ImprimitiveAction(K,g)@S2toP1>;
    Known:=[i : i in [1..Ngens(K)] | IsId(beta(K.i))];
    betainv:=hom<P1->GL(2,q) | K.(Random({1..Ngens(K)} diff Seqset(Known)))>;
    K2:=SchreierGeneratorsIndex2(K : Known:=Known);
    K2:=sub<GL(2,q) | K2>;
    B:=Blocks(K);
    mat:=Matrix([B[1].1,B[2].1]);
    mat:=GL(2,q)!(mat^-1);
    M,mu:=MultiplicativeGroup(GF(q));
    gamma:=func<g | ((g^mat)[1][1]/(g^mat)[2][2])@@mu>;
    ims:=[gamma(K2.i) : i in [1..Ngens(K2)] ];
    A,inc:=sub<M | ims>;
    P2,AtoP2:=PCGroup(A);
    gamma:=func<g | gamma(g)@@inc@AtoP2>;    
    gammainv:=Homomorphism(P2,GL(2,q),[AtoP2(ims[i]@@inc) : i in [1..Ngens(K2)] ],[K2.i : i in [1..Ngens(K2)] ]);
    delta:=func<g | (g^mat)[1][1]@@mu>;
    z:=PrimitiveElement(GF(q))^((q-1) div 2^pPart(q-1,2));
    z:=GL(2,q)!ScalarMatrix(GF(q),2,z);
    Z:=sub<GL(2,q) | z>;
    B,inc2:=sub<M | delta(z)>;
    P3,BtoP3:=PCGroup(B);
    delta:=func<g | delta(g)@@inc2@BtoP3>;
    deltainv:=Homomorphism(P3,GL(2,q),[delta(z)],[z]);
    Pc,K2toPc,PctoK2:=PCPresOfComposite(K2,gamma,gammainv,P2,Z,delta,deltainv,P3);
    Pc,inc3:=sub<Pc | [K2toPc(K2.i) : i in [1..Ngens(K2)] ]>;
    K2toPc:=func<g | K2toPc(g)@@inc3>;
    PctoK2:=Homomorphism(Pc,GL(2,q),[K2toPc(K2.i) : i in [1..Ngens(K2)] ],[K2.i : i in [1..Ngens(K2)] ]);

    Pc,KtoPc,PctoK:=PCPresOfComposite(K,beta,betainv,P1,K2,K2toPc,PctoK2,Pc);
    Pc,PtoPc,PctoP:=PCPresOfComposite(P,alpha,alphainv,C2,K,KtoPc,PctoK,Pc);
  else
    error "Not completely reducible or cyclic ot imprimitive";
  end if;
  return Pc,PtoPc,PctoP;
end function;


function ClassicalSylowtoPC2(P,type)
  if Dimension(P) eq 2 then return Sylow2Dim2toPC(P,type); end if;
  M:=GModule(P); n:=Dimension(P); q:=#BaseRing(P);

  if IsIrreducible(P) then
// P is primitive
    rho,X,K,E:=MyImprimitiveAction2(P);
    M:=GModule(K);
    rhoinv:=Homomorphism(X,GL(n,q),[rho(P.i) : i in [1..Ngens(P)] ],[P.i : i in [1..Ngens(P)] ]);
    reps:=[Id(GL(n,q))];
    for i in [2..Degree(X)] do
      _,t:=IsConjugate(X,i,1);
      Append(~reps,rhoinv(t));
    end for;
    m:=n div 2;
    mat:=GL(n,q)!(Matrix(&cat[ [M!E[i].j : j in [1..2] ] : i in [1..#E] ]))^-1;
    KtoK1:=func<g | GL(2,q)!ExtractBlock(g^mat,1,1,2,2)>;
    I:=IdentityMatrix(GF(q),n);
    K1:=sub<GL(2,q) | {KtoK1(g) : g in Generators(K)}>;
    P1,K1toP1,P1toK1:=Sylow2Dim2toPC(K1,type);    
    Pc,injs:=DirectProduct([P1 : i in [1..m] ]);
    KtoPc:=function(g)
      im:=Pc!1;
      for i in [1..m] do
        im:=im*injs[i]((g^reps[i]) @ KtoK1 @ K1toP1);
      end for;
      return im;
    end function;
    Pc,inc:=sub<Pc | {KtoPc(x) : x in Generators(K)} >;
    KtoPc:=func<g | KtoPc(g)@@inc>;
    PctoK:=Homomorphism(Pc,GL(n,q),[KtoPc(K.i) : i in [1..Ngens(K)] ],[K.i : i in [1..Ngens(K)] ]);    
    W,XtoW:=PCGroup(X);
    alpha:=func<g | XtoW(rho(g))>;
    alphainv:=Homomorphism(W,GL(n,q),[alpha(P.i) : i in [1..Ngens(P)] ],[P.i : i in [1..Ngens(P)] ]);    
    Pc,PtoPc,PctoP:=PCPresOfComposite(P,alpha,alphainv,W,K,KtoPc,PctoK,Pc);    
    return Pc,PtoPc,PctoP;
  else
    E:=IndecomposableSummands(M);
    mat:=GL(n,q)!(Matrix(&cat[ [M!E[i].j : j in [1..Dimension(E[i])] ] : i in [1..#E] ]))^-1;
    PtoB:=[**]; B:=[**]; BPc:=[]; BtoPc:=[**]; PctoB:=[**];
    count:=1;
    for i in [1..#E] do
      dB:=Dimension(E[i]);
      PtoB[i]:=func<g | GL(dB,q)!ExtractBlock(g^mat,count,count,dB,dB)>;
      B[i]:=sub<GL(dB,q) | {PtoB[i](g) : g in Generators(P)}>;
      if dB ne 1 then
        BPc[i],BtoPc[i],PctoB[i]:=$$(B[i],type);
      else
        M,mu:=MultiplicativeGroup(GF(q));
        alpha:=func<g | g[1][1]@@mu>;
        A,inc:=sub<M | {alpha(x) : x in Generators(B[i])}>;
        BPc[i],AtoBPc:=PCGroup(A);
        BtoPc[i]:=func<g | alpha(g)@@inc@AtoBPc>;
        PctoB[i]:=Homomorphism(BPc[i],GL(dB,q),[BtoPc[i](B[i].j) : j in [1..Ngens(B[i])] ],[B[i].j : j in [1..Ngens(B[i])] ]);
      end if;
      count+:=dB;
    end for;
    Pc,injs:=DirectProduct(BPc);
    PtoPc:=function(g)
      im:=Pc!1;
      for i in [1..#E] do
        im:=im*injs[i](g @ PtoB[i] @ BtoPc[i]);
      end for;
      return im;
    end function;
    Pc,inc:=sub<Pc | {PtoPc(x) : x in Generators(P)} >;
    PtoPc:=func<g | PtoPc(g)@@inc>;
    PctoP:=Homomorphism(Pc,GL(n,q),[PtoPc(P.i) : i in [1..Ngens(P)] ],[P.i : i in [1..Ngens(P)] ]);    
    return Pc,PtoPc,PctoP;
  end if;
end function; 

intrinsic ClassicalSylowToPC(G::GrpMat, P::GrpMat)->GrpPC, UserProgram, Map
{ Constructs a PC presentations of the Sylow p-subgroup P of a classical group G.
Returns to PC group, a map from P->Pc and a map from Pc->P
}
  if IsTrivial(P) then
    Pc:=AbelianGroup(GrpPC,[1]);
    PtoPc:=func<x | Pc!1>;
    PctoP:=hom<Pc->Generic(P) | P!1>;
    return Pc,PtoPc,PctoP;
  end if;
  type := ClassicalType(G);
  _, p := IspGroup(P);
  if type in {"SL","GL"} then type2:="linear";
  elif type in {"Sp"} then type2:="symplectic";
  elif type in {"SO","GO","Omega"} then type2:="orth";
  elif type in {"SO+","GO+","Omega+"} then type2:="orth+";
  elif type in {"SO-","GO-","Omega-"} then type2:="orth-";
  elif type in {"SU","GU"} then type2:="unitary";
  else type2:=type;
  end if;
  if p eq Characteristic(BaseRing(P)) then Pc,PtoPc,PctoP:=
     ClassicalSylowtoPC3(P);
  elif p eq 2 then Pc,PtoPc,PctoP:=ClassicalSylowtoPC2(P,type2);
  else Pc,PtoPc,PctoP:=ClassicalSylowtoPC1(P,type2,p);
  end if;
  return Pc,PtoPc,PctoP;  
end intrinsic; 
