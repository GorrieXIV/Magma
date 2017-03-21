freeze;

/******************************************************************************
 *
 * ellchab.m
 *
 * date:   22/9/2003
 * author: Nils Bruin
 *
 * Routines for Elliptic Curve Chabauty. Interface:
 *
 * RelevantCosets - finite field arguments at a collection of
 *                  same-characteristic primes
 * ChabautyEquations - System of equations 
 * TestEquations     - testing for eqations if 0 is only integral solution
 * SolveEquations    - Separated zero finder
 * Chabauty          - Wrapper routine to combine all functionality.
 *
 ******************************************************************************/

import "newell.m":ProjectiveReduction;
import "../Arith/loctools.m":
       Minim, Maxim, IntNInf, MinValuation, MinPrec, ShiftVal,
       StripPrecisionlessTerms, FlattenPrecision, pAdicEvaluate, CoefficientByExponentVector;
import "../Arith/pointlift.m":Hensel;

declare verbose EllChab,3;

intrinsic RelevantCosets(MWmap::Map,Ecov::MapSch,Prs::{RngOrdIdl})->Tup
  {Computes useful information for Chabauty methods using elliptic covers}
  MWgrp:=Domain(MWmap);
  E:=Domain(Ecov);
  require Codomain(MWmap) eq E:"MWmap should correspond to cover";
  require ISA(Type(Codomain(Ecov)),Prj) and Dimension(Codomain(Ecov)) eq 1:
    "cover should be to a projective line";
  require BaseRing(Codomain(Ecov)) eq Rationals():
    "The cover should map to a projective line defined over the rationals.";
  require forall{P:P in Prs|IsPrime(P)}: "Ideals should all be prime";
  L:={Minimum(P):P in Prs};
  require #L eq 1: "Primes should all be of same residue characteristic";
  p:=Rep(L);
  Prs:=[LookupPrime(P):P in Prs];
  
  Ep,toEp:=Explode(<[v[1]:v in V],[v[2]:v in V]>) where
               V:=[<a,b>where a,b:=Reduction(E,P):P in Prs];
  k,tok:=Explode(<[v[1]:v in V],[v[2]:v in V]>) where
               V:=[<a,b>where a,b:=ResidueClassField(p):p in Prs];
  P1p:=ProjectiveSpace(GF(p),1);
  Ecovp:=[map<Ep[i]->P1p|ProjectiveReduction(
     DefiningEquations(Ecov),Prs[i],CoordinateRing(Ambient(Ep[i])))>:i in
     [1..#Prs]];
  require forall{cv : cv in Ecovp |
                   generic_image[2] ne 0 and
                   Degree(generic_image[1]/generic_image[2]) gt 0 where
                       generic_image:=cv(GenericPoint(Domain(cv)))}:
     "Given representation of cover does not have good reduction at all given primes";
  MWred,EpGrpMap:=Explode(<[v[1]:v in V],[v[2]:v in V]>) where
                        V:=[<a,b>where a,b:=Reduction(MWmap,P):P in Prs];
  IDX:=1;

  fibs:=[PowerStructure(Assoc)|];
  for i in [1..#Prs] do
    vprintf EllChab,2:"Considering prime #%o with <f,e>=%o\n",i,<InertiaDegree(Prs[i]),RamificationDegree(Prs[i])>;
    P1k:=P1p(k[i]);
    V:={pt:pt in RationalPoints(P1p)};
    IDX:=LCM(IDX,#(Codomain(MWred[i])/Image(MWred[i])));
    //If the image of the Mordell-Weil map is much bigger than p+1
    //then it's probably worth it to use discrete logarithms to lift the points
    //back into Image(MWred[i]). Otherwise, we may as well just enumerate
    //Image(MWred[i]) and see which images we get.
    //(if p is totally split, then the latter is the case, otherwise
    //discrete logarithms are probably less costly, provided the group order is
    //sufficiently smooth.

    if #Image(MWred[i]) gt 2*#V then
      vprint EllChab,2:"Using discrete log";
      //first build an associative array that allows quick lookup of
      //the images of rational points in the base locus of the map
      Images:=AssociativeArray(V);
      BadLocus:={Ep[i]!p:p in RationalPoints(BaseScheme(Ecovp[i]))};
      for v in V do
        Images[v]:={p: p in RationalPoints(v@@Ecovp[i])|p notin BadLocus};
      end for;
      for p in BadLocus do
        //we extend the map locally to get the value
        v:=EvaluateByPowerSeries(Ecovp[i],p);
        if v in V then
           Include(~Images[v],p);
         end if;
      end for;
      for v in V do
        Images[v]:={a:p in Images[v]|a in Image(MWred[i]) where a:=p@@EpGrpMap[i]};
      end for;
    else
      vprint EllChab,2:"Using enumeration";
      Images:=AssociativeArray(V);
      for p in Image(MWred[i]) do
        v:=EvaluateByPowerSeries(Ecovp[i],EpGrpMap[i](p));
        if v in V then
          if IsDefined(Images,v) then
            Include(~Images[v],p);
          else
            Images[v]:={p};
          end if;
        end if;
      end for;
    end if;
    fibs[i]:=Images;
  end for;

  fib1:=fibs[1];
  m1:=MWred[1];
  G:=FreeAbelianGroup(Ngens(MWgrp));
  m1:=hom<G->Image(m1)|[m1(g):g in OrderedGenerators(Domain(m1))]>;

  for i in [2..#Prs] do
    fib2:=fibs[i];
    m2:=MWred[i];
    m2:=hom<G->Image(m2)|[m2(g):g in OrderedGenerators(Domain(m2))]>;

    gcd,togcd:=quo<G|Generators(Kernel(m1))join Generators(Kernel(m2))>;
    lcm,tolcm:=quo<G|Kernel(m1) meet Kernel(m2)>;
    lcmto1:=hom<lcm->Codomain(m1)|[m1(a@@tolcm):a in OrderedGenerators(lcm)]>;
    lcmto2:=hom<lcm->Codomain(m2)|[m2(a@@tolcm):a in OrderedGenerators(lcm)]>;
    m1togcd:=hom<Codomain(m1)->gcd|
        [togcd(a@@m1):a in OrderedGenerators(Codomain(m1))]>;
    m2togcd:=hom<Codomain(m2)->gcd|
        [togcd(a@@m2):a in OrderedGenerators(Codomain(m2))]>;
    function CRT(e1,e2)
      if m1togcd(e1) eq m2togcd(e2) then
        v:=Eltseq(e1@@m1-e2@@m2);
        A1:=[Eltseq(G!a):a in OrderedGenerators(Kernel(m1))];
        A2:=[Eltseq(G!a):a in OrderedGenerators(Kernel(m2))];
        w:=Solution(Matrix(A1 cat A2),Vector(v));
        crt:=tolcm(e1@@m1-Kernel(m1)![w[i]:i in [1..Ngens(Kernel(m1))]]);
        return {crt+a:a in Kernel(lcmto1)meet Kernel(lcmto2)};
      else
        return {lcm|};
      end if;
    end function;
    for v in V do
      if IsDefined(fib1,v) and IsDefined(fib2,v) then
        fib1[v]:=&join[CRT(e1,e2):e1 in fib1[v],e2 in fib2[v]];
      else
        fib1[v]:={lcm|};
      end if;
    end for;
    m1:=tolcm;
  end for;
  quomap:=hom<MWgrp->Codomain(m1)|[m1(g):g in OrderedGenerators(G)]>;
  fibers:=ChangeUniverse(&join[fib1[v]:v in Keys(fib1)],Codomain(m1));

  return <quomap, fibers>,IDX;
end intrinsic;

intrinsic FactorialValuation(n::RngIntElt,p::RngIntElt)->RngIntElt
  {Number of factors of p in n!}
  e:=1;
  R:=0;
  repeat
    v:=Floor(n/(p^e));
    R+:=v;
    e+:=1;
  until v eq 0;
  return R;
end intrinsic;

function FormalLog(E: Precision:=10)
   R:=BaseRing(E);
   a1,a2,a3,a4,a6:=Explode(aInvariants(E));
   Rz:=LaurentSeriesRing(R:Precision:=Precision); 
   z := Rz.1;  // removing the minus sign so that T = -x/y  again (Nils)
   Rzw := PolynomialRing(Rz); w := Rzw.1;  // z, w is a confusing choice of names
   rt:=Roots(w-(z^3+a1*z*w+a2*z^2*w+a3*w^2+a4*z*w^2+a6*w^3));
   rt:=[r:r in rt | Valuation(r[1]) eq 3];
   assert #rt eq 1 and rt[1][2] eq 1;
   Wz:=rt[1][1];
   assert Valuation(Wz) eq 3;
   omega:=(Wz-z*Derivative(Wz))/Wz/(a1*z+a3*Wz-2);
   log:= PowerSeriesRing(R)! Integral(omega);
   Pz:=E(Rz)![z/Wz,-1/Wz];
   assert IsWeaklyZero( Pz[1]/Pz[2] + Rz.1 );
   return log,Pz;
end function;

intrinsic ChabautyEquations(P0::PtEll,Ecov::MapSch,
                MWmap::Map,Prs::{RngOrdIdl}:Precision:=10,Centred:=false)->SetEnum
  {Returns a set of equations used in Chabauty methods}

  E:=Codomain(MWmap);
  require Codomain(MWmap) eq E:"MWmap should correspond to cover";
  require ISA(Type(Codomain(Ecov)),Prj) and Dimension(Codomain(Ecov)) eq 1:
    "cover should be to a projective line";
  require BaseRing(Codomain(Ecov)) eq Rationals():
    "The cover should map to a projective line defined over the rationals.";
  require forall{P:P in Prs|IsPrime(P)}: "Ideals should all be prime";
  L:={Minimum(P):P in Prs};
  require #L eq 1: "Primes should all be of same residue characteristic";
  p:=Rep(L);
  require P0 in E: "Point should be on elliptic curve";
  
  Elog,Pz:=FormalLog(Domain(Ecov):Precision:=Precision-1);
  assert AbsolutePrecision(Elog) ge Precision;

  Prs:=[LookupPrime(P):P in Prs];
  
  covP0z:=a[1]/a[2] where a:=Ecov(P0+Pz);
  Kz:=Parent(covP0z);
  if Valuation(covP0z) lt 0 then covP0z:=1/covP0z; end if;

  covP0:=Evaluate(covP0z,0);
  if Centred and not(covP0 in Rationals()) then
    error "P0 has no rational image";
  end if;

  vals:=[Valuation(covP0,p):p in Prs];
  
  if Rep(vals) lt 0 then
    covP0z:=1/covP0z;
  end if;
  
  if Centred then
    covP0z:=covP0z-Evaluate(covP0z,0);
    order:=Valuation(covP0z);
    vprint EllChab,3:"Centred power series expansion:",covP0z;
  else
    vprint EllChab,3:"Power series expansion:",covP0z;
    order:=0;
  end if;
    
  SeriesPrec:=AbsolutePrecision(covP0z);
  pAdicPrec:=SeriesPrec-FactorialValuation(SeriesPrec,p);
  assert pAdicPrec gt order;
  
  KerPrs:=Domain(MWmap);
  for P in Prs do
    KerPrs meet:=Kernel(Reduction(MWmap,P));
  end for;

  KerPrsVec:=[Eltseq(Domain(MWmap)!g):g in OrderedGenerators(KerPrs)];

  Qp:=pAdicField(Minimum(Prs[1]));
  Qpn:=LazyPowerSeriesRing(Qp,Ngens(KerPrs));

  Eqs:=[];
  zBmat:=[];

  for p in Prs do
    Kp,toKp:=MyCompletion(p);
    error if Valuation(Kp!Minimum(p))/(Minimum(p)-1) ge 1,
      "Prime has too high ramification compared to residue characteristic.";

    // ensure BaseRing(Kp) is pAdicField(Minimum(p))
    // Completion, in the unramified case, sometimes returns a trivial extension 
    // SRD, April 2016
    if Degree(Kp) eq 1 then
      Kp := BaseRing(Kp);
    end if;
    
    pi:=UniformizingElement(Kp);
    prc:=2*(pAdicPrec+1)*AbsoluteRamificationDegree(Kp);
    oldprec:=Kp`DefaultPrecision;
    repeat
      Kp`DefaultPrecision:=prc;
      EKp:=PointSet(E,map<Domain(toKp)->Codomain(toKp)|a:->toKp(a)>);
      error if prc gt Kp`DefaultPrecision, "Insufficient precision available";
      Gp:=[EKp![toKp(c)+O(pi^prc):c in Eltseq(MWmap(g))]:
                   g in OrderedGenerators(Domain(MWmap))];
      L:=[p where p:=&+[v[i]*Gp[i]:i in [1..#Gp]]: v in KerPrsVec];
      zBp:=[-p[1]/p[2]:v in KerPrsVec | RelativePrecision(p[2]) gt 0 where p:=&+[v[i]*Gp[i]:i in [1..#Gp]]];
      prc:=prc*2;
    until #zBp eq #KerPrsVec and MinPrec(zBp) ge (pAdicPrec+1)*RamificationDegree(Kp);
    Kp`DefaultPrecision:=oldprec;

    zBmat:=zBmat cat [[Integers()!(Eltseq(a)[i]/Minimum(p)): a in zBp]:
                    i in [1..Degree(Kp)]];

    Kpz:=LaurentSeriesRing(Kp:Precision:=Kz`Precision);
    toKpz:=map<Kz->Kpz|f:->elt<Kpz|Valuation(f),[toKp(a):a in Eltseq(f)]>>;
    Elogp:=toKpz(Elog);
    Eexpp:=Reverse(Elogp);
    lBp:=[Evaluate(Elogp,b)+O(pi^(Valuation(b)*AbsolutePrecision(Elogp))):b in zBp];
    Kpn:=LazyPowerSeriesRing(Kp,#lBp);
    lBpn:=&+[lBp[i]*Kpn.i:i in [1..#lBp]];

    covP0pz:=toKpz(covP0z);
    zBpn:=Evaluate(Eexpp,lBpn);
    covBpn:=Evaluate(covP0pz,zBpn);
    RcovBpn:=[elt<Qpn|map<CartesianPower(Integers(),Rank(Qpn))->Qp|
           v:->(Eltseq(Coefficient(covBpn,[c:c in v])))[j]+O(Qp!Prime(Qp)^pAdicPrec)>>:
            j in [1..Degree(Kp)]];
    Append(~Eqs,RcovBpn);
  end for;
  vprint EllChab,3:"Reduction of matrix of Z-coordinates:",
                     Matrix(GF(Minimum(Prs[1])),zBmat);
  Eq0:=Eqs[1][1];
  Eqs:=&cat[[i eq 1 select l[i]-Eq0 else l[i]:i in [1..#l]]:l in Eqs];
  if Rank(Matrix(GF(Minimum(Prs[1])),zBmat)) lt Ngens(KerPrs) then
    vprint EllChab,3:
      "Matrix does not have maximal rank. Provide separate proof that MW-group",
      "is saturated at",Minimum(Prs[1]),"if required";
    return Eqs[2..#Eqs],order,Minimum(Prs[1]);
  else
    vprint EllChab,3:
      "Matrix has full rank. Implicit proof that MW-group is saturated at",
      Minimum(Prs[1]);
    return Eqs[2..#Eqs],order,1;
  end if;
end intrinsic;

intrinsic TestEquations(Eqs::[RngPowLazElt],d::RngIntElt)->BoolElt
  {Test equations}
  R:=Universe(Eqs);
  r:=Rank(R);
  Qp:=BaseRing(R);
  p:=Prime(Qp);
  dpad:=d-FactorialValuation(d,p);
  v:=Minimum( [Valuation(c):c in &cat[Coefficients(f,d,d):f in Eqs]]);
  d2:=d+1;
  while d2-FactorialValuation(d2,p) le v do
    v2:=Minimum( [Valuation(c):c in &cat[Coefficients(f,d2,d2):f in Eqs]]);
    if v2 le v then
       vprint EllChab,3:"Homogeneous part not decisive for this equation";
       return false;
    end if;
    d2+:=1;
  end while;
  Fp,toFp:=ResidueClassField(IntegerRing(Qp));
  if d eq 1 then
    M:=Matrix([[toFp(c/p^v):c in Coefficients(l,1,1)]:l in Eqs]);
    vprint EllChab,3:"Linear approximation gives matrix:",M;
    return Rank(M) eq NumberOfColumns(M);
  else
    P:=ProjectiveSpace(Fp,r-1);
    V:=MonomialsOfDegree(CoordinateRing(P),d);
    L:=[&+[toFp(Coefficient(f,Exponents(m))/p^v)*m:m in V]:f in Eqs];
    X:=Scheme(P,L);
    W:=RationalPoints(X);
    return #W eq 0;
  end if;
end intrinsic;

function AllIntegralPoints(L,prec)
  //takes a list of polynomials L and an assumed dimension 0
  //finds all integral points and tries to lift them to precision prec
  //integral points. (assumes no rational singular points exist!)
  //returns a set of sequences.

  //some quantities that don't change during the computations.
  Rpol:=Universe(L);
  R:=BaseRing(Rpol);
  error if not ISA(Type(R),RngPad), "must have polynomials over local ring";
  u:=UniformizingElement(R);
  n:=Rank(Rpol);
  cd:=n;
  k,Rtok:=ResidueClassField(R);
  Ak:=AffineSpace(k,n);
  kpol:=CoordinateRing(Ak);
  Rpoltokpol:=hom<Rpol->kpol|[kpol.i:i in [1..n]]>;

  //the hard (recursive) work.
  test:=function(L,lvl)
    vprint LocSol,2: "Entering test level ",lvl;
    vprint LocSol,2: "Passed argument:",L;
    L:=[FlattenPrecision(f+O(u^(prec-lvl))):f in L];
    L:=[MyPrimitivePart(Q) : P in L | Q ne 0 where Q:=StripPrecisionlessTerms(P)];
    vprint LocSol,2: "Primmed and stripped:",L;
    if exists{f:f in L|MinPrec(f) lt 1} or #L lt cd then
      vprint LocSol,2:
        "Degeneracy occurred. Returning Neigbourhood as unchecked";
      return {},{[O(R!1):i in [1..Rank(Rpol)]]};
    end if;      
    Lk:=[Rpoltokpol(P):P in L];
    Lkschm:=Scheme(Ak,[Rpoltokpol(P):P in L]);
    J:=JacobianMatrix(Lk);
    kpoints:=RationalPoints(Lkschm);
    vprint LocSol,2: "Points on reduction:",kpoints;
    res1:={};res2:={};
    for p in kpoints do
      Jp := Matrix(Ncols(J), [ Evaluate(f,Eltseq(p)) : f in Eltseq(J) ]);
      E,T:=EchelonForm(Jp);
      rk:=Rank(E);
      error if rk gt cd, "Jacobian has too large a rank. d wrong?";
      P:=[c@@Rtok+O(u):c in Eltseq(p)];
      if rk eq cd then
        if exists(l){l:l in L| RelativePrecision(Evaluate(l,P)) ne 0} then
          vprint LocSol,2:
            "Before lifting, one equation does not even lift.",
            "Value",Evaluate(l,P),"Disregarding point";
        else        
          vprint LocSol,2: "Found ",P,". This point lifts uniquely...";
          plift:=Hensel(L,0,P,prec-lvl:
                  Strict:=false);
          if exists(l){l:l in L| RelativePrecision(Evaluate(l,plift)) ne 0} then
            vprint LocSol,2:
              "After lifting, one equation does not vanish at point.",
              "Value",Evaluate(l,plift),"Disregarding point";
          else
            res1 join:={plift};
          end if;
        end if;
      else
        vprint LocSol,2: "Looking around ",p,"...";
        plift:=[p[i]@@Rtok+O(u^(prec-lvl))+(u+O(u^(prec-lvl)))*Rpol.i:i in [1..n]];
        L2:=[MyPrimitivePart(Evaluate(f,plift)):f in L];
        repeat
          B:=Matrix([[Rtok(CoefficientByExponentVector(f,
                             [j eq i select 1 else 0:j in [1..n]])):
                                 i in [1..Rank(Rpol)]]:f in L2]);
          E,T:=EchelonForm(B);
          vprint LocSol,2:"Changing the basis of the ideal by:",T;
          TT:=Matrix(Rpol,Ncols(T),Nrows(T),[a@@Rtok:a in Eltseq(T)]);
          L2:=Eltseq(Vector(L2)*Transpose(TT));
          flag:=false;
          vprint LocSol,2:"to",L2;
          for i in [1..#L2] do
            v:=MinValuation(L2[i]);
            if v gt 0 then
              L2[i]:=ShiftVal(L2[i],-v);
              vprint LocSol,2:"Extra content",v,"removed from",i,"th polynomial";
              flag:=true;
            end if;
          end for;
        until not(flag); 
        vprint LocSol,2:"Newly obtained basis is:",L2;

        IndentPush();
        nr1,nr2:=$$(L2,lvl+1);
        IndentPop();
        if #nr1 gt 0 or #nr2 gt 0 then
          vprint LocSol,2: "Found points. We tranform them back and add them.";
          res1 join:={[Evaluate(c,pt):c in plift]:pt in nr1};
          res2 join:={[Evaluate(c,pt):c in plift]:pt in nr2};
        end if;
      end if;
    end for;
    vprint LocSol,2: "Leaving test level ",lvl;
    return res1,res2;
  end function;
  L2:=[MyPrimitivePart(f):f in L];
  repeat
    B:=Matrix([[Rtok(CoefficientByExponentVector(f,
                       [j eq i select 1 else 0:j in [1..n]])):
                           i in [1..Rank(Rpol)]]:f in L2]);
    E,T:=EchelonForm(B);
    vprint LocSol,2:"Changing the basis of the ideal by:",T;
    TT:=Matrix(Rpol,Ncols(T),Nrows(T),[a@@Rtok:a in Eltseq(T)]);
    L2:=Eltseq(Vector(L2)*Transpose(TT));
    flag:=false;
    vprint LocSol,2:"to",L2;
    for i in [1..#L2] do
      v:=MinValuation(L2[i]);
      if v gt 0 then
        L2[i]:=ShiftVal(L2[i],-v);
        vprint LocSol,2:"Extra content",v,"removed from",i,"th polynomial";
        flag:=true;
      end if;
    end for;
  until not(flag); 
  
  return test(L2,1);
end function;

intrinsic SolveEquations(L::[RngPowLazElt])->SetEnum
  {For internal use}
  R:=Universe(L);
  Qp:=BaseRing(R);
  Zp:=IntegerRing(Qp);
  p:=Prime(Qp);
  r:=Rank(R);
  pAdicPrec:=AbsolutePrecision(Coefficient(L[1],[0:i in [1..r]]));
  degree:=pAdicPrec+FactorialValuation(pAdicPrec,p);
  while degree-FactorialValuation(degree,p) lt pAdicPrec do
    degree:=pAdicPrec+FactorialValuation(degree,p);
  end while;
  P:=PolynomialRing(Zp,r);
  LP:=[&+[&+[Zp!Coefficient(l,Exponents(v))*v:v in MonomialsOfDegree(P,d)]:
           d in [0..degree]]:l in L];
  return AllIntegralPoints(LP,pAdicPrec);
end intrinsic;

function toint(a)
  Zp:=Parent(a);
  p:=Prime(Zp);
  N:=p^AbsolutePrecision(a);
  an:=Integers()!a;
  if Abs(an-N) lt Abs(an) then
    return an-N;
  else
    return an;
  end if;
end function;

intrinsic Chabauty(MWmap::Map, Ecov::MapSch,
            p::RngIntElt:Cosets:=false,Aux:={},Precision:=10,Bound:=5)->SetEnum,RngIntElt
  {Straightforward attempt for determining the set of points in the image
  of MWmap that have a rational image under Ecov}
  K:=BaseRing(Domain(Ecov));
  OK:=IntegerRing(K);
  Prs:=Support(p*OK);
  vprint EllChab:"Computing relevant cosets using the primes above",p;
  fibp,IDX:=RelevantCosets(MWmap,Ecov,Prs);
  vprint EllChab:"Found cosets",fibp[2];
  vprint EllChab:"Modulo kernel",Kernel(fibp[1]);
  vprint EllChab:"LCM of indices:",IDX;
  if Cosets cmpne false then
    require #Aux eq 0:"Either specify Cosets OR Aux, but not both.";
    fibp:=CosetIntersection(fibp,Cosets:Weak);
    vprint EllChab:
      "Insersecting with supplied cosets cuts down cosets to",fibp[2];
  else
    for q in Aux do
      vprint EllChab:"Computing relevant cosets using the primes above",q;
      fibq,IDXq:=RelevantCosets(MWmap,Ecov,Support(q*OK));
      vprint EllChab:"Found cosets:",fibq[2];
      vprint EllChab:"Modulo kernel:",Kernel(fibq[1]);
      vprint EllChab:"LCM of indices:",IDXq;
      fibp:=CosetIntersection(fibp,fibq:Weak);
      vprint EllChab:"For",p,"this cuts down cosets to",fibp[2];
      IDX:=LCM(IDX,IDXq);
    end for;
  end if;
  vprint EllChab:
    "Testing linear combinations in Mordell-Weil group up to bound",Bound;
  V:={v: c in CartesianPower([-Bound..Bound],Ngens(Domain(MWmap))) |
         fibp[1](v) in fibp[2] where v:=Domain(MWmap)![d:d in c]};
  QQ:=Rationals();
  MWfib:={a: a in V| b[1] in QQ and b[2] in QQ where b:=
              EvaluateByPowerSeries(Ecov,MWmap(a))};
  vprint EllChab:"Found",MWfib;

  if {fibp[1](pt):pt in MWfib} ne fibp[2] then
    vprint EllChab:
    "Cannot find representatives for all cosets. We'll see what happens.";
  end if;
  rem:=fibp[2];
  kerlev:=Infinity();
  nogos:=[];
  NrPoints:=0;
  for g in MWfib do
    P0:=MWmap(g);
    vprint EllChab:"P0 =",P0;
    vprint EllChab:"Image under cover:",EvaluateByPowerSeries(Ecov,P0);
    Eqs,order,IDXq:=ChabautyEquations(P0,Ecov,MWmap,Prs:
                                  Centred,Precision:=Precision);
    vprint EllChab:"Order of vanishing:",order;
    IDX:=LCM(IDX,IDXq);
    bl:=TestEquations(Eqs,order);
    if bl then
      vprint EllChab:"P0 is the only point in its fibre.";
      NrPoints+:=1;
      rem:=rem diff {fibp[1](g)};
    else
      vprint EllChab:"P0 is not necessarily unique in its fibre.";
      if order gt 1 then      
        vprint EllChab:
          "P0 is a ramification point.",
          "We do not get a bound on the number of rational points";
      end if;      
    end if;
  end for;
  if #rem eq 0 then
    vprint EllChab:"Done!!";
  else
    vprint EllChab:"Will try to deal with remaining points";
  end if;
  candidates:=[];
  for g in rem do
    bl:=exists(gr){gr:gr in MWfib| fibp[1](gr) eq g};
    if not bl then
      gr:=ShortLift(fibp[1],g);
    end if;
    P0:=MWmap(gr);
    vprint EllChab:"P0 =",P0;
    Eqs,order,IDXq:=ChabautyEquations(P0,Ecov,MWmap,Prs:Precision:=Precision);
    IDX:=LCM(IDX,IDXq);
    V1,V2:=SolveEquations(Eqs);
    vprint EllChab:"Solutions to p-adic system of equations:",V1;
    vprint EllChab:"Unresolved neighbourhoods:",V2;
    NrPoints+:=#V1;
    if #V2 ne 0 then
      NrPoints:=Infinity();
    end if;
    kerlev:=Minimum(kerlev,MinPrec(&cat Setseq(V1)));
    kerlev:=Minimum(kerlev,MinPrec(&cat Setseq(V2)));
    for v in V1 do
      Append(~candidates,gr+Kernel(fibp[1])![toint(c):c in v]);
    end for;
    for v in V2 do
      Append(~nogos,gr+Kernel(fibp[1])![toint(c):c in v]);
    end for;
  end for;
  for a in candidates do
    if forall{c: c in Eltseq(a)| Abs(c) lt 20} then
      vprint EllChab:"Point",a,"looks promisingly small. Let's try it.";
      b:=EvaluateByPowerSeries(Ecov,MWmap(a));
      if b[1] in QQ and b[2] in QQ then
        vprint EllChab:"Found point",a,"with rational image",b;
        MWfib join:={a};
      else
        vprint EllChab:"Didn't work out";
        Append(~nogos,a);
      end if;
    else
      vprint EllChab:"Point",a,"is supposedly a sole candidate,",
        "but looks too big to really try.";
      Append(~nogos,a);
    end if;
  end for;
  if #nogos eq 0 then
    vprint EllChab:
      "Returned set gives all points with rational image if given MWmap is",IDX,
      "saturated.";
    newtup:=<fibp[1],{Universe(fibp[2])|}>;
  else  
    vprint EllChab:
      "There are unresolved neighbourhoods.";
    _,toquo:=quo<Domain(MWmap)|
     [p^kerlev*g:g in OrderedGenerators(Kernel(fibp[1]))]>;
    newtup:=<toquo,{toquo(a):a in nogos}>;
  end if;
  return NrPoints,MWfib,IDX,newtup;
end intrinsic;
