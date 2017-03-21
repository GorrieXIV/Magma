freeze;

/***** (11) OTHER BUILT-IN LSER SIGNATURES *****/

import "Lseries.m" : DefaultCfGrowth;
lcf_list           := 0;
lcf_localfactors   := 1;
lcf_function       := 2;

intrinsic LSeries
(HS::HodgeStruc,N::RngIntElt,cffun::. :
 Sign:=0,Poles:=[],Residues:=[],Parent:=false,Name:="unknown origin",
 CoefficientGrowth:=DefaultCfGrowth,Precision:=0,ImS:=0,Asymptotics:=true)
 -> LSer {"} //"
 return LSeries(1+HS`w,GammaFactors(HS),N,cffun :
		Sign:=Sign,Poles:=Poles,Residues:=Residues,Parent:=Parent,
		Name:=Name,CoefficientGrowth:=CoefficientGrowth,
		Precision:=Precision,ImS:=ImS,Asymptotics:=true);
  end intrinsic;


intrinsic Conductor(L:: LSer) -> .
{Conductor of an L-series} return L`conductor; end intrinsic;

intrinsic GammaFactors(L:: LSer) -> SeqEnum
{Gamma factors of an L-series} return L`gamma; end intrinsic;

intrinsic Sign(L:: LSer) -> .
{Sign of an L-series, 0 if not computed yet (use CheckFunctionalEquation then)}
 return L`sign; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic HodgeStructure(f::ModFrmElt) -> HodgeStruc
{The HodgeStructure of a modular form}
 require IsZero(EisensteinProjection(f)): "Modular form must be cuspidal";
 w:=Weight(f); require IsIntegral(w): "Weight must be integral";
 require Type(w) eq RngIntElt and w gt 1: "Weight must be greater than one";
 return HodgeStructure([<0,w-1>,<w-1,0>]); end intrinsic;

intrinsic LSeries(M::ModSym : Precision:=0) -> LSer
{The LSeries attached to a 1-dimensional cuspidal modular symbol space.
 No checks for newness or Hecke stability are made.}
 require Dimension(M) eq 1: "Space must be 1-dimensional";
 require IsCuspidal(M): "Space must be cuspidal"; N:=Level(M); w:=Weight(M);
  function cf(p,d) T:=PolynomialRing(Rationals()).1;
   ap:=DualHeckeOperator(M,p)[1][1];
   return 1-ap*T+DirichletCharacter(M)(p)*p^(w-1)*T^2; end function;
 return LSeries(w,[0,1],N,cf : Parent:=M, Precision:=Precision); end intrinsic;

intrinsic LSeries(f::ModFrmElt : Embedding:=0, Precision:=0) -> LSer
{L-series associated to a modular form f, assuming that it satisfies
 the standard functional equation.
 Embedding (default identity) gives an embedding of the coefficients
 of f into the complex numbers and must be either a Map or a name e
 of a function e(x) that does it.}
             
  require IsZero(EisensteinProjection(f)): "Modular form must be cuspidal";
  require IsIntegral(Weight(f)) and Weight(f) ge 2: "Weight must be >=2 in Z";
  B:=BaseRing(f); basetype:=Type(B);
  if (Embedding cmpeq 0) then
    if ISA(basetype,FldNum) or ISA(basetype,RngOrd) 
      then error "For f over a number field, "*
                 "you have to specify a complex embedding";
    else Embedding:=func<x|x>; embed:=false; end if; else embed:=true; end if;
  
  if Type(Embedding) eq Map then
    require Domain(Embedding) cmpeq B:
      "Domain(Embedding) must equal to BaseRing(f)";
    Embedding:=func<x|Embedding(x)>; end if;

  if Coefficient(f,0) cmpeq 0 then  poles:=[];  residues:=[];
  else poles:=[0];
    residues:=
      func<p|[2*Sqrt(Pi(RealField(p)))*ComplexField(p)!Coefficient(f,0)]>;
  end if;
  L := LSeries(Weight(f),[0,1],Level(f),
	       func<k|Embedding(Coefficient(f,k))>: Poles:=poles, 
	       Residues:=residues, Parent:=f, Precision:=Precision);
  L`embed:=embed; return L; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic RiemannZeta( : Precision:=0) -> LSer
{L-series associated to the Riemann zeta function}
  P:=PolynomialRing(Integers()); x:=P.1;
  return LSeries(1,[0],1,func<p,d|1-x> : Name:="Riemann zeta function",
		 Poles:=[1], Residues:=[-1], Sign:=1,
		 Precision:=Precision, Parent:=Rationals()); end intrinsic;

intrinsic LSeries
(K::FldRat: Precision:=0, ClassNumberFormula:=false, Method:="Default") -> LSer
{The Riemann zeta-function in a different guise}
 return RiemannZeta(:Precision:=Precision); end intrinsic;

intrinsic LSeries(K::FldNum :
		  Precision:=0, ClassNumberFormula:=false, Method:="Default")
  -> LSer
{Dedekind zeta function of a number field K/Q}
  require Method in ["Direct","Artin","Default"]:
    "Method must be \"Direct\", \"Artin\" or \"Default\"";
  if AbsoluteDegree(K) eq 1 then
    return RiemannZeta(: Precision:=Precision);
  end if;
  if (Method eq "Artin") or (Method eq "Default")  then
    _:=ArtinRepresentations(K); // not to inherit ComputeArtinRepresentations
       //ComputeArtinRepresentations(~K);
    rep:=PermutationCharacter(K);
    L:=LSeries(rep: Precision:=Precision);
    L`parent:=K; //?
    L`name:=K; P:=PolynomialRing(Integers()); x:=P.1;
    L`condK:=1*IntegerRing(K);
    L`cffuncK:=func<P,d : Precision:=0 | (1-x^Degree(P))>; L`degreeK:=<1,K>;
    L`hodgeK:=[<[0,0,0],ip> : ip in InfinitePlaces(K)];
    return L;
  end if;
  M:=MaximalOrder(K);
  r1,r2:=Signature(K);
  gamma:=[0: k in [1..r1+r2]] cat [1: k in [1..r2]];
  disc:=Abs(Discriminant(M));

  // Regulator _always_ seems to work to precision 28,
  // so for higher precision return [] anyway
  if ClassNumberFormula then
    h:=#ClassGroup(M);
    mu:=#TorsionSubgroup(UnitGroup(M));
    /* r:=func<prec|prec gt 28 select [] else
       [-2^(r1+r2)*Pi(R)^(r2/2)*R!Regulator(K)*h/mu]
       where R is RealField(prec)>; */
    function r(prec) R:=RealField(prec); op:=GetKantPrecision();
     SetKantPrecision(prec); A:=[-2^(r1+r2)*Pi(R)^(r2/2)*Regulator(K)*h/mu];
     SetKantPrecision(op); return A; end function;
  else
    r:=[];
  end if;

  P:=PolynomialRing(Integers()); x:=P.1;
  cf:=func<p,d|&*[1-x^Degree(k[1]): k in Decomposition(M,p)]>;
  L:=LSeries(1, gamma, disc, cf:
	     Parent:=K, Poles:=[1], Residues:=r, Sign:=1,Precision:=Precision);
  L`cffuncK:=func<P,d : Precision:=0 | (1-x^Degree(P))>; L`degreeK:=<1,K>;
  L`condK:=1*IntegerRing(K);
  L`hodgeK:=[<[0,0,0],ip> : ip in InfinitePlaces(K)];
  return L;
end intrinsic;

////////////////////////////////////////////////////////////////////////

function LSeries_E_Q(E: Precision:=0)           // Elliptic curves over Q
  N:=Conductor(E);
  P:=PolynomialRing(Integers()); x:=P.1;
  cf:=
    func<p,d|1-FrobeniusTraceDirect(E,p)*x+(N mod p ne 0 select p else 0)*x^2>;
  return LSeries(2,[0,1],N,cf :
		 Parent:=E, Sign:=RootNumber(E), Precision:=Precision);
end function;

function LSeries_E_NF(E: Precision:=0)   // Elliptic curves over number fields
  K:=BaseField(E);
  O:=IntegerRing(K);
  N:=Conductor(E);
  Sign:=RootNumber(E);
  NQ:=Abs(AbsoluteNorm(N));
  d:=AbsoluteDegree(K);
  gammas:=[0: i in [1..d]] cat [1: i in [1..d]];
  R:=PolynomialRing(Rationals()); x:=R.1;
  D:=Discriminant(E);
  D:=Integers()!(AbsoluteNorm(Numerator(D))*Denominator(D));
  a1,a2,a3,a4,a6:=Explode(aInvariants(E));
  denom:=LCM([Denominator(a) : a in aInvariants(E)]);

  function locPgen(P,p,d)
    locinf,EM:=LocalInformation(E,P);
    a1,a2,a3,a4,a6:=Explode(aInvariants(EM));
    cond:=locinf[3];
    F,m:=ResidueClassField(P);
    q:=#F;
    if q gt p^d then return R!1; end if;
    _,p,f:=IsPrimePower(q);
    if cond gt 1 then return R!1; end if;    // additive
    if cond eq 1 then                        // multiplicative
      return 1-((#Roots(PolynomialRing(F)![1,m(a1),m(-a2)]) ne 0)
         select 1 else -1)*x^f;              // split/nonsplit
    end if;
    ap:=q+1-#EllipticCurve([F|m(a1),m(a2),m(a3),m(a4),m(a6)]);
    return 1-ap*x^f+q*x^(2*f); // good reduction, original model was bad
  end function;

  function locPgood(P,p,d)
    F,m:=ResidueClassField(P);
    q:=#F;
    if q gt p^d then return R!1; end if;
    _,p,f:=IsPrimePower(q);
    ap:=q+1-#EllipticCurve([F|m(a1),m(a2),m(a3),m(a4),m(a6)]);
    return 1-ap*x^f+q*x^(2*f);
  end function;

  function loc(p,d)
    return (D mod p ne 0) and (denom mod p ne 0)
      select &*[R!locPgood(Ideal(P[1]),p,d): P in AbsoluteDecomposition(K,p)]
      else   &*[R!locPgen(Ideal(P[1]),p,d):  P in AbsoluteDecomposition(K,p)];
  end function;


  L:=LSeries(2,gammas,NQ*AbsoluteDiscriminant(O)^2,loc:
	     Parent:=E, Precision:=Precision, Sign:=Sign);
  L`degreeK:=<2,K>; L`condK:=Conductor(E);
  L`cffuncK:=
    function(P,d : Precision:=0) _,p:=IsPrimePower(Norm(P));
     return (D mod p ne 0) select R!locPgood(P,p,d) else R!locPgen(P,p,d);
    end function;
  L`hodgeK:=&cat[[<[0,1,2],ip>,<[1,0,2],ip>] : ip in InfinitePlaces(K)];
  return L;
end function;


intrinsic LSeries(E::CrvEll : Precision:=0) -> LSer
{L-series associated to an elliptic curve over Q or over a number field}
  K:=BaseRing(E);
  if K cmpeq Rationals() then 
    return LSeries_E_Q(E: Precision:=Precision); 
  end if;
  if ISA(Type(K),FldNum) then 
    a:=aInvariants(E);
    if forall{x: x in a | IsCoercible(Rationals(),x)} then
      a:=[Rationals()!x: x in a];
      L:=LSeries(EllipticCurve(a),K: Precision:=Precision);
         LC:=LSeries_E_NF(E: Precision:=Precision); // kludge to get K-info
         L`degreeK:=LC`degreeK; L`cffuncK:=LC`cffuncK; L`hodgeK:=LC`hodgeK;
         L`condK:=Conductor(E);
      return L;
       // If E is base changed from Q, then LSeries(E,K) is much faster
       // (no point counting over GF(p^n) for n>1)
    end if;
    return LSeries_E_NF(E: Precision:=Precision); 
  end if;
  error "Elliptic curve must be defined over Q or a number field"; 
end intrinsic;


intrinsic LSeries
(E::CrvEll[FldRat], K::FldNum : Method:="Default", Precision:=0) -> LSer
{L-series associated to an elliptic curve E/Q base changed to a number field K}
  require Method in ["Direct","Artin","Default"]:
    "Method must be \"Direct\", \"Artin\" or \"Default\"";

  Artin := Method in ["Artin","Default"];  // Default is currently Artin

  NE:=Conductor(E);
  EK:=BaseChange(E,K);

  if Artin then
    L:=LSeries(E,PermutationCharacter(K): Precision:=Precision);
    if Sign(L) eq 0 then L`sign:=RootNumber(EK); end if;
    L`name:=<E," base changed to ",K>;
    return L;
  end if;

  M:=MaximalOrder(K);
  KDisc:=Discriminant(M);
  R:=PolynomialRing(Integers()); x:=R.1;
  NEK:=Norm(Conductor(EK))*Discriminant(M)^2;

  ExcFactors:=[];
  for p in PrimeDivisors(NEK) do
    plocal:=R!1;
    for Q in Decomposition(M,p) do
      P:=Q[1];
      info,model:=LocalInformation(EK,P);
      _,vpd,fp,cp,kod:=Explode(info);
      if fp eq 0 then                        // good reduction 
        Plocal:=1-TraceOfFrobenius(Reduction(model,P))*x+p^Degree(P)*x^2;
        vprint LSeries,1: "Prime P above "*Sprint(p)*
          ": good reduction, local factor "*Sprint(Plocal);
      elif kod ne KodairaSymbol("In") then   // additive reduction   
        Plocal:=1;
        vprint LSeries,1: "Prime P above "*Sprint(p)*
          ": additive reduction, v(disc)="*Sprint(vpd)*
          ", v(cond)="*Sprint(fp)*", c_p="*Sprint(cp);
      else                                   // multiplicative reduction
        c4,c6:=Explode(cInvariants(model));
        _,h:=Completion(K,P);
        split:=IsSquare(h(-c6));             // split/non-split
        Plocal:=split select 1-x else 1+x;
        vprint LSeries,1: "Prime P above "*Sprint(p)*": "*
          (split select "split" else "non-split")*
          " multiplicative reduction, local factor="*Sprint(Plocal);
      end if;
      plocal*:=Evaluate(R!Plocal,x^Degree(P));
    end for;
    cond:=Valuation(NEK,p);
    Append(~ExcFactors,<p,cond,plocal>);
  end for;

  vprint LSeries,2:
  "Now calling TensorProduct(E,K) with exceptional local factors";
  vprint LSeries,2: ExcFactors;

  L:=TensorProduct
    (LSeries(E),LSeries(K),ExcFactors:
     Sign:=RootNumber(BaseChange(E,K)), Precision:=Precision);
  L`name:=<E," base changed to ",K>;
  return L;

end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic LSeries(Chi::GrpDrchElt : Precision:=0) -> LSer
{L-series associated to a Dirichlet character Chi: (Z/mZ)^* to C^*}
 if Conductor(Chi) eq 1 then
  L:=RiemannZeta(:Precision:=Precision); return L; end if;
 require PrimeDivisors(Modulus(Chi)) eq PrimeDivisors(Conductor(Chi)):
   "Modulus(Chi) and Conductor(Chi) must have the same prime divisors";
 require Type(BaseRing(Parent(Chi))) in
   [FldCyc,RngInt,FldRat,FldRe,FldCom]:
   "Character must take values in Z, a cyclotomic field, real or complexes";
 precision:=Precision gt 0 select Precision else GetPrecision(0.5);
 if Order(Chi) eq 2 then cf:=func<n:Precision:=precision|Integers()!Chi(n)>;
 else cf:=func<n:Precision:=precision|ComplexField(Precision)!Chi(n)>; end if;
 return LSeries(1,[Real(Chi(-1)) gt 0 select 0 else 1],Conductor(Chi),cf:
		Parent:=Chi, Precision:=precision); end intrinsic;

intrinsic HodgeStructure(chi::GrpDrchElt) -> HodgeStruc
{HodgeStructure associated to a Dirichlet character Chi: (Z/mZ)^* to C^*}
 require PrimeDivisors(Modulus(chi)) eq PrimeDivisors(Conductor(chi)):
   "Modulus(chi) and Conductor(chi) must have the same prime divisors";
 require Type(BaseRing(Parent(chi))) in
   [FldCyc,RngInt,FldRat,FldRe,FldCom]:
   "Character must take values in Z, a cyclotomic field, real or complexes";
 return HodgeStructure([<0,0,chi(-1) eq 1 select 0 else 1>]);  end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Degree(L::LSer) -> RngIntElt
{Given an L-series, return its degree}
 return #L`gamma; end intrinsic;

intrinsic MotivicWeight(L::LSer) -> RngIntElt
{Given an L-series, return its motivic weight}
 return L`weight-1; end intrinsic;

intrinsic CentralValue(L::LSer) -> FldComElt
{Given an L-series of odd motivic weight, compute the central value}
 require IsCoercible(Integers(),L`weight) : "Weight must be integral";
 require (Integers()!L`weight) mod 2 eq 0: "Weight of L-series must be even";
 return Evaluate(L,(Integers()!L`weight) div 2); end intrinsic;

intrinsic Translate(L::LSer,z::RngIntElt : Precision:=L`precision) -> LSer
{Given an L-series, translate it by the rational number z}
 return Translate(L,Rationals()!z : Precision:=Precision); end intrinsic;

intrinsic Translate(L::LSer,z::FldRatElt : Precision:=L`precision)->LSer {"}//"
 if IsOne(L) then return L; end if;
 if z eq 0 and Precision eq L`precision then return L; end if;
 // if L itself is a translation, then don't layer it on?
 if L`prod cmpne false then
  return LProduct([<Translate(l[1],z : Precision:=Precision),l[2]> :
			       l in L`prod] : Precision:=Precision); end if;
 name:=<"Translation by ",z," of ",L>;
 wt:=L`weight+2*z; G:=[g-z : g in L`gamma];
 prec:=Precision; P:=[p+z : p in L`lpoles];
 R:=[r*(Conductor(L)/Pi(RealField(prec))^(Degree(L)))^(z/2): r in L`lresidues];
 function f(p,d : Precision:=prec)
  poly:=Polynomial(Coefficients(EulerFactor(L,p : Degree:=d)));
  BR:=BaseRing(Parent(poly));
  if Type(BR) in {FldRat,RngInt} and Denominator(z) eq 1 then
   R:=BR; zz:=Integers()!z; else R:=ComplexField(Precision); zz:=z; end if;
  T:=PowerSeriesRing(R,1+d).1; return Evaluate(poly,T*p^zz); end function;
 if IsCoercible(Integers(),wt) then wt:=Integers()!wt; end if;
 return LSeries(wt,G,Conductor(L),f :
		Name:=name,Parent:=L,Precision:=prec,
		Sign:=L`sign,Poles:=P,Residues:=R); end intrinsic;
