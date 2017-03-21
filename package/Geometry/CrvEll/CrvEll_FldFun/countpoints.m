freeze;

//////////////////////////////////////////////////////////////////
//                                                              //
//  Some function related to point counting and L-functions     //
//          for elliptic curves over function fields            //
//                                                              //
//                         Februari 2006                        //
//                                                              //
//////////////////////////////////////////////////////////////////


/***********     CHANGES LOG      ********************************

   July 2006 (pre-release), Steve:
     * Supplied several forgotten universes
       (only some of these had caused bugs)
   July 2006, Jasper:
     * Excluded constant curves from LFunction
   July 23, 2006, Jasper:
     * Corrected a bug in FrobeniusActionOnReducibleFiber
   Juli 30, 2006, Jasper:
     * Speedup of LFunction in certain cases
   Aug 4, 2006, Jasper:
     * Corrected a bug in PowerPolynomial
   Oct 19, 2006, Jasper:
     * Corrected a bug in LFunction, which affected the computation of LFunctions of degree 1
   June 2014, Mike:
     * Fixed complex root computation for (reverse) charpoly possibilities in
       LFunction and added test (of absolute values of roots) that should remove
       the need for final point count in most cases.

******************************************************************/

declare attributes CrvEll:
   LFunction;


intrinsic CharacteristicPolynomialFromTraces(traces::SeqEnum) -> RngUPolElt
  { Reciprocal characteristic polynomial from traces of 
    powers of Frobenius}
  d:=#traces;
  if Type(Universe(traces)) eq RngInt then
    R:=Rationals();
  else 
    R:=Universe(traces);
  end if;
  K := PolynomialRing(R); T := K.1;
  sumtrace:=&+[K| -traces[i]/i*T^i : i in [1..d]];
  lfunction:=K!1;
  sumtracepower:=K!1;  
  for i in [1..d] do
    sumtracepower:=sumtracepower*sumtrace/i mod T^(d+1);
    lfunction+:=sumtracepower;
  end for;
  return lfunction;
end intrinsic;


intrinsic CharacteristicPolynomialFromTraces(traces::SeqEnum, d::RngIntElt, q::RngIntElt, i::RngIntElt) -> RngUPolElt, RngUPolElt
  { Degree d reciprocal characteristic polynomials with zeroes of absolute value
    q^(i/2) from traces of powers of Frobenius. If there are two possible signs of the
    constant coefficient, then it lists both possibilities. Otherwise it lists the polynomial 
    twice. }
  lfunctionhalf:=CharacteristicPolynomialFromTraces(traces);
  K<T>:=Parent(lfunctionhalf);
  n:=#traces;
  require 2*n ge d-1 :
    "Not enough traces given";

  lfunction1:=T^(d-n)*(K![-q^((i*d div 2)-i*k)*Coefficient(lfunctionhalf,k) : k in [n..0 by -1]]);
  comp1:=&and[Coefficient(lfunctionhalf,k) eq Coefficient(lfunction1,k) : k in [d-n..n]];
  lfunction1+:=K![Coefficient(lfunctionhalf,k) : k in [0..d-n-1]];
  lfunction2:=T^(d-n)*(K![q^((i*d div 2)-i*k)*Coefficient(lfunctionhalf,k) : k in [n..0 by -1]]);
  comp2:=&and[Coefficient(lfunctionhalf,k) eq Coefficient(lfunction2,k) : k in [d-n..n]];
  lfunction2+:=K![Coefficient(lfunctionhalf,k) : k in [0..d-n-1]];
  error if not (comp1 or comp2) , "Given traces not compatible";

  case [comp1,comp2] :
  when [true,true]  : return lfunction1,lfunction2;
  when [false,true] : return lfunction2,lfunction2;
  when [true,false] : return lfunction1,lfunction1;
  end case;
end intrinsic


intrinsic ReciprocalPolynomial(poly::RngUPolElt) -> RngUPolElt
  { Reciprocal of a univariate polynomial }
  return Parent(poly) ! Reverse(Eltseq(poly));
end intrinsic;


function CardinalityOfSingularFiber(locinfo,q,e)
  // locinfo is the 5- or 6-tuple output of LocalInformation.
  // Fiber is not allowed to have KodairaType I0
  qe:=q^e;
  case locinfo[5]:
  when KodairaSymbol("In"):
    return locinfo[6] or IsEven(e) select locinfo[2]*qe else locinfo[4]*qe+2;  // distinction between split/nonsplit
  when KodairaSymbol("IV"):
    return IsEven(e) select 3*qe+1 else locinfo[4]*qe+1; 
  when KodairaSymbol("I0*"):
    case locinfo[4]:
    when 1:
      return IsDivisibleBy(e,3) select 5*qe+1 else 2*qe+1;
    when 2:
      return IsEven(e) select 5*qe+1 else 3*qe+1;
    else 
      return 5*qe+1;
    end case;
  when KodairaSymbol("In*"):
    n:=0;     // Determine the n from In* in an ugly way...
    repeat n+:=1;
    until KodairaSymbol("I" cat IntegerToString(n) cat "*") eq locinfo[5];
    return IsEven(e) select (n+5)*qe+1 else (n+1+locinfo[4])*qe+1;
  when KodairaSymbol("IV*"):
    return IsEven(e) select 7*qe+1 else 2*locinfo[4]*qe+qe+1;
  when KodairaSymbol("III*"):
    return 8*qe+1;
  when KodairaSymbol("II*"):
    return 9*qe+1;
  else   // Types II or III
    return locinfo[4]*qe+1;
  end case;
end function;



intrinsic FrobeniusActionOnReducibleFiber(locinfo::Tup) -> AlgMatElt
  { Given LocalInformation, computes the matrix representing the Frobenius action 
    on the non-identy components of a reducible fiber}
  
  case locinfo[5]:
  when KodairaSymbol("In"):
    if locinfo[4] gt 2 then 
      M:=IdentityMatrix(Integers(),locinfo[4]-1);
    else
      n:=NumberOfComponents(locinfo[5])-1;
      M:=DirectSum(IdentityMatrix(Integers(),n mod 2),
                   TensorProduct(IdentityMatrix(Integers(),n div 2),Matrix(2,[0,1,1,0])));
    end if;
  when KodairaSymbol("IV"):
    M:=locinfo[4] eq 1 select Matrix(2,[0,1,1,0]) else Matrix(2,[1,0,0,1]);
  when KodairaSymbol("I0*"):
    case locinfo[4]:
    when 1: M:=DirectSum(Matrix(1,[1]),Matrix(3,[0,1,0,0,0,1,1,0,0]));
    when 2: M:=DirectSum(Matrix(2,[1,0,0,1]),Matrix(2,[0,1,1,0]));
    when 4: M:=IdentityMatrix(Integers(),4);
    end case;
  when KodairaSymbol("In*"):
    n:=NumberOfComponents(locinfo[5])-1;
    M:=locinfo[4] eq 4 select
         IdentityMatrix(Integers(),n)
       else
         DirectSum(IdentityMatrix(Integers(),n-2),Matrix(2,[0,1,1,0]));
  when KodairaSymbol("IV*"):
    M:=locinfo[4] eq 3 select
         IdentityMatrix(Integers(),6)
       else
         DirectSum(Matrix(2,[1,0,0,1]),TensorProduct(Matrix(2,[1,0,0,1]),Matrix(2,[0,1,1,0])));
  else    // Always trivial galois action on components
    n:=NumberOfComponents(locinfo[5])-1;
    M:=IdentityMatrix(Integers(),n);
  end case;
  d:=Degree(locinfo[1]);
  if d eq 1 then
    return M;
  else
    n:=NumberOfRows(M);
    M1:=VerticalJoin(ZeroMatrix(Integers(),n,(d-1)*n),IdentityMatrix(Integers(),(d-1)*n));
    M2:=VerticalJoin(M,ZeroMatrix(Integers(),(d-1)*n,n));
    return HorizontalJoin(M1,M2);
    // return TensorProduct(PermutationMatrix(Integers(),CyclicGroup(d).1),M);
  end if;
end intrinsic;


intrinsic FrobeniusActionOnTrivialLattice(E::CrvEll[FldFunRat]) -> AlgMatElt
  { Matrix representing the Frobenius action on the sublattice of Neron Severi group 
    of elliptic surface that is generated by fiber components and zero section}
  M:=Matrix(2,[1,0,0,1]);  // action on fiber and zero section
  K<t>:=BaseRing(E);
  factoren:=&join[{K!b[1]} : b in Factorisation(Denominator(a)), a in aInvariants(E)];
  factoren join:=&join[{K!b[1]} : b in Factorisation(Numerator(Discriminant(E)))];
  factoren join:={1/t};
  for f in factoren do
    locinfo:=LocalInformation(E,f);
    M:=DirectSum(M,FrobeniusActionOnReducibleFiber(locinfo));
  end for;
  return M;
end intrinsic;


//////////////////////////////////////////////////////////
// TO DO:                                               //
// FrobeniusActionOnTrivialLattice(E::CrvEll[FldFun])   //
// FOR GENERAL FUNCTION FIELDS                          //
//////////////////////////////////////////////////////////




intrinsic BettiNumber(E::CrvEll[FldFunG], i::RngIntElt) -> RngIntElt
  { i-th Betti number of elliptic surface}
  k:=AbsoluteValue(i-2);
  K:=BaseRing(E);
  case k:
  when 0: 
    lis:=LocalInformation(E);
    if IsZero(#lis) then   // test whether surface is constant
      return 4*Genus(K)+2;
    else
      eulerchar:=&+[ Integers() | Degree(li[1])*li[2] : li in lis];
      return eulerchar-2+2*Genus(K);
    end if;
  when 1:
    lis:=LocalInformation(E);
    if IsZero(#lis) then   // test whether surface is constant
      return 2+2*Genus(K);
    else
      return Genus(K);
    end if;
  when 2: 
    return 1;
  else 
    return 0;
  end case;
end intrinsic;


intrinsic NumbersOfPointsOnSurface(E::CrvEll[FldFun], e::RngIntElt) -> SeqEnum,SeqEnum
{}
  K:=BaseRing(E);
  q:=#BaseField(CoefficientRing(K));
  inf:=InfinitePlaces(K);
  nopc:=[0 : i in [1..e]];
  nops:=nopc;

  factoren:=&join[SequenceToSet(Poles(a)): a in aInvariants(E)| not IsZero(a)];
  factoren join:=SequenceToSet(Zeroes(Discriminant(E)));


  for place in inf do
    deg:=Degree(place); 
    if deg le e then
      discr:=true;  // indicates good reduction
      if place in factoren then
        locinfo,C:=LocalInformation(E,place);
        discr:=IsZero(locinfo[2]);
        if discr then 
          Ep:=EllipticCurve([Evaluate(ai,place) : ai in aInvariants(C)]);
        end if;
      else
        Ep:=EllipticCurve([Evaluate(ai,place) : ai in aInvariants(E)]);
      end if;

      for i in [1..(e div deg)] do 
        nopc[i*deg]+:=deg; 
        nops[i*deg]+:=discr select 
            deg*(#ChangeRing(Ep,ext<BaseRing(Ep) | i>))
          else
            deg*CardinalityOfSingularFiber(locinfo,q^deg,i);
      end for;
    end if;
  end for;

  L:=PlaceEnumInit(K);
  place:=PlaceEnumNext(L);
  repeat
    
    deg:=Degree(place);
    if deg le e then

      discr:=true;  // indicates good reduction
      if place in factoren then
        locinfo,C:=LocalInformation(E,place);
        discr:=IsZero(locinfo[2]);
        if discr then 
          Ep:=EllipticCurve([Evaluate(ai,place) : ai in aInvariants(C)]);
        end if;
      else
        Ep:=EllipticCurve([Evaluate(ai,place) : ai in aInvariants(E)]);
      end if;


      for i in [1..(e div deg)] do 
        nopc[i*deg]+:=deg; 
        nops[i*deg]+:=discr select 
            deg*(#ChangeRing(Ep,ext<BaseRing(Ep) | i>))
          else
            deg*CardinalityOfSingularFiber(locinfo,q^deg,i);
      end for;
    
    end if;
    place:=PlaceEnumNext(L);
  until PlaceEnumPosition(L)[1] gt e;

  return nops,nopc;
end intrinsic;


intrinsic NumbersOfPointsOnSurface(E::CrvEll[FldFunRat], e::RngIntElt) -> SeqEnum,SeqEnum
{A sequence containing the numbers of points on the Kodaira-Neron model of E over the 
field extensions of degrees 1 up to e, and sequence containing the numbers of points 
the base curve over the same fields.}

  K<t>:=BaseRing(E);
  F:=CoefficientRing(K);

  require Type(F) eq FldFin :
    "Elliptic Surface not defined over a Finite Field";
  q:=#F;
 
  badred:=LCM([Denominator(ai) : ai in aInvariants(E)] cat [Numerator(Discriminant(E))]);

  nopc:=[0 : i in [1..e]];
  nops:=nopc;

  for deg in [1..e] do


    Fe:=ext<F | deg>;
    qem1:=#Fe-1;
    u:=PrimitiveElement(Fe);
    v:=Fe!1;
    for ii in [1..qem1] do
      v*:=u;
      orbit:=[ii*q^tt mod qem1 : tt in [0..deg-1]];
     
      if (orbit[1] eq Min(orbit)) and 
         not (orbit[1] in [orbit[tt] : tt in [2..#orbit]]) then 
         discr:=true;  // indicates good reduction
         if IsZero(Evaluate(badred,v)) then 
           locinfo,C:=LocalInformation(E,K!MinimalPolynomial(v,F));
           discr:=IsZero(locinfo[2]);
           if discr then 
             Ep:=EllipticCurve([Evaluate(ai,v) : ai in aInvariants(C)]);
           end if;
         else
           Ep:=EllipticCurve([Evaluate(ai,v) : ai in aInvariants(E)]);
         end if;
         for i in [1..(e div deg)] do 
           nopc[i*deg]+:=deg; 
           nops[i*deg]+:=discr select 
             deg*(#ChangeRing(Ep,ext<BaseRing(Ep) | i>))
           else
             deg*CardinalityOfSingularFiber(locinfo,q^deg,i);
         end for;
      end if;
    end for;
  end for;


// count points above 0 and infinity

  for place in [t,1/t] do
    EE:=EllipticCurve([Evaluate(ai,place) : ai in aInvariants(E)]);
    locinfo,C:=LocalInformation(EE,t);
    discr:=IsZero(locinfo[2]);
    if discr then 
      Ep:=EllipticCurve([Evaluate(ai,0) : ai in aInvariants(C)]);
    end if;
    for i in [1..e] do 
      nopc[i]+:=1; 
      nops[i]+:=discr select 
           #ChangeRing(Ep,ext<BaseRing(Ep) | i>)
         else
           CardinalityOfSingularFiber(locinfo,q,i);
    end for;
  end for;

  return nops,nopc;
end intrinsic;


//still need to do this function

intrinsic NumberOfPointsOnSurface(E::CrvEll[FldFunRat], e::RngIntElt) -> RngIntElt
{The number of points on the Kodaira-Neron model of E over the constant field extension 
of degree e. }

  K<t>:=BaseRing(E);
  F:=CoefficientRing(K);

  require Type(F) eq FldFin :
    "Elliptic Surface not defined over a Finite Field";
  q:=#F;
 
  badred:=LCM([Denominator(ai) : ai in aInvariants(E)] cat [Numerator(Discriminant(E))]);

  nops:=0;

  reqdegs:=Divisors(e);

  for deg in reqdegs do

    
       // count point over extension of degree deg
      Fe:=ext<F | deg>;
      qem1:=#Fe-1;
      u:=PrimitiveElement(Fe);
      v:=Fe!1;
      for ii in [1..qem1] do
        v*:=u;
        orbit:=[ii*q^tt mod qem1 : tt in [0..deg-1]];
     
        if (orbit[1] eq Min(orbit)) and 
           not (orbit[1] in [orbit[tt] : tt in [2..#orbit]]) then 
           discr:=true;  // indicates good reduction
           if IsZero(Evaluate(badred,v)) then
             locinfo,C:=LocalInformation(E,K!MinimalPolynomial(v,F));
             discr:=IsZero(locinfo[2]);
             if discr then 
               Ep:=EllipticCurve([Evaluate(ai,v) : ai in aInvariants(C)]);
             end if;
           else
             Ep:=EllipticCurve([Evaluate(ai,v) : ai in aInvariants(E)]);
           end if;
           nops+:=discr select 
             deg*(#ChangeRing(Ep,ext<BaseRing(Ep) | e div deg>))
           else
             deg*CardinalityOfSingularFiber(locinfo,q^deg, e div deg);
        end if;
      end for;
    
  end for;


// count points above 0 and infinity


  for place in [t,1/t] do
    EE:=EllipticCurve([Evaluate(ai,place) : ai in aInvariants(E)]);
    locinfo,C:=LocalInformation(EE,t);
    discr:=IsZero(locinfo[2]);
    if discr then 
      Ep:=EllipticCurve([Evaluate(ai,0) : ai in aInvariants(C)]);
    end if;
    nops+:=discr select 
         #ChangeRing(Ep,ext<BaseRing(Ep) | e>)
       else
         CardinalityOfSingularFiber(locinfo,q,e);
  end for;


  return nops;
end intrinsic;

intrinsic LFunction(E::CrvEll[FldFunRat]) -> RngUPolElt
  { L-Function of E. }
  return LFunction(E,[E|]);
end intrinsic;

intrinsic LFunction(E::CrvEll[FldFunRat],s::SeqEnum : Check:=true)
                                                            -> RngUPolElt
{L-Function of E. To speed up the compution, points in s are used to
reduce the unknown part of H^2. If the parameter Check is false, then the
points in s must form a basis for a subgroup of the geometric Mordell-Weil
group modulo torsion that is stable under Galois action.}

  require not IsConstantCurve(E) :
    "Curve is a constant curve. This case is not yet implemented";

  if assigned E`LFunction then
     return E`LFunction;
  end if;



  if IsZero(#s) then
     Check:=false;
  end if;

  if Check then
     q:=#CoefficientRing(BaseRing(E));
     s2:=[Universe(s)|];
     for P in s do
        Q:=P;
        repeat
          if (not Q in s2) and (not -Q in s2) then Append(~s2,Q); end if;
          Q:=Frobenius(Q,q);
        until P eq Q;
     end for;
     s,gram:=Basis(s2);
  end if;

  h2:=BettiNumber(E,2);
  q:=#CoefficientRing(BaseRing(E));
  if assigned E`GeometricMordellWeilLattice then
     geom:=E`GeometricMordellWeilLattice;
     s:=[geom[2](x) : x in Basis(geom[1])];
  end if;
  if Check then
     Mknown:=FrobeniusActionOnPoints(s,q,gram);
  else
     Mknown:=FrobeniusActionOnPoints(s,q);
  end if;
  Lknown:=CharacteristicPolynomial(Mknown);
  Lknown*:=Sign(Coefficient(Lknown,0));
  Lknownq:=Evaluate(Lknown,q*Parent(Lknown).1);
  M:=DirectSum(ChangeRing(FrobeniusActionOnTrivialLattice(E),Rationals()),Mknown);
  d:=h2-NumberOfRows(M);
  nop:=NumbersOfPointsOnSurface(E,Floor(d/2));
  traces:=[nop[i]-1-q^(2*i)-q^i*Trace(M^i) : i in [1..Floor(d/2)]];
  if IsZero(#traces) then
     charpoly1,charpoly2:=CharacteristicPolynomialFromTraces([Rationals()|],d,q,2);
  else
     charpoly1,charpoly2:=CharacteristicPolynomialFromTraces(traces,d,q,2);
  end if;

  if charpoly1 ne charpoly2 then

    // Sign of functional equation not yet determined.

    // First try to determine the sign with the Artin-Tate formula
    // and the fact that cardinality of sha is a square

    aninfo1:=AnalyticInformation(E,charpoly1*Lknownq);
    if IsZero(aninfo1[1]) and not IsSquare(aninfo1[3]) then
         E`LFunction:= charpoly2*Lknownq;
         return charpoly2*Lknownq;
    else
         aninfo2:=AnalyticInformation(E,charpoly2*Lknownq);
         if IsZero(aninfo2[1]) and not IsSquare(aninfo2[3]) then
            E`LFunction:= charpoly1*Lknownq;
            return charpoly1*Lknownq;
         end if;
    end if;

    // Sign not yet determined. Need to count points over larger field.

    coefs1:=[(-1)^i*Eltseq(charpoly1)[i+1] : i in [1..d]];
    coefs2:=[(-1)^i*Eltseq(charpoly2)[i+1] : i in [1..d]];
    i:=Ceiling(d/2);
    while coefs1[i] eq 0 do i+:=1; end while;

    cpols := [cp*Lknownq : cp in [charpoly1,charpoly2]];
    RC:=PolynomialRing (ComplexField());
    r1 := &cat[[<r[1],fac[2]> : r in Roots(RC!(fac[1]))] : fac in
		Factorisation(ReciprocalPolynomial(charpoly1))];
    r2 := &cat[[<r[1],fac[2]> : r in Roots(RC!(fac[1]))] : fac in
		Factorisation(ReciprocalPolynomial(charpoly2))];

    // mch - 06/14 - test that all roots in r1 or r2 have absolute value
    // q. This should often(?) eliminate the wrong charpoly.
    // q assumed small enough that an error estimate of 0.1 (for default complex
    // field precision) should be OK for the correct charpoly
    qc := BaseRing(RC)!q;
    bgood := [&and[Abs(Abs(r[1])-qc) lt 0.1 : r in rs] : rs in [r1,r2]];
    error if not &or(bgood), "traces not correct";
    if not &and(bgood) then
	E`LFunction := (bgood[1] select cpols[1] else cpols[2]);
	return E`LFunction;
    end if;

    tr1:=&+[np[2]*np[1]^i : np in r1];
    tr2:=&+[np[2]*np[1]^i : np in r2];

    nopi:=NumberOfPointsOnSurface(E,i);

    trace_i:=nopi-1-q^(2*i)-q^i*Trace(M^i);

    if AbsoluteValue(tr1 - trace_i) lt 1 then
       E`LFunction:= cpols[1];
    elif AbsoluteValue(tr2 - trace_i) lt 1 then
       E`LFunction:= cpols[2];
    else error "traces not correct";
    end if;
    return E`LFunction;

  end if;

  E`LFunction:= charpoly1*Lknownq;
  return E`LFunction;
end intrinsic;


intrinsic LFunction(E::CrvEll[FldFunG], e::RngIntElt) -> RngUPolElt
  {The L-function for the base change of E by a constant field extension 
    of degree e.}
  L:=LFunction(E);
  return PowerPolynomial(L,e);
end intrinsic;


intrinsic AnalyticInformation(E::CrvEll[FldFunG], e::RngIntElt) -> Tup
  {Given elliptic curve E over a function field over a finite field,
   output a tuple consisting of the rank, geometric rank, and product 
   of order of Tate-Shafarevich group and regulator of E after extending 
   the constant field with degree e. }
  K:=BaseRing(E);
  F:=ConstantField(K);
  if Type(K) eq FldFunRat then
    Ke:=FunctionField(ext<F | e>);
  else
    Ke:=ConstantFieldExtension(K,ext<F | e>);
  end if;
  Ee:=ChangeRing(E,Ke);
  Le:=LFunction(E,e);
  return AnalyticInformation(Ee,Le);
end intrinsic;


intrinsic AnalyticInformation(E::CrvEll[FldFunG]) -> Tup
  {Given elliptic curve E over a function field over a finite field,
   output a tuple consisting of the rank, geometric rank, and product 
   of order of Tate-Shafarevich group and regulator. }

  lfun:=LFunction(E);
  return AnalyticInformation(E,lfun);
end intrinsic;

intrinsic AnalyticInformation(E::CrvEll[FldFunG], lfun::RngUPolElt) -> Tup
  {Given E, together with its L-function, output a tuple consisting of the 
   rank, geometric rank, and product of order of Tate-Shafarevich group 
   and regulator. }

   K:=BaseRing(E);
   locinfo:=LocalInformation(E);
   F:=CoefficientRing(AbsoluteFunctionField(K));
   require Type(F) eq FldFin: 
     "E is not defined over a function field over a finite field";

   q:=#F;
   R<T>:=Parent(lfun);
   d:=Degree(lfun);
   f:=Factorisation(IntegerRing()!Coefficient(lfun,d));
//   q:=f[1][1]^(f[1][2] div d);
   L:=Evaluate(lfun,T/q);
   Lfac:=Factorisation(L);

   rank:=0;
   rankgeom:=0;
   for f in Lfac do
     if f[1] eq T-1 then 
       rank:=f[2]; 
     end if;
     if &and[IsIntegral(a) : a in Eltseq(f[1])] then 
       rankgeom+:=Degree(f[1])*f[2];
     end if;
   end for;

   tor:=#TorsionSubgroup(E);
   cp:=&*[Integers()| li[4] : li in locinfo];
   alpha:=((&+[Integers()| li[2]*Degree(li[1]) : li in locinfo]) div 12) - 1 + Genus(K);

   L div:=(1-T)^rank;

   TSdisc:=Evaluate(L,1)*(q^alpha)*(tor)^2/cp;

return <rank,rankgeom,TSdisc>;
end intrinsic;

intrinsic AnalyticRank(E::CrvEll[FldFunG]) -> RngIntElt
  { Analytic rank of E }
  return AnalyticInformation(E)[1];
end intrinsic;


intrinsic PowerPolynomial(f::RngUPolElt, n::RngIntElt) -> RngUPolElt
{A polynomial whose roots are the nth powers of the roots of f.}
  d:=Degree(f);
  R:=Parent(f);
  if n lt 15 then
    Q:=CoefficientRing(R);
    phi:=Factorisation(R!CyclotomicPolynomial(n))[1][1];
    if Degree(phi) eq 1 then 
      K:=Q;
      z:=Roots(phi)[1][1];
    else
      K<z>:=ext<Q | phi>;
    end if;
    Rz := PolynomialRing(K); Tz := Rz.1;
    prod:=Eltseq(&*[Rz| Evaluate(f,z^i*Tz) : i in [0..n-1]]);
    return R![Q!prod[n*i+1] : i in [0..d]];
  else
    M:=MatrixWithGivenCharacteristicPolynomial(f);
    g:=R!CharacteristicPolynomial(M^n);
    return g*Coefficient(f,d)^n;
  end if;
end intrinsic;



intrinsic MatrixWithGivenCharacteristicPolynomial(f::RngUPolElt) -> AlgMatElt
  { Matrix with characteristic polynomial f}

  d:=Degree(f);
  K:=CoefficientRing(f);

  if d lt 1 then return IdentityMatrix(K,0); end if;

  require ISA(Type(K),Fld) or LeadingCoefficient(f) eq 1 :
    "For non-monic polynomials the coefficients should lie in a field";

  if ISA(Type(K),Fld) then f/:=LeadingCoefficient(f); end if; 

  coef:=Eltseq(f);
  if d eq 1 then
    return Matrix(1,[-coef[1]]);
  else
    M1:=IdentityMatrix(K,d-1);
    M2:=Matrix(d-1,1,[-coef[i] : i in [2..d]]);
    M3:=HorizontalJoin(M1,M2);
    M4:=VerticalJoin(Matrix(1,d,[0 : i in [1..d-1]] cat [-coef[1]]),M3);

    return M4;
  end if;
end intrinsic;


