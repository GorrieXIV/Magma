freeze;

/******************************************************************************
 *
 * pointsearch.m
 *
 * date:   25/8/2003
 * author: Nils Bruin
 *
 * Routines to search for rational points on (hyper)elliptic curves over
 * number fields. The algorithm in FindIntegerPoints is described in
 * Nils Bruin's thesis, Appendix A.
 * implementation by Geoff Bailey ("Sieve" intrinsic)
 * 
 * Modified by Steve Donnelly, April 2011
 *
 ******************************************************************************/

declare attributes CrvEll:Algebra;
declare attributes Map:Algebra;
declare attributes RngOrd:NonInertPrimes; // only used in NonInertPrimes

import "selmer.m":IsogenyIsMultiplicationByTwo;

// NonInertPrimes(O::RngOrd,M::RngOrdIdl,N::RngIntElt)->SeqEnum
// {The first N primes of O that have inertia degree 1 and that are coprime to M}
// Note: would be slightly better to store them on NumberField(O)

function NonInertPrimes(O,M,N:Store:=false)
  PIO := PowerIdeal(O);
  R:=[PIO|];
  if assigned O`NonInertPrimes then
    for P in O`NonInertPrimes do 
      if Valuation(M,P) eq 0 then
        Append(~R,P);
      end if;
      if #R ge N then
        return R;
      end if;
    end for;
  elif Store then
    O`NonInertPrimes := [PIO|];
  end if;
  p:=1;
  while #R lt N do 
    p:=NextPrime(p:Proof:=false);
    // TO DO: save time by using DecompositionType(O, p) here
    S:=Support(O*p);
    for P in S do
      if InertiaDegree(P) eq 1 and Valuation(M,P) eq 0 then
        Append(~R,P);
	if #R ge N then
	  break;
	end if;
      end if;
    end for;
  end while;
  if Store then
    O`NonInertPrimes cat:= [P : P in R | P notin O`NonInertPrimes];
  end if;
  return R;
end function;

// Return bounds defining a rectangular box of volume = Bound^n
// that contains small elements in the span of the given basis
// (square box scaled by the Minkowski L_2 norms of the basis)

function box(basis, Bound)
  heights := [];
  for b in basis do 
    c := Conjugates(b);   // only need order of magnitude
    Append(~heights, Sqrt(&+[Abs(c[i])^2 : i in [1..#c]]));
  end for;
//"heights:", ChangeUniverse(heights, RealField(8));
  ha := (&*heights) ^ (1/#heights);
  return [Max(1, Round(Bound*ha/h)) : h in heights]; // or allow zero?
end function;

function FindIntegerPoints(F, deg, basis, bounds, Primes)
  O := Universe(basis);
  assert O eq BaseRing(F);
  sieved := Sieve(F, Primes, bounds : Basis:=basis, Degree:=deg);
  xcoords := [O| &+[ v[i]*basis[i] : i in [1..#basis]] : v in sieved];
  return [O| x : x in xcoords | v eq 0 or IsPower(v, deg) 
                                where v is Evaluate(F,x)];
end function;

// Either Bound or bounds may be specified.
// The basis must consist of order elements in O, 
// but is not required to be a basis of O

function FindRationalPoints(F,deg,Bound:basis:=0,bounds:=0,
                            DenominatorBound:=-1,Denominators:=[],
                            Max:=Infinity(),
                            NPrimes:=30)
  K:=BaseRing(F);

  if basis cmpeq 0 then
    // Use an LLL basis here (since we want to test small x-values)
    O := LLL(Integers(AbsoluteField(K)));
    basis := ChangeUniverse(Basis(O),O);
  else
    O := Universe(basis);
    assert IsAbsoluteOrder(O);
  end if;

  if bounds cmpeq 0 then
    bounds := box(basis, Bound);
  end if;

  // Make F integral 
  // TO DO: use minimal scaling (only matters for the leading_primes)
  dn := LCM([d where _,d:=IsIntegral(c) : c in Coefficients(F)]); // MW
  F := dn^deg*F;
  f := Eltseq(F);
  leading_primes := {Minimum(t[1]) : t in Factorization(f[#f]*O)};

  if IsEmpty(Denominators) then
    if DenominatorBound le 0 then
      assert Bound ge 1;
      DenominatorBound:=Bound;
    end if;
    g := deg div GCD(deg, Degree(F));
    if g gt 1 then
      D1 := [d^g : d in [1..Ceiling(DenominatorBound^(1/2))]];
      D2 := [d : d in [1..DenominatorBound] | PrimeDivisors(d) subset leading_primes];
      Denominators := ChangeUniverse(Sort([d1*d2 : d1 in D1, d2 in D2]), O);
    else
      Denominators := [O| d : d in [1..DenominatorBound]];
    end if;
    // TO DO: for larger Degree(F), say >= 4, maybe use not only integers. 
  else
    bool, Denominators := CanChangeUniverse(Denominators, O);
    error if not bool, "'Denominators' should be integral elements in the field";
  end if;

  primes:=NonInertPrimes(O,deg*dn*Discriminant(F)*O,NPrimes:Store);
  R:={K|};
  for d in Denominators do
    s:=O!d^((-Degree(F)) mod deg);
    G:=s*Polynomial(O,[O|f[i]*d^(#f-i) : i in [1..#f]]);
    IP:=FindIntegerPoints(G,deg,basis,bounds,primes);
    for x in IP do
      Include(~R, K!(x/d));
    end for;
    if #R ge Max then
      break;
    end if;
  end for;

  return R;
end function;

intrinsic RationalPoints(f::RngUPolElt,n::RngIntElt:Bound:=0,
                         DenominatorBound:=-1,Denominators:=[],
                         Max:=Infinity(),
                         NPrimes:=30)
       -> SetIndx
  {Searches for rational points on y^n = F(x), in a box bounded by 'Bound' 
   (which must be specified)}

  require n ge 2 : "The second argument must be at least 2";
  require Discriminant(f) ne 0 : "The polynomial has discriminant zero";
  require Bound gt 0 : 
          "A (positive) value for the parameter 'Bound' must be specified";

  K := BaseRing(f);
  if Type(K) eq FldRat then
    KK := RationalsAsNumberField();
    pts := Points(ChangeRing(f,KK), n : Bound:=Bound,NPrimes:=NPrimes,Max:=Max,
                                        DenominatorBound:=DenominatorBound,
                                        Denominators:=Denominators);
    return {@ ChangeUniverse(pt,K) : pt in pts @};
  else
    require ISA(Type(K), FldAlg) : 
      "The first argument should be a polynomial over the rationals or a number field";
  end if;

  rts := [r[1] : r in Roots(PolynomialRing(K).1^n - 1)];
  L:=FindRationalPoints(f,n,Bound:NPrimes:=NPrimes,Max:=Max,
                        DenominatorBound:=DenominatorBound,
                        Denominators:=Denominators);
  pts := {@ [x[1],0,1] : x in Roots(f) @};
  for x in L do
    _,y := IsPower(Evaluate(f,x), n);
    pts join:= {@ [x,r*y,1] : r in rts @};
  end for;

  if IsPrime(n) then
    if Degree(f) mod n ne 0 then
      //homgenize f(x) using weight(x) = n
      m := Integers()!( -(GF(n)!Degree(f))^-1 );
      c := LeadingCoefficient(f);
      pts join:= {@ [c^m,c^(Integers()!( (Degree(f)*m+1)/n )),0] @};
    else
      //homogenize f(x) using weight(x) = 1
      boo,pow := IsPower(LeadingCoefficient(f),n);
      if boo then
        pts join:= {@ [1,pow,0] @};
      end if;
    end if; //Degree(f) mod m ne 0
  end if; //IsPrime(n)

  return pts;
end intrinsic;

intrinsic Points(f::RngUPolElt,n::RngIntElt:Bound:=0,
                         DenominatorBound:=-1,Denominators:=[],
                         Max:=Infinity(),
                         NPrimes:=30)
       -> SetIndx
  {Searches for rational points on y^n = F(x), in a box bounded by 'Bound' 
   (which must be specified)}

  require n ge 2 : "The second argument must be at least 2";
  require Discriminant(f) ne 0 : "The polynomial has discriminant zero";
  require Bound gt 0 : 
          "A (positive) value for the parameter 'Bound' must be specified";

  return RationalPoints(f,n:Bound:=Bound,NPrimes:=NPrimes,Max:=Max,
                            DenominatorBound:=DenominatorBound,
                            Denominators:=Denominators);
end intrinsic;

intrinsic RationalPoints(C::CrvHyp[FldAlg]:Bound:=0,
                         DenominatorBound:=-1,Denominators:=[],
                         Max:=Infinity(),
                         NPrimes:=30)
       -> SetIndx
  {Searches for rational points on C in a box bounded by 'Bound' 
   (which must be specified)}

  require Bound gt 0 : 
          "A (positive) value for the parameter 'Bound' must be specified";
  f,h:=HyperellipticPolynomials(C);
  F:=f+h^2/4;
  L:=FindRationalPoints(F,2,Bound:NPrimes:=NPrimes,Max:=Max,
                        DenominatorBound:=DenominatorBound,
                        Denominators:=Denominators);
  pts := RationalPoints(C,Infinity()) join
         {@ C![x[1],-Evaluate(h/2,x[1])] : x in Roots(F) @};
  for x in L do
    _,y := IsSquare(Evaluate(F,x));
    y1 := Evaluate(h/2,x);
    pts join:= {@ C![x,y-y1], C![x,-y-y1] @};
  end for;
  return pts;
end intrinsic;

intrinsic Points(C::CrvHyp[FldAlg]:Bound:=0,
                         DenominatorBound:=-1,Denominators:=[],
                         Max:=Infinity(),
                         NPrimes:=30)
       -> SetIndx
  {"} // "
  require Bound gt 0 : 
          "A (positive) value for the parameter 'Bound' must be specified";
  return RationalPoints(C:Bound:=Bound,NPrimes:=NPrimes,Max:=Max,
                        DenominatorBound:=DenominatorBound,
                        Denominators:=Denominators);
end intrinsic;

intrinsic RationalPoints(C::CrvEll[FldAlg]:Bound:= 0,
                         DenominatorBound:=-1,Denominators:=[],
                         Max:=Infinity(),
                         NPrimes:=30)
       -> SetIndx
  {"} // "
  require Bound gt 0 : 
          "A (positive) value for the parameter 'Bound' must be specified";
  f,h:=HyperellipticPolynomials(C);
  F:=f+h^2/4;
  L:=FindRationalPoints(F,2,Bound:NPrimes:=NPrimes,Max:=Max,
                        DenominatorBound:=DenominatorBound,
                        Denominators:=Denominators);
  pts := {@ Zero(C) @} join {@ C![x[1],-Evaluate(h/2,x[1])] : x in Roots(F) @};
  for x in L do
    _,y := IsSquare(Evaluate(F,x));
    y1 := Evaluate(h/2,x);
    pts join:= {@ C![x,y-y1], C![x,-y-y1] @};
  end for;
  return pts;
end intrinsic;

intrinsic Points(C::CrvEll[FldAlg]:Bound:=0,
                         DenominatorBound:=-1,Denominators:=[],
                         Max:=Infinity(),
                         NPrimes:=30)
       -> SetIndx
  {"} // "
  require Bound gt 0 : 
          "A (positive) value for the parameter 'Bound' must be specified";
  return RationalPoints(C:Bound:=Bound,NPrimes:=NPrimes,Max:=Max,
                        DenominatorBound:=DenominatorBound,
                        Denominators:=Denominators);
end intrinsic;

intrinsic Quartic(X::Sch:Reduced:=true)->CrvHyp,MapSch
  {Given a curve (of genus one) whose equations are 2 quadrics in P^3 
   returns an isomorphic hyperelliptic curve C, 
   together with an isomorphism from X to C.}
  Q:=DefiningEquations(X);
  require IsProjective(X) and
          Dimension(Ambient(X)) eq 3 and
          #Q eq 2 and
          forall{q:q in Q|TotalDegree(q) eq 2}:
    "Scheme must be the locus of a quadratic pencil in P3";
  K:=BaseRing(X);
  x:=PolynomialRing(K).1;
  M:=[SymmetricMatrix(q):q in Q];
  det:=Determinant(x*M[1]+M[2]);
  disc:=Discriminant(det);
  require Degree(det) in {3,4} and disc ne 0:
    "Pencil must have a nonsingular locus";
  if Degree(det) eq 3 then
    S:=M[1];
    Q:=M[2];
  else
    bl,xval:=HasRoot(det);
    require bl:
      "Pencil must contain a rational singular quadric";
    S:=xval*M[1]+M[2];
    Q:=M[1];
  end if;
  if IsZero(Vector([K|0,0,0,1])*S) then
    T:=Parent(S)!1;
  else
    T:=Basis(Kernel(S));
    assert #T eq 1;
    T:=Matrix(Reverse(ExtendBasis(T,Generic(Universe(T)))));
    S:=T*S*Transpose(T);
    Q:=T*Q*Transpose(T);
    assert IsZero(Vector([K|0,0,0,1])*S);
  end if;
  C:=Submatrix(S,1,1,3,3);
  P2:=ProjectiveSpace(K,2);
  v:=Vector([P2.1,P2.2,P2.3]);
  C:=Conic(P2,InnerProduct(v*Matrix(BaseRing(v),C),v));
  if Type(K) eq FldRat then
  //require HasPoint(C): "Singular quadric must have a rational point"; 
    require IsLocallySolvable(C): "Singular quadric must have a rational point"; // SRD, March '08
    w:=DefiningPolynomials(Parametrization(C));
  else
    bl,P:=HasPoint(C);
    require bl: "Singular quadric must have a rational point";
    w:=DefiningPolynomials(Parametrization(C,P));    
  end if;
  R:=PolynomialRing(Parent(x));
  v:=Vector(Append([Evaluate(f,[R!x,1]):f in w],R.1));
  f:=InnerProduct(v*Matrix(BaseRing(v),Q),v);
  assert Degree(f) eq 2;
  assert Coefficient(f,2) in K;
  f:=f/K!Coefficient(f,2);
  hc:=HyperellipticCurve(-Coefficient(f,0),Coefficient(f,1));
  mp:=Vector(Append([Evaluate(f,[hc.1,hc.3]):f in w],hc.2));
  mp:=Eltseq(mp*Matrix(BaseRing(mp),T));
//mp:=map<hc->Ambient(X)|mp>;
  mp:=map<hc->X|mp:Check:=false>; // SRD, March '08
  if Type(K) eq FldRat and Reduced then
    hc,mpm:=ReducedMinimalWeierstrassModel(hc);
    hc,mps:=SimplifiedModel(hc);
    mp:=Expand(Inverse(mpm*mps)*mp);
  end if;
  return hc,mp;
end intrinsic;

function DefaultIsogeny(E,Isogeny)
  if Isogeny cmpeq "Default" then
    T,m:=TwoTorsionSubgroup(E);
    if #T gt 1 then
      return TwoIsogeny(m(T.1));
    else
      phi:=MultiplicationByMMap(E,2);
      if assigned E`Algebra then
        phi`Algebra:=E`Algebra;
      end if;
      return phi;
    end if;
  elif ISA(Type(Isogeny),PtEll) then
    error if not(Isogeny ne 0 and 2*Isogeny eq 0),
      "Must specify a 2-torsion point";
    return TwoIsogeny(Isogeny);
  elif ISA(Type(Isogeny),RngIntElt) and Isogeny eq 2 then
    phi:=MultiplicationByMMap(E,2);
    if assigned E`Algebra then
      phi`Algebra:=E`Algebra;
    end if;
    return phi;
  elif ISA(Type(Isogeny),Map) then
    return Isogeny;
  end if;
end function;

function VeryNaiveHeight(a)
 if ISA(Type(a),FldRatElt) then
   return Abs(Numerator(a)*Denominator(a));
 else
   return Abs(Norm(a*Denominator(a))*Denominator(a));
 end if;
end function;

function TwoIsoPointSearch(phi,SearchBound,UseHomogeneousSpaces)
  E:=Codomain(phi);
  S,toS:=SelmerGroup(phi);
  mu,tor:=CasselsMap(phi);
  T,mT:=TorsionSubgroup(E);
  tg:=[mT(g):g in OrderedGenerators(T)];
  G:=[Parent(E!0)|];
  MWgrp:=sub<S|[toS(mu(g)):g in tg]>;
  if MWgrp eq S then
    return true,G,tg,AbelianInvariants(T);
  end if;
  V:=Setseq(RationalPoints(E : Bound := SearchBound));
  Sort(~V,func<p,q|VeryNaiveHeight(p[1])-VeryNaiveHeight(q[1])>);
  for p in V do
    c:=toS(mu(p));
    if c notin MWgrp then
      Append(~G,p);
      MWgrp:=sub<S|OrderedGenerators(MWgrp) cat [c]>;
      if MWgrp eq S then
        return true,G,tg,AbelianInvariants(T);
      end if;
    end if;
  end for;
  if UseHomogeneousSpaces then
    for s in S do
      if s notin MWgrp then
        cov:=tor(s@@toS);
        V:=Setseq(RationalPoints(Domain(cov) : Bound := SearchBound));
        Sort(~V,func<p,q|VeryNaiveHeight(p[1])-VeryNaiveHeight(q[1])>);
        if #V ne 0 then
          Append(~G,EvaluateByPowerSeries(cov,V[1]));
          MWgrp:=sub<S|OrderedGenerators(MWgrp) cat [s]>;
          if MWgrp eq S then
            return true,G,tg,AbelianInvariants(T);
          end if;
        end if;
      end if;
    end for;
  end if;
  return false,G,tg,AbelianInvariants(T);
end function;
        
function TwoPointSearch(phi,SearchBound,UseHomogeneousSpaces)
  E:=Codomain(phi);
  S,toS:=SelmerGroup(phi);
  mu,tor:=CasselsMap(phi);
  T,mT:=TorsionSubgroup(E);
  tg:=[mT(g):g in OrderedGenerators(T)];
  G:=[Parent(E!0)|];
  MWgrp:=sub<S|[toS(mu(g)):g in tg]>;
  if MWgrp eq S then
    return true,G,tg,AbelianInvariants(T);
  end if;
  V:=Setseq(RationalPoints(E : Bound := SearchBound));
  Sort(~V,func<p,q|VeryNaiveHeight(p[1])-VeryNaiveHeight(q[1])>);
  for p in V do
    c:=toS(mu(p));
    if c notin MWgrp then
      Append(~G,p);
      MWgrp:=sub<S|OrderedGenerators(MWgrp) cat [c]>;
      if MWgrp eq S then
        return true,G,tg,AbelianInvariants(T);
      end if;
    end if;
  end for;
  if UseHomogeneousSpaces then
    for s in S do
      if s notin MWgrp then
        cov:=tor(s@@toS);
        qr,mp:=Quartic(Domain(cov));
        cov:=Expand(mp*cov);
        V:=Setseq(RationalPoints(qr : Bound := SearchBound));
        Sort(~V,func<p,q|VeryNaiveHeight(p[1])-VeryNaiveHeight(q[1])>);
        if #V ne 0 then
          Append(~G,EvaluateByPowerSeries(cov,V[1]));
          MWgrp:=sub<S|OrderedGenerators(MWgrp) cat [s]>;
          if MWgrp eq S then
            return true,G,tg,AbelianInvariants(T);
          end if;
        end if;
      end if;
    end for;
  end if;
  return false,G,tg,AbelianInvariants(T);
end function;
 
intrinsic MordellWeilSubgroup(E::CrvEll:
                         Isogeny:="Default",
                         SearchBound:="Default",
                         UseHomogeneousSpaces:="Default")
        ->BoolElt,GrpAb,Map
{Same as PseudoMordellWeilGroup}
  return PseudoMordellWeilGroup(E : Isogeny:=Isogeny, SearchBound:=SearchBound, 
                                    UseHomogeneousSpaces:=UseHomogeneousSpaces);
end intrinsic;

intrinsic PseudoMordellWeilGroup(E::CrvEll:
                         Isogeny:="Default",
                         SearchBound:="Default",
                         UseHomogeneousSpaces:="Default")->BoolElt,GrpAb,Map
{For E defined over a number field K (or Q), returns bool, A, AtoE.
  A is a subgroup of E(K), via the injection given by AtoE. 
  A is known to have finite odd index in E(K) when bool is true.}
  Isogeny:=DefaultIsogeny(E,Isogeny);
  require Domain(Isogeny) eq E or Codomain(Isogeny) eq E:
    "Isogeny must be related to E";
  K:=BaseRing(E);
  if SearchBound cmpeq "Default" then
    if Type(K) eq FldRat then
      SearchBound:=10000;
    else
      SearchBound:=Ceiling(10000^(1/Degree(K)));
    end if;
  end if;
  if UseHomogeneousSpaces cmpeq "Default" then
    UseHomogeneousSpaces:=(Type(K) eq FldRat) or Degree(Isogeny) eq 2;
  end if;
  
  case Degree(Isogeny):
  when 2:
    if Domain(Isogeny) eq E then
      Isogeny:=DualIsogeny(Isogeny);
    end if;
    bl,G,tg,abinvar:=TwoIsoPointSearch(Isogeny,SearchBound,
                                             UseHomogeneousSpaces);
    bld,Gd:=TwoIsoPointSearch(DualIsogeny(Isogeny),SearchBound,
                                             UseHomogeneousSpaces);
    bl:=bl and bld;
    abinvar:=abinvar cat [0: i in [1..#G+#Gd]];
    G:=G cat [Isogeny(g):g in Gd];
  when 4:
    require IsogenyIsMultiplicationByTwo(Isogeny):
      "Isogeny type not supported";
    bl,G,tg,abinvar:=TwoPointSearch(Isogeny,SearchBound,
                                             UseHomogeneousSpaces);
    abinvar:=abinvar cat [0: i in [1..#G]];
  else
    require false:"Isogeny type not supported";
  end case;
  gs:=tg cat G;
  G:=AbelianGroup(abinvar);
  if abinvar eq [] then
    mwmap := map<G->E | a :-> E!0>;
  else
    mwmap:=map<G->E|a:-> &+[a[i]*gs[i]:i in [1..#gs]] where a:=Eltseq(a)>;
  end if;
  return bl,G,mwmap;
end intrinsic;

