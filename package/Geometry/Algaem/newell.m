freeze;

/******************************************************************************
 *
 * newell.m
 *
 * date:   14/ 8/2001
 *         28/11/2002
 * author: Nils Bruin
 *
 * Some routines for added functionality for elliptic curves over number fields
 *
 ******************************************************************************/

import "localdata.m": GetLocalData, StoreLocalData;

/**
 ** IsIntegralModel
 **
 ** tests whether an elliptic curve over the rationals or over a number field
 ** has integral coefficients.
 **/
 
intrinsic IsIntegralModel(E::CrvEll[FldAlg]) -> BoolElt
  {returns true if an elliptic curve over a number field
  has integral coefficients}
  return forall{a:a in aInvariants(E)|IsIntegral(a)};
end intrinsic; 

intrinsic IsIntegralModel(E::CrvEll[FldAlg],p::RngOrdIdl) ->BoolElt
  {returns true if the defining coefficients of E have non-negative valuation at
  the prime ideal p}
  cfs:=Eltseq(E);
  return forall{c:c in cfs|Valuation(c,p) ge 0};
end intrinsic;

/**
 ** IntegralModel
 **
 ** Changes the model of an elliptic curve over the rationals or over a number
 ** field to one with integral coefficients.
 ** it tries to do so in a carefull way, but the returned model is not
 ** necessarily minimal in the standard sence.
 **/
 
intrinsic IntegralModel(E::CrvEll[FldAlg]) -> CrvEll, MapSch, MapSch
  {A model with integral coefficients of the elliptic curve E,
   defined over a number field}

  dn:=1; 
  ecn:=E;
  phi:=IdentityMap(E);

  repeat
    for a in aInvariants(ecn) do
      flag, d := IsIntegral(a);
      if not flag then
        break;
      end if;
    end for;
 
    if not flag then 
      dn*:=d;
      ecn,phi:=Transformation(E,[0,0,0,dn]);
    end if;
  until flag;
 
  return ecn,phi,Inverse(phi);
end intrinsic;


intrinsic HyperellipticPolynomials(E::CrvEll)->RngUPolElt,RngUPolElt
  {Return x^3+a2*x^2+a4*x+a6, a1*x+a3.}
  a:=aInvariants(E);
  return Polynomial(BaseRing(E),[a[5],a[4],a[2],1]),
         Polynomial(BaseRing(E),[a[3],a[1]]);
end intrinsic;


// DualIsogeny rewritten March 2009, SRD

declare attributes MapSch:Isogeny_Dual;

intrinsic DualIsogeny(phi::MapSch)->MapSch
{The dual isogeny of the given isogeny phi between two elliptic curves.  
 This satisfies phi*dual = [m] where m is the degree of phi}

 if not(assigned phi`Isogeny_Dual) then
   E := Domain(phi); 
   K := BaseRing(E);
   /*
   // If phi is a composite of several isogenies, do duals componentwise
   // (Currently though, this would almost never get called because for 
   // elliptic curve isogenies, compositions are expanded on creation)
   comps := Components(phi);
   if #comps gt 1 and forall {c: c in comps | ISA(Type(Domain(c)),CrvEll) and ISA(Type(Codomain(c)),CrvEll)
                                              and c(Domain(c)!0) cmpeq Codomain(c)!0 } 
   then 
     dual := &* Reverse([ DualIsogeny(c) : c in comps ]);
     phi`Isogeny_Dual:=dual;
     dual`Isogeny_Dual:=phi;
     return dual;
   end if;
   */
   d := Degree(phi);
   k := DivisionPolynomial(E,d);
   p := Characteristic(K);
   // Let v be such that InseparableDegree(dual) = p^v
   if p eq 0 or d mod p ne 0 then 
     v := 0;
   else
     if IsSupersingular(E) then
       v := Valuation(d, p);
     else
       id := InseparableDegree(phi);
       v := Valuation(d div id, p);
     end if;
   end if;
   phik := PushThroughIsogeny(phi,k);
   _,dual := IsogenyFromKernel(Codomain(phi), phik, v);
   bool,isom := IsIsomorphic(Codomain(dual),E); assert bool;
   dual:=dual*isom;

   // Replace dual by dual*auto if necessary to ensure phi*dual eq m  
   // TO DO: could also use formal group with 3 or 4 terms, for cases
   //        where (d,p)=1 but the automorphism group is larger 
   if p eq 0 or 
      d mod p ne 0 and p ne 2 and (p ne 3 or jInvariant(E) ne 0) 
   then
     // The automorphisms are all scalings by some u in K, and the value of u can be 
     // identified from the leading coefficient of the formal group homomorphisms.
     // The formal group homomorphism for phi*dual should be d*T + O(T^2).
     // TO DO: could still use leading coeff, even when v > 0
     fphi := FormalGroupHomomorphism(phi, 1); 
     fdual := FormalGroupHomomorphism(dual, 1); 
     f1 := Coefficient(fphi,1) * Coefficient(fdual,1);  assert f1 ne 0;
     u := d/f1;
     if u eq -1 then  
       aut := NegationMap(E);
       dual := dual * aut;
     elif u ne 1 then
       Aut, Autmap := AutomorphismGroup(E);
       for a in {a : a in Aut | Order(a) gt 2} do 
         aut := a@Autmap;
         faut := FormalGroupHomomorphism(aut, 1);
         if Coefficient(faut,1) eq u then 
           dual := dual * aut;
           break a;
         end if;
       end for; 
     end if;
   else
     Aut, Autmap := AutomorphismGroup(E);
     // Check that phi*dual agrees with [d] on enough points. 
     // By Riemann-Hurwitz, at most 3 points can be fixed by an automorphism of order >= 3.
     // For all possible automorphism groups, the only automorphism of order 2 is [-1].
     // So suffices to check 2 points P1,P2 such that {d*P1,-d*P1,d*P2,-d*P2} are distinct.
     num := (#Aut eq 2) select 1 else 2; // number of pts needed
     pts := [* *]; 
     dpts := [* *]; 
     if IsFinite(K) then 
       l := 1 + Ilog(#K, 16*d^2);
     else 
       l := 1 + Ilog(p, 16*d^2);
     end if;
     while #pts lt num do 
       // choose random x value
       if IsFinite(K) then 
         x0 := Random(GF(#K^l));
       else
         x0 := &+[Random(GF(p)) * K.1^i : i in [0..l-1]];
       end if;
       y := PolynomialRing(Parent(x0)).1;
       pol := Evaluate(DefiningEquation(E), [x0,y,1]);
       bool, y0 := HasRoot(pol);
       if not bool then 
         _<y0> := ext< Parent(x0) | pol >;
       end if;
       P := E(Parent(y0))! [x0,y0,1];
       dP := d*P; mdP := -dP;
       if dP eq mdP or exists{R : R in dpts | dP cmpeq R or mdP cmpeq R} then 
         continue;
       else 
         Append(~pts, P);
         Append(~dpts, dP);
       end if;
     end while; 
     ddpts := [* P@phi@dual : P in pts *];
     if not forall {i: i in [1..#pts] | dpts[i] eq ddpts[i]} then 
       for a in [a: a in Aut | Order(a) gt 1] do 
         aut := a@Autmap;
         if forall {i: i in [1..#pts] | dpts[i] eq ddpts[i]@aut} then 
           dual := dual*aut; 
           break a;
         end if;
       end for;
     end if;
   end if; 

   phi`Isogeny_Dual:=dual;
   dual`Isogeny_Dual:=phi;
 end if;
 return phi`Isogeny_Dual;  
end intrinsic;

intrinsic TwoIsogeny(P::PtEll)->Map
  {computes the 2-isogeny with the 2-torsion point P in the kernel}
  E:=Curve(P);
  a:=aInvariants(E);
  require not(IsZero(P)) and IsZero(2*P):
    "Point P must be a 2-torsion point";
  E1,mp1:=Transformation(E,[-P[1]/P[3],a[1]/2,a[3]/2,1]);
  mp2:=Inverse(mp1);
  P:=CoordinateRing(Ambient(AffinePatch(E1,1)));
  x:=P.1;y:=P.2;
  _,A,_,B:=Explode(aInvariants(E1));
  D:=A^2-4*B;
  E2:=EllipticCurve([0,-2*A,0,D,0]);
  psi1:=mp1*Isogeny(E1,E2,x,(x^2+A*x+B),y*(B-x^2));
  psi2:=Isogeny(E2,E1,x,(x^2-2*A*x+D)/4,y*(D-x^2)/8)*mp2;
  psi1`Isogeny_Dual:=psi2;
  psi2`Isogeny_Dual:=psi1;
  return psi1;
end intrinsic;

intrinsic Reduction(E::CrvEll,p::RngOrdIdl:ReturnMap:=true)->CrvEll,Map
  {Returns the reduction of an elliptic curve at a prime ideal, provided the
  given model has good reduction at the prime. The map gives the reduction map
  on the Mordell-Weil group of the curve.}

  if not(assigned GetLocalData(E,p)`reduction) then
    K := BaseRing(E);
    if ISA(Type(K), RngOrd) then
      K := NumberField(K);
    end if;
    require ISA(Type(K), FldAlg) and NumberField(Order(p)) eq K:
      "Field of definition and ideal are not compatible";
    cfs:=Eltseq(E);
    require IsIntegralModel(E,p) and Valuation(Discriminant(E),p) eq 0:
      "model should be integral and of good reduction at the prime";
    Kbar,red:=ResidueClassField(IntegerRing(K),p);
    Ebar:=EllipticCurve([red(c):c in cfs]);
    if not ReturnMap then
      return Ebar;
    end if;
    // The rest of this is far too slow. 
    // TO DO: for a start, SafeUniformiser is very slow, and unnecessary
    u:=SafeUniformiser(p);
    fn:=function(P)
      L:=Eltseq(P);
      dn:=&*[Denominator(c):c in L];
      L:=[dn*c:c in L];
      v:=Minimum([Valuation(c,p):c in L|c ne 0]);
      return Ebar![red(c/u^v):c in L];
    end function;
    rc:=GetLocalData(E,p);
    rc`reduction:=map<E->Ebar| P:-> fn(P)>;
    StoreLocalData(E,p,rc);
  end if;
  rc:=GetLocalData(E,p);
  return Codomain(rc`reduction),rc`reduction;
end intrinsic;

function DiscreteLog(EpGrpMap,g)
  grp:=Domain(EpGrpMap);
  if Ngens(grp) eq 1 then
    return Log(EpGrpMap(grp.1),g);
  elif Ngens(grp) eq 2 then
    error if not( Order(grp.2) mod Order(grp.1) eq 0), "Unexpected group order";
    g1:=EpGrpMap(grp.1);
    g2:=EpGrpMap(grp.2);
    n:=Order(grp.1); m:=Order(grp.2) div n;
    e:=Log(n*g2,n*g);
    mg2:=m*g2;
    bl:=exists(a){grp![i,m*j]:i,j in [0..n-1]|
                       i*g1+j*mg2 eq g0} where g0:=g-e*g2;
    error if not(bl), "Element does not lie in the specified group";
    assert EpGrpMap(e*grp.2+a) eq g;
    return e*grp.2+a;
  else
    error "Impossible group structure for elliptic curve";
  end if;
end function;

function ProjectiveReduction(L,p,Rp)
  pi:=SafeUniformiser(p);
  v:=Minimum([Minimum([Valuation(c,p):c in Coefficients(l)]):l in L]);
  L:=[pi^(-v)*l:l in L];
  
  R:=Universe(L);
  K:=BaseRing(R);
  k,tok:=ResidueClassField(p);
  assert BaseRing(Rp) eq k;
  assert IntegerRing(K) eq Order(p);
  assert Rank(R) eq Rank(Rp);

  toRp:=hom<Universe(L)->Rp|map<K->Rp|c:->Rp!(tok(c))>,OrderedGenerators(Rp)>;

  return [Rp|toRp(l):l in L];
end function;

intrinsic Reduction(MWmap::Map,P::RngOrdIdl)->Map,Map,Map
  {Computes the map between Abelian groups induced by the reduction of
   an elliptic curve.
   The codomain of the returned map is isomorphic to the group of rational
   points on the curve in reduction. Presently, the elliptic curve must have
   good reduction at P.
   The second return value is an isomorphism from an abstract abelian group
   to the group of rational points on the reduction of the curve.}
   
  require ISA(Type(Domain(MWmap)),GrpAb) and
          (ISA(Type(Codomain(MWmap)),CrvEll) or
             (ISA(Type(Codomain(MWmap)),SetPtEll) and
              Ring(Codomain(MWmap)) cmpeq BaseRing(Scheme(Codomain(MWmap))))):
    "The map should be from an abelian group into an elliptic curve or its",
    "point set over the base ring";
  if not(assigned GetLocalData(MWmap,P)`reduction) then
    E:=Codomain(MWmap);
    if ISA(Type(Codomain(MWmap)),SetPtEll) then
      E:=Scheme(E);
    end if;
    Ep,toEp:=Reduction(E,P);
    k,tok:=ResidueClassField(P);
    EpGrp,EpGrpMap:=AbelianGroup(Ep);
//    map<Codomain(EpGrpMap)->Domain(EpGrpMap)|
//                                 g:->DiscreteLog(EpGrpMap,g)>;
//We're probably better off using Stoll's version and install that as
//the inverse mapping. Once the generig discrete logarithm implementations
//are updated, we can probably revert this back.
    InvEpGrpMap:=DiscreteLogMapSmooth(EpGrp,EpGrpMap);
    EpGrpMap:=map<Domain(EpGrpMap)->Codomain(EpGrpMap)|
                              a:->EpGrpMap(a),p:->InvEpGrpMap(p)>;
    rc:=GetLocalData(MWmap,P);
    rc`reduction:=<
        hom<Domain(MWmap)->EpGrp|
         [g@MWmap@toEp@InvEpGrpMap:g in OrderedGenerators(Domain(MWmap))]>,
        EpGrpMap,InvEpGrpMap>;
    StoreLocalData(MWmap,P,rc);
  end if;
  rc:=GetLocalData(MWmap,P);
  return rc`reduction[1],rc`reduction[2],rc`reduction[3];
end intrinsic;

function num_den(e,bnum)
// simple function to get a correct numerator/denominator for an
// element e of a number field. Used by TorsionBound below.

    b,n := IsIntegral(e);
    if bnum then return n*Numerator(e); 
    else return n; end if;
end function;

// TO DO: use communally stored primes, see also pointsearch.m

intrinsic TorsionBound(E::CrvEll[FldNum],n::RngIntElt) -> RngIntElt
  {Returns a bound on the size of the torsion subgroup of E by considering
  at least n primes (with early exit in some cases, such as when the torsion
  is shown to be only two-torsion)}

  O:=IntegerRing(BaseRing(E));
  coeffs:=Coefficients(E);
  bad:=2*AbsoluteDiscriminant(O)
       *LCM([num_den(c,false):c in coeffs])
       *AbsoluteNorm(num_den(Discriminant(E),true));
  bad:=Integers()!bad;
  // Now disallowing a few primes that were previously allowed,
  // to make screening simpler (was way too slow)  -- SRD, Feb 2011
  tt:=0;
  Bound:=0;
  attempt:=0;
  p:=1;
  while true do
    repeat
      p:=NextPrime(p:Proof:=false);
    until bad mod p ne 0;
    // TO DO use fe_only info first to locate a degree 1 prime
    S:=Support(p*O);
    S:=[P : P in S | AbsoluteInertiaDegree(P) eq 1];
    // not too many P for same p (they are not independent for some fields)
    if #S gt 2 then
      S:=S[1..2];
    end if;
    for P in S do
      attempt+:=1;
      _,red:=ResidueClassField(P);
      BP:=#EllipticCurve([red(c):c in coeffs]);
      Bound:=GCD(Bound,BP);
      if Bound eq 1 then
        return Bound;
      end if;
      maxpp:=Max([tup[1]^tup[2] : tup in Factorization(Bound)]);
      if attempt ge n*maxpp then 
        // will need to factorize poly of degree O(maxpp)
        return Bound;
      elif 4 mod Bound eq 0 and attempt ge 2 then
        // check 2-torsion
        if tt eq 0 then
          tt:=1+#Roots(DivisionPolynomial(E,2));
          assert Bound mod tt eq 0;
        end if;
        if tt eq Bound then
          return Bound;
        end if;
      end if;
    end for;
  end while;
end intrinsic;

function remove_common_factors(f,g)
  g := GCD(f,g);
  while Degree(g) gt 0 do 
    f := ExactQuotient(f,g); 
    g := GCD(f,g);
  end while;
  return f;
end function;

function pPowerGenerators(E,p:Bound:=-1)
  a:=0;b:=0;
  L:=[];
  defpol:=DefiningPolynomial(AffinePatch(E,1));
  if p eq 2 then
    Fn:=DivisionPolynomial(E,p);
    n:=1;
    L[1]:=[x[1]:x in Roots(Fn)|HasRoot(Evaluate(defpol,[x[1],Parent(Fn).1]))];
    if #L[1] ge 1 then
      a+:=1;
    end if;
    if #L[1] eq 3 then
      b+:=1;
    end if;
  else
    n:=0;
    Fn:=1;
  end if;
  while n eq 0 or (#L[n] gt 0 and (Bound lt 0 or p^(a+b) lt Bound)) do
    Fnm1:=Fn;
    n:=n+1;
    Fn:=DivisionPolynomial(E,p^n);  // TO DO: DivisionPoints should be better
    if Characteristic(BaseField(E)) eq p then
      // the lower stuff occurs multiple times (this case added by Steve)
      Fn_pure := remove_common_factors(Fn,Fnm1);
    else
      Fn_pure := Parent(Fn)!(Fn/Fnm1);
    end if;
    L[n]:=[x[1]:x in Roots(Fn_pure)|HasRoot(Evaluate(defpol,[x[1],Parent(Fn).1]))];
    if #L[n] ge (p^(n-1)*(p-1))/2 then
      a+:=1;
    end if;
    if #L[n] ge (p^(2*n-2)*(p^2-1))/2 then
      b+:=1;
    end if;
  end while;
  assert a ge b;
  result:=[];
  if a ge 1 then
    T1:=E![L[a][1],Roots(Evaluate(defpol,[L[a][1],Parent(Fn).1]))[1][1]];
    Append(~result,<T1,p^a>);
  end if;
  if b ge 1 then
    // get an element in E[p] that independent of T1, then lift it to E[p^b]
    xcoords := [ (c*U1)[1] : c in [1..(p div 2)] ] where U1 := p^(a-1)*T1;
    bool := exists(T2x){x: x in L[1]| not(x in xcoords)};
    error if not bool, "Can't find second generator for p-power torsion";
    T2 := E![T2x,Roots(Evaluate(defpol,[T2x,Parent(Fn).1]))[1][1]];
    for bb := 2 to b do T2 := DivisionPoints(T2,p)[1]; end for;
    // assert IsEmpty(DivisionPoints(T2,p));
    Append(~result,<T2,p^b>);
  end if;
  /* Old version of the T2 part, which contains a simple mistake:
  if b ge 1 then
    pT1:=p^(a-b)*T1;
    xcoors:={(c*pT1)[1]:c in [1..p^(b-1)*(p-1)]| c mod p ne 0};
    error if not exists(T2x){x: x in L[b]| not(x in xcoors)},
      "can't find second generator for torsion";
    T2:=E![T2x,Roots(Evaluate(defpol,[T2x,Parent(Fn).1]))[1][1]];
    Append(~result,<T2,p^b>);
  end if; */
  return result;
end function;

intrinsic pPowerTorsion(E::CrvEll,p::RngIntElt:Bound:=-1)->GrpAb,Map
  {returns the pPower torsion on E. The optional parameter gives an upper bound
  on the size of the p-power torsion subgroup that is used in the computations.}
  require IsPrime(p):"p should be a prime";
  L:=pPowerGenerators(E,p:Bound:=Bound);
  A:=AbelianGroup([l[2]:l in L]);
  g:=[l[1]:l in L];
  return A, map<A->E | a:->&+[n[i]*g[i]:i in [1..#g]] where n:=Eltseq(a)>;
end intrinsic;

declare attributes CrvEll : TorsionSubgroup;

intrinsic TorsionSubgroup(E::CrvEll[FldNum])->GrpAb, Map
  {The torsion subgroup of E over its base field}

  if assigned E`TorsionSubgroup then
     mp := E`TorsionSubgroup;
     return Domain(mp), mp;
  end if;

  T1:=E!0;ordT1:=1;
  T2:=E!0;ordT2:=1;
  // don't use a large number of primes, it doesn't cost 
  // too much extra work if the torsion bound isn't sharp
  for tup in Factorisation(TorsionBound(E,5)) do
    tor:=pPowerGenerators(E,tup[1]:Bound:=tup[1]^tup[2]);
    if #tor ge 1 then
      T1+:=tor[1][1];
      ordT1*:=tor[1][2];
    end if;
    if #tor eq 2 then
      T2+:=tor[2][1];
      ordT2*:=tor[2][2];
    end if;
  end for;
  if ordT1 eq 1 then
    grp:=AbelianGroup([]);
    mp:=map<grp->E|a:->E!0>;
  elif ordT2 eq 1 then
    grp:=AbelianGroup([ordT1]);
    mp:=map<grp->E|a:->Eltseq(a)[1]*T1>;
  else
    grp:=AbelianGroup([ordT2,ordT1]);
    mp:=map<grp->E|a:->Eltseq(a)[1]*T2+Eltseq(a)[2]*T1>;
  end if;

  E`TorsionSubgroup:=mp;
  return grp,mp;
end intrinsic;

// TO DO: call Saturation

intrinsic IsPSaturated(mwmap::Map,p::RngIntElt)->BoolElt
  {Tests if given MWmap is p-saturated}
  G:=Domain(mwmap);
  pG:=sub<G|[p*g:g in OrderedGenerators(G)]>;
  GModpG,ModMap:=quo<G|pG>;
  return forall{g:g in GModpG| g eq Zero(GModpG) or
    #DivisionPoints(mwmap(g@@ModMap),p) eq 0};
end intrinsic;
