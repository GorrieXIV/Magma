freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Arithmetic Fuchsian groups
// February-May 2006, June 2007, John Voight
//
//////////////////////////////////////////////////////////////////////////////

import "definvs.m" : TotallyPositiveUnits;

intrinsic Factorization(f::RngUPolElt, K::Rng) -> SeqEnum
  {Factorization of f over K, assuming the coefficient ring of f
   is coercible into K.}

  return Factorization(ChangeRing(f,K));
end intrinsic;

function RationalApproximation(x)
// (x::FldReElt) -> FldRatElt
// {Gives a rational approximation to x given by the
// continued fraction of x.}

  cf := ContinuedFraction(x);
  cv := Convergents(cf);
  if cv[2,1] eq 0 then
    return cv[1,1];
  else
    return cv[1,1]/cv[2,1];
  end if;
end function;

//-------------
//
// Isometric circles
//
//-------------

intrinsic IsometricCircle(g::GrpPSL2Elt) -> RngElt, RngElt
  {Returns the center and radius of the set of points in the upper half-plane
   where g acts as a Euclidean isometry.}

  return IsometricCircle(g, UpperHalfPlane());
end intrinsic;

intrinsic IsometricCircle(g::GrpPSL2Elt, H::SpcHyp) -> RngElt, RngElt
  {Returns the center and radius of the set of points in the upper half-plane H
   where g acts as a Euclidean isometry.}

  M := Matrix(g);
  det := Determinant(M);
  return -M[2,2]/M[2,1], 1/Abs(M[2,1]);
end intrinsic;

intrinsic IsometricCircle(g::GrpPSL2Elt, D::SpcHyd) -> RngElt, RngElt
  {Returns the center and radius of the set of points in the unit disc D
   where g acts as a Euclidean isometry.}

  M := Matrix(g, D);
  det := Determinant(M);
  return -M[2,2]/M[2,1], 1/Abs(M[2,1]);
end intrinsic;

//-------------
//
// Basic invariants of Arithmetic Fuchsian groups
//
//-------------

intrinsic QuaternionOrder(G::GrpPSL2) -> .
{The order used to define the Fuchsian group G}
  O := BaseRing(G);
  if Type(O) in {AlgQuatOrd, AlgAssVOrd} then
     return O;
  elif Type(O) eq AlgQuat then
     return MaximalOrder(O);
  else
    require false: "G must be an arithmetic Fuchsian group";
  end if;
end intrinsic;

intrinsic QuaternionAlgebra(G::GrpPSL2) -> AlgQuat
{The algebra used to define the Fuchsian group G}
  O := BaseRing(G);
  if Type(O) in {AlgQuatOrd, AlgAssVOrd} then
     return Algebra(O);
  elif Type(O) eq AlgQuat then
     return O;
  else
     require false: "G must be an arithmetic Fuchsian group";
  end if;
end intrinsic;

intrinsic Volume(G::GrpPSL2) -> FldRatElt
{Same as ArithmeticVolume}
  return ArithmeticVolume(G); 
end intrinsic;

intrinsic ArithmeticVolume(G::GrpPSL2) -> FldRatElt
  {Returns the hyperbolic volume of the quotient of the upper half-plane by G 
   for an arithmetic Fuchsian group G.  The volume is normalized "arithmetic" 
   volume, so the usual volume is divided by pi; this gives an ideal triangle
   volume 1.}

  require Type(BaseRing(G)) in {AlgQuat, AlgQuatOrd, AlgAssVOrd} or assigned G`ShimData :
    "G must be an arithmetic Fuchsian group";

  if assigned G`ShimVolume then
    return G`ShimVolume;
  end if;

  if assigned G`ShimData then
    F := G`ShimData[1];
    D := [pp[1] : pp in Factorization(G`ShimData[2])];
    N := G`ShimData[3];
  else
    if Type(G) eq AlgQuat then
      A := BaseRing(G);
    else
      A := Algebra(BaseRing(G));
    end if;
    F := BaseField(A);
    if Type(F) eq FldRat then
      D := RamifiedPrimes(A);
    else
      D := RamifiedPlaces(A);
    end if;
    N := G`ShimLevel;
  end if;
  d := Degree(F);
  
  R := RealField();
  if Type(F) eq FldRat then
    if #D eq 0 then
      vol := 1/6;
    else
      vol := 1/6* &*[ p-1 : p in D];
    end if;
  else
    // Formula of Shimizu
    Lden := LCM(CyclotomicQuadraticExtensions(F));
    z := Real(Evaluate( LSeries(NumberField(F) : Precision := 6), -1 ));
    tz10 := Log(Lden*Abs(z))/Log(10);
    if tz10 ge 4 then
      z := Real(Evaluate( LSeries(NumberField(F) : Precision := Ceiling(tz10)+3), -1 ));
    end if;
    z := Round(Lden*z)/Lden;
    vol := (-1)^d/2^(d-2)*z;
//             RationalApproximation(Real(Evaluate( LSeries(NumberField(F)), -1 )));
    if #D gt 0 then
      vol *:= &*[ Norm(p)-1 : p in D];
    end if;
  end if;

  for pp in Factorization(N) do
    q := Norm(pp[1]);
    vol *:= q^(pp[2]-1)*(q+1);
  end for;

  if assigned G`ShimTotallyPositiveFlag and G`ShimTotallyPositiveFlag then
    Z_F := MaximalOrder(F);
    UF, mUF := UnitGroup(Z_F);
    vol /:= #TotallyPositiveUnits(Z_F, UF, mUF);
  end if;

  G`ShimVolume := vol;

  return vol;
end intrinsic;

OddLocalEmbeddingNumber := function(d,e,f,pp);
  // Returns the number of embeddings of the order of conductor pp^f in
  // a local quadratic order of discriminant d into an Eichler order of level pp^e.

  k, mk := ResidueClassField(pp);
  kappa := #k;
  pi := SafeUniformiser(pp);
  r := Valuation(d,pp);
  if IsSquare(mk(d/pi^r)) then
    issq := 2;
  else
    issq := 0;
  end if;
 
  if r eq 0 then
    return issq;
  elif e lt r then
    if e mod 2 eq 1 then
      return 2*kappa^((e-1) div 2);
    else
      return kappa^((e div 2)-1)*(kappa+1);
    end if;
  elif e eq r then
    if r mod 2 eq 1 then
      return kappa^((r-1) div 2);
    else
      return kappa^(r div 2) + kappa^((r div 2)-1)*issq;
    end if;
  elif e gt r then
    if r mod 2 eq 1 then
      return 0;
    else
      return kappa^((r div 2)-1)*(kappa+1)*issq;
    end if;
  end if;
/*
  if Valuation(d,pp) eq 0 then
    if f eq 0 then
      if IsSquare(mk(d)) then
        return 2;
      else
        return 0;
      end if;
    else
      if e le f then
        return 1;
      elif e le 2*f then
        return 2;
      else
        if IsSquare(mk(d)) then
          return 2;
        else
          return 0;
        end if;
      end if;
    end if;
  else
    r := Valuation(d,pp);
    if e lt r then
      if e eq 1 then
        return 2;
      elif e eq 2 then
        return 1+#k;
      elif e mod 2 eq 0 then
        return e-1;
      else
        return e;
      end if;
    else
      if r mod 2 eq 1 then
        if e eq r then
          return #k^Floor(r/2);
        else
          return 0;
        end if;
      else
        vprint Shimura: "HEY!", r, e;
        pi := SafeUniformiser(pp);
        issq := IsSquare(mk(d/pi^r));
        if e eq r then
          if issq then
            return #k^(r div 2) + 2*#k^(r div 2-1);
          else
            return #k^(r div 2);
          end if;
        else
          if issq then
            return 2*#k^(r div 2) + 2*(#k)^(r div 2-1);
          else
            return 0;
          end if;
        end if;
      end if;
    end if;
  end if;
*/
end function;

EvenQuadraticHenselLift := function(t,n,pp,m : Al := "Brutal");
  // Returns all solutions to x^2 - t*x + n = 0 (mod pp^m)

  Z_F := Order(pp);
  e := Valuation(Z_F!2,pp);

  pi := SafeUniformiser(pp);
  k, mk := ResidueClassField(pp);

  if Al eq "Brutal" then
    // Brutal enumeration
    sols := [];
    for u in CartesianPower(k,m) do
      x := &+[u[i]@@mk*pi^(i-1) : i in [1..m]];
      if Valuation(x^2-t*x+n,pp) ge m then
        Append(~sols, x);
      end if;
    end for;
    return sols;
  end if;

  // Otherwise, use a Hensel lift, probably could use some debugging.
  // For low-enough levels the algorithm is not really any faster.

  PiEltSeq := function(u,m);
    useq := [];
    for i := 1 to m do
      useq cat:= Eltseq(mk(u));
      u := (u-mk(u)@@mk)/pi;
    end for;
    return useq;
  end function;
  if m lt e then
    mm := m;
  else
    mm := e;
  end if;
  M := Matrix([ PiEltSeq(x^2-t*x,mm) : x in [u@@mk*pi^i : u in Basis(k), i in [0..mm-1]] ] cat 
                [PiEltSeq(-n,mm)] );
  d := #Basis(k);
  N := [v : v in Nullspace(M) | v[mm*d+1] ne 0];
  N := [[ v[i]/v[mm*d+1] : i in [1..mm*d] ] : v in N];
  Nscal := [ u@@mk*pi^i : u in Basis(k), i in [0..mm-1] ];
  N := [&+[ v[i]@@mk*Nscal[i] : i in [1..mm*d]] : v in N];
  if m le e then
    return N;
  end if;

  if m lt 2*e then
    mm := m;
  else
    mm := 2*e;
  end if;
  N4 := [];
  for x in N do 
    if t eq 0 then
      if Valuation(x^2-t*x+n,pp) ge mm then
        Append(~N4, x);
      end if;
    else
      fx := x^2-t*x+n;
      vt := Valuation(t,pp);
      if Valuation(fx/2,pp) ge Min(mm-e,vt) then
        if Valuation(fx/2,pp) ge mm-e then
          for u in CartesianPower(k,mm-e) do
            Append(~N4, x+2*&+[u[i]@@mk*pi^(i-1) : i in [1..mm-e]]);
          end for;
        else
          z := fx/pi^vt*(mk(pi^vt/t)@@mk);
          for u in CartesianPower(k,vt) do
            Append(~N4, x+z+pi^(mm-vt)*&+[u[i]@@mk*pi^(i-1) : i in [1..vt]]);
          end for;
        end if;
      end if;
    end if;
  end for;
  if m le 2*e then
    return N4;
  end if;

  for x in N4 do
    if Valuation(x^2-t*x+n,pp) lt 2*e then
      error "Failed solution", x;
    end if;
  end for;

  return N4;
end function;

EvenLocalEmbeddingNumber := function(t,n,e,pp);
  if Valuation(t^2-4*n,pp) eq 0 then
    emb := #[x : x in EvenQuadraticHenselLift(t,n,pp,e) | Valuation(2*x-t,pp) ge 0];
  else
    q, mq := quo<Order(pp) | pp^(e)>;
    emb := #[x : x in EvenQuadraticHenselLift(t,n,pp,e) | Valuation(2*x-t,pp) ge 0] + 
           #{mq(x) : x in EvenQuadraticHenselLift(t,n,pp,e+1) | Valuation(2*x-t,pp) ge 0};
  end if;
  return emb;
end function;

AlmostTotallyPositiveUnits := function(Z_F, UF, mUF, Foos);
  // Stupid function, the isomorphism {1,-1} -> {0,1}.
  hiota := function(u);
    if u eq -1 then
      return 1;
    else
      return 0;
    end if;
  end function;

  F := NumberField(Z_F);
  UZd := AbelianGroup([2 : i in [1..Degree(F)-1]]);
  phi := hom<UF -> UZd | 
               [[hiota(Sign(Evaluate(mUF(UF.i), v))) : v in Foos] :
                i in [1..#Generators(UF)]]>;
  UFmodsq, fsq := quo<UF | [2*u : u in Generators(UF)]>;
  return fsq(Kernel(phi)), fsq;
end function;

declare attributes FldNum: CyclotomicClassNumbers;

intrinsic CyclotomicClassNumbers(F::FldNum : Bound := 0) -> Tup
  {For a totally real field F, computes and stores the class numbers 
   and associated data for all cyclotomic quadratic extensions of F.}

  Z_F := MaximalOrder(F);
  UF, mUF := UnitGroup(Z_F);

  S := LCM(CyclotomicQuadraticExtensions(F));
  // S = all prime powers m such that [F(zeta_m):F] = 2
  // Now get all possible m such that [F(zeta_m):F] = 2
  Sdiv := [m : m in Divisors(S) | m ne 1 and Valuation(m,2) ne 1]; // avoid repetition
  Sdiv := [m : m in Sdiv |
           forall{ f : f in Factorization(CyclotomicPolynomial(m), F) | Degree(f[1]) eq 2} ];
  Sdiv := [IsEven(m) select m else 2*m : m in Sdiv];
//"Values for q:", Sdiv;

  hKs := [];
  Rs := [];
  Z_Ks := [];

  for i := 1 to #Sdiv do
    s := Sdiv[i];
    vprintf Shimura : "Computing class number for %o\n", s;
    fs := Factorization(CyclotomicPolynomial(s), F)[1][1];
    K := ext<F | fs>;
    Z_K := MaximalOrder(K);
    Z_Ks[i] := Z_K;

    Kabs := AbsoluteField(K);

    // This is the hugely expensive step.
    if Bound cmpeq 0 then
      hK := ClassNumber(Kabs);
    elif Bound cmpeq "BachBound" then
      hK := ClassNumber(Kabs : Bound := Floor(BachBound(Kabs)/40));
    else
      hK := ClassNumber(Kabs : Bound := Bound);
    end if;
    hKs[i] := hK;

    // Compute the order Oq = Z_F[zeta_2s] and its conductor.
    Oq := Order([K.1]);
    Dq := Discriminant(MinimalPolynomial(K.1));
    ff := SquareRoot(Z_F!!Discriminant(Oq)/Discriminant(Z_K));

    UK, mUK := UnitGroup(AbsoluteOrder(Z_K));
    wK := #TorsionSubgroup(UK);

    Rdata := [];

    // Loop over orders by their conductor dff.
    for jf := 1 to #Divisors(ff) do
      dff := Divisors(ff)[jf];

      // if Z_K is maximal, we have Cl(O_dff)/Cl(K) = 1.
      if dff eq ideal<Z_F | 1> then
        Oq := Z_K;
        UOq := UK;
        mUOq := mUK;
        wOq := wK;
        hOq := 1;
      // Otherwise, use the classic formula to compute the relative class number.
      else
        Oq := sub<Z_K | [K!g*zki*Z_K.2 : g in Generators(dff),
                  zki in Generators(PseudoBasis(Module(Z_K))[2][1])]>;
        UOq, mUOq := UnitGroup(AbsoluteOrder(Oq));
        wOq := #TorsionSubgroup(UOq);
        hOq := 1/#quo<UK | [mUOq(u)@@mUK : u in Generators(UOq)]> * AbsoluteNorm(dff) *
                       &*[1-UnramifiedSquareSymbol(Dq,pp[1])/
                          AbsoluteNorm(pp[1]) : pp in Factorization(dff)];
//        assert hOq eq #PicardGroup(AbsoluteOrder(Oq));
      end if;

      // We only take orders where Oq has exact torsion unit group of order s.
      if wOq ne s*2/Gcd(2,s) then
        hQOq := 0;
      else
        // The local unit adjustment.
        UQ := sub<UF | [Norm(Z_K!mUOq(u))@@mUF : u in Generators(UOq)]>;
        QOq := #quo<UQ | [2*u : u in Generators(UF)]>;
        hQOq := hOq/QOq;
      end if;

      Append(~Rdata, <dff, Rationals()!hQOq>);
    end for;

    Rs cat:= [Rdata];
  end for;

  tup := <Sdiv, Z_Ks, hKs, Rs>;
  F`CyclotomicClassNumbers := tup;
  return tup;
end intrinsic;

intrinsic EllipticInvariants(G::GrpPSL2 : 
                    CoerceIntegers := true, Bound := 0) -> SeqEnum
  {Returns the signature of the unit group of an order of A
   as a sequence of elliptic orders with multiplicities.}

  require Type(BaseRing(G)) in {AlgQuat, AlgQuatOrd, AlgAssVOrd} or assigned G`ShimData:
    "G must be an arithmetic Fuchsian group";

  if assigned G`ShimData then
    Z_F := Integers(G`ShimData[1]);
  else
    Z_F := BaseRing(BaseRing(G));
  end if;
  if (not assigned G`ShimTotallyPositiveFlag or G`ShimTotallyPositiveFlag) and NarrowClassNumber(Z_F) gt 1 then
    // Compute the hard way by computing a fundamental domain
    if not assigned G`BaseRing or Type(G`BaseRing) eq FldNum then
      F := G`ShimData[1];
      B := QuaternionAlgebra(G`ShimData[2], RealPlaces(F)[1..Degree(F)-1]);
      Omax := MaximalOrder(B);
      O := Order(Omax, G`ShimData[3]);
      G`BaseRing := O;
      G`EichlerOrder := true;
      G`ShimLevel := G`ShimData[3];
      G`MatrixRepresentation := FuchsianMatrixRepresentation(B);
      G`MatrixGroup := Codomain(G`MatrixRepresentation);
      G`IsShimuraGroup := true;
      G`ShimTotallyPositiveFlag := true;
    end if;
    _ := FundamentalDomain(G);
    U := Group(G);
    R := Relations(U);
    
    RelationOrder := function(r);
      assert Eltseq(RHS(r)) eq [];
      g := Eltseq(LHS(r));
      n := #g;
      if #SequenceToSet(g) eq 1 then
        return n;
      else
        D := [d : d in Divisors(n) | d ne 1 and 
                &and[g[1..d] eq g[(i-1)*d+1..i*d] : i in [1..n div d]]];
        if #D eq 0 then
          return 1;
        else
          return n div Min(D);
        end if;
      end if;
    end function;

    qs := [];
    es := [];
    for r in R do
      q := RelationOrder(r);
      if q ne 1 then
        if q in qs then
          es[Index(qs,q)] +:= 1;
        else
          Append(~qs, q);
          Append(~es, 1);
        end if;
      end if;
    end for;
    sig := [<qs[i], es[i]> : i in [1..#qs]];
    G`ShimEllipticInvariants := sig;
  end if;

  // If already computed, just return the previous result.
  if assigned G`ShimEllipticInvariants then
    return G`ShimEllipticInvariants;
  end if;

  Z_F := BaseRing(BaseRing(G));
  UF, mUF := UnitGroup(Z_F);
  if assigned G`ShimTotallyPositiveFlag and G`ShimTotallyPositiveFlag and
    #TotallyPositiveUnits(Z_F, UF, mUF) gt 1 then
    U, m := Group(G);
    R := [LHS(r) : r in Relations(U)];
    replength := function(r);
      esr := Eltseq(r);
      lesr := #esr;
      return #esr/Min([d : d in Divisors(lesr) | esr eq &cat[esr[1..d] : i in [1..(lesr div d)]]]);
    end function;
    Rlen := [replength(r) : r in R];
    Rlen := Sort([r : r in Rlen | r ne 1]);
    sig := Sort([<r, #[x : x in Rlen | x eq r]> : r in SequenceToSet(Rlen)]);
    G`ShimEllipticInvariants := sig;
    return sig;
  end if;

  // If the Shimura group is defined without computing the underlying algebra,
  // assign the various fields.
  if assigned G`ShimData then
    F := G`ShimData[1];
    D := [pp[1] : pp in Factorization(G`ShimData[2])];
    N := G`ShimData[3];
    Foos := RealPlaces(F)[1..Degree(F)-1];
  else
    if Type(G) eq AlgQuat then
      A := BaseRing(G);
    else
      A := Algebra(BaseRing(G));
    end if;
    F := BaseField(A);
    if Type(F) eq FldRat then
      D := RamifiedPrimes(A);
    else
      D, Foos := RamifiedPlaces(A);
    end if;
    N := G`ShimLevel;
  end if;

  // If F is the rationals, then there is an easy formula.
  if Type(F) eq FldRat then
    if N mod 4 eq 0 then
      e2 := 0;
    else
      e2 := &*[1-KroneckerSymbol(-4,p) : p in D];
      if N gt 1 then
        e2 *:= &*[1+KroneckerSymbol(-4,p) : p in PrimeDivisors(N)];
      end if;
    end if;
    if N mod 9 eq 0 then 
      e3 := 0;
    else       
      e3 := &*[1-KroneckerSymbol(-3,p) : p in D];
      if N gt 1 then
        e3 *:= &*[1+KroneckerSymbol(-3,p) : p in PrimeDivisors(N)];
      end if;
    end if;
    sig := [<2, e2>, <3, e3>];

  // Otherwise, we gotta work.
  else
    if Type(F) eq FldOrd then
      F := NumberField(F);
    end if;
    Z_F := MaximalOrder(F);

    Z_F := MaximalOrder(F);
    if #D eq 0 then
      Dprod := ideal<Z_F | 1>;
    else
      Dprod := &*D;
    end if;

    sig := [];
    N := Factorization(N);
   
    // Compute the unit group and class group.
    UF, mUF := UnitGroup(Z_F);
    hF := ClassNumber(F);

    // Compute associated field data.
    if not assigned F`CyclotomicClassNumbers then
      F`CyclotomicClassNumbers := CyclotomicClassNumbers(F : Bound := Bound);
    end if;
    Fshim := F`CyclotomicClassNumbers;

    // Iterate over each possible elliptic cycle order length s.
    for i := 1 to #Fshim[1] do
      s := Fshim[1][i];
      es := [Rationals()|];

      Z_K := Fshim[2][i];

      for R in Fshim[4][i] do
        if R[1] + Dprod ne ideal<Z_F | 1> then
          Append(~es, 0);
          continue;
        end if;

        dff := R[1];
        es0 := R[2];

        // The local embedding numbers are easy for primes dividing the discriminant of B.
        if #D gt 0 then
          for p in D do
            pKfact := Factorization(Z_K!!p);
            if #pKfact eq 2 then 
              es0 *:= 0;
            elif pKfact[1][2] eq 1 then
              es0 *:= 2;
            end if;
          end for;
        end if;

        // Embedding numbers for primes dividing N are complicated!
        if #N gt 0 then
          for qq in N do
            dffzk := dff*PseudoBasis(Module(Z_K))[2][1];
            e := Valuation(dffzk,qq[1]);
            if dffzk eq qq[1]^e then
              dffzkpF := [];
            else
              dffzkpF := Factorization(dffzk/qq[1]^e);
            end if;
            u := WeakApproximation([pp[1] : pp in dffzkpF] cat [qq[1]],
                                   [pp[2] : pp in dffzkpF] cat [0]);
            pi := SafeUniformiser(qq[1]);
            alpha := u*Z_K.2*pi^e;
            f := Eltseq(MinimalPolynomial(alpha));

            if Norm(qq[1]) mod 2 eq 0 then
              es0 *:= EvenLocalEmbeddingNumber(-f[2],f[1], qq[2], qq[1]);
            else
              es0 *:= OddLocalEmbeddingNumber(f[2]^2-4*f[1], qq[2], Valuation(dff,qq[1]), qq[1]);
            end if;
          end for;
        end if;
        Append(~es, es0);
      end for;

      hK := Fshim[3][i];
      e := hK/hF*&+es;
      if e gt 0 then
        if CoerceIntegers then
          Append(~sig, <s div 2, Integers()!e>);
        else
          Append(~sig, <s div 2, e>);
        end if;
      end if;
    end for;
  end if;

  G`ShimEllipticInvariants := sig;

  return sig;
end intrinsic;

intrinsic Signature(G::GrpPSL2) -> Tup
  {Returns the signature of the Fuchsian group G.}

  if Type(BaseRing(G)) notin {AlgQuat, AlgQuatOrd, AlgAssVOrd} and not 
    assigned G`IsShimuraGroup then
    StabilizerOrder := function(g);
      if Trace(Matrix(g)) eq 0 then
        return 2;
      else
        return 3;
      end if;
    end function;
    return <Genus(G), 
            [StabilizerOrder(Stabilizer(z,G)) : z in EllipticPoints(G)], 
          #Cusps(G)>;
  end if;

  inv := EllipticInvariants(G);
  sig := [Integers()|];
  for i := 1 to #inv do
    for j := 1 to Integers()!inv[i][2] do
      Append(~sig, inv[i][1]);
    end for;
  end for;
  return <Genus(G), Sort(sig)>;
end intrinsic;

//-------------
//
// Substitute definite norm; takes the inverse radius at the split real place.
//
//-------------

// dn_init splits out initializations that are
// independent of the element, to avoid repeating them
// SRD, Feb 2011

function dn_init(A, q);
 
  F := BaseField(A);
  real_places := RealPlaces(F);
  indx := Index(real_places,SplitRealPlace(A));

  if Type(q) eq RngIntElt then
    prec := A`prec;
  else
    prec := Parent(q)`prec;
  end if;

  h := FuchsianMatrixRepresentation(A : Precision := prec);
  p := DiscToPlane(UpperHalfPlane(), q);
  p := ComplexValue(p);

  return [* F, real_places, indx, h, p *];
end function;

function dn(gamma, w, init)

  F, real_places, indx, h, p := Explode(init);

  if Type(p) eq SpcHydElt then
    prec := Parent(p)`prec;
  else
    prec := Precision(Parent(p));
  end if;

  hg := h(gamma);
  fgp := hg[2,1]*p^2+(hg[2,2]-hg[1,1])*p-hg[1,2];
  if w cmpeq [] then
    s := Trace(Norm(gamma)) + Abs(fgp)^2/(2*Im(p)^2);
  else
    Ngamma := Norm(gamma);
    s := 0;
    for i := 1 to Degree(F) do
      s +:= w[i]*Evaluate(Ngamma,real_places[i] : Precision := prec);
    end for;
    s +:= w[indx]*Abs(fgp)^2/(2*Im(p)^2);
  end if;

  return s;
end function;

intrinsic DefiniteNorm(gamma::AlgQuatElt : q := UnitDisc()!0, w := []) -> FldReElt
  {Returns a definite norm of gamma.}

  A := Parent(gamma);
  init := dn_init(A, q);

  return dn(gamma, w, init);
end intrinsic;

intrinsic DefiniteGramMatrix(B::SeqEnum[AlgQuatElt] : q := UnitDisc()!0, w := []) -> FldReElt
  {Returns a definite Gram matrix for the basis B.}

  A := Universe(B);
  init := dn_init(A, q);
  prec := Parent(q)`prec;

  N := [dn(b, w, init) : b in B];
  M := DiagonalMatrix(RealField(prec), [2*n : n in N]);
  for i := 1 to #B do
    for j := i+1 to #B do
      mij := dn(B[i]+B[j], w, init) - N[i] - N[j];
      M[i,j] := mij;
      M[j,i] := mij;
    end for;
  end for;

  return M;
end intrinsic;

//-------------
//
// Miscellaneous
//
//-------------

intrinsic MultiplicativeOrder(gamma::AlgAssVOrdElt : PlusMinus := true) -> SeqEnum
  {}

  A := Algebra(Parent(gamma));
  require Type(A) eq AlgQuat : 
    "Hastily implemented only for quaternion algebras";

  return MultiplicativeOrder(A!gamma : PlusMinus := PlusMinus);
end intrinsic;

intrinsic MultiplicativeOrder(gamma::AlgQuatElt : PlusMinus := true) -> SeqEnum
  {Computes the order of the element gamma of a quaternion algebra; 
   either a finite number or $0$.  If PlusMinus eq true, then 
   compute the order in the group of units modulo -1.}

  if gamma eq 0 then 
    return 0;
  end if;

  m := LCM(CyclotomicQuadraticExtensions(BaseField(Parent(gamma))));
  for d in Divisors(m) do
    if gamma^d eq 1 or (gamma^d eq -1 and PlusMinus) then
      return d;
    end if;
  end for;
  return 0;
end intrinsic;
