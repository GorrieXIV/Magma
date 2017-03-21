freeze;
//

/*
 * k<w> := GF(4);
   kt<t> := PolynomialRing(k);
   kty<y> := PolynomialRing(kt);
   K := FunctionField(y^3 + t^3 + w^2*t^2 + w*t + w^2);
   lp := InfinitePlaces(K);
   ChangeModel(K, lp[1]);
   KK := $1;
   InfinitePlaces(KK);
   lp := $1;
   AnalyticDrinfeldModule(KK, lp[1]);
 * to AlgebraicDrinfeldModule...
 *
 * Degree(P) eq 2!!
 * k := GF(5);
 * kt<t> := PolynomialRing(k);
 * kty<y> := PolynomialRing(kt);
 * K := FunctionField(y^2 + 3*t^4 + 3*t^3 + 3*t^2 + 3*t);
 * P := InfinitePlaces(K)[1];
 *    s := InternalSolve(b, Eltseq(n2)[i], MyExpand(KK!x, P:RelPrec := prec, Store), px+1);
 *    t := [&cat [Eltseq(x) : x in Eltseq(s[i])] : i in [1..Nrows(s)]];
 *    t := Matrix(t);
 *    k := KernelMatrix(t);
 *    Nrows(k);
 *
 * 
 * <example>
 
   k<w> := GF(4);
   kx<x> := PolynomialRing(k);
   kxy<y> := PolynomialRing(kx);
   K := FunctionField(y^3+x*y*w+x^2+w*x+1);
   // has C6 class group
   //

   lp := InfinitePlaces(K);
   D, U := HCF(K, lp[1]);
   H := AbelianExtension(D, U);

   g := [x, K.1];

   prec := 200;
   R := LaurentSeriesRing(ResidueClassField(lp[1]));
   time exp  := Exp(PolynomialRing(R).1, lp[1]:InfBound := 8, Map := 
          func<x|MyExpand(x, lp[1]:RelPrec := prec)>);
   time z := AnalyticModule(g[1], lp[1]: Ex := exp, Map := func<x|MyExpand(x, 
          lp[1]:RelPrec := prec)>);
   _, n1, z1 := CanNormalize(z);
   time zz := AnalyticModule(g[2], lp[1]: Ex := exp, Map := func<x|MyExpand(x, 
           lp[1]:RelPrec := prec)>);
   _, n2, z2 := CanNormalize(zz);

   M := MyMaximalOrder(H);
   MI := MyMaximalOrder(H:Infinite);
   B := MyBasis(M, kx);
   B := ShortBasis(Divisor(1*M));
   time b := [ MyExpand(x, lp[1]:RelPrec := prec,Store) : x in B];
   max_x := 10+1;
   assert max_x*#B le prec; 
   s := InternalSolve(b, Eltseq(n2)[2], MyExpand(K!kx.1, lp[1]:RelPrec := prec,Store), max_x);
   k := KernelMatrix(s);
   e := Eltseq(k);
   &+ [ B[i]*Polynomial(e[(i-1)*n+1..i*n]) : i in [1..#B]] where n := max_x;
   y := $1;
   l2 := TwistedPolynomials(H)![g[2], 0, y, 0, 1];
   l1 := Extend(l2, g[1], lp[1]);


   
   G := GensToPoly(g, lp[1], K);
   GetRelations(g, G);
   time B := Combine($1, K, lp[1]);
   time dr := DrinfeldModule(g, G, B);
   p2 := Places(K, 2);

   TwoGenerators(p2[1]);
   A := dr(G[1]) + w^2;
   B := dr(G[2])^2 + w^2*dr(G[2]) + dr(G[1]);
   time C := GCD(A,B);


   k := GF(2);
   kx<x> := PolynomialRing(k);
   kxy<y> := PolynomialRing(kx);
   K := FunctionField(y^2+y+x^3+x); // C5?
   lp := InfinitePlaces(K);
   g := [x, K.1];
   G := GensToPoly(g, lp[1], K);
   GetRelations(g, G);
   B := Combine($1, K, lp[1]);
   dr := DrinfeldModule(g, G, B);
   p := Places(K, 4)[2];
   TwoGenerators(p);
   time A := dr(G[1]^4 + G[1]^3 + G[1]^2 + G[1] + 1);
   time B := dr(G[2] + G[1]^4 + G[1]^2 + G[1] + 1);
   time C := GCD(A,B);
   Degree(C);
   f := Polynomial(C);
   LeadingCoefficient(f);
   f / $1;
   $1 div Parent(f).1;
   F := $1;
   Fp := FunctionField(F);

===================================================================
   k<w> := GF(4);
   kx<x> := PolynomialRing(k);
   kxy<y> := PolynomialRing(kx); 
   K := FunctionField(y^3+y+x^4+x^3+y^2);  // C12xC12 - REALLY difficult
   lp := InfinitePlaces(K);
   g := [x, K.1];
   r := Expand(g[1], lp[1]);
   R := Parent(r);
   prec := 2000;
   time exp  := Exp(PolynomialRing(R).1, lp[1]:InfBound := 7, Map := 
     func<x|MyExpand(x, lp[1]:RelPrec := prec, Store)>);
   time z := AnalyticModule(g[1], lp[1]: Ex := exp, Map := func<x|MyExpand(x, 
     lp[1]:RelPrec := prec, Store)>);
   _, n1, z1 := CanNormalize(z);
   time zz := AnalyticModule(g[2], lp[1]: Ex := exp, Map := func<x|MyExpand(x, 
     lp[1]:RelPrec := prec, Store)>);
   _, n2, z2 := CanNormalize(zz);



   
   
   G := GensToPoly(g, lp[1], K);
   r := GetRelations(g, G);
   R5 := PolynomialRing(K, 5);
   R12 := Universe(r);
   hh := hom<R12->R5 | [0,R5.1,0,R5.2,0,0,R5.3,0,R5.4,0,R5.5,0]>;
   rr := hh(r);
   rr := [rr[3], rr[5], rr[7], rr[9], rr[11],rr[13]];
   n2 := Parent(n1)!Eltseq(n2);
   GG := [TwistedPolynomials(R5) | [ g[1],R5.1, R5.2, 1], [g[2], 
     R5.3,R5.4,R5.5,1]]; 
   n2 := Parent(n1)!Eltseq(n2);  
   s := LiftAll([n1, n2], GG, rr[1..5], lp[1]: RelPrec := 10000);
   // g := Gcd(s[1], s[2]);

   time    s, t := LiftAll([n1, n2], GG, rr[1..5], lp[1]: RelPrec := 35000); //30min
   M := MyMaximalOrder(H); 
   B := MyBasis(M, kx); 
   time eB := [ MyGetLowPrecisionExpand(x, lp[1]:RelPrec := 35000) : x in B];  //approx 10h

 =========================================================
   k := GF(2);
   kx<x> := PolynomialRing(k);
   kxy<y> := PolynomialRing(kx);
   K := FunctionField(y^3 + (x^4 + x^3 + x^2 + x + 1)*y + x^6 + x^5 + x + 1);
   ClassGroup(K);
   Places(K, 1);
   ChangeModel(K, $1[1]);
   K, mK := $1;
   InfinitePlaces(K);
   Degree($1[1]);
   lp := InfinitePlaces(K);
   RiemannRochSpace(lp[1]);
   RiemannRochSpace(2*lp[1]);
   MaximalOrderFinite(K);
   g := K!$2.2;
   g;
   R := LaurentSeriesRing(ResidueClassField(lp[1]));
   prec := 1000;
   SetIsClaus(false);
   time exp  := Exp(PolynomialRing(R).1, lp[1]:InfBound := 10, Map := 
         func<x|MyExpand(x, lp[1]:RelPrec := prec, Store)>);
   time z := AnalyticModule(g, lp[1]: Ex := exp, Map := 
         func<x|MyExpand(x, lp[1]:RelPrec := prec, Store)>);
   _, n2, z2 := CanNormalize(z);
   D, U := HCF(K, lp[1]);
   H := AbelianExtension(D, U);
   M := MyMaximalOrder(H);
   B := MyBasis(M, kx);
   time b := [ MyExpand(x, lp[1]:RelPrec := 1000,Store) : x in B];
   s := InternalSolve(b, Eltseq(n2)[2], MyExpand(K!kx.1, lp[1]:RelPrec := 1000,Store), 
     50);
   k := KernelMatrix(Submatrix(s, 1, 1, 401, 900));
   e := Eltseq(k);
   &+ [ B[i]*Polynomial(e[(i-1)*n+1..i*n]) : i in [1..#B]] where n := 50;
   y := $1;
   l2 := TwistedPolynomials(H)![g, y, 1];

 =========================================================
  
   k := GF(2);
   kx<x> := PolynomialRing(k);
   kxy<y> := PolynomialRing(kx);
   K := FunctionField(y^2+y+x^3+1); // C3

   lp := InfinitePlaces(K);
   D, U := HCF(K, lp[1]);
   H := AbelianExtension(D, U);

   g := [x, K.1];
   G := GensToPoly(g, lp[1], K);
   r := GetRelations(g, G);

   R := LaurentSeriesRing(ResidueClassField(lp[1]));

   exp  := Exp(PolynomialRing(R).1, lp[1]:InfBound := 7, Map := 
     func<x|MyExpand(x, lp[1]:RelPrec := 100)>);
   z := AnalyticModule(g[1], lp[1]: Ex := exp, Map := func<x|MyExpand(x, 
     lp[1]:RelPrec := 100)>);
   _, n1, z1 := CanNormalize(z);
   zz := AnalyticModule(g[2], lp[1]: Ex := exp, Map := func<x|MyExpand(x, 
     lp[1]:RelPrec := 100)>);
   _, n2, z2 := CanNormalize(zz);

   n2 := Parent(n1)!Eltseq(n2);
   q := LiftAll([n1, n2], G, r[2..4], lp[1]);

   xx := RelExpand(H!g[1], P:RelPrec := 40);
   yK := RelExpand(H!K.1, P:RelPrec := 40);

   b := Basis(MaximalOrderFinite(H));
   b := [ RelExpand(x, P:RelPrec := 40) : x in b];
   B := b cat [ yK*x : x in b];
   pi := RelExpand(H!UniformizingElement(lp[1]), P:RelPrec := 40);
   q1 := Evaluate(ChangePrecision(q[1], 40), pi);
   InternalSolve(B, q1, xx, 6);
   KernelMatrix($1);
   e := Eltseq($1);
   bH := Basis(MaximalOrderFinite(H));
   BH := bH cat [ K.1*x : x in bH];
   &+ [ BH[i]*Polynomial(e[(i-1)*6+1..i*6]) : i in [1..6]];
   hh := $1;
   nH1 := TwistedPolynomials(H)![x, hh, 1];
   nH2 := Extend(nH1, g[2], lp[1]);
   h := hom<Universe(r) -> H | [hh, Eltseq(nH2)[2], Eltseq(nH2)[3]]>;
   h(r);
   // proves that this is THE Drinfeld module we were looking for!

====================================================

   k := GF(3);
   kx<x> := PolynomialRing(k);
   kxy<y> := PolynomialRing(kx);
   kx<x> := PolynomialRing(k);
   kxy<y> := PolynomialRing(kx);
   K := FunctionField(y^3+x^2+y+1);
   Genus(K);
   ClassGroup(K);
   lp := InfinitePlaces(K);
   #lp;
   MaximalOrderFinite(K);

   D, U := HCF(K, lp[1]);
   H := AbelianExtension(D, U);
   g := [x, K.1];
   R := LaurentSeriesRing(ResidueClassField(lp[1]));
   exp  := Exp(PolynomialRing(R).1, lp[1]:InfBound := 7, Map := 
      func<x|MyExpand(x, lp[1]:RelPrec := 300)>);

   
   G := GensToPoly(g, lp[1], K);
   GetRelations([x, K.1], G);
   i := Ideal($1);
   B := Basis(GroebnerBasis(i));
   dr := DrinfeldModule(g, G, Basis(B));
   
   </example>
 */

/////////////////////////////////////////////////////////////////////////
//
//                         General Stuff
//
////////////////////////////////////////////////////////////////////////


declare verbose Drinfeld, 2;

intrinsic HilbertClassField(K::FldFun, I::PlcFunElt) -> FldFunAb
  {The Hilbert class field of K, ie. the maximal unramified Abelian extension where I is totally split.}
  
  D := DivisorGroup(K)!0;  
  R, mR := RayClassGroup(D);
  U := sub<R | I@@mR>;

  return AbelianExtension(D, U);
end intrinsic;

declare attributes RngFunOrd: BasisGenerators;

intrinsic MyMaximalOrder(F::FldFun:Infinite := false) -> RngFunOrd
  {Computes the maximal order of F componentwise.}
  l := DefiningPolynomials(F);
  vprint Drinfeld, 1: "initial maximal orders...";
  if Infinite then
    mo := MaximalOrderInfinite;
    eo := EquationOrderInfinite;
    // XXX: works ONLY if the coeff. ring has a maximal equation order.
    // eo(F) is an equation order over an equation order. What we need is
    // the equation order over the maximal order....
  else
    mo := MaximalOrderFinite;
    eo := EquationOrderFinite;
  end if;
  vprint Drinfeld, 1: "Computing the component maximal orders...";
  vtime Drinfeld, 2: l := [ mo(FunctionField(i:Check := false)) : i in l];

  B := [];
  I := [];
  for i in [1..#l] do
    h := hom<FunctionField(l[i]) -> F | F.i>;
    b := Basis(l[i]);
    pb := PseudoBasis(Module(l[i]));
    Append(~B, [h(x) : x in b]);
    Append(~I, [x[1] : x in pb]);
  end for;

  vprint Drinfeld, 2: "Forming products of the basis";
  b := [ &* [x[y] : y in [1..#B]] : x in CartesianProduct(B)];
  i := [ &* [x[y] : y in [1..#B]] : x in CartesianProduct(I)];
  vprint Drinfeld, 1:  "Order()...";            
  if (eo(CoefficientRing(F)) ne mo(CoefficientRing(F))) then
    vprint Drinfeld, 2 : "Creating from generators";
    vtime Drinfeld, 2: O := Order(mo(CoefficientRing(F)), 
      &cat [[b[j]*x : x in Generators(i[j])] : j in [1..#b]] : Order := true, Verify := false);
  else
    vprint Drinfeld, 2: "Creating with module";
    M := Module([<i[x], 1/d*Vector(Eltseq(c)) where 
                c,d := IntegralSplit(b[x], eo(F))> : x in [1..#b]]);
    vtime Drinfeld, 2: O := Order(eo(F), M:Check := false);
  end if;
  O`BasisGenerators := B;
  /* TODO:
   * WE can (and should) do better. If the discriminants in l are coprime
   * this works too and if not, then we know the small set of places that need
   * attention. On the other hand, here we need only the HCF case....
   */
  vprint Drinfeld, 1: "Discriminant()..."; 
  fail := false;
  for i in [1..#l] do
    for j in [i+1..#l] do
      if Discriminant(l[i]) + Discriminant(l[j]) ne 1*CoefficientRing(l[1]) then
        fail := true;
        break;
      end if;
    end for;
    if fail then break; end if;
  end for;
  if not fail then 
    SetOrderMaximal(O, true);
  end if;
  return O;
end intrinsic;

intrinsic MyBasis(I::RngFunOrdIdl, R::Rng) -> []
  {}

  M := Order(I);
  if Type(CoefficientRing(M)) eq RngUPol then
    b := Basis(I);
  else
    pb := PseudoBasis(Module(I));
    error "Not implemented yet";
  end if;

  return b;
end intrinsic;    

intrinsic MyBasis(M::RngFunOrd, R::Rng) -> []
  {In the implemented case, this returns a R-basis for M}
  if R cmpeq CoefficientRing(M) then
    return Basis(M);
  else
    require CoefficientRing(CoefficientRing(M)) cmpeq R:
      "cannot do too many steps (yet)";
    b := Basis(M);
    li := [x[1] : x in PseudoBasis(Module(M))];
    li := [ Basis(i) : i in li];
    return &cat [ [ x*b[j] : x in li[j]] : j in [1..#b]];
  end if;
end intrinsic;


intrinsic Sign(x::FldFunElt, I::PlcFunElt:PE := false) -> FldFinElt
  {The sign of x at I, ie. the 1st non-zero coefficient in the expansion.}
  if Degree(I) eq 1 then  
    if PE cmpne false then  
      r := MyExpand(x, I, PE:RelPrec := 1);
      r := Eltseq(r);
      assert r[1] eq Eltseq(Expand(x, I, PE:RelPrec := 1))[1];
    else
      r := MyExpand(x, I:RelPrec := 1);
      r := Eltseq(r);
      assert r[1] eq Eltseq(Expand(x, I:RelPrec := 1))[1];
    end if;
//    assert #r eq 1;
    return r[1];
  else
    x := x/UniformizingElement(I)^Valuation(x, I);
    return Evaluate(x, I);
  end if;
end intrinsic;

intrinsic ChangeModel(K::FldFun, P::PlcFunElt) -> FldFun, Map
  {Change the representation of K so that P is the only infinite place.}

  function FindPi()
    n := 1;
    repeat
      R := RiemannRochSpace(n*P);
      for i in R do
        pi := K!i;
        if Valuation(pi, P) ne -n then
          continue;
        end if;
        f := MinimalPolynomial(pi);
        if Degree(f) lt Degree(K) then
          continue;
        end if;
        return pi, f;
      end for;
      n +:= 1;
    until false;
  end function;

  pi, f := FindPi();

  kxy<y> := Parent(f);
  kx<x> := CoefficientRing(f);
  if Type(kx) ne RngUPol then
    kx := RingOfIntegers(kx);
    f := MinimalPolynomial(pi, kx);
    kxy<y> := Parent(f);
  end if;

  h :=hom<kx -> kxy|y>;
  h := hom<kxy -> kxy | hom<kx -> kxy|y>, x>;
  KK := FunctionField(h(f)); // make sure it's seperating!

  m := hom<KK -> K | hom<CoefficientRing(KK) -> K | pi>, K!x>;
  KKT<T> := PolynomialRing(KK);
  ff := hom<kxy -> KKT | hom<kx -> KKT|KK.1>, T>(DefiningPolynomial(K));
  rr := Roots(ff);
  assert #rr ge 1;
  for i in rr do
    if m(i[1]) eq K.1 then
      r := i[1];
    end if;
  end for;
  mm := hom<K -> KK | hom<CoefficientRing(K) -> KK| KK.1>, r>;
  KKK, mKKK := OptimizedRepresentation(KK);
  return KKK, map<KK -> K | x:->m(x), y:->mm(y)>*mKKK;
end intrinsic;

intrinsic RationalReconstruction(e::FldFunElt, f::RngUPolElt) -> BoolElt, FldFunElt
  {Tries to apply rational reconstruction modulo f to all coefficients of e.}
  if e eq 0 then return true, e;  end if;
  K := Parent(e);  
  e := Eltseq(e);  
  kx := Parent(f);
  q, mq := quo<kx|f>;
  i := 1;
  repeat
    fl, x := RationalReconstruction(q!kx!e[i]);
    if fl then
      e[i] := x;
      i +:= 1;
    else
      return false, _;
    end if;
  until i gt #e;
  return true, K!e;
end intrinsic;

///////////////////////////////////////////////////////////////////////////
//
//                    ANALYTIC THEORY
//                    
//////////////////////////////////////////////////////////////////////////
/*
 * According to the new book on function fields, a Drinfeld module is uniquely
 * determined by the image of any non-constant. (Rem. 2.4.3, page 43)
 * Extend realises this. ImA is the image of any non-constant (which we can
 * recover as the abolsute term) and b is the element where we want the image
 * of.
 * Note that if ImA is just a random polynomial, we can still compute b - but
 * in general we won't get a homomorphism defined this way.
 */

intrinsic MinimalPolynomial(x::FldFunOrdElt) -> RngUPolElt
  {The minimal polynomial of x.}
    return MinimalPolynomial(FunctionField(Order(Parent(x)))!x);
end intrinsic;

intrinsic AnalyticDrinfeldModule(K::FldFun, P::PlcFunElt: Class := false) -> FldFunElt, RngUPolTwstElt
  {For an infinite place P of degree 1 in K, compute the image of a non-constant under a sign-normalised Drinfeld module of rank 1}
 
  require not IsFinite(P) :
    "The 2nd argument must be an infinite place";
  if not true then
    KK, mKK := ChangeModel(K, P);
    P := InfinitePlaces(KK);
    assert #P eq 1;
    P := P[1];
  else 
    KK := K;
    mKK := 1;
  end if;

  // Step1 would be to find an integral element of small valuation at P
  i := 0;
  old_R := false;
  q := false;
  repeat
    D := i*P;
    R, mR := RiemannRochSpace(D);
    if i ne 0 then
      q, mq := quo<R|old_R>;
    end if;
    old_R := R;
    i +:= 1;
  until i ge 2 and Dimension(q) ge 1;
  X := KK!(q.1 @@ mq); 
  if Degree(P) eq 1 then
    X := X/Sign(X, P);
  end if;
  x := CoefficientRing(KK).1;
  vx := Valuation(KK!x, P);
  
  vprint Drinfeld, 1: 
    "The standard transcendental should be ", x, "of valuation", vx;

  vprint Drinfeld, 1: 
    "Using ", X, " as a generator. Should have valuation ", i-1;

  ib := 8;
  C, mC := ClassGroup(KK);
  q, mq := quo<C|P @@ mC>;
  assert IsFinite(q);
  lv := [InternalGetNormalisedDrinfeldVal(X, P:InfBound := ib, Class := y @@mq @ mC) : y in q];
  

  m := Floor(Minimum(&cat lv));

  vprint Drinfeld, 1: "Image should have valuation at least ", m;
  vprint Drinfeld, 2: "valuation vector is bounded by", lv;
  px := Ceiling(m/vx)+0;
  if Degree(P) ne 1 then
    px *:= 5;
  end if;
  vprint Drinfeld, 1: "which means powers of", x, "should be bounded by ", px;

  vprint Drinfeld, 1: "Computing Hilbert class field ...";
  H := HilbertClassField(KK, P);
  H := FunctionField(H);
  vprint Drinfeld, 1: 
    "Class field is of degree", Degree(H), 
    "thus total degree is ", Degree(H)*Degree(KK);

  vprint Drinfeld, 1: "ShortBasis will have ", 
    Degree(H)*Degree(KK)*(px+1), "elements";

  prec := Degree(H)*Degree(KK)*(px+1)-m;
  prec *:= 1;
  aprec := prec;
  repeat
    aprec +:= aprec div 3;

    vprint Drinfeld, 1: "Using precision of ", aprec, "and InfBound", ib;

    vprint Drinfeld, 1: "Computing analytic element...";
    R := LaurentSeriesRing(ResidueClassField(P));
    vtime Drinfeld, 2: exp  := Exp(PolynomialRing(R).1, P: Map := 
                      func<x|MyExpand(x, P:RelPrec := aprec)>, 
                        InfBound := Infinity(),
                        Limit := ib);
    vtime Drinfeld, 2: 
       zz := AnalyticModule(X, P: Ex := exp, Map := func<x|MyExpand(x, 
                                     P:RelPrec := aprec)>);
    if Degree(P) eq 1 then                                 
      _, n2 := CanSignNormalize(zz);
      additional := 0;
    else
      _, n2 := CanNormalize(zz);
      additional := 1;
    end if;
    new_m := Minimum([Valuation(x) : x in Eltseq(n2)]);
    if new_m lt m then
      vprint Drinfeld, 1: "Cancellation: readjusting precision estimates...";
      m := new_m;
      px := Ceiling(m/vx)+0;
      vprint Drinfeld, 1: "means powers of x should be bounded by ", px;
      prec := Maximum(prec, Degree(H)*Degree(KK)*(px+1)-m);
      aprec := prec;
    end if;
  until RelativePrecision(Eltseq(n2)[2]) ge prec + prec div 10;

  vprint Drinfeld, 1: "computing algebraic reprensentation....";
  vprint Drinfeld, 1: "max orders...";
  M := MyMaximalOrder(H);
  _ := MyMaximalOrder(H:Infinite);
  vprint Drinfeld, 1: "short basis...";
  B, S := ShortBasis(Divisor(1*M));
  vprint Drinfeld, 1: "completions of the basis";
  prec -:= vx*(px+1);
//  b := func<|[ MyExpand(x, P:RelPrec := prec, Store) : x in B]>();
//  b := func<|[ Expand(x, P:RelPrec := prec) : x in B]>();
  b := func<|[ MyGetLowPrecisionExpand(x, P:RelPrec := prec) : x in B]>();
  l2 := [H!X];
  for i in [2..-Valuation(X, P)*Degree(P)+additional] do
    if Degree(P) eq 1 then
      s := InternalSolve(b, Eltseq(n2)[i], MyExpand(KK!x, P:RelPrec := prec, Store), px+1);
      k := KernelMatrix(s);
      assert Nrows(k) eq 1;
      e := Eltseq(k);
      y := func<|&+[ B[i]*Polynomial(e[(i-1)*n+1..i*n]) : i in [1..#B]] where n := px+1>();
      vprint Drinfeld, 2: "Powers of ", x, "used:",
        [ Degree(Polynomial(e[(i-1)*n+1..i*n])) : i in [1..#B]] where n := px+1;
      assert Valuation(Eltseq(n2)[i]) gt m or Maximum([ Degree(Polynomial(e[(i-1)*n+1..i*n])) : i in [1..#B]] where n := px+1) ge px-1;
    else
      s := InternalSolve(b, Eltseq(n2)[i], MyExpand(KK!x, P:RelPrec := prec, Store), px+1:Integral := false, Over := ConstantField(K));
      k := KernelMatrix(s);
      assert Nrows(k) ge 1;
      e := Eltseq(k[1]);
      y := func<|&+[ B[i]*Polynomial(e[(i-1)*n+1..i*n]) : i in [1..#B]] where n := px+1>();
      yy := Polynomial(e[(i-1)*n+1..i*n]) where i := #B+1 where n := px+1;
      y := y/yy;
      vprint Drinfeld, 2: "Powers of ", x, "used:",
        [ Degree(Polynomial(e[(i-1)*n+1..i*n])) : i in [1..#B]] where n := px+1;
      vprint Drinfeld, 2: "and", 
        Degree(Polynomial(e[(i-1)*n+1..i*n])) where i := #B+1 where n := px+1;

    end if;
    Append(~l2, -y);
  end for;
  //CanNormalize is too weak. It won't be able to completely normalize
  //for a variety of reasons:
  //- it might need to extend the underlying finite field (easy)
  //- it might not know that it's missing information (difficult) as only
  //  other elements might reveal the incomplete normalisation...
  //assert IsWeaklyZero(LeadingCoefficient(n2)-1);
  if Degree(P) eq 1 then
    assert #Eltseq(LeadingCoefficient(n2)) eq 1; 
    Append(~l2, Eltseq(LeadingCoefficient(n2))[1]);
  end if;
  l2 := TwistedPolynomials(H:q := #ConstantField(FunctionField(P)))!l2;
  return X, l2;
end intrinsic;

intrinsic AlgebraicToAnalytic(R_a :: RngUPolTwstElt, P::PlcFunElt:RelPrec := 5) -> RngUPolTwstElt
  {Given the non-trivial image R_a under a Drinfel module, find approximations for the lattice used to define the module.}

  // The "Plan" is (according to Rosen) as follows:
  // - compute f (a twisted power series) such that
  //   fa = R_a f
  // - the zeros of f should define the correct lattice, f is monic
  //   (and I recon square-free), so f should be the exp-function
  //   for the correct lattice
  // - thus, up to scaling, f should be like exp (well, I may have to guess
  //   the proper class in the class group as well)
  // We'll see.
  //
  // To fa = R_a f we use the following
  // f   = sum j=0 infty f_j t^j
  // R_a = sum i=0 n     a_i t^i
  // Thus
  // fa = sum j=0 infty a^q^j f_j t^j
  // R_a f = sum l=0 infty (sum i=0 n a_i f_l-i^q^i) t^l
  // (after setting f_0 := 1, f_-i := 0, a_0 = a)
  // So we should be able to find the f_i's by using recursion:
  // f_l a + sum i=1 n a_i f_l-i^q^i = a^q^l f_l
  // And therefore
  // f_l = (sum i=1 n a_i f_(l-i)^q^i) / (a^q^l - a)
  // Let's try.

  a := Eltseq(R_a);
  n := #a-1;
  f := [0 : i in [1..n]] cat [1];
  ChangeUniverse(~f, Universe(a));
  q := Parent(R_a)`q;

  for l in [1..RelPrec] do
    f[l+n+1] := ( &+ [ a[i+1]*f[l-i+n+1]^(q^i) : i in [1..n]]) / (a[1]^(q^l) - a[1]);
  end for;

  return Parent(R_a)!f[n+1..#f];
end intrinsic;

intrinsic Extend(ImA::RngUPolTwstElt, b::RngElt, P::PlcFunElt: Map := func<x|x>) -> RngUPolElt
  {Given a non-constant image ImA under a Drinfeld module and an arbitrary integral element b, copute the image of b. P has to be the infinite place used.}
  a := Eltseq(ImA);
  q := #ConstantField(FunctionField(P));
  assert q eq Parent(ImA)`q;

  require Poles(b) eq [P]:
    "The element must only have poles at the 3rd argument";
  d := Degree(P);
  if Type(b) eq FldFunElt then
    d := -Valuation(b, P)*d;
  elif Type(b) eq RngSerLaurElt then
    d := - Valuation(b)*d;
  else
    error "Ring type not supported";
  end if;
  b_orig := b;
  b := [Universe(a)!Map(b)];
  for k in [1..d+1] do
    if #a le k then
      Append(~a, 0);
    end if;
    b[k+1] := 1/(a[1]^(q^k)-a[1]) *
       &+ [ a[i+1]*b[k-i+1]^(q^i) - a[i+1]^(q^(k-i))*b[k-i+1] : i in [1..k]];
  end for;
  //assert IsConstant(b[#b]);

  return Parent(ImA)!b;
end intrinsic;

intrinsic InternalGetExpCoeffVal(P::PlcFunElt: InfBound := 5, Class := false) -> []
  {}
  if Class cmpeq false then  
    s := [ #RiemannRochSpace(i*P) : i in [0..InfBound]];
  else
    s := [ #RiemannRochSpace(i*P+Class) : i in [0..InfBound]];
  end if;
  for i in Reverse([1..InfBound]) do
    s[i+1] -:= s[i];
  end for;
  s[1] -:= 1; // to compensate for the 0

  q := #ConstantField(FunctionField(P));
  v := [0]; // for the leading coeff. of 1
  j := 1;
  while q^j le &+s+1 do
    k := q^j-1;
    l := 0;
    m := 1;
    while k gt 0 do
      n := Minimum(s[m], k);
      l +:= n*(m-1);
      k -:= n;
      m +:= 1;
    end while;
    j +:= 1;
    Append(~v, l);
  end while;
     
  return v;
end intrinsic;

intrinsic InternalGetExpCoeffValError(P::PlcFunElt: InfBound := 5, Class := false) -> []
  {Computes estimates for the error in the coefficients of exp when only using elements on L(InfBound*P) for the approximation.}

  // Based on the following:
  // L_n := RiemannRochSpace(n*P);
  // P_n(t) = prod_{L_n} (r-t) = sum a_i t^i
  // Gamma_n(t) = P_n(t)/a_0
  // P_(n+1) = (P_n(x)^(q-1)-t) * P_n (for some basis element x in L_(n+1)\L_n)
  // Then P_(n+1) = \sum b_i t^i for
  // b_0 = a_0*P_n(x)^(q-1)
  // b_i = a_i*P_n(x)^(q-1) - a_(i-1)^q
  //
  // => for the coefficients of Gamma (=Exp here) we have
  // v(b_i/b_0 - a_i/a_0) 
  //  = v((a_i*r - a_(i-1)^q)/a_0/r - a_i/a_0) 
  //  = v(a_(i-1)^q/b_0) = q*v(a_(i-1)) - v(b_0)

  InfBound +:=1;  
  if Class cmpeq false then
    s := [ #RiemannRochSpace(i*P) : i in [0..InfBound]];
  else
    s := [ #RiemannRochSpace(i*P+Class) : i in [0..InfBound]];
  end if;
  for i in Reverse([1..InfBound]) do
    s[i+1] -:= s[i];
  end for;
  InfBound -:= 1;  

  cf := InternalGetExpCoeffVal(P: InfBound := InfBound, Class := Class);
  // we need to convert from Exp to AdditivePolynomialFromRoots for our estimates (and then back)
  // The conversion is a multiplication/ divison by the product
  // of all elements in L(nP) which is a_0 or b_0.
  
  s[1] -:= 1; // to compensate for the 0

  q := #ConstantField(FunctionField(P));

  s_n := &+ [ s[i] * (i-1) : i in [1..#s-1]];
  // s_n = v(a_0)
  
  cf := [s_n - x : x in cf];
  // cf[i+1] = v(a_i)

  s_n1 := s_n+s[#s]*(#s-1);
  // = v(b_0)-v(a_0) = v(P_n(x)^(q-1))
  
  return [Infinity()] cat [s_n1-q*x : x in cf];
end intrinsic;

intrinsic InternalGetExpVal(x::RngElt, P::PlcFunElt : InfBound := 5, CoeffVal := false, Error := false, Class := false) -> RngIntElt, RngIntElt
  {Computes a lower bound of the valuation of Exp(x) where Exp is the exponetial associated to the MaximalOrderFinite and Expand.}
  if x eq 0 then
    return Infinity();
  end if;
  if CoeffVal cmpeq false then
    if Error then
      CoeffVal := InternalGetExpCoeffValError(P:InfBound := InfBound, Class := Class);
    else
      CoeffVal := InternalGetExpCoeffVal(P:InfBound := InfBound, Class := Class);
    end if;
  end if;
  q := #ConstantField(FunctionField(P));
  v := Valuation(x, P);
  return Minimum([q^(i-1)*v+CoeffVal[i] : i in [1..#CoeffVal]]);
end intrinsic;

intrinsic InternalGetDrinfeldVal(x::RngElt, P::PlcFunElt: InfBound := 5, Error := false, Class := false) -> []
  {Computes lower bounds for the valuation of the coefficients of the image of x under the Drinfeld module.}
  /* Careful: this valuations are wrt. to T = (.)^q and NOT
   *          for                         T = (.)^p
   * The missing valuations are Infinity (the coefficients are zero).         
   */
 
  k := ConstantField(FunctionField(P));   
  c := InternalCosetModABasis(x^-1:Class := Class);
  c := [ &+ [x[i]*c[i] : i in [1..#c]] : x in CartesianPower(k, #c)];
  if Error then
    cf := InternalGetExpCoeffValError(P:InfBound := InfBound, Class := Class);
  else
    cf := InternalGetExpCoeffVal(P:InfBound := InfBound, Class := Class);
  end if;
  c := [InternalGetExpVal(x, P:CoeffVal := cf, Error := Error, Class := Class) : x in c | x ne 0];
  if Error then
    c := Sort(c);
  else
    c := Reverse(Sort(c));
  end if;
  q := #k;
  v := Valuation(x, P);
  return [v] cat [v*q^i-&+ c[1..q^i-1] : i in [1..Ilog(q, #c+1)]];
end intrinsic;

intrinsic InternalGetNormalisedDrinfeldVal(x::RngElt, P::PlcFunElt: InfBound := 5, Class := false) -> RngIntElt
  {Computes lower bounds for the valuation of the coefficients of the image of x under the sign normalised Drinfeld module.}
  v := InternalGetDrinfeldVal(x, P: InfBound := InfBound, Class := Class);  
  q := #ConstantField(FunctionField(P));
  n := -Valuation(x, P)*Degree(P);
  assert #v eq n+1;
  ChangeUniverse(~v, Rationals());

  v_zeta := v[n+1]/(q^n-1);
//  v_zeta;
  for i in [1..n+1] do
    v[i] -:= v_zeta*(q^(i-1)-1);
  end for;
  return v;
end intrinsic;

intrinsic AdditivePolynomialFromRoots(x::RngElt, P::PlcFunElt:
      InfBound := 5, Map := func<x|x>, Class := false, 
      Scale := false, Limit := Infinity(), doExp := false) -> .
  {Computes (essentially) the polynomial whose roots are L(InfBound*P + Class), evaluated at x}
  //Based on Goss, Prop. 1.3.5 page 7
  // the algorithms here is linear (essentially) in InfBound.
  if Type(InfBound) cmpeq RngIntElt then
    Start := InfBound;
  else
    assert doExp;
    Start := 5;
  end if;
  Last := 0;

  tail := [1];
  lastRR := false;
  K := FunctionField(P);
  q := #ConstantField(K);
//  q := #ResidueClassField(P);
  repeat
    //"RR-space for", Start, Last;
    if Class cmpeq false then
      lp := RiemannRochSpace(Start * P);
    else
      lp := RiemannRochSpace(Start * P + Class);
    end if;
    if lastRR cmpne false then
      lpq, mlpq := quo<lp|lastRR>;
      b := [K!(i@@mlpq) : i in Basis(lpq)];
    else
      b := [K!i : i in Basis(lp)];
    end if;
    lastRR := lp;
    if Scale cmpne false and Type(Scale) cmpeq Type(b[1]) then
      b := [i*Scale : i in b];
    end if;
    b := [Map(i) : i in b];
    ImPrec := ISA(Type(b[1]), RngSerElt);
    if Scale cmpne false and Type(Scale) cmpeq Type(b[1]) then
      b := [i*Scale : i in b];
    end if;
    if ImPrec then
      b := Sort(b, func<x,y|Valuation(y)-Valuation(x)>);
    end if;
    Last := Start+1;
    Start := Minimum(Start+1, InfBound);
    if not assigned ll then
      ll := Universe(b);
      PT := TwistedPolynomials(ll: q := #ConstantField(FunctionField(P)));
      AdditivePolynomialFromRoots := PT ![1];
    end if;

    lastPol := AdditivePolynomialFromRoots;
    for i in b do
      AdditivePolynomialFromRoots := (PT!([-SpecialEvaluate(AdditivePolynomialFromRoots, i)^(q-1)] cat tail))*AdditivePolynomialFromRoots;
      AdditivePolynomialFromRoots := PT!Eltseq(AdditivePolynomialFromRoots)[1..Minimum(Degree(AdditivePolynomialFromRoots)+1, Limit)];
      if doExp then
        AdditivePolynomialFromRoots := PT![d*x : x in ePol] where d := 1/ePol[1] where ePol := Eltseq(AdditivePolynomialFromRoots);
      end if;
      if ImPrec then
        AdditivePolynomialFromRoots := PT![ RelativePrecision(x) lt 2 select 0 else x : x in Eltseq(AdditivePolynomialFromRoots)];
      end if;
    end for;
  until Last ge InfBound or 
    (Type(InfBound) ne RngIntElt 
      and forall{x : x in Eltseq(AdditivePolynomialFromRoots - lastPol) | IsWeaklyZero(x)});
  return AdditivePolynomialFromRoots, Last-1;
end intrinsic;

intrinsic Exp(x::RngElt, P::PlcFunElt: InfBound := 5, Map := func<x|x>, Class := false, Scale := false, Limit := Infinity()) -> RngUPolTwstElt
  {An approximation to the Exponential of L(n*P), n -> Infty}
  pl := P;
  P, IB := AdditivePolynomialFromRoots(x, P:InfBound := InfBound, Map := Map, Class := Class, Scale := Scale, Limit := Limit, doExp);  
  PT := Parent(P);
  P := Eltseq(P);
  if true and Type(Universe(P)) eq RngSerLaur then
    e := InternalGetExpCoeffValError(pl:InfBound := IB, Class := Class);
    e := e[1..Minimum(#e, Limit)];
    for i in [2..#P] do
      vprint Drinfeld, 2: "ChangePrecision from ", Valuation(P[i]), RelativePrecision(P[i]), e[i];
      if RelativePrecision(P[i]) ne Infinity() then
        P[i] := ChangePrecision(P[i], Minimum(e[i] - Valuation(P[i]), RelativePrecision(P[i]))+Valuation(P[i]));
      end if;
    end for;
    for i in [#P+1..#e] do
      vprint Drinfeld, 2: "Appending";
//      Append(~P, O(Universe(P).1^e[i]));
      Append(~P, 0);
    end for;
  end if;
  P := PT!P;
  return P;
end intrinsic;


intrinsic InternalCosetModABasis(A::FldFunElt: Class := false) -> []
  {AM mod M is a F_q vectorspce. This computes a basis for it.
   If Class is given, M is replaced by the ideal generating it.}
  K := Parent(A);
  if true or #InfinitePlaces(K) gt 1 then
    Ai := A^-1;
    inf := Poles(Ai);
    require #inf eq 1: "A^-1 can only have 1 pole!";
    assert not IsFinite(inf[1]);
    inf:= inf[1];
    n := 2;
    v := Valuation(A, inf);
    k := Degree(inf)*v;
    assert k gt 0;
    // we are looking for a F_q subspace of dimension k
    // it should be contained in some L((n+v)*inf)/Ai*L(n*inf)
    // Also, the basis found here should be a F_q[A] basis for the
    // maximal order that we cannot compute.
    repeat
      if Class cmpeq false then
        L1, mL1 := RiemannRochSpace((n)*inf);
        L2, mL2 := RiemannRochSpace((n+v)*inf);
      else
        L1, mL1 := RiemannRochSpace((n)*inf + Class);
        L2, mL2 := RiemannRochSpace((n+v)*inf + Class);
      end if;
      L3, mL3 := quo<L2| [ (Ai*mL1(L1.i))@@mL2 : i in [1..Ngens(L1)]]>;
      n +:= 1;
    until Dimension(L3) eq k;
    r := [A*L3.i@@mL3@mL2 : i in [1..k]];
    if Class cmpeq false and GetAssertions() ge 1 then
      function InM(x)
        return Support(PoleDivisor(Divisor(x))) subset [inf];
      end function;
      assert forall{x : x in r|InM(x*Ai)};
      assert forall{x : x in r| forall{y : y in r | x eq y or not InM(x-y)}};
    end if;
    return r;
  else
    M := MaximalOrderFinite(Parent(A));
    Ai := A^-1;

    d := Denominator(Ai, M);
    assert d eq 1;
    dAi := d*Ai;
    I := dAi * M;
    B := BasisMatrix(I);
    Fqx := CoefficientRing(M);
    b := Basis(M);
    L := [];
    for i in [1..Degree(M)] do
      for j in [0..Degree(B[i][i])-1] do
        Append(~L, b[i]*Fqx.1^j*A);
      end for;
    end for;
  end if;
  return L;
end intrinsic;


intrinsic AnalyticModule(x::RngElt, P::PlcFunElt: Ex := false, Map := func<x|x>, InfBound := 5, Class := false, Scale := false) -> .
  {Computes the image of x under "the" Drinfeld module. Ex, when given, must be a twisted polynomial approximating the Exponential fction for this lattice.}
  //Based on Goss, Prop. 1.3.5 page 7
  if Ex cmpeq false then
    R := PolynomialRing(Parent(Map(x)));
    Ex := Exp(R.1, P:InfBound := InfBound, Map := Map, Class := Class);
  end if;
  K := FunctionField(P);
  b := InternalCosetModABasis(x^-1: Class := Class);

  if Scale cmpne false and Type(Scale) cmpeq Type(b[1]) then
    b := [i*Scale : i in b];
  end if;
  b := [Map(i) : i in b];
  if Scale cmpne false and Type(Scale) cmpeq Type(b[1]) then
    b := [i*Scale : i in b];
  end if;
  b := [SpecialEvaluate(Ex, i) : i in b];
  q := #ResidueClassField(P);
  p := #ConstantField(FunctionField(P));
  tail := [1];
  ll := Universe(b);
  PT := TwistedPolynomials(ll:q := p);
  P := PT ![1];
  //TODO: probably s.th. WRONG here....
  for i in b do
    P := (PT!([-SpecialEvaluate(P, i)^(p-1)] cat tail))*P;
    P := PT![x*d : x in Eltseq(P)] where d := 1/ConstantCoefficient(P);
  end for;
  P := Eltseq(P);
  d := Map(x);
  P := [x*d : x in P];
  P := PT!P;
  return P;
end intrinsic;

intrinsic CanNormalize(T::RngUPolTwstElt) -> BoolElt, RngUPolTwstElt, RngElt
  {Scales the image T under the Drinfeld module to have smaller, positive valuations.}
  
  c := Eltseq(T);
  ij := [i-1 : i in [2..#c] | RelativePrecision(c[i]) gt Valuation(c[i])];
  q := Parent(T)`q;
  g, e := XGCD([q^i-1 : i in ij]);
  lg := &* [ c[ij[i]+1]^e[i] : i in [1..#e]];
  for i in ij do
    c[ij[i]+1] *:= lg^((1-q^ij[i]) div g);
  end for;
  return true, Parent(T)!c, lg, g;
end intrinsic;

intrinsic CanSignNormalize(T::RngUPolTwstElt) -> BoolElt, RngUPolTwstElt, RngElt
  {Given a twisted polynomial T (which should be the image under a Drinfeld module), attempt to normalize the leading term to be in the finite field.}
  r := Eltseq(T);
  n := #r - 1;
  e := r[n+1];
  R := Parent(e);
  if ISA(Type(R), RngSer) then
    p := Parent(T)`q;
    q := #CoefficientRing(R);
    v := Valuation(e);
    // First, we fix the valuation to be 0:
    if v mod (p^n-1) ne 0 then
      vprint Drinfeld, 1: "Need to extend the field in order to proceed...";
      P := PuiseuxSeriesRing(CoefficientRing(R));
      P`DefaultPrecision := RelativePrecision(e)*20;
      r := [ IsZero(x) select 0 else elt<P|v, s where s,v := Eltseq(x)>  : x in r];
    else
      P := R;
    end if;
    zeta := P.1^(v/(p^n-1));
    for i in [1..n] do
      // The complicated formula seems to be important for
      // precision loss - it shold be the same as
      // zeta^(1-p^i) - but it's not...
      r[i+1] := P.1^(v/(p^n-1)*(1-p^i)) * r[i+1]; 
    end for;
   
    // Second, we adjust the leading coefficient to be in the finite field.
    e := r[n+1];
    i := -1;
    pr := O(Parent(e).1^Precision(e));
    repeat
      i +:= 1;
      s, v := Eltseq(e^(q^i)+pr);
    until #s eq 1;
    
    z := e^(Modinv(p^n-1, q^i));
    for i in [1..n] do
      r[i+1] := z^(1-p^i) * r[i+1];
    end for;
    // Last: we need to restrict our result back into the original ring.
    if P cmpne R then
      s := [];
      for i in r do
        if IsZero(i) then
          zz := R!0;
        else
          c, v, d := Eltseq(i);
          if d eq 1 then
            zz := elt<R|v, c>;
          else
            zz := elt<R|v, [ c[d*i-1] : i in [1..#c div d]]>;
            error "CF1: ERROR:";
//            i - elt<P|v, s, #s+1 > where s,v := Eltseq(z);
          end if;
          ChangePrecision(~zz, Floor(RelativePrecision(i) +v));
        end if;
        Append(~s, zz);
      end for;
      r := s;
    end if;
    return true, Parent(T)!r, zeta*z;
  else
    // exact ring
    "Sorry - cannot handle exact rings yet";
    return false, _, _;
  end if;
end intrinsic;


intrinsic InternalSolve(B::[], q::RngSerElt, x::RngSerElt, n :: RngIntElt: Integral := true, Over := false) -> .
  {}

  if not Integral then
    Append(~B, q);
  end if;
  if Over cmpeq false then
    es := Eltseq;
    d := 1;
  else
    es := func<X|&cat [Eltseq(x, Over) : x in Eltseq(X)]>;
    d := Degree(CoefficientRing(Parent(q)), Over);
  end if;
  v := [ Valuation(x) : x in B];
  if Valuation(x) lt 0 then
    v := Minimum(v) + (n-1)*Valuation(x);
  else
    error "should not happen";
  end if;
  r := Minimum([r eq Infinity() select 10^6 else r where r := Minimum(RelativePrecision(y), RelativePrecision(x)) : y in B]);
  r := Minimum(r+v, RelativePrecision(q)+Valuation(q))*d;

  //"v:", v, " r: ", r;
  M := [];
  //"Building Matrix...(products)";
  for i in B do
    l := i;
  //MUCH faster than the above approach
    for j in [1..n] do
      Append(~M, func<|[0: k in [v*d..Valuation(l)*d-1]] cat es(l)>());
      l := func<|l*x>();
    end for;
  end for;
  if Integral then
    Append(~M, [0: k in [v*d..Valuation(q)*d-1]] cat es(q));
  end if;
  //"Building Matrix...(extend)";
  for i in [1..#M] do
    if #M[i] lt r then
      //"extend", i, " by ", r-#M[i];
      M[i] := M[i] cat [0: k in [#M[i]..r-1]];
    else
      M[i] := M[i][1..r];
    end if;
  end for;
  M := Matrix(M);
  return M;
end intrinsic;


/*
 * y^4 + y^2 + (x^2 + x)*y + x^3 + x^2 + w^2*x + w
 * 2 1
 * [ 12, 0 ]
 * y^4 + (w*x + 1)*y^2 + (w*x^2 + w)*y + x^3 + w*x^2 + w^2
 * 2 1
 * [ 12, 0 ]
 * y^4 + w^2*y^2 + (w*x + w^2)*y + x^2 + x + w
 * 1 1
 * [ 4, 0 ]
 * 
 * */
  
/*
  k<w> := GF(4);
  kx<x> := PolynomialRing(k);
  kxy<y> := PolynomialRing(kx);
  K := FunctionField(y^3+x*y*w+x^2+w*x+1); // has C6 class group
  lp := InfinitePlaces(K);

  D, U := HCF(K, lp[1]);
  H := AbelianExtension(D, U);

  g := [x, K.1];

  r := Expand(g[1], lp[1]);
  R := Parent(r);
  time exp := Exp(PolynomialRing(R).1, lp[1]:InfBound := 5, 
                   Map := func<x|MyExpand(x, lp[1]:RelPrec := 400)>);
  Rx := Parent(exp);
  e := Parent(exp)![IsWeaklyZero(x) select R!0 else x : x in Eltseq(exp)];
  time z := AnalyticModule(g[1], lp[1]: Ex := e, Map := func<x|MyExpand(x, lp[1]:RelPrec := 400)>);
  _, n1, z1 := CanNormalize(z);
  z := AnalyticModule(g[2], lp[1]: Ex := e, Map := func<x|MyExpand(x, lp[1]:RelPrec := 400)>);
  _, n2, z2 := CanNormalize(z);
  n2 := Parent(n1)!Eltseq(n2);

  G := GensToPoly(g, lp[1], K);
  r := GetRelations(g, G);
  R8 := Universe(r);
  R3 := PolynomialRing(K, 3);
  hh := hom<R8 -> R3 | [ 0, R3.1, 0, R3.2, 0, 0, R3.3, 0]>;
  rr := hh(r);
  rr := [rr[3], rr[5], rr[7], rr[9]];
  GG := [ TwistedPolynomials(R3)| [ x, R3.1, R3.2, 1], [g[2], R3.3, 1]];
  N1 := Parent(n1)![x[1], x[3], x[5], x[7]] where x := Eltseq(n1);
  N2 := Parent(n1)![x[1], x[3], x[5]] where x := Eltseq(n2);
  LiftAll([N1, N2], GG, rr[1..3], lp[1]);


  [ Valuation(x) : x in Eltseq(n1*n2 - n2*n1)];
  [ 1612, Infinity, 1379, Infinity, 481, Infinity, -3055, Infinity, -16815, Infinity, 
    -68015, Infinity, -260525, Infinity, 1619 ]
  [ Valuation(x) : x in Eltseq(N1*N2 - N2*N1)];
      [ 1612, -234, -1100, -4120, -8416, -17408, -32768, 1619 ]

*/
