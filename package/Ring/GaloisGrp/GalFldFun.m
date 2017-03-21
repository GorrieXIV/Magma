freeze;

declare attributes GaloisData : h_Fqt_EP, h_KP_Fqt;

/*
  <example>
  Qt<t>:=RationalFunctionField(Rationals());
  Qtx<x>:=PolynomialRing(Qt);
  f:=108*t*x^2 - 108*x - 252*x^3 - 84*x^5 - 4*x^7 - 81*t
     - 54*t*x^4 + 12*t*x^6 - t*x^8;
  S, R, e, r := InternalGalQt_ComputeRoots(f, Zx!(x-11), <10>);
  S, R, e, r := InternalGalQt_ComputeRoots(f, Zx!(x^2-11), <10>);

  f := x^3 + (-3*t^2 - 3*t - 3)*x - 2*t^3 - 3*t^2 - 3*t - 1;
  s := InternalGalQt_ComputeRoots(f, Zx!(x-11), <20>);
  G := Sym(3);
  m := MaximalSubgroups(G:IsTransitive);
  q,w,e,r := Stauduhar(G, m[1]`subgroup, s, 1);q;
  Evaluate(r, PermuteSequence(Z`Error[3][1][1], Random(Parent(w[1]))));

  </exmaple>  
*/

np := NextPrime;

import "Galois.m" : GenericStauduhar, GaloisStartingGroup, TestShapes, get_frobenius;  
declare attributes GaloisData : S, mKQ;

intrinsic Constants(f::RngSLPolElt) -> []
{Return the constants in the SL polynomial f}
    of := Operator(f);
    if of eq "const" then
	return [Operands(f)];
    elif of eq "var" then
	return [1];
    end if;
    f1, f2 := Operands(f);
    consts := Constants(f1);
    
    if of eq "perm" then
	return consts;
    elif of eq "^" then
	return [x^f2 : x in consts];
    end if;

    assert of in {"+", "-", "*"};
    return consts cat Constants(f2);
end intrinsic;

intrinsic Denominator(f::RngUPolElt) -> RngElt
  {The denominator of the polynomial f considered as a rational function}
  return Parent(f)!1;
end intrinsic;

/* Double lift of a root as a p-adic powerseries.

   Effects on precision:
   - Number of coefficients doubles. New coefficients get precision of old ones
   - Precision of known coefficients doubles  */
function DoubleLift(a, w, p, f)
//intrinsic DoubleLift(a::RngSerPowElt, w::RngSerPowElt, p::Tup, f::RngUPolElt) -> RngSerPowElt,RngSerPowElt
//  {}

  a := ChangePrecision(a, p);
  w := ChangePrecision(w, p);
  a := a-Evaluate(f, a)*w;
  return a, w*(2-w*Evaluate(Derivative(f), a));
end function;

/*
intrinsic LiftRoot(m::., f::RngUPolElt, p ::Tup, r::RngSerPowElt) -> RngSerPowElt
  {}
  t := Precision(r);
  ff := Polynomial([m(x, t[2]) : x in Eltseq(f)]);
  a := r;
  w := 1/Evaluate(Derivative(ff), a);
  // assert Precision(w) ge Precision(a);
  while t lt p do
    t := <t[1], Minimum(2*t[2], p[2])>;
    ff := Polynomial([m(x, t[2]) : x in Eltseq(f)]);
    a,w := DoubleLift(a, w, t, ff);
    t := <Minimum(2*t[1], p[1]), t[2]>;
    a,w := DoubleLift(a, w, t, ff);
  end while;
  return a;
end intrinsic;
*/

/* Debug-function print precision we have and we hope for */
function print_check(f,a,w)
 Precision(a);
 
 cc := Evaluate(f,a);
 #Coefficients(cc);
 [Valuation(b) : b in Coefficients(cc)];

 cc := Evaluate(Derivative(f),a)*w  - 1; // w should be 1/f'(a)
 #Coefficients(cc);
 [Valuation(b) : b in Coefficients(cc)];

 return 0;
end function;

/* In case the constant term of the derivative is not a p-adic unit,
   we neet p[1] + p[2]*Valuation(ConstantTerm(Derivative)) p-adic digits to get a root with precision p[1]. */
intrinsic HenselLift(f::RngUPolElt[RngSerPow], r::RngSerPowElt[FldPad], p::Tup) -> RngSerPowElt
  {Lift the series r as a root of f to precision p}
//  "Hensel", f, r, p;
 
  err := 0;
  repeat
   t := Precision(r);
   t := <Minimum(t[1], p[1]), Minimum(t[2], p[2] + err*p[1])>;
   a := ChangePrecision(r, <Minimum(t[1], p[1]), Minimum(t[2], p[2] + err*p[1])>);
   w := Evaluate(Derivative(f), a);
   assert WeakValuation(w) eq 0;
   err := Max(0,Valuation(Eltseq(w)[1]));
  until t[2] eq Minimum(Precision(r)[2], p[2] + err*p[1]);
  w := 1/w;
  assert err*p[1] le Precision(Coefficients(f)[1])[2] - p[2]; // Otherwise the polynomial is not given with sufficient precision
// err is the precision loss in the hensel step.
  //assert Precision(w) ge Precision(a);
//  cc := print_check(f,a,w);
  k := 1;
  repeat
    k := k + 1;
    old_w_prec := Precision(w);
    t := <Min(2*t[1],p[1]), Min(p[2] + 2*p[1] * err, 2*t[2])>; 
    a := ChangePrecision(a, t);
    w := ChangePrecision(w, t);
    fa := Evaluate(f, a);
    delta := fa*w;
    a := a - delta;
    w := w * (2-w*Evaluate(Derivative(f),a));
    if t[1] eq p[1] then // More precise error analysis:
/* Second order term for Newton Iteration is (1/2) * f^2 fss  / fs^3  = (1/2) delta^2 * fss * w. 
   In the p-adic world we can estimate |fss| by 1. */
     dc, dv := Eltseq(delta); // Coefficients and valuation of delta
     wc, wv := Eltseq(w);     // Coefficients and valuation of w
     assert dv ge 0;
     assert wv ge 0;
     dcv := [Min(Valuation(a),old_w_prec[2]) : a in dc]; 
     dcv := [Min([dcv[j+1] + dcv[i - j] : j in [0..i-1]]) : i in [1..#dc]]; // Bound for valuation of coefficients of delta^2
     wcv := [Valuation(a) : a in wc];
     dcv := [Min([dcv[j+1] + wcv[i - j] : j in [0..i-1]]) : i in [1..#dc]]; // Bound for valuation of coefficients of delta^2 * w
    end if; 
  until (t[1] eq p[1]) and Min(dcv) ge p[2]+Valuation(Parent(dc[1])!2);  
//  "returning", a;
  return ChangePrecision(a,p);
end intrinsic;

intrinsic InternalQtLiftRoots(S :: GaloisData, Prec :: Tup)
{Lifts roots in S to precision at least Prec}
 
// Find precision of the coefficients needed: 
  f := S`f;
  pol_Prec := Prec;
  err := 0;
  repeat
    pol_Prec := <Prec[1], 1 + Prec[2] + 2*err * Prec[1]>;
    g := Polynomial([S`BaseMap(x, pol_Prec) : x in Eltseq(f)]);
    R := S`Ring;
    g := Polynomial(R, g);
    w_seq := [Evaluate(Derivative(g), ChangePrecision(a,<2,pol_Prec[2]>)) : a in S`Roots];
    assert &and [WeakValuation(a) eq 0 : a in w_seq];
    err := Max([0] cat [Valuation(Eltseq(a)[1]) : a in w_seq]);
  until pol_Prec[2] ge  1 + Prec[2] + 2*err * Prec[1];
  lift_prec := <Prec[1], Max(2*err + 1, Prec[2])>;
// Lift roots and w_seq:
  S`Roots := [HenselLift(g, r, lift_prec) : r in S`Roots];   
end intrinsic;


intrinsic HenselLift(f::RngUPolElt[RngSerPow], r::RngSerPowElt[FldFin], p::RngIntElt) -> RngSerPowElt
  {Lift the series r as a root of f to precision p}
//  "Hensel", f, r, p;
  t := AbsolutePrecision(r);
  t := Minimum(t, p);
  a := ChangePrecision(r, t);
  w := 1/Evaluate(Derivative(f), a);
  off := Valuation(w);
  //assert Precision(w) ge Precision(a);
  //while t lt p-off do
  // Bad primes can occur in subgroup recursion so we need the stricter condition
  // on the valuation but the t condition will be cheaper to check so do this as
  // long as we can 
  while t lt p - off or Valuation(Evaluate(f, a)) lt p do
//Valuation(Evaluate(f, a));
    t := Minimum(2*t, p-off);
    a,w := DoubleLift(a, w, t-off, f);
    assert Precision(a) ge t+off;
    t := Precision(a);
  end while;
//t, p, off;
//assert Valuation(Evaluate(f, a)) ge p;

//  "returning", a;
  return a;
end intrinsic;


intrinsic InternalGaloisDataCreate(p::RngUPolElt) -> GaloisData
  {}
  S := New(MakeType("GaloisData"));
  S`Prime := p;
  return S;
end intrinsic;

intrinsic InternalGaloisDataCreate(p::RngFunOrdIdl) -> GaloisData
  {}
  S := New(MakeType("GaloisData"));
  S`Prime := p;
  return S;
end intrinsic;

intrinsic EvaluateDerivatives(f::RngUPolElt, x::RngElt) -> RngElt
  {Computes f^(i)(x)/i! for all i in [0..Deg(f)]}
  // Shaw & Traub: on the number of multiplications ...
  // Journal ACM, Vol21 No 1, 1974, pp 161-167
  n := Degree(f);
  f := Eltseq(f);
  f := Reverse(f);
  X := [1, x];
  for i in [2..n] do
    Append(~X, X[i]*x);
  end for;
  T := [[f[i+1+1]*X[n-i-1+1] : i in [0..n-1]]];
  y := f[0+1]*X[n+1];
  for i in [0..n] do
    t := [];
    t[i+1] := y;
    T[i+2] := t;
  end for;
  for j in [0..n-1] do
    for i in [j+1..n] do
      T[j+2][i+1] := T[j-1+2][i-1+1] + T[j+2][i-1+1];
    end for;
  end for;
  return [ T[j+2][n+1] div X[j+1] : j in [0..n]];
end intrinsic;

intrinsic LinearShift(f::RngUPolElt, t::RngElt) -> RngUPolElt
  {Computes f(x-t) with an optimal(?) number of multiplications}
  f := EvaluateDerivatives(f, t);
  return Polynomial(f);
end intrinsic;
 
intrinsic InternalGalQt_Lift(f::RngUPolElt, a::RngElt, fsa::RngElt, m::RngIntElt, n::RngIntElt) -> RngUPolElt, RngUPolElt
  {}
  //Lifts a, with f(a) = 0 mod p^m to a root mod p^n
  //fsa should be 1/f`(a) mod p^m as well
  a := ChangePrecision(a, m);
  fsa := ChangePrecision(fsa, m);
  fs := Derivative(f);
  repeat
    if 2*m gt n then
      m := n;
    else
      m*:= 2;
    end if;
    a := ChangePrecision(a, m);
    fsa := ChangePrecision(fsa, m);
    a := (a-fsa*Evaluate(f, a));
    if m lt n then
      fsa := (fsa*(2-fsa*Evaluate(fs, a)));
    end if;
  until m ge n;
  return a;
end intrinsic;

intrinsic InternalGalQt_Lift(f::RngUPolElt, p::RngUPolElt, a::RngUPolElt, fsa::RngUPolElt, m::RngIntElt, n::RngIntElt) -> RngUPolElt, RngUPolElt
  {}
  //Lifts a, with f(a) = 0 mod p^m to a root mod p^n
  //fsa should be 1/f`(a) mod p^m as well
  pm := p^m;
  fs := Derivative(f);
//  Evaluate(f, a) mod pm;
//  Evaluate(fs, a)*fsa mod pm;
//  Can be improved by computing powers of "a" only once
//  Algo: Klueners, PhD
  repeat
    if 2*m gt n then
      pm := pm*p^(n-m);
      m := n;
    else
      pm *:= pm;
      m*:= 2;
    end if;
    a := (a-fsa*Evaluate(f, a)) mod pm;
    fsa := (fsa*(2-fsa*Evaluate(fs, a))) mod pm;
  until m ge n;
  return a, fsa;
end intrinsic;

intrinsic AbsEltseq(f::RngSerLaurElt:FixedLength := false) -> []
  {Similar to Eltseq, but initial zeroes are returned as well.}
  x, vx := Eltseq(f);
  assert vx ge 0;
  if FixedLength then
    assert Type(AbsolutePrecision(f)) ne Infty;
    l :=  [Universe(x)|0 : i in [1..vx]] cat x;
    return l cat [Universe(x)|0 : i in [#l+1..AbsolutePrecision(f)]];
  else
    return [Universe(x)|0 : i in [1..vx]] cat x;
  end if;
end intrinsic;


intrinsic AbsEltseq(f::RngSerPowElt:FixedLength) -> []
  {"} // "
  x, vx := Eltseq(f);
  assert vx ge 0;
  if FixedLength then
    assert Type(AbsolutePrecision(f)) ne Infty;
    l :=  [Universe(x)|0 : i in [1..vx]] cat x;
    return l cat [Universe(x)|0 : i in [#l+1..AbsolutePrecision(f)]];
  else
    return [Universe(x)|0 : i in [1..vx]] cat x;
  end if;
end intrinsic;

intrinsic AbsDenominator(x::FldFunRatElt) -> RngElt
  {Computes the Lcm of all denominators occuring in the argument}
  return Denominator(x)*Lcm([Denominator(y) : y in Eltseq(Denominator(x))] cat
         [Denominator(y) : y in Eltseq(Numerator(x))]);
end intrinsic;
intrinsic AbsDenominator(x::RngUPolElt) -> RngElt
  {"} // "
  return Lcm([Denominator(y) : y in Eltseq(x)]);
end intrinsic;

intrinsic NonNormalizedLcm(e::[RngUPolElt]) -> RngElt
  {Computes a integral Lcm of the arguments}
  k := CoefficientRing(e[1]);
  R := Integers(k);
  return Polynomial(k, Lcm([PolynomialRing(R)|x*AbsDenominator(x) : x in e])) *
         Lcm([AbsDenominator(x) : x in e]);
end intrinsic;

intrinsic Numerator(x::RngUPolElt) -> RngUPolElt
  {The numerator of the polynomial f considered as a rational function}
  return x;
end intrinsic;

intrinsic InternalGalQt_ComputeRoots(f::RngUPolElt[RngUPol[FldRat]], P::RngUPolElt, prec::<>
  :RatPrime := false, pAdic := false, S := false, NextPrime := np) -> GaloisData
{}

  return InternalGalQt_ComputeRoots(Polynomial(FieldOfFractions(CoefficientRing(f)), f), P, prec:RatPrime := RatPrime, pAdic := pAdic, S := S, NextPrime := NextPrime);
end intrinsic;
  
_Bound := Bound;

intrinsic InternalGalQt_ComputeRoots(f::RngUPolElt[FldFunRat], P::RngUPolElt, 
          prec::<>: RatPrime := false,
            pAdic := false, S := false, NextPrime := np) -> GaloisData
  {}
  // P should be a prime polynomial
  require IsPrime(P) : "the 2nd argument must be a prime polynomial";
  k := CoefficientRing(f);
  require Type(k) eq FldFunRat : 
    "The 1st argument must be a polynomial over some rational function field";
  Q := BaseRing(k);
  P := Polynomial(Q, P);
  assert IsMonic(P) and IsCoercible(PolynomialRing(Integers(Q)), P);

  /*************************************************************************/
  /* P-adic completion
  /* =================  
  /* We will be dealing with the following situation:
  /*   Given a polynomial f in Q(t)[x] and a prime P in Q[t], we want
  /*   to compute an extension of the P-adic completion of Q(t) that 
  /*   splits f completely.
  /* Let K := ext<Q|P> the residue class field mod P. Then
  /* the P-adic completion if Q(t) is K[[s]]. The map
  /* from Q[t] to K[s] is given by writing 
  /* Q[t] ni g = \sum i=0^n a_it^i = \sum i=0^m b_i(t) P^i
  /* for polynomials b_i(t) in Q[t] with deg b_i < deg P,
  /* using Q[t]/P = K, we see that the b_i(t) are in K:
  /*   g = \sum i=0^m b_i(t) P(t)^i = \sum i=0^m b_i(K.1) s in K[s]
  /* 
  /* Therefore one way of getting the map Q(t) -> K[[s]] is using P-adic
  /* representations for Q[t].
  /* To obtain pre-images of Q(t)/P^n -> K[[s]]/s^n we compute some
  /* a in Q(t) mod P^n s.th. P(a) = 0 mod P^n (lifting mod P^n in Q[t], 
  /* starting with a = t mod P) and map s to P.
  /* (Using this map we can then also compute the image of t in K[[s]]/s^n)
  /* 
  /* Now f in K[[s]] is most likely still irreducible, so we extend K further:
  /* K -> K_p -> ext<K_p|d> where K_p is a p-adic completion of K at some
  /* prime (place) p of K (unrelated with P) and d is an integer such that
  /* f in ext<K_p|d> splits completely.
  /* Now the roots of f in ext<K_p|d>[[s]] can be obtained by lifting.
  /*  
  /* In total we now have
  /*   Q(t) -> K[[s]] -> K_p[[s]] -> ext<K_p|d>[[s]]
  /* and all (forward) maps are explicit. To map back from
  /* K_p to K requires rational reconstruction, thus bounds on either
  /* the coefficients in K or the conjugates.
  /*
  /* Remember: the final goal is to write down elements in ext<K_p|d>[[s]]
  /* and to decide if they are in/from elements in Q(t).
  /*
  /* Bounds:
  /* =======  
  /* We need two kinds of bounds, one for the degree in t of results and one 
  /* for the coefficients of the powers of t.
  /* The degree in t bounds come from looking at the valuations of the roots
  /* of f over the infinite completion of Q(t), ie. (Q[1/t], deg).
  /* The actual valuation come from Newton polygons.
  /* 
  /* The other bounds come from looking at complex roots:
  /* Q(t) -> C[[t]] and f splits completely over C[[t]].
  /* Thus this gives bounds for the Coefficients in Q[t].
  /*   
  /* For K[[s]] we have two choices (at least):
  /*   Transfer the Q[t] bounds to K[[s]] to get coefficient bounds 
  /*     or
  /*   Consider K[[s]] -> C[[s]] for all complex embeddings and compute 
  /*   roots there.
  /* 
  /* Denominators:
  /* =============
  /* To avoid problems with denominators (and work only in Q[t]) we
  /* compute c in Z[t] such that cf in Z[t]. This should ensure that
  /* if alpha is a root of f then c alpha is integral over Z[t], thus
  /* avoiding denominators everywhere.
  /* (P monic implies that Z[t] subset Z[K.1][s])  XXX WRONG!!!
  /*************************************************************************/

  if S cmpeq false then
    KQ := NumberField(P);
    KQs := RationalFunctionField(KQ);
    s := KQs.1; // to avoid renaming it in case the user already named it
                // if Deg(P) eq 1 then KQs = k and k.1 is probably named.
    //the residue clas field mod P, mKQ will be the embedding map.
    if KQ eq Q then // P must be linear in this case!
      mKQ := hom<k -> KQ | -Eltseq(P)[1]>;
    else
      mKQ := hom<k -> KQ | KQ.1>;
    end if;
    ff := Polynomial([mKQ(x) : x in Eltseq(f)]);
    if not IsSquarefree(ff) then
      return false;
    end if;
    r_ff := ff;

    KK := NumberField(ff:Check := false, DoLinearExtension); // cheating: ff is not irreducible
    S := GaloisData(KK:Prime := RatPrime, NextPrime := NextPrime);
    if not assigned S`BaseMap then
      assert Q eq KQ;
      BaseMap := function(x, p)
        SetPrecision(S`Ring, Maximum(p, S`Ring`DefaultPrecision));
        return S`Ring!x;
      end function;
      S`BaseMap := BaseMap;
    end if;
    // S`Ring is ext<K_p|d>
    R<pT> := PowerSeriesRing(FieldOfFractions(S`Ring));
    _<rT> := PolynomialRing(R);
    SS := InternalGaloisDataCreate(P);
    SS`Base := S`Base;
    SS`Ring := R;
    AddAttribute(MakeType("GaloisData"), "S");
    SS`S := S;
    SS`Type := "Q(t)";
    if assigned S`CycleTypes then
      SS`CycleTypes := S`CycleTypes;
    end if;
    AddAttribute(MakeType("GaloisData"), "mKQ");
    SS`mKQ := mKQ;
    if assigned S`KnownSubgroup then
      SS`KnownSubgroup := S`KnownSubgroup; // the cyclic group generated
                                           // by the Frobenius
    end if;
  else
    SS := S;
    S := SS`S;
    R := SS`Ring;
    mKQ := SS`mKQ;
    KQ := Codomain(mKQ);
    KQs<s> := RationalFunctionField(KQ);
    ff := Polynomial([mKQ(x) : x in Eltseq(f)]);
    r_ff := ff;
  end if;
  R`DefaultPrecision := prec[1];
  if assigned SS`Scale then
    Scale := SS`Scale;
  else
    Scale := y*AbsDenominator(y) where
      y := NonNormalizedLcm([AbsDenominator(x) :x  in Eltseq(f/LeadingCoefficient(f))]);
    SS`Scale := Scale;  
  end if;
//  assert forall{x : x in Eltseq(Scale*f) | 
//             IsCoercible(PolynomialRing(Integers(Q)), x)};
//  assert IsCoercible(PolynomialRing(Integers(Q)), Scale);

  AddAttribute(Type(SS), "h");
  AddAttribute(Type(SS), "h_pr");
  AddAttribute(Type(SS), "h_a");
  _AssertAttribute := procedure(q, w, e);
    q``w := e;
  end procedure;
  function DataAtPrec(pr)
    is_c, pr := IsCoercible(Integers(), pr);
    assert is_c;
    if assigned SS`h_pr and pr le SS`h_pr then
      h := hom<k -> KQs | KQs!Integers(KQs)!(SS`h[1..pr])>;
      return h;
    end if;
//    "Incresing precision at DataAtPrec to", pr, "!!";
    a, ga := InternalGalQt_Lift(P, P, Polynomial(Q, [0,1]),
          Polynomial(Q, Eltseq(1/Evaluate(Derivative(P), KQ.1))), 1, pr);
  //  "a:", a;
    // a is the image of KQ.1 in Q[[t]] mod P^n,
    // P is the image of s and
    // now we need the image of t in KQ[[s]] mod s^l.
    ss := [];
    Rk := Integers(k);
    cur := Rk.1;
    for i in [1..pr] do
      y := (Rk!cur) mod (Rk!P);
      cur -:= Evaluate(y, a) mod P^pr;
      y := mKQ(y);
      Append(~ss, y);
      assert cur mod (Rk!P) eq 0;
      cur div:= (Rk!P);
    end for;
  //  ss;
    h := hom<k -> KQs | KQs!Integers(KQs)!ss>;
    _AssertAttribute(SS, "h", ss);
    _AssertAttribute(SS, "h_pr", pr);
    _AssertAttribute(SS, "h_a", a);
    return h;
  end function;

  BaseMap := function(x, p)
    assert Type(p) eq Tup;
    assert p[1] ge 1;
    assert p[2] ge 1;
    h := DataAtPrec(p[1]);
    op := SS`Ring`DefaultPrecision;
    AssertAttribute(SS`Ring, "DefaultPrecision", Maximum(p[1], op));
/*
if not IsExport() then
"This is non-export printing";
SS`Ring;
if x ne 0 then
Universe([S`BaseMap(xx, p[2]) : xx in Eltseq(Numerator(h(Numerator(x))))]);
Universe([S`BaseMap(xx, p[2]) : xx in Eltseq(Numerator(h(Denominator(x))))]);
end if;
end if;
*/
    inner := func<f | elt<SS`Ring | [CoefficientRing(SS`Ring) | S`BaseMap(x, p[2]) : x in Eltseq(f)], p[1]>>;
    // needs more careful handling: the denominator is always monic and thus
    // the leading cofficient of the denominator might end up in the numerator
    // L6[4] with Zx.1^2-2 has this problem: a spurious 19 crops up
    return SS`Ring!inner(Numerator(h(Numerator(x)))) *
           SS`Ring!(1/inner(Numerator(h(Denominator(x)))));
  end function;
  if not assigned SS`BaseMap then
      SS`BaseMap := BaseMap;
  end if;
    


  // needs more careful handling: the denominator is always monic and thus the 
  // leading cofficient of the denominator might end up in the numerator
  // L6[4] with Zx.1^2-2 has this problem: a spurious 19 crops up

  Den := Evaluate(Derivative(P), KQ.1);        

  if pAdic then
    vprint GaloisGroup, 1:
      "Computing p-adic roots (FldFun over Q) for precision", prec;
    SS`Ring`DefaultPrecision := prec[1];
    pRoots := func<|[GaloisRoot(i, S:Prec := prec[2]) : i in [1..#S`Roots]]>();
    Sc := SS`BaseMap(Scale, prec);
    g := Polynomial([S`BaseMap(x, prec[2]) : x in Eltseq(Derivative(r_ff))]);
    ff := Polynomial([ SS`BaseMap(x, prec): x in Eltseq(f)]);
    if assigned S`Scale then
      pRoots := [Parent(x)!(x/S`Scale) : x in pRoots];
    end if;
//    "Pre-Verify roots:", [ [Valuation(y) : y in Eltseq(Evaluate(ff, x))] : x in pRoots];
    pRoots := func<|[ InternalGalQt_Lift(ff, R!i, R!1/Evaluate(g, i), 1, prec[1]): i in pRoots]>();
//    "Verify roots:", [ [Valuation(y) : y in Eltseq(Evaluate(ff, x))] : x in pRoots];
    assert #Set(pRoots) eq #pRoots;
    assert #pRoots eq Degree(f);
    SS`Roots := pRoots;

    function _IsInt(x, B, SS:EasyNonInt := false, full := false)
//      "IsInt?", x;
//      "IsInt?B:", B;
//      if EasyNonInt then return true, 1; end if;
      if IsWeaklyZero(x) then
        return true, Integers(k)!0;
      end if;
      pr := Precision(x);
      if pr[1] lt 1 or pr[2] lt 1 then
        if EasyNonInt then
          return true, 1;
        end if;
        error "precision loss";
        return false, 0;
      end if;
      B := <AbsolutePrecision(B), Maximum(Eltseq(B))>;
      if KQ eq Q then  
        is_int := hom<PolynomialRing(KQ) -> k | P>;  
      else
        if Type(pr[1]) eq Infty then
          pr := <Maximum(Valuation(x) + #Eltseq(x), B[1]), pr[2]>;
        end if;
        _ := DataAtPrec(pr[1]);
        a := SS`h_a;
        is_int := hom<PolynomialRing(KQ) -> k | hom<KQ -> k| a>, P>;  
      end if;
      assert pr[1] ge B[1] or EasyNonInt;
      x, vx := Eltseq(x);
      xx := [KQ|];
      if EasyNonInt then
        x := x[1..Minimum(3, #x)];
      end if;
      d := Den^(2*vx+1);
      den_p := SS`S`BaseMap(Den, pr[2]);
      Den_p := den_p^(2*vx+1);
      for i in [1..#x] do
        if assigned S`IsInt then
          f, t := S`IsInt(x[i]*Den_p, B[2], S);
        else
          f, t := IsInt(x[i]*Den_p, B[2], S);
        end if;
        if not full and not f then
            //"fail2", x[i], B[2], i, #x;
          return false, _;
        else
//          "OK:", t;
        end if;
        xx[i] := t/d;
        d *:= Den^2;
        Den_p *:= den_p^2;
      end for;
      x := Polynomial(xx);
//      "IsInt", Degree(x), vx;
//      x, "transformed to"; 
      x := is_int(x);
//      "IsInt", Degree(Numerator(x)), Degree(Denominator(x));
      x := Numerator(x) mod P^pr[1];
//      x;
//      "IsInt:", Degree(x), Degree(P), B[1], pr[1], EasyNonInt;
      if Degree(x) le B[1]*Degree(P) or EasyNonInt then
//        "success", x;
        return true, x;
      else
//          "fail3", x, B;
        return false, x;
      end if;
    end function;
    SS`IsInt := _IsInt;
  end if;

  /* Complex roots... */
  if not pAdic then
    vprint GaloisGroup,1 : 
      "Computing COMPLEX roots (FldFun over Q) up to", prec[1];
    t0 := 0;
    R := Integers(k);
    gf := f/LeadingCoefficient(f)*Scale;
    while Degree(gg) ne Degree(f) or
      not IsSquarefree(gg) 
        where gg := Polynomial(Q,[(R!x) mod (R.1-t0) : x in Eltseq(gf)]) do
      t0 +:= 1;
//      "Substitute!!";
    end while;
    C<I> := ComplexField(100);
    RC<T> := PowerSeriesRing(C, prec[1]);
    RC`DefaultPrecision := prec[1];
    R, mR := ResidueClassField(RC);
    C_R := [];

/*    //this gives bounds in Q(t)
    //not used....
    if false then
    for pl in InfinitePlaces(Q) do  
      h_k_RC := hom<k -> RC | RC.1+t0>; // here, in general the place is used
      h_RC_RC := map<RC -> RC | x:-> Evaluate(x, RC.1-t0)>;
      C_Scale := h_RC_RC(h_k_RC(Scale));
      g := Polynomial([h_k_RC(x)@mR : x in Eltseq(Derivative(f))]);
      ff := Polynomial([ h_k_RC(x): x in Eltseq(f)]);
      rt := Roots(Polynomial(C, [x@mR : x in Eltseq(ff)]));
      Append(~C_R, func<|[C_Scale *
               h_RC_RC(InternalGalQt_Lift(ff, RC!i[1], RC!(1/Evaluate(g, i[1])), 1, prec[1])):
        i in rt]>());
    end for;
    M := PowerSeriesRing(Integers(), prec[1])!
      [Maximum([Ceiling(Abs(AbsEltseq(C_R[i][j])[k])) 
            : i in [1..#C_R], j in [1..Degree(f)]]) : k in [1..prec[1]]];

    _<IT> := Parent(M);        
    SS`max_comp := M;
    vprint GaloisGroup, 2: "Q(t) bound:", M;
    end if; */

    // now bounds in K[[s]]:
    //prec[1] := Ceiling(prec[1]/Degree(P));
    h := DataAtPrec(prec[1]);
    f_K := Polynomial([h(x) : x in Eltseq(f)]);
    Scale_K := h(Scale);
    gf := f_K/h(LeadingCoefficient(f))*Scale_K;
    t0 := 0;
    R := Integers(KQs);
    while Degree(gg) ne Degree(f) or
      not IsSquarefree(gg) 
        where gg := Polynomial(KQ,[((R!Numerator(x)) mod (R.1-t0)) / ((R!Denominator(x)) mod (R.1 - t0)) : x in Eltseq(gf)]) do
      t0 +:= 1;
//      "Substitute!! (KQ)";
    end while;
    assert t0 eq 0;  //the choice of K should make f squarefree!!!

    C_R := [];
    for pl in InfinitePlaces(KQ) do
      Den_pl := Evaluate(Den, pl);
      h_k_RC := hom<KQs -> RC | map<KQ -> RC|x :-> Evaluate(x, pl)>, 
                                        RC.1+t0>;
      h_RC_RC := map<RC -> RC | x:-> Evaluate(x, RC.1-t0)>;
      h_Den := map<RC -> RC | x :-> Den_pl*Evaluate(x, RC.1*Den_pl^2)>;
      C_Scale := h_RC_RC(h_k_RC(Scale_K));
      g := Polynomial([h_k_RC(x)@mR : x in Eltseq(Derivative(f_K))]);
      ff := Polynomial([ h_k_RC(x): x in Eltseq(f_K)]);
      rt := Roots(Polynomial(C, [x@mR : x in Eltseq(ff)]));
      Append(~C_R, func<|[h_Den(C_Scale *
             h_RC_RC(InternalGalQt_Lift(ff, RC!i[1], RC!(1/Evaluate(g, i[1])), 1, prec[1]))):
        i in rt]>());
    end for;
    M := PowerSeriesRing(Integers(), prec[1])!
      [Maximum([Ceiling(Abs(AbsEltseq(C_R[i][j])[k])) 
            : i in [1..#C_R], j in [1..Degree(f)]]) : k in [1..prec[1]]];

    _<IT> := Parent(M);        
    M := ChangePrecision(M, prec[1]);
    SS`max_comp := M;
    vprint GaloisGroup, 2:
      "K[[s]] bound:", AbsolutePrecision(M), Maximum(Eltseq(M));
    SS`max_comp := M;
  end if;

  procedure GetRoots(SS:Prec := <5,20>)
    old := assigned SS`GetRoots;
    if Type(Prec) eq RngIntElt then
      error "Illegal Int passed";
      Prec := <2, Prec>;
    end if;
    if Prec[1] gt AbsolutePrecision(SS`max_comp) then
      _ := InternalGalQt_ComputeRoots(f,P, Prec:S := SS);
    end if;
    _ := InternalGalQt_ComputeRoots(f,P, Prec:S := SS, pAdic);
    assert (assigned SS`GetRoots) eq old;
  end procedure;
  SS`GetRoots := GetRoots;
  function GetPrec(B, S)
    if Type(B) eq RngIntElt then
      if assigned S`S`GetPrec then
        return <2, S`S`GetPrec(B, S`S)>;
      end if;
      return <2, Ceiling(Log(B+1)/Log(S`S`Prime))+5>;
    end if;
    // B should be a power series over the integers...
    pr := <AbsolutePrecision(B), 2>;
    if #Eltseq(B) eq 0 then
      return <AbsolutePrecision(B), 0>;
    end if;
    m := Maximum([x : x in Eltseq(B)]);
    if assigned S`S`GetPrec then
      pr[2] := S`S`GetPrec(m, S`S);
    else
      if m eq 0 then m := 1; end if;
      pr[2] := Floor(Log(m)/
                        Log(Characteristic(ResidueClassField(S`S`Base)))+5);
    end if;
    return pr;
  end function;

  SS`GetPrec := GetPrec;
  rb, df := InternalGalFt_ComputeDegreeBound(f);
  rb := -(rb + df) + Degree(Scale);
  assert rb ge 0;

  function Bound(tschirni, inv, idx:LowTest := false, B)
    d := TotalDegreeAbstract(inv)*Degree(tschirni)*rb/Degree(P);
    d := Ceiling(d) +2;
    d +:= idx;
    if idx gt 1 then d := d + 1; end if; // Check this!

    vprint GaloisGroup, 2: "Computed a bound of", d, "for invar of Deg", TotalDegreeAbstract(inv), Degree(tschirni), idx, rb, Degree(P);
    vprint GaloisGroup, 2: "Using idx", idx;
    if LowTest then 
     d := Min(d,3);  // Reduce d to 3. This will make the next step faster and still trigger the final if for LowTest 
     vprint GaloisGroup, 2: "Changing bound for LowTest to", d;
    end if; 
    if AbsolutePrecision(SS`max_comp) lt d then
	get_roots := assigned SS`GetRoots;
	if get_roots then
	  gr := SS`GetRoots;
        end if;
      _ := InternalGalQt_ComputeRoots(f, P, <d, 1>: S := SS);
      if not get_roots then
	  delete SS`GetRoots;
      end if;
    end if;
    // SS`max_comp is a "bound" for the complex size of the integral
    // coefficients, thus the necessary bound for the T2-norm is
    // Degree(P) * ()^2
    if LowTest and d gt 2 then
      x := ChangePrecision(SS`max_comp, 2);
      x := Degree(P)*_Bound(inv, Evaluate(tschirni, x))^2;
      vprint GaloisGroup, 3: "LowTest:";
      vprint GaloisGroup, 4: "\tTschirn", tschirni;
      vprint GaloisGroup, 4: "\tDeg and Type", TotalDegreeAbstract(inv), inv`GalInvType;
      vprint GaloisGroup, 3: "\tResult", x;
      return x;
    end if;
    vprint GaloisGroup, 3: "AbsPrec max_comp:", AbsolutePrecision(SS`max_comp);
    return Degree(P)*_Bound(inv, Evaluate(tschirni, ChangePrecision(SS`max_comp, d)))^2;
  end function;

  SS`Bound := Bound;
  return SS;
end intrinsic;

intrinsic InternalGalQt_ComputeRoots(f::RngUPolElt[FldFun], P::RngFunOrdIdl, 
          prec::<>: RatPrime := false,
            pAdic := false, S := false, NextPrime := np) -> GaloisData
  {}
end intrinsic;

intrinsic InternalGalFqt_setup(f :: RngUPolElt[FldFunRat], P :: RngUPolElt, prec :: RngIntElt : S := false) -> GaloisData
{Set up the galois data structure for the computation of the Galois Group of
the polynomial f using completion at the prime P and precision prec}

    // P should be a prime polynomial
    require IsPrime(P) : "the 2nd argument must be a prime polynomial";
    k := CoefficientRing(f);
    require Type(k) eq FldFunRat : 
    "The 1st argument must be a polynomial over some rational function field";
    Fq := BaseRing(k);
    P := Polynomial(Fq, P);
    Fqt := Parent(P);
    assert IsMonic(P);
    n := Degree(f);

auto_compl := false;

    if S cmpeq false then
	/*
	Want to find some series ring E[[P]] such that f splits
	as we want all the roots of f.
	Construct E = F_{q^r^d} where r is the degree of P
	*/
	K := ext<Fq | P>;
	h := hom<CoefficientRing(f) -> K | K.1>;
	K, h := ResidueClassField(P);
    if auto_compl then 
      C, cm := Completion(k, P);
      K, m := ResidueClassField(Integers(C));
      h := cm*m;
    else 
      cm := 0;
    end if;
	ff := Polynomial([h(Numerator(x))/h(Denominator(x)) : x in Eltseq(f)]);
	if not IsSquarefree(ff) then
	    return false;
	end if;
	fact := Factorization(ff);
	d := LCM([Degree(fa[1]) : fa in fact]);
	E := ext<K | d>;
	EP := PowerSeriesRing(E : Precision := prec);

	SS := InternalGaloisDataCreate(P);
	SS`Base := PowerSeriesRing(K);
	SS`Type := "F_q(t)";
	SS`Ring := EP;
	SS`Prec := prec;
	SS`f := f;

	assert IsCoercible(SS`Base, SS`Ring!1);

    else
	SS := S;
	EP := SS`Ring;
	E := CoefficientRing(EP);
	K := CoefficientRing(SS`Base);
	cm := 0;
    end if;

    _AssertAttribute := procedure(q, w, e);
	q``w := e;
    end procedure;

    function get_h_Fqt_EP(prec)

	if assigned SS`h_Fqt_EP then
	    hFqtEP := SS`h_Fqt_EP;
	    precs := [x[2] : x in hFqtEP];
	    pos := Position(precs, prec);
	    if pos gt 0 then
		return hFqtEP[pos][1];
	    end if;
	    max := precs[1];
	    T := hFqtEP[1][1](CoefficientRing(f).1);
	    if prec lt max then
		T := ChangePrecision(T, prec);
		h_Fqt_EP := hom<CoefficientRing(f) -> EP | T>;
		// keep the largest precision at the beginning
		Append(~hFqtEP, <h_Fqt_EP, prec>);
		_AssertAttribute(SS, "h_Fqt_EP", hFqtEP);
		return h_Fqt_EP;
	    end if;
	    T := ChangePrecision(T, max);
	else 
	    max := 1;
	    //K.1 is a root of (P(t) - P) mod P
	    T := EP!E!K.1;
	    T := ChangePrecision(T, 1);
	    hFqtEP := [];
	    assert Type(SS) eq MakeType("GaloisData");
	    _AssertAttribute(SS, "h_Fqt_EP", hFqtEP);
	end if;

	/*
	Need to map between Fqt and E[[P]] to map f over to E[[P]] and
	to map the roots of f in E[[P]] back to Fqt

	p is the prime in Fq[t]. We want to set up K[[P]] in such a way that
	computations modulo p^n in Fq[t] correspond to modulo P^n in K[[P]]
	where K is the residue class field modulo p.
	In particular, p is the "uniformizer" so we want to map P to p.
	*/
	/*
	First map Fq[t] -> E[[P]]
	Need to find image of t in E[[P]]
	Know P(t) -> P, find T image of t as a root of P(t) - P
	*/
	g := Polynomial(EP, P) - EP.1;
	assert Valuation(Evaluate(g, T)) ge max;
/*
EP;
Precision(EP);
EP`DefaultPrecision;
Valuation(Evaluate(g, T));
Valuation(Evaluate(Derivative(g), T));
T;
g;
Evaluate(g, T);
HenselLift(g, ChangePrecision(T, 1), 15);
HenselLift(g, ChangePrecision(T, 1), 20);
Evaluate(g, HenselLift(g, ChangePrecision(T, 1), 16));
Valuation(Evaluate(g, HenselLift(g, ChangePrecision(T, 1), 16)));
*/
	T := HenselLift(g, T, prec);
//"val, prec = ", Valuation(Evaluate(g, T)), prec;
	assert Valuation(Evaluate(g, T)) ge prec;

	h_Fqt_EP := hom<CoefficientRing(f) -> EP | T>;
	// keep the largest precision at the beginning
	Insert(~hFqtEP, 1, <h_Fqt_EP, prec>);
	_AssertAttribute(SS, "h_Fqt_EP", hFqtEP);
	return h_Fqt_EP;
    end function;

    // Note that this really maps in K[[P]] as a BaseMap should 
    // (coeff ring of S`Ring)
    function BaseMap(x, prec)
	h_Fqt_EP := get_h_Fqt_EP(prec);
	return h_Fqt_EP(x);
    end function;
    SS`BaseMap := BaseMap;
    if auto_compl then
    function BaseMap(x, prec)
	//Need field here but not is IsInt
	C, cm := Completion(k, P);
	C := Codomain(cm);
	C`Precision := prec;
        //SS`Ring!(Eltseq(cm(x))[1]);
	return SS`Ring!cm(x); //Expand(x, Place(P) : RelPrec := prec);
    end function;
    SS`BaseMap := BaseMap;
    end if;


    function get_h_KP_Fqt(prec)

	KP := PowerSeriesRing(K);
	Kp := PolynomialRing(K);
	function KptoKP(h_Kp_Fqt, prec)
	    //CF: reduce everything modulo P^prec. Maybe change the map to work 
	    //in quo<..|P^prec> for faster arithmetic?
	    mu := function(x)
	      l := IsZero(x) select Zero(Fqt) else (h_Kp_Fqt(Kp!Eltseq(x)*Kp.1^Valuation(x))) mod P^prec;
	      return l;
	    end function;
	    h_KP_Fqt := map<KP -> Fqt | x :-> mu(x)>;
	    return h_KP_Fqt;
	end function;

	if not false and assigned SS`h_KP_Fqt then
	    hKPFqt := SS`h_KP_Fqt;
	    precs := [x[2] : x in hKPFqt];
//precs, prec;
	    pos := Position(precs, prec);
	    if pos gt 0 then
		return KptoKP(hKPFqt[pos][1], prec);
	    end if;
	    max := precs[1];
	    imK := hKPFqt[1][1](K.1);
//imK;
	    if prec lt max then
		h_Kp_Fqt := hom<Kp -> Fqt | map<K -> Fqt | x:->Evaluate(Polynomial(Eltseq(x, Fq)), imK)>, P>;
		// keep the largest precision at the beginning
		Append(~hKPFqt, <h_Kp_Fqt, prec>);
		_AssertAttribute(SS, "h_KP_Fqt", hKPFqt);
		return KptoKP(h_Kp_Fqt, prec);
	    end if;
	else
	    hKPFqt := [];
	    assert Type(SS) eq MakeType("GaloisData");
	    _AssertAttribute(SS, "h_KP_Fqt", hKPFqt);
	    imK := Fqt.1; //CF XXX
	    max := 1;
	end if;
	/*
	Map back from E[[P]] to Fq[t] 
	Know P -> P, but need image of K.1 
	(what about E.1? - must be in KP to map)
	K.1 is a root of P
	t is a root of P mod P
	so lift t as a root of P to the image of K.1
	*/

	_, fsa := XGCD(Evaluate(Derivative(P), imK), P^max);
	imK := InternalGalQt_Lift(P, P, imK, fsa, max, prec);
//prec, imK;

	// Use polynomial ring for series ring over K
	// We map back from KP rather than EP since elements of EP
	// not in KP are not going to be the ones that we want
	h_Kp_Fqt := hom<Kp -> Fqt | map<K -> Fqt | x:->Evaluate(Polynomial(Eltseq(x, Fq)), imK)>, P>;

//        bm := SS`BaseMap(Fqt.1, prec);
//        assert Fqt.1 eq h_KP_Fqt(bm);
	// keep the largest precision at the beginning
	Insert(~hKPFqt, 1, <h_Kp_Fqt, prec>);
	_AssertAttribute(SS, "h_KP_Fqt", hKPFqt);
	return KptoKP(h_Kp_Fqt, prec);
    end function;
    
    // non - integral polynomials
    Scale := LCM([Denominator(x) : x in Eltseq(f)]);
    f *:= Scale;
    // for non monic polynomials
    if assigned SS`Scale then
	Scale := SS`Scale;
    else
	Scale := LCM([Denominator(x) : x in Eltseq(f/LeadingCoefficient(f))]);
	SS`Scale := Scale;  
    end if;


    procedure GetRoots(S : Prec := 5)
//"GetRoots";
//f;
//Prec;
//S`Ring;
//S`Base;
//_<t> := S`Ring;
//_<w> := CoefficientRing(S`Ring);
//[S`BaseMap(c, 5*Prec) : c in Coefficients(f)];
	i := 2;
	repeat
	    //S`Roots := PuiseuxExpansion(Polynomial([S`BaseMap(c, i*Prec) : c in Coefficients(f)]), Prec : TestSquarefree := false);
	    _f := Polynomial([S`BaseMap(c, i*Prec) : c in Coefficients(f)]);
	    // Roots stumbles on polys with O() constant coefficients
	    cc := ConstantCoefficient(_f);
	    if IsWeaklyZero(cc) and not IsZero(cc) then
		i +:= 1;
		continue;
	    end if;
	    S`Roots := Roots(_f, Prec);
	    assert &and[Valuation(Evaluate(_f, r[1])) ge Prec: r in S`Roots];
	    i +:= 1;
	    //S`Ring should be a splitting field for f so must have all roots in
	    //here
	until assigned S`Roots and #S`Roots eq Degree(f);
	assert #S`Roots eq Degree(f);
	S`Roots := [S`Ring | r[1] : r in S`Roots];
    end procedure;
    SS`GetRoots := GetRoots;

    if not assigned SS`KnownSubgroup and (not assigned SS`Roots or #SS`Roots eq Degree(f)) then
	q := #K;
	if not assigned ff then
	    h := hom<CoefficientRing(f) -> K | K.1>;
	    _, h := ResidueClassField(P);
	    ff := Polynomial([h(Numerator(x))/h(Denominator(x)) : x in Eltseq(f)]);
	end if;
	  /*
	  Need roots in the correct order and need them to stay in that order
	  so delete the GetRoots function so it can't be called again when
	  the order may be changed
	  */
	  if false then
	  R, mR := ResidueClassField(SS`Ring);
	    r := [ GaloisRoot(i, SS: Prec := 1)@mR : i in [1..n]];
	  rt := [ x^q : x in r] where q := #ResidueClassField(SS`Base);
	    p := [ Position(rt, x) : x in r];
	    else
	    p := get_frobenius(SS, n);
	    end if;
	SS`KnownSubgroup := sub<Sym(n) | p>;
	assert assigned SS`Roots;
	delete SS`GetRoots;
    end if;
//SS`KnownSubgroup;

    // mapping back from E[[P]] to Fq[t]
    // first need to be able to coerce down to K[[P]]
    // then map back into Fq[t]
    // return true if degree is less than B
    // NEED SOME PRECISION TO CREATE h_KP_Fqt???
    function _IsInt(x, B, S : EasyNonInt := false)
	if IsWeaklyZero(x) then
//	  "IsInt: 0 -> True";
	    return true, Fqt!0;
	end if;

	KP := S`Base;

//	_<TT> := Parent(x);
//	_<w> := CoefficientRing(Parent(x));

//	"IsInt", x, MinimalPolynomial(Eltseq(x)[1], GF(5));

	if not IsCoercible(KP, x) then
//"IsInt: no coerce -> false";
	    return false, _;
	end if;

	prec := AbsolutePrecision(x);
	if prec eq Infinity() then
	    prec := Maximum(Valuation(x) + #Eltseq(x), Parent(x)`DefaultPrecision);
	end if;
	h_KP_Fqt := get_h_KP_Fqt(prec);
	y := h_KP_Fqt(x);

        if auto_compl then
	y := x @@ cm;//Evaluate(x, UniformizingElement(Place(P)));
	is_c, y := IsCoercible(Integers(k), y);
	assert is_c;
	if not is_c then
//"IsInt : non int";
	    return false, y;
	end if;
        end if;

        //assert Valuation(S`BaseMap(y, prec) - x) ge prec;
if Degree(y) gt B then
//"IsInt: possible", y, B;
end if;
//	Parent(y);

	return Degree(y) le B, y;
    end function;
    SS`IsInt := _IsInt;

    function GetPrec(B, S)
//"GetPrec B:", B;
//Ceiling(B/Degree(P)) + 3;
	return Ceiling(B/Degree(P)) + 3;
    end function;
    SS`GetPrec := GetPrec;

    //need to set S`max_comp
    rb, df := InternalGalFt_ComputeDegreeBound(f);
//rb, df;
    rb := -(rb + df) + Degree(Scale);
    assert rb ge 0;
    // max_comp is tested for type RngIntElt somewhere where we don't fall 
    // into that case so we want the type check to fail
    SS`max_comp := Rationals()!rb;
//"max_comp = ", SS`max_comp;

    function Bound(tschirni, inv, idx : LowTest := false)
//inv;
//tschirni;
//Need to include the coefficient size of the tschirnis in the bound!
if true then
//idx;
//nICOLE's version (which she didn't commit quickly!)
	if CoefficientRing(tschirni) cmpne Integers() then
	    bound := Maximum([i*Maximum(SS`max_comp, 1/10) + Degree(et[i+1]) : i in [0 .. Degree(tschirni)]]) where et := Eltseq(tschirni);
	else
	    bound := Degree(tschirni)*Maximum(SS`max_comp, 1/10);
	end if;
	bound := TotalDegreeAbstract(inv)*bound;
	function max_coeff_val(Inv)
	    /*
	    Invariant can degenerate at a point
	    m := hom<CoefficientRing(Parent(inv)) -> PolynomialRing(Integers()) | Polynomial([0, 1])>;
	    m := Coercion(CoefficientRing(Parent(inv)), PolynomialRing(Integers()));
	    return Degree(Evaluate(inv, [Codomain(m) | 1 : i in [1 .. Rank(Parent(inv))]], m));
	    */
	    if assigned Inv`MaxCoeffVal then
		return Inv`MaxCoeffVal;
	    end if;
	    oinv := Operator(Inv);
	    inv1, inv2 := Operands(Inv);
	    case oinv :
		when "const" :
		    m :=  Degree(inv1);
		when "var" :
		    m :=  0;
		when "perm" :
		    m :=  max_coeff_val(inv1);
		when "^" :
		    m :=  max_coeff_val(inv1)*inv2;
		when "+", "-":
		    m :=  Maximum(max_coeff_val(inv1), max_coeff_val(inv2));
		when "*" :
		    m :=  max_coeff_val(inv1) + max_coeff_val(inv2);
	    end case;
	    Inv`MaxCoeffVal := m;
	    return m;
	end function;
	if CoefficientRing(Parent(inv)) cmpne Integers() then
	    inv`MaxCoeffVal := -1;
	    assert not assigned inv`MaxCoeffVal;
	    bound +:= max_coeff_val(inv);
	    inv`MaxCoeffVal := -1;
	end if;
	bound *:= idx;
//bound;
else
//Claus' version (which he did commit quickly)
        if Type(CoefficientRing(tschirni)) eq RngInt then
          mx := 0;
        else
          mx := Maximum([Degree(x) : x in Eltseq(tschirni)]);
        end if;
	bound := TotalDegreeAbstract(inv)*Degree(tschirni)*Maximum(SS`max_comp+mx, 0.1)*idx;
bound;
end if;
//        bound := TotalDegreeAbstract(inv)*Degree(tschirni)*Maximum(SS`max_comp, 0.1)*idx;
//SS`max_comp;
//bound;

        _ := GaloisRoot(1, SS:Prec := 10);
	sum_roots := &+SS`Roots;
	pr := AbsolutePrecision(sum_roots);
	if Type(pr) eq Infty then
	    pr := SS`Prec;
	end if;
	h_KP_Fqt := get_h_KP_Fqt(pr);
        //CF: the assertion is/was wrong. Only if the precision of the roots
        //is large enough will the degree be correct.
        //Main problem however was in h_KP_Fqt: the result is only defined 
        //modulo P^prec, the reduction however was missing....
/*
h_KP_Fqt;
Parent(sum_roots);
sum_roots;
*/
	assert Degree(Eltseq(SS`f)[Degree(SS`f)]) - Degree(SS`Scale) lt pr/Degree(SS`Prime) or
          bound ge Degree(h_KP_Fqt(sum_roots));
//bound;
	return bound;
    end function;
    SS`Bound := Bound;
    return SS;

end intrinsic;

intrinsic InternalGalFqt_setup(f :: RngUPolElt[FldFun], P :: RngFunOrdIdl, prec :: RngIntElt : S := false) -> GaloisData
{Set up the galois data structure for the computation of the Galois Group of
the polynomial f using completion at the prime P and precision prec}

    // P should be a prime 
    require IsPrime(P) : "the 2nd argument must be a prime ideal";
    k := CoefficientRing(f);
    require Type(k) eq FldFun: 
    "The 1st argument must be a polynomial over some function field";

    if S cmpeq false then
	/*
	Want to find some series ring E[[P]] such that f splits
	as we want all the roots of f.
	Construct E = F_{q^r^d} where r is the degree of P
	*/
	K, h := ResidueClassField(Place(P));
	ff := Polynomial([h(x) : x in Eltseq(f)]);
	if not IsSquarefree(ff) then
	    return false;
	end if;
	fact := Factorization(ff);
	d := LCM([Degree(fa[1]) : fa in fact]);
	E := ext<K | d>;
	EP := PowerSeriesRing(E : Precision := prec);

	SS := InternalGaloisDataCreate(P);
	SS`Base := PowerSeriesRing(K);
	SS`Type := "F_q(t)";
	SS`Ring := EP;
	SS`Prec := prec;
	SS`f := f;

    else
	SS := S;
	EP := SS`Ring;
	E := CoefficientRing(EP);
	K := CoefficientRing(SS`Base);
    end if;

    Pl := Place(P);
    C, cm := Completion(k, Pl);
    function BaseMap(x, prec)
	//Need field here but not in IsInt
	C := Codomain(cm);
	C`Precision := prec;
	return SS`Ring!cm(x); //Expand(x, Place(P) : RelPrec := prec);
    end function;
    SS`BaseMap := BaseMap;
    C, cm := Completion(MaximalOrderFinite(k), Pl);

    // for non monic polynomials
    if assigned SS`Scale then
	Scale := SS`Scale;
    else
	Scale := LCM([Denominator(x, MaximalOrderFinite(k)) : x in Eltseq(f/LeadingCoefficient(f))]);
	SS`Scale := Scale;  
    end if;

    // Note that this really maps in K[[P]] as a BaseMap should 
    procedure GetRoots(S : Prec := 5)
	i := 2;
	repeat
	    _f := Polynomial([S`BaseMap(c, i*Prec) : c in Coefficients(f)]);
	    cc := ConstantCoefficient(_f);
	    if IsWeaklyZero(cc) and not IsZero(cc) then
		i +:= 1;
		continue;
	    end if;
	    S`Roots := Roots(_f, Prec);
	    i +:= 1;
	    //S`Ring should be a splitting field for f so must have all roots in
	    //here
	until #S`Roots eq Degree(f);
	assert #S`Roots eq Degree(f);
	S`Roots := [S`Ring | r[1] : r in S`Roots];
    end procedure;
    SS`GetRoots := GetRoots;

    /*
    Need to include Valuation(Scale, ip)
    */
    IP := InfinitePlaces(k);
    SS`max_comp := 2^30;
    for ip in IP do
//SS`max_comp;
//ValuationsOfRoots(f, ip);
//Valuation(Scale, ip);
	SS`max_comp := Minimum(SS`max_comp, (Minimum([x[1] : x in ValuationsOfRoots(f, ip)]) + Valuation(Scale, ip)));
//Valuation(Scale, ip);
//SS`max_comp;
    end for;
    SS`max_comp := -SS`max_comp;
//"max_comp ", SS`max_comp;
//Scale;
    //SS`max_comp should be negative since f should be an integral polynomial

    function IsInt(x, B, S : EasyNonInt := false)
	if IsWeaklyZero(x) then
	    return true, k!0;
	end if;

	KP := S`Base;

	if not IsCoercible(KP, x) then
//"IsInt : no coerce";
	    return false, _;
	end if;

	prec := AbsolutePrecision(x);
	if prec eq Infinity() then
	    prec := Maximum(Valuation(x) + #Eltseq(x), Parent(x)`DefaultPrecision);
	end if;
//"IsInt x : ", x;
	x := x @@ cm;//Evaluate(x, UniformizingElement(Place(P)));
	is_c, y := IsCoercible(MaximalOrderFinite(k), x);
	assert is_c;
	if not is_c then
//"IsInt : non int";
	    return false, x;
	end if;
//"\n\n\nRECONSTRUCTION\n\n\n";
	R := ReconstructionEnvironment(P, prec);
	x := Reconstruct(y, R);


	//check all infinite valuations of x are less than or greater than B
	for ip in IP do
	    if -Valuation(x, ip) gt B then
//-Valuation(x, ip), B, RamificationDegree(ip);
		return false, x;
	    end if;
	end for;
	return true, x;
    end function;
    SS`IsInt := IsInt;
    
    function Bound(tschirni, inv, idx : LowTest := false)
	if CoefficientRing(tschirni) cmpne Integers() then
	    bound := Maximum([i*Maximum(SS`max_comp, 1/10) + (et[i+1] eq 0 select 0 else Maximum([-Valuation(et[i+1], ip) : ip in IP])) : i in [0 .. Degree(tschirni)]]) where et := Eltseq(tschirni);
//SS`max_comp;
//[i*Maximum(SS`max_comp, 0.1) : i in [0 .. Degree(tschirni)]];
//[(et[i+1] eq 0 select 0 else Maximum([-Valuation(et[i+1], ip) : ip in IP])) : 
//i in [0 .. Degree(tschirni)]] where et := Eltseq(tschirni);
//IP;
	else
	    bound := Degree(tschirni)*Maximum(SS`max_comp, 1/10);
	end if;
//bound;
	bound := TotalDegreeAbstract(inv)*bound;
	function max_coeff_val(inv, IP)
	/*
	    m := hom<CoefficientRing(Parent(inv)) -> PolynomialRing(Integers()) | Polynomial([0, 1])>;
	    m := Coercion(CoefficientRing(Parent(inv)), PolynomialRing(Integers()));
	    c := Evaluate(inv, [Codomain(m) | 1 : i in [1 .. Rank(Parent(inv))]], m);
"MAX_COEFF_VAL =", c;
assert not IsZero(c);
	    c := CoefficientRing(Parent(inv))!c;
	    return Maximum([-Valuation(c, ip) : ip in IP]);
	*/
	    if assigned inv`MaxCoeffVal then
		return inv`MaxCoeffVal;
	    end if;
	    oinv := Operator(inv);
	    inv1, inv2 := Operands(inv);
	    case oinv :
		when "const" :
		    m := Maximum([-Valuation(inv1, ip) : ip in IP]);
		when "var" :
		    m := 0;
		when "perm" :
		    m := max_coeff_val(inv1, IP);
		when "^" :
		    m := max_coeff_val(inv1, IP)*inv2;
		when "+", "-":
		    m := Maximum(max_coeff_val(inv1, IP), max_coeff_val(inv2, IP));
		when "*" :
		    m := max_coeff_val(inv1, IP) + max_coeff_val(inv2, IP);
	    end case;
	    inv`MaxCoeffVal := m;
	    return m;
	end function;
	if CoefficientRing(Parent(inv)) cmpne Integers() then
	    bound +:= max_coeff_val(inv, IP);//&+[ : x in Constants(inv)];
	    inv`MaxCoeffVal := -1;
	end if;
	bound *:= idx;
return bound;
	bound := TotalDegreeAbstract(inv)*Degree(tschirni)*Maximum(SS`max_comp, 0.1)*idx;
bound;
	return bound;
    end function;
    SS`Bound := Bound;

    function GetPrec(B, S)
//"\n\nSmaller precision ? : ", Degree(P), Max([Degree(p) : p in IP]);
	return Ceiling(Max([Degree(p) : p in IP])*B*#IP/Degree(P)) + 3;
    end function;
    SS`GetPrec := GetPrec;

    return SS;

end intrinsic;

intrinsic Ilog2(B::RngSerElt[RngInt]) -> RngIntElt
  {}
  if IsWeaklyZero(B) then
    return 10^400;//TODO: not a good idea....
  end if;
  return AbsolutePrecision(B)*Ilog2(Maximum(Eltseq(B)));
end intrinsic;

intrinsic Ilog2(B::FldRatElt) -> RngIntElt
{}
    return Ilog2(RealField()!B + 1);
end intrinsic;

/*
intrinsic 'ge'(a::<>, b::RngIntElt) -> BoolElt
  {}
  error "";
  if a[2] ge b then
    return true;
  else
    return false;
  end if;
end intrinsic;
*/

/*
intrinsic 'ge'(a::<>, b::<>) -> BoolElt
  {}
  require #a eq #b : "Lengths of inputs must be the same";
  require IsCoercible(Parent(a), b) or IsCoercible(Parent(b), a) : "Inputs must lie in compatible cartesian products";

  return &and[a[i] ge b[i] : i in [1 .. #a]];
end intrinsic;
*/

intrinsic '+'(a::<>, b::<>) -> <>
  {Sum of a and b where a and b contain only ring or algebra elements}

  require #a eq #b : "Lengths of inputs must be the same";
  require IsCoercible(Parent(a), b) or IsCoercible(Parent(b), a) : "Inputs must lie in compatible cartesian products";

  T := <>;
  for c in a do
    require ISA(Type(c), RngElt) or ISA(Type(c), AlgElt) : "Tuples must contain ring or algebra elements";
  end for;
  for i in [1 .. #a] do
    Append(~T, a[i] + b[i]);
  end for;
  return T;
end intrinsic;

intrinsic Precision(x::RngSerElt[FldPad]) -> <>
  {}
  return <AbsolutePrecision(x), AbsolutePrecision(Eltseq(x)[1])>;
end intrinsic;

intrinsic Precision(x::RngSerElt[FldFin]) -> RngIntElt
{Return the absolute precision of x}
    return AbsolutePrecision(x);
end intrinsic;


// We need the absolute precision at this point. For the series and for the coefficients!
intrinsic ChangePrecision(x::RngSerPowElt[FldPad], p::<>) -> RngSerPowElt
  {Change the absolute precision of the series to be p[1] and the p-adic coefficients
  of the series to be p[2]}
//    "Changing precision from", Precision(x), " to ", p;
  px := Parent(x);
  x := ChangePrecision(x, p[1]);
  x, vx := Eltseq(x);
  x := [ ChangePrecision(t, (Valuation(t) lt 0) select (p[2] - Valuation(t)) else p[2])  + elt<Parent(t) | 0,p[2]> : t in x]; 
 
 return elt<px|vx, x, p[1]-vx>;
end intrinsic;

// We need the absolute precision at this point. For the series and for the coefficients!
intrinsic ChangePrecision(x::RngSerLaurElt[FldPad], p::<>) -> RngSerLaurElt
  {Change the absolute precision of the series to be p[1] and the p-adic coefficients
  of the series to be p[2]}
//    "Changing precision from", Precision(x), " to ", p;
  px := Parent(x);
  x := ChangePrecision(x, p[1]);
  x, vx := Eltseq(x);
 
  x := [ ChangePrecision(t, (Valuation(t) lt 0) select (p[2] - Valuation(t)) else p[2]) + elt<Parent(t) | 0,p[2]> : t in x];  
  return elt<px|vx, x, p[1]-vx>;
end intrinsic;


intrinsic InternalGalFt_ComputeDegreeBound(f::RngUPolElt) -> []
  {Computes lower bounds for the infinite valuation of the roots of f}
  // OK, we need to convert to
  // - a monic, integral (wrt to the degree valuation) polynomial first

  if Type(CoefficientRing(f)) eq FldFunRat then
    R := ValuationRing(CoefficientRing(f));
    v := func<x|Degree(Denominator(x)) - Degree(Numerator(x))>;
  else
    assert Type(CoefficientRing(f)) eq RngUPol;
    R := ValuationRing(FieldOfFractions(CoefficientRing(f)));
    v := func<x|-Degree(x)>;
  end if;
  f := Eltseq(f);
  vf := [ x eq 0 select -Infinity() else v(x) : x in f];
  df := vf[#f];
  vf := [ x - df : x in vf]; // Valuations of the monic polynomial 
                             // after division by leading coeff.
  n := #f-1;
  /* I know what I'm doing here, but I don't know why...
   * d is maximal such that
   * t^(dn)f(x/t^d) is integral monic
   * (integral means all valuations (v) of the coefficients will have to 
   * be negative.)
   * Since this just shifts and scales the polygon there is no
   * real point here...
   */
  d := Maximum([Ceiling(vf[i+1]/(n-i)) : i in [0..n-1] | 
                               IsCoercible(Rationals(), vf[i+1])] cat [0]);
  x := R!(1/Universe(f).1);
  assert Valuation(x) eq 1;
  vf := [ vf[i]+d*(n-i+1) : i in [1..#f]];
  n := NewtonPolygon({<i-1, -Rationals()!vf[i]> : i in [1..#f] | 
                           IsCoercible(Rationals(), vf[i])});
  sn := Slopes(n);
  if #sn eq 0 then
    // f is a power, roots are zero
    return -d, df;
  end if;
  return Minimum(sn)-d, df;
end intrinsic;

import "Galois.m" : galois_group_for_all;

forward get_primes, get_primes_rel;

function galois_group(f, prime, next_p, ShortOK, Ring, ProofEffort)
    Pff := FieldOfFractions(CoefficientRing(f));
    ff := Polynomial(Pff, f);

    if IsIrreducible(ff) then
	if not IsSeparable(ff) then
	    error "Polynomial must be separable";
	end if;
	K := FunctionField(ff);
	return GaloisGroup(K:Prime := prime, NextPrime := next_p, Ring := Ring, ProofEffort := ProofEffort);
    end if;

    if Characteristic(Pff) eq 0 then
	error "Polynomial must be irreducible when characteristic is 0";
    end if;

    assert Ring eq false;
    if Type(CoefficientRing(f)) ne RngUPol and not IsMonic(f) then
        lllf, lc := Factorization(Polynomial(FieldOfFractions(CoefficientRing(f)), f));
        llf := [];
        Px := PolynomialRing(CoefficientRing(f));
        for lf in lllf do
            if IsCoercible(Px, lf[1]) then
                Append(~llf, <Px!lf[1], lf[2]>);
            else
                Append(~llf, <Px!(lc*lf[1]), lf[2]>);
            end if;
        end for;
        assert #llf eq #lllf;
    else
        llf, lc := Factorization(f);
    end if;

    // leave the linears for now and the multiplicities (have to include each
    // root to its multiplicity)
    lf := [car<Parent(f), Integers()> | x : x in llf | Degree(x[1]) gt 1]; 

    ff := &* [Parent(f) | x[1] : x in lf];
    if Degree(ff) gt 0 and not IsSeparable(Polynomial(Pff, ff)) then
	error "Polynomial must be separable";
    end if;

    lF := [];
    for g in lf do
	Append(~lF, FunctionField(g[1] : Check := false));
    end for;

    if prime cmpeq false then
	prime, min_deg := get_primes(ff, Maximum([Degree(g[1]) : g in lf] cat [1]), &cat[[DefiningPolynomial(x[1]) : x in Subfields(F)] : F in lF]);
	assert exists(prime){x[1] : x in prime | x[2] eq min_deg};
    end if;

    return galois_group_for_all(f, prime, ShortOK, lf, lF, llf, ff);

end function;

intrinsic GaloisGroup(f::RngUPolElt[RngUPol[FldRat]]:Prime := false, NextPrime := np, Old := false, ShortOK := false, Ring := false, ProofEffort := 10) -> GrpPerm, [], GaloisData
{Return the galois group of the splitting field of the polynomial f}

  if Old then
    if Prime cmpne false then
      return InternalGaloisGroup(f: Prime := Prime);
    else
      return InternalGaloisGroup(f);
    end if;
  end if;
  return galois_group(f, Prime, NextPrime, ShortOK, Ring, ProofEffort);
end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[RngUPol[FldFin]] : Prime := false, Old := false, ShortOK := false, Ring := false, ProofEffort := 10) -> GrpPerm, [], GaloisData
{"} // "
  if Old then
    if Prime cmpne false then
      return InternalGaloisGroup(f: Prime := Prime);
    else
      return InternalGaloisGroup(f);
    end if;
  end if;
    return galois_group(f, Prime, NextPrime, ShortOK, Ring, ProofEffort);
end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[FldFunRat]:Prime := false, NextPrime := np, Old := false, ShortOK := false, Ring := false, ProofEffort := 10) -> GaloisData
{"} // "
  require Type(CoefficientRing(CoefficientRing(f))) in [FldFin, FldRat] : "Constant field must be the rationals or a finite field";
  //require IsIrreducible(f) : "Polynomial must be irreducible";
  if Old then
    if Prime cmpne false then
      return InternalGaloisGroup(f: Prime := Prime);
    else
      return InternalGaloisGroup(f);
    end if;
  end if;
  d := LCM([Denominator(x) : x in Eltseq(f)]);
    return galois_group(Polynomial(Integers(CoefficientRing(f)), f*d), Prime, NextPrime, ShortOK, Ring, ProofEffort);
end intrinsic;

function next_prime(f, next_deg)

    f +:= 1;
    if Characteristic(CoefficientRing(f)) eq 0 then
	if next_deg then
	    f +:= Parent(f).1^(Degree(f) + 1);
	end if;
	while not IsPrime(f) do
	    f +:= 1;
	end while;
    else 
	while false and not IsPrime(f) do
	    if Coefficient(f, 0) eq 0 then
		f +:= Parent(f).1;
		i := 1;
		while Coefficient(f, i) eq 0 do
		    i +:= 1;
		    if i eq Degree(f) then
			// remove leading coeff ready to add leading
			// coeff of 1 higher degree
			f -:= Parent(f).1^i;
			i +:= 1;
		    end if;
		    f +:= Parent(f).1^i;
		end while;
	    end if;
	    f +:= 1;
	end while;
	f := RandomIrreduciblePolynomial(CoefficientRing(f), next_deg select Degree(f) + 1 else Degree(f));
    end if;

    return f;

end function;

function first_prime(F)
    if Characteristic(F) eq 0 then 
	return Polynomial(F, [7, 0, 1]);
    end if;

    f := Polynomial(F, [2, 0, 1]);
    if not IsPrime(f) then
	return next_prime(f, false);
    end if;

    return f;
end function;

function get_primes(f, max_fact_deg, subf)

    C := CoefficientRing(f);
    if Type(C) in {FldFun, RngFunOrd, FldFunOrd} then
	return get_primes_rel(f, max_fact_deg, subf);
    end if;
    Prime := first_prime(BaseRing(C));
    primes := [];
    degrees := {};
    other_primes := [];
    min_deg := 2^30;
    min_dl := 2^30;
    max_dl := -1;
    this_prime_degree_fail := 0;
    char_multiplier := Characteristic(C) eq 0 select 1/2 else 5;
    fail_limit := Integers()!(char_multiplier*2);
    this_prime_degree_succ := 0;
    succ_limit := Ceiling(char_multiplier);
    cycletype := {};
    cfe := true;
    // try limited number of failing primes of each degree
    // keep only a limited number of useful primes
    //"Prime time";
    n := Degree(f);
    subf_disc := &*([Discriminant(x) : x in subf] cat [1]);
    while #primes lt char_multiplier*n + 1 and Degree(Prime) le min_deg 
	  and #other_primes lt char_multiplier*n + 1 do
	//Prime;
	ff := LCM([Denominator(x) : x in Coefficients(f)])*f;
	d := Parent(Prime)!LeadingCoefficient(ff);
	if d mod Prime ne 0 then
	    rf := ext<BaseRing(CoefficientRing(ff)) | Prime>;
	    h := hom<CoefficientRing(ff) -> rf | rf.1>;
	    fp := Polynomial([h(x) : x in Eltseq(ff)]);
	    fact_fp := Factorization(fp);
	    if exists(x){x : x in fact_fp | x[2] gt 1} then
		this_prime_degree_fail +:= 1;
		Prime := next_prime(Prime, this_prime_degree_fail ge fail_limit);
		this_prime_degree_fail := this_prime_degree_fail mod fail_limit;
		continue;
	    end if;
	    if Numerator(subf_disc) mod Prime eq 0 or Denominator(subf_disc) mod Prime eq 0 then
		continue;
	    end if;
	    // The degrees from each factorization form cycle shapes
	    degs := [Integers() | Degree(t[1]) : t in fact_fp];
	    k := GCD(n, Degree(Prime));
	    ndk := n div k;
	    cfe := cfe and #degs eq k and &and{deg eq ndk : deg in degs};
//Prime, degs;
	    Include(~cycletype, degs);
	    dl := Degree(Prime)*LCM(degs)*Floor((#degs)^1.5);
	    degs := Seqset(degs);
	    degrees := degrees join degs;
//"Residue splitting field degree", dl;
	    if dl gt max_fact_deg/4 then
		Append(~primes, <Prime, dl>);
		min_dl := Minimum(min_dl, dl);
		min_deg := Minimum(min_deg, Degree(Prime)*LCM(degs));
		this_prime_degree_succ +:= 1;
		Prime := next_prime(Prime, this_prime_degree_succ ge succ_limit);
		this_prime_degree_succ := this_prime_degree_succ mod succ_limit;
		continue;
	    elif #primes eq 0 then
		max_dl := Maximum(max_dl, dl);
		Append(~other_primes, <Prime, dl>);
	    end if;
	end if;
	this_prime_degree_fail +:= 1;
	Prime := next_prime(Prime, this_prime_degree_fail ge fail_limit);
	this_prime_degree_fail := this_prime_degree_fail mod fail_limit;
    end while;
    if min_dl le Degree(f)/4 then
	degs := {p[2] : p in primes | p[2] gt Degree(f)/4};
	if #degs eq 0 then
	    min_dl := Maximum([p[2] : p in primes]);
	else
	    min_dl := Minimum(degs);
	end if;
    end if;
// primes, other_primes;
    if #primes eq 0 then
	primes := other_primes;
	min_dl := max_dl;
    end if;

    return primes, min_dl, degrees, cycletype, cfe;
end function;

forward galois_group_fld_fun, LiftGaloisGroupOfExactConstantField;

function get_trivial_S(f, Prime)
    if Characteristic(CoefficientRing(f)) gt 0 then
	return InternalGalFqt_setup(f, Prime, 1);
    else 
	return InternalGalQt_ComputeRoots(f, Prime, <1, 5>);
    end if;
end function;

function return_trivial(data_only, S, G)
    if assigned S`GetRoots then
	S`GetRoots(S);
	delete S`GetRoots;
    end if;
    if data_only then
	return S, _, _;
    else
	r := [ GaloisRoot(i, S:Bound := 1) : i in [1..Degree(S`f)]];
	return S, G, r;
    end if;
end function;

function GetGaloisData(K, data_only : Prime := false, NextPrime := np, Ring := false)

  C := CoefficientField(K);
  // defined over the standard rational
  if Type(C) eq FldFun then
	C := FieldOfFractions(CoefficientRing(EquationOrderInfinite(K)));
  end if;

  f := DefiningPolynomial(K);
  f := Polynomial(C, f);
  if Type(CoefficientRing(f)) eq RngUPol then
  end if;
  cfe := false;
  assert Ring cmpeq false or Prime cmpeq false or Prime cmpeq Ring`Prime;
  if Prime cmpeq false then
     subf := Subfields(K);
      n := Degree(K);
      primes, min_deg, degrees, cycletype, cfe := get_primes(f, Degree(f), [DefiningPolynomial(a[1]) : a in subf | Degree(a[1]) lt n]);
      // choose a prime out of primes based on the LCMs
      // want a prime such that Degree(Prime)*LCM is minimal but
      // greater than Degree(K)/4 (so that the automorphism from E is not
      // trivial
      //Prime := primes[1][1];//first_prime(BaseRing(CoefficientRing(K)));
      // WANT A GOOD PRIME HERE TO DO THE ComputeRoots and GetRoots in Sn/An
      // CASE TOO!!!
     assert exists(Prime){x[1] : x in primes | x[2] eq min_deg};
     Exclude(~primes, <Prime, min_deg>);
	// Sn/ An test:
	// if there is a cycle of length n/2 < p < n-2 then we are Sn or An
	// (p prime)
      poss_p := { p : p in [n div 2+1 .. n-3] | IsPrime(p)};
      if #(poss_p meet degrees) gt 0 and Characteristic(K) ne 2 then
	  d := Discriminant(DefiningPolynomial(K));
	  isEven := IsSquare(d);
	  S:= get_trivial_S(f, Prime);
	  S`Subfields := subf;
	  if not assigned S`CycleTypes then
	    if assigned cycletype then
		S`CycleTypes := cycletype;
	    else
	    S`CycleTypes := {};
	    end if;
	  end if;
	if isEven then
	  // Since An is a normal subgroup in Sn (the only index 2 subgroup)
	  // the ordering of the roots does not matter (I think)
	  S`DescentChain := [<Alt(n), true>];
	  return return_trivial(data_only, S, Alt(n));
	else
	  S`DescentChain := [<Sym(n), true>];
	  return return_trivial(data_only, S, Sym(n));
	end if;
      end if;
    end if;
    if Type(Prime) eq Tup then
	RatPrime := Prime[2];
    Prime := PolynomialRing(BaseRing(CoefficientRing(K)))!Prime[1];
  else
    RatPrime := false;
    Prime := PolynomialRing(BaseRing(CoefficientRing(K)))!Prime;
  end if;

  if Ring cmpeq false or not assigned Ring`Roots then
    repeat
//Prime;
      if Characteristic(K) gt 0 then
	S := InternalGalFqt_setup(f, Prime, 1 : S := Ring);
      else 
	S := InternalGalQt_ComputeRoots(f, Prime, <1, 5>:RatPrime := RatPrime, NextPrime := NextPrime, S := Ring);
      end if;
     // We hope one of these works otherwise next_prime might give us
     // denominator issues (but if it is called since the user passed in a 
     // Prime then that is their problem)
     if assigned primes and #primes gt 0 then
	 while not exists(Prime){x[1] : x in primes | x[2] eq min_deg} do
	    min_deg +:= 1;
	 end while;
	 Exclude(~primes, <Prime, min_deg>);
     else
      Prime := next_prime(Prime, false);
     end if;
    until S cmpne false or Ring cmpne false;
    S`f := f;
    if assigned S`GetRoots then
    S`GetRoots(S);
    delete S`GetRoots;
    end if;
    if assigned subf then
	S`Subfields := subf;
    end if;
  else 
    S := Ring;
  end if;
  if not assigned S`CycleTypes then
    if assigned cycletype then
	S`CycleTypes := cycletype;
    else
    S`CycleTypes := {};
    end if;
  end if;
  if cfe and DimensionOfExactConstantField(K) eq Degree(K) then
    if Characteristic(K) gt 0 then
	GE := func<|GaloisGroup(ExactConstantField(K), ConstantField(K))>();
    else
	GE := GaloisGroup(ExactConstantField(K));
    end if;
    vprint GaloisGroup, 1 : "Field is a constant field extension";
    // What about the root ordering?
    //return GaloisGroup(ExactConstantField(K), ConstantField(K)), r, S;	
    Gs := [SymmetricGroup(Degree(K)), Alt(Degree(K))];
    for G in Gs do
	if #G eq #GE then
	    vprint GaloisGroup, 1 : "Found group as S_n or A_n same size as the Galois group of the exact constant field";
	  S`DescentChain := [*<G, true>*];
	    return return_trivial(data_only, S, G);
	end if;
    end for;

    if assigned S`KnownSubgroup and #GE eq #S`KnownSubgroup then
	vprint GaloisGroup, 1 : "Found group as Frobenius subgroup same size as the Galois group of the exact constant field";
	  S`DescentChain := [*<S`KnownSubgroup, true>*];
	return return_trivial(data_only, S, S`KnownSubgroup);
    end if;
    vprint GaloisGroup, 1 : "but couldn't match a known subgroup";
    lift, G := LiftGaloisGroupOfExactConstantField(K, ConstantField(K), S);
    if lift then
	vprint GaloisGroup, 1 : "but could lift from exact constant field";
	S`DescentChain := [*<G, true>*];
	return return_trivial(data_only, S, G);
    end if;
  end if;
  if data_only or not assigned S`DescentChain then
      return S, _, _;
  else
      return return_trivial(data_only, S, S`DescentChain[#S`DescentChain][1]);
  end if;

end function;

function LiftGaloisGroupOfExactConstantField(F, c0, S)
// c0 is the exact constant field of the coefficient field of F
// This is needed when F is relative
    p := Characteristic(F);
    d := DimensionOfExactConstantField(F);

    assert Degree(F) eq d;

    if GCD([p, d]) ne 1 then
	return false, _;
    end if;

    assert d eq Degree(F);

    if false and d le 2 then 
	return false, _;
    end if;

    vprint GaloisGroup, 1 : "We have a pure constant field extension : Galois group will degenerate";

    time ff, incl := ExactConstantField(F);
    tm := Polynomial([S`BaseMap(a,5) : a in Coefficients(Polynomial(ElementToSequence(incl(ff.1))))]);

    assert assigned S`Roots;
    im := [Evaluate(tm,S`Roots[i]) : i in [1..d]];
    im_f := [a^#c0 : a in im];
    res := [[j : j in [1..d] | Valuation(im_f[i] - im[j]) gt 0 ] : i in [1..d]];
    assert {#a : a in res} eq {1};
    res := [a[1] : a in res];
    assert Set(res) eq {1..d};

    gal := sub<Sym(d) | res>;
    return true, gal;
end function;

intrinsic GaloisGroup(K::FldFun[FldFunRat]:Prime := false, ShortOK := false, Ring := false, NextPrime := np, SubfieldsComplete := true, ProofEffort := 10) -> GrpPerm, [], GaloisData
{Return the galois group of the function field K}

    require IsSimple(K) : "Function field must be a simple extension";

    S, G, r := GetGaloisData(K, false : Prime := Prime, NextPrime := NextPrime, Ring := Ring);
    if assigned G and assigned r then
	return G, r, S;
    end if;
    div_order := 1;
    return galois_group_fld_fun(K, S : ShortOK := ShortOK, SubfieldsComplete := SubfieldsComplete, ProofEffort := ProofEffort, DivisorOfOrder := div_order);
end intrinsic;

intrinsic GaloisData(K::FldFun[FldFunRat]:Prime := false, NextPrime := np) -> GaloisData
{Return the data structure for the galois group computation for the function field K}

  require IsSimple(K) : "Function field must be a simple extension";

  S := GetGaloisData(K, true : Prime := Prime, NextPrime := NextPrime);
  return S;
end intrinsic;

function galois_group_fld_fun(K, S : SubfieldsComplete := true, ProofEffort := 10, ShortOK := false, DivisorOfOrder := 1)
  G := Sym(Degree(K));
  assert not assigned S`GetRoots;
  G, reject := GaloisStartingGroup(K, S : ShortOK := ShortOK, Subfields := SubfieldsComplete);//:Subfields := Characteristic(K) eq 0);
// CHECK FOR K BEING A CONSTANT FIELD EXTENSION BEFORE THIS : GROUP IS THAT
// OF THE ECF THEN
// COMPUTE ORDER OF GALOIS GROUP OF THE ECF : USE AS DivisorOfOrder
  assert not assigned S`GetRoots;
  S`DescentChain := [*<G, true>*];
  return GenericStauduhar(G, S, 1,
        func<X|[x`subgroup : x in MaximalSubgroups(X:IsTransitive)]>,
        func<X|IsTransitive(X) and TestShapes(X, S`CycleTypes)>:
	  ShortOK := ShortOK,
	  ProofEffort := ProofEffort,
	  Reject := reject, DivisorOfOrder := DivisorOfOrder,
          Subfields := SubfieldsComplete, //true,//Characteristic(K) eq 0, 
          SubfieldsComplete := false); // because we used generating subfields
end function;

function get_primes_rel(f, max_fact_deg, sfp)
    Prime := first_prime(BaseRing(BaseRing(CoefficientRing(f))));
    primes := [];
    degrees := {};
    other_primes := [];
    min_deg := 2^30;
    min_dl := 2^30;
    max_dl := -1;
    this_prime_degree_fail := 0;
    char_multiplier := Characteristic(CoefficientRing(f)) eq 0 select 1/2 else 5;
    fail_limit := Ceiling(char_multiplier*2);
    this_prime_degree_succ := 0;
    succ_limit := Ceiling(char_multiplier);
    // try limited number of failing primes of each degree
    // keep only a limited number of useful primes
    //"Prime time";
    cycletype := {};
    cfe := true;
    MF := CoefficientRing(f);
    if IsField(CoefficientRing(f)) then
	MF := MaximalOrderFinite(MF);
	ff := LCM([Denominator(x, MF) : x in Coefficients(f)])*f;
    else 
	ff := f;
    end if;
    n := Degree(f);
    while #primes lt char_multiplier*n + 1 and Degree(Prime) lt min_deg 
    	and #other_primes lt char_multiplier*n + 1 do
	P := Decomposition(MF, Prime);
	d := Parent(Prime)!LeadingCoefficient(ff);
	if d mod Prime ne 0 then
	    for p in P do
		rf, h := ResidueClassField(p);
		fp := Polynomial([h(x) : x in Eltseq(ff)]);
		fact_ff := Factorization(fp);
		/* 
		This checks the valuation of the discriminant is 0
		Otherwise two roots are the same in the residue field
		and since the discriminant is the product of the differences
		of the roots it will have positive valuation
		*/
		if exists(x){x : x in fact_ff | x[2] gt 1} then
		    this_prime_degree_fail +:= 1;
		    while #primes gt 0 and Minimum(primes[#primes][1]) eq Minimum(p) do
			Remove(~primes, #primes);
//"Removal";
		    end while;
		    min_deg := 2^30;
		    min_dl := 2^30;
		    if #primes gt 0 and not exists{x[1] : x in primes | x[2] eq min_dl} then
			min_dl := Minimum([p[2] : p in primes]);
			min_deg := Minimum([p[3] : p in primes]);
		    end if;
		    break;
		end if;
		for sfpp in sfp do
		    g := Polynomial([h(x) : x in Eltseq(sfpp)]);
		    fact_g := Factorization(g);
		    if exists{x : x in fact_g | x[2] gt 1} then
			this_prime_degree_fail +:= 1;
			while #primes gt 0 and Minimum(primes[#primes][1]) eq Minimum(p) do
			    Remove(~primes, #primes);
			end while;
			min_deg := 2^30;
			min_dl := 2^30;
			if #primes gt 0 and not exists{x[1] : x in primes | x[2] eq min_dl} then
			    min_dl := Minimum([p[2] : p in primes]);
			    min_deg := Minimum([p[3] : p in primes]);
			end if;
			break p;
		    end if;
		end for;
		// The degrees from each factorization form cycle shapes
		degs := [Integers() | Degree(t[1]) : t in fact_ff];
		k := GCD(n, Degree(Prime));
		ndk := n div k;
		cfe := cfe and #degs eq k and &and{deg eq ndk : deg in degs};
		Include(~cycletype, degs);
		dl := Degree(p)*LCM(degs)*#degs;
		degs := Seqset(degs);
		degrees := degrees join degs;
		if dl gt max_fact_deg/4 then
		    Append(~primes, <p, dl, Degree(p)*LCM(degs)>);
		    min_dl := Minimum(min_dl, dl);
		    min_deg := Minimum(min_dl, Degree(p)*LCM(degs));
		    this_prime_degree_succ +:= 1;
		    continue;
		elif #primes eq 0 then
		    Append(~other_primes, <p, dl>);
		    max_dl := Maximum(max_dl, dl);
		end if;
		this_prime_degree_fail +:= 1;
	    end for;
	else
	    this_prime_degree_fail +:= 1;
	end if;
	Prime := next_prime(Prime, this_prime_degree_succ ge succ_limit or this_prime_degree_fail ge fail_limit);
	this_prime_degree_succ := this_prime_degree_succ mod succ_limit;
	this_prime_degree_fail := this_prime_degree_fail mod fail_limit;
    end while;
    if min_dl le Degree(f)/4 then
	degs := {p[2] : p in primes | p[2] gt Degree(f)/4};
	if #degs eq 0 then
	    min_dl := Maximum([p[2] : p in primes]);
	else
	    min_dl := Minimum(degs);
	end if;
    end if;

    if #primes eq 0 then
	primes := other_primes;
	min_dl := max_dl;
    end if;

    return primes, min_dl, degrees, ff, cycletype, cfe;
end function;

function GetGaloisDataRel(K, data_only : Prime := false, NextPrime := np, Ring := false)

    f := DefiningPolynomial(K);
    if Type(CoefficientRing(f)) eq RngFunOrd then
	f := Polynomial(FieldOfFractions(CoefficientRing(f)), f);
    end if;

  cfe := false;
  assert Ring cmpeq false or Prime cmpeq false or Prime cmpeq Ring`Prime;
    if Prime cmpeq false and (not data_only or Ring cmpeq false) then 
	 subf := Subfields(K);
	primes, min_deg, degrees, ff, cycletype, cfe := get_primes_rel(f, Degree(f), [DefiningPolynomial(x[1]) : x in subf]);
//primes;
//[Minimum(p[1]) : p in primes];
//Discriminant(ff);
if not IsExport() and true then 
assert &and[Valuation(Discriminant(ff), p) eq 0 : p in &cat[Decomposition(CoefficientRing(MaximalOrderFinite(K)), Minimum(prime[1])) : prime in primes]];
end if;
//Factorization(Discriminant(ff)*MaximalOrderFinite(CoefficientRing(K)));
	// choose a prime out of primes based on the LCMs
	// want a prime such that Degree(Prime)*LCM is minimal but
	// greater than Degree(K)/4 (so that the automorphism from E is not
	// trivial
	// WANT A GOOD PRIME HERE TO DO THE ComputeRoots and GetRoots in Sn/An
	// CASE TOO!!!
	n := Degree(K);
	assert exists(Prime){x : x in primes | x[2] eq min_deg};
	Exclude(~primes, Prime);
	Prime := Prime[1];

	// Sn/ An test:
	// if there is a cycle of length n/2 < p < n-2 then we are Sn or An
	// (p prime)
	poss_p := { p : p in [n div 2+1 .. n-3] | IsPrime(p)};
	if #(poss_p meet degrees) gt 0 and Characteristic(K) ne 2 then
	    d := Discriminant(DefiningPolynomial(K));
	    isEven := IsSquare(d);
	    S, r := get_trivial_S(f, Prime);
	    S`Subfields := subf;
	    if not assigned S`CycleTypes then
		if assigned cycletype then
		    S`CycleTypes := cycletype;
		else
		    S`CycleTypes := {};
		end if;
	    end if;
	    if isEven then
	    // Since An is a normal subgroup in Sn (the only index 2 subgroup)
	    // the ordering of the roots does not matter (I think)
		S`DescentChain := [<Alt(n), true>];
		return return_trivial(data_only, S, Alt(n));
	    else
		S`DescentChain := [<Sym(n), true>];
		return return_trivial(data_only, S, Sym(n));
	    end if;
	end if;
    end if;

    if Type(Prime) eq Tup then
	RatPrime := Prime[2];
	Prime := Prime[1];
    else
	RatPrime := false;
    end if;
    
    if Ring cmpeq false or not assigned Ring`Roots then
	repeat
	    if Characteristic(K) gt 0 then
		S := InternalGalFqt_setup(f, Prime, 1 : S := Ring);
	    else
		S := InternalGalQt_ComputeRoots(f, Prime, <1, 5> : S := Ring);
	    end if;

	    if S cmpne false then
		break;
	    end if;

	    // We hope one of these works otherwise next_prime might give us
	    // denominator issues (but if it is called since the user passed in a 
	    // Prime then that is their problem)
	    if assigned primes and #primes gt 0 then
		while not exists(Prime){x[1] : x in primes | x[2] eq min_deg} do
		    min_deg +:= 1;
		end while;
		Exclude(~primes, <Prime, min_deg>);
	    else
		Prime := next_prime(Prime, false);
	    end if;
	until S cmpne false;
	S`f := f;
	if assigned S`GetRoots then
	S`GetRoots(S);
	delete S`GetRoots;
	end if;
	if assigned subf then
	    S`Subfields := subf;
	end if;
    else
	S := Ring;
    end if;

    if not assigned S`CycleTypes then
	if assigned cycletype then
	    S`CycleTypes := cycletype;
	else
	    S`CycleTypes := {};
	end if;
    end if;

    if cfe and DimensionOfExactConstantField(K) eq Degree(K) then
	GE := func<|GaloisGroup(ExactConstantField(K), ExactConstantField(CoefficientField(K)))>(); 
	// What about the root ordering?
	//return GaloisGroup(ExactConstantField(K), ExactConstantField(CoefficientField(K))), r, S;	
	vprint GaloisGroup, 1 : "Field is a constant field extension";
	if not assigned G then 
	    G := SymmetricGroup(Degree(K));
	end if;
	if #G eq #GE then
	    S`DescentChain := [*<G, true>*];
	    vprint GaloisGroup, 1 : "Found group as S_n or A_n same size as the Galois group of the exact constant field";
	    return return_trivial(data_only, S, G);
	end if;
	
	if assigned S`KnownSubgroup and #GE eq #S`KnownSubgroup then
	      S`DescentChain := [*<S`KnownSubgroup, true>*];
	    vprint GaloisGroup, 1 : "Found group as Frobenius subgroup same size as the Galois group of the exact constant field";
	    return return_trivial(data_only, S, S`KnownSubgroup);
	end if;
	vprint GaloisGroup, 1 : "but couldn't match a known subgroup";
	lift, G := LiftGaloisGroupOfExactConstantField(K, ConstantField(K), S);
	if lift then
	    vprint GaloisGroup, 1 : "but could lift from exact constant field";
	    S`DescentChain := [*<G, true>*];
	    return return_trivial(data_only, S, G);
	end if;
    end if;

    if data_only or not assigned S`DescentChain then
	return S, _, _;
    else
	return return_trivial(data_only, S, S`DescentChain[#S`DescentChain][1]);
    end if;
end function;

intrinsic GaloisGroup(K::FldFun[FldFun[FldFunRat[FldFin]]]:Prime := false, ShortOK := false, Ring := false, NextPrime := np, SubfieldsComplete := true, ProofEffort := 10) -> GrpPerm, [], GaloisData
{Return the galois group of the function field K}
 
    require IsSimple(K) : "Function field must be a simple extension";
    S, G, r := GetGaloisDataRel(K, false : Prime := Prime, NextPrime := NextPrime, Ring := Ring);

    if assigned G and assigned r then
	return G, r, S;
    end if;

    return galois_group_fld_fun(K, S : ShortOK := ShortOK, SubfieldsComplete := SubfieldsComplete, ProofEffort := ProofEffort, DivisorOfOrder := 1);
end intrinsic;

intrinsic GaloisData(K::FldFun[FldFun[FldFunRat]]:Prime := false, NextPrime := np) -> GaloisData
{Return the data structure for the galois group computation for the function field K}
 
    require IsSimple(K) : "Function field must be a simple extension";
    return GetGaloisDataRel(K, true : Prime := Prime, NextPrime := NextPrime);

end intrinsic;

intrinsic GaloisGroup(K::FldFun:Prime := false, ShortOK := false, Ring := false, NextPrime := np, ProofEffort := 10) -> GrpPerm, [], GaloisData
{Return the galois group of the function field K}
 
    require IsSimple(K) : "Function field must be a simple extension";
    A := RationalExtensionRepresentation(CoefficientRing(K));
    KK := FunctionField(Polynomial(A, DefiningPolynomial(K)));

    G, R, S := GaloisGroup(
		    KK : Prime := Prime, ShortOK := ShortOK, Ring := Ring,
		    NextPrime := NextPrime, ProofEffort := ProofEffort
	       );
									              return G, R, S;

end intrinsic;

intrinsic GaloisGroup(K::FldFun[FldRat]:Prime := false, ShortOK := false, Ring := false, NextPrime := np, ProofEffort := 10) -> GrpPerm, [], GaloisData
{Return the galois group of the function field K}
    return GaloisGroup(RationalExtensionRepresentation(K) : Prime := Prime, ShortOK := ShortOK, Ring := Ring, NextPrime := NextPrime, ProofEffort := ProofEffort);
end intrinsic;

intrinsic GaloisGroup(K::FldFun[FldFin]:Prime := false, ShortOK := false, Ring := false, NextPrime := np, ProofEffort := 10) -> GrpPerm, [], GaloisData
{Return the galois group of the function field K}
    return GaloisGroup(RationalExtensionRepresentation(K) : Prime := Prime, ShortOK := ShortOK, Ring := Ring, NextPrime := NextPrime, ProofEffort := ProofEffort);
end intrinsic;

intrinsic GaloisData(K::FldFun[FldRat]:Prime := false, NextPrime := np) -> GaloisData
{Return the data structure for the galois group of the function field K}
    return GaloisData(RationalExtensionRepresentation(K) : Prime := Prime, NextPrime := NextPrime);
end intrinsic;

intrinsic GaloisData(K::FldFun[FldFin]:Prime := false, NextPrime := np) -> GaloisData
{Return the data structure for the galois group of the function field K}
    return GaloisData(RationalExtensionRepresentation(K) : Prime := Prime, NextPrime := NextPrime);
end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[FldFun[FldFunRat]]:Prime := false, ShortOK := false, Ring := false, NextPrime := np, ProofEffort := 10) -> GrpPerm, [], GaloisData
{Return the galois group of the polynomial f}
    E := MaximalOrderFinite(CoefficientRing(f));
    d := CoefficientRing(f)!LCM([Denominator(x, E) : x in Eltseq(f)]);
    return galois_group(Polynomial(E, f*d), Prime, NextPrime, ShortOK, Ring, ProofEffort);
   K := FunctionField(f);
   G, R, S := GaloisGroup(K : 
		    Prime := Prime, ShortOK := ShortOK, Ring := Ring,
		    NextPrime := NextPrime, ProofEffort := ProofEffort
	      );

    return G, R, S;
end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[FldFun]:Prime := false, ShortOK := false, Ring := false, NextPrime := np, ProofEffort := 10) -> GrpPerm, [], GaloisData
{Return the galois group of the polynomial f}
 
    A := RationalExtensionRepresentation(CoefficientRing(f));
    f := Polynomial(A, f);

    G, R, S := GaloisGroup(
		    f : Prime := Prime, ShortOK := ShortOK, Ring := Ring,
		    NextPrime := NextPrime, ProofEffort := ProofEffort
	       );
									              return G, R, S;

end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[RngFunOrd[RngUPol]]:Prime := false, ShortOK := false, Ring := false, NextPrime := np, ProofEffort := 10) -> GrpPerm, [], GaloisData
{Return the galois group of the polynomial f}
    return galois_group(f, Prime, NextPrime, ShortOK, Ring, ProofEffort);
   f := Polynomial(FunctionField(CoefficientRing(f)), f);
   G, R, S := GaloisGroup(f : 
		    Prime := Prime, ShortOK := ShortOK, Ring := Ring,
		    NextPrime := NextPrime, ProofEffort := ProofEffort
	      );

    return G, R, S;
end intrinsic;

