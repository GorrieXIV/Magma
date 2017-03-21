freeze;

/*******************************************************
   Functions used in CasselsTatePairing intrinsics

   Steve Donnelly
*******************************************************/

import "FourDesc/hints.m" : GetLocalQuarticSolution;

// Search on the twists C_D for squarefree D in the interval [min..max], until success
/* TO DO (bug?) : why so hard to run IsLocallySolvable at 2 on twists of
                  y^2 = 11005*x^4 - 77066*x^3 + 132897*x^2 + 122636*x + 6324
   Even worse: E = 50582a1 of rank 0, i = 1, j = 1, Seed is 1 73106365
   Looking for a better quadratic point (with 2 <= D < 4) ... Time: 241.970
*/

function better_quadratic_point(C, min, max)
  assert min gt 0 and min lt max;
  quartic,h := HyperellipticPolynomials(C);  
  assert IsZero(h);
  quarticZ := PolynomialRing(Integers())! quartic;
  badprimes := BadPrimes(C);

  // Prefer positive D, since we want small class group
  if LeadingCoefficient(quartic) gt 0 or HasRoot(quartic, RealField()) then
    Ds := [ D :  D in [min..max] | IsSquarefree(D) ]; 
  else
    Ds := [ -D : D in [min..max] | IsSquarefree(D) ];
  end if;

  for D in Ds do
    CC := HyperellipticCurve(D*quartic, h);
    // Check locally solvability primes where that's guaranteed to be quick to test
    testprimes := Sort(Setseq({l : l in PrimeDivisors(D) cat badprimes | l ne 2 and l lt 1000}));
    for l in testprimes do
      if not InternalIsSoluble(D*quarticZ, l) then 
        continue D; 
      end if;
    end for;
    pts := Points(CC : Bound:=10^3); // Bound less than this not worthwhile
    for pt in pts do
      if pt[3] eq 0 then continue; end if;
      x := pt[1]/pt[3];
      ysquared := Evaluate(quartic,x);
      assert IsSquare(D*ysquared);
      if ysquared eq 0 then continue; end if;
      return D, x, ysquared;
    end for;
  end for;

  return 0,_,_;
end function;

function quadratic_point_FldNum(C, CcovE : avoid:={}, avoid2tors:=true) // -> FldNum, Pt 
  // totally stupid
  E := Codomain(CcovE);
  quartic := HyperellipticPolynomials(C);
  K := BaseField(C);
  xs := [-100 .. 100];
  xDs := [<x,Evaluate(quartic,x)> : x in xs];
  xDs := [xD : xD in xDs | forall{A : A in avoid | not IsSquare(xD[2]/A)}];
  
  // square value (ignore avoid2tors here)
  if exists(xD) {xD : xD in xDs | IsSquare(xD[2])} then
    return C(K)! [xD[1],Sqrt(xD[2])], K; 
  end if;

  Sort(~xDs, func<t1,t2|AbsoluteLogarithmicHeight(t1[2])-AbsoluteLogarithmicHeight(t2[2])>);
  for xD in xDs do 
    F := ext< K | Polynomial([-xD[2], 0, 1]) >;
    pt := C(F)! [xD[1], F.1];
    if not (avoid2tors and 2*CcovE(pt) eq E(F)![0,1,0]) then
      return pt, F;
    end if;
  end for;
end function;

function quadratic_point(C, CcovE : num:=100, better_bound:=0, avoid:={}, avoid2tors:=true) // -> FldNum, Pt

  q := HyperellipticPolynomials(C);

  ZZ := Integers();
  Pol<X,Z> := PolynomialRing(ZZ, 2);
  hq := Pol! (Z^4*Evaluate(q, X/Z));

  // Case where quartic has large content is important
  // (occurs when E is a quadratic twist)
CC := 1;
if false then
  CC := GCD(Coefficients(hq));
  CCF := [t : t in Factorization(CC) | IsOdd(t[2])];
  CC := 1;
  if not IsEmpty(CCF) then
"Content =", GCD(Coefficients(hq)); 
    lattices := [];
    for tup in CCF do
      p, e := Explode(tup);
      // locally soluble ==> quartic has a local root
      if exists(r){r[1] : r in 
                   Roots(ChangeRing(q div p^e, GF(p))) | r[2] eq 1} 
      then
        Append(~lattices, Matrix(2, [ZZ| r, 1, p, 0, 0, p]));
        CC *:= p;
      end if;
    end for;
    L := BasisMatrix(&meet [RowSpace(L) : L in lattices]);
    L := LLL(L);
    assert Abs(Determinant(L)) eq CC;
    // Substitute hq = hq(X*L.1 + Z*L.2)
    hq := Evaluate(hq, Eltseq(X*_L[1] + Z*_L[2]) )
                       where _L is ChangeRing(L,Pol);
    hq := hq div CC^2;
"New content =", GCD(Coefficients(hq));
  end if;
end if;

  // Find real value xx0 where q(xx0) is small
  // (this will be the center of our search intervals)
  // TO DO: use more than one interval
  if CC gt 1 then
    q := Evaluate(hq, [Parent(q).1,1]);
  end if;
  dq := Derivative(q);
  roots := [ r[1] : r in Roots(q, RealField(10)) ];
  if #roots gt 0 then
    xx0 := roots[i] where _,i is Min([ Abs(Evaluate(dq, r)) : r in roots ]);
  else
    roots := [ r[1] : r in Roots(dq, RealField(10)) ];
    xx0 := roots[i] where _,i is Min([ Abs(Evaluate(q, r)) : r in roots ]);
  end if;

  points := [];
  discs := [];
  Dmin := Infinity();
  // try z up to const*sqrt{num} and try const*sqrt{num} x's for each z
  r := Ceiling(Sqrt(num));
  zz := 0;
  count := 0;
  vprintf CasselsTate,2: "Getting %o quadratic points: ", num; 
  vtime CasselsTate,2:
  while count lt num do
    zz +:= 1;
    c := Floor(xx0*zz);
    for xx in [c-r .. c+r] do
      if GCD(xx,zz) eq 1 then
        y2 := Evaluate(hq, [xx,zz]);
        if y2 ne 0 then
          count +:= 1;
          D := Squarefree(y2);
          Da := Abs(D);
          Dmin := Min(Dmin, Da);
          // only keep enough points
          if #points lt 20 or Da lt 100*Dmin then
            Append(~points, [xx, zz, y2]);
            Append(~discs, D);
          end if;
        end if;
      end if;
    end for;
  end while;
  vprintf CasselsTate,2: "Some quadratic fields where the 2-cover has a point are\n%o\n",
                          Sort(discs, func<d1,d2| Abs(d1)-Abs(d2)>);

  if CC gt 1 then
    CC2 := CC^2;
    points := [Eltseq(pt[1]*L[1] + pt[2]*L[2]) cat [CC2*pt[3]] : pt in points];
    for i := #points to 1 by -1 do
      if points[i,2] eq 0 then
        Remove(~points, i);
        Remove(~discs, i);
      end if;
    end for;
  end if;

  if 1 in avoid then
    for i := #discs to 1 by -1 do
      if discs[i] eq 1 then
        Remove(~points, i);
        Remove(~discs, i);
      end if;
    end for;
  end if;

  pairs := [[xx/zz,y2/zz^4] where xx,zz,y2 is Explode(points[i]) : i in [1..#points]];

  // Now choose the smallest disc that does not give a point mapping to E[2]
  // Also look for a smaller disc
  LB := 2; // lower bound for the '//better' search
  while true do
    Dmin := Min([Abs(D) : D in discs]);
    UB := Min(Dmin, better_bound);
    if LB lt UB then
      vprintf CasselsTate, 2: "Looking for a better quadratic point (with %o <= |D| < %o) : ", LB, UB;
      vtime CasselsTate, 2:
      D,x,ysquared := better_quadratic_point(C, LB, UB);
      if D ne 0 then
        Append(~discs, D);
        Append(~pairs, [x,ysquared]);
        Dmin := D;
        LB := Abs(D) + 1;
      else
        LB := Dmin;
      end if;
    end if;
    // if several D's have this size choose the point with smallest height
    pts := [* *];
    inds := [i : i in [1..#discs] | Abs(discs[i]) eq Dmin];
    for i in inds do
      xx, ysquared := Explode(pairs[i]);
      issqr, sqrt := IsSquare(ysquared);
      if issqr then return C![xx,sqrt], Rationals(); end if;
      denom := Denominator(ysquared);
      D,S := SquarefreeFactorization(Integers()!(ysquared*denom^2));
      F := NumberField(Polynomial([-D,0,1]));
      pt := C(F)![xx, F.1*S/denom];
      if D in avoid or avoid2tors and 2*CcovE(pt) eq Codomain(CcovE)!0 then continue; end if;
      Append(~pts, <pt,F,ysquared>);
    end for;
    if not IsEmpty(pts) then
      pt,F := Explode(pts[i]) where  _,i := Min([tup[3] : tup in pts]);
      vprintf CasselsTate: "Found point over Q(sqrt(%o))\n", -ConstantCoefficient(DefiningPolynomial(F));
      return pt, F;
    end if;
    discs := [discs[i] : i in [1..#discs] | i notin inds];
    pairs := [pairs[i] : i in [1..#pairs] | i notin inds];
  end while;
end function;

// For quartic over a FldNum, find a random local solution, 
// and return an approximation of it in the FldNum

/* 
// (TO DO) Example where we (used to) need to search near roots
// (in completion above 2, quartic td[1] factors into two quadratics 
//  whose discriminants both have valuation 28)
K := NumberField(x^2 + 5) where x is PolynomialRing(Rationals()).1;
E := BaseChange(EllipticCurve([1,0,1,-289,3092]), K);
td := TwoDescent(E : RemoveTorsion);
CasselsTatePairing(td[1], td[2]);

// TO DO: not sufficiently random! 
// In this example, it always returns the same point, which is rejected
F, ZF, w := nf(x^2 - 3);
E := EllipticCurve([ 0, (-77760*w + 124416) ]);
td, _, tds := TwoDescent(E : MinRed);
CasselsTatePairing(td[5], td[1]);
// (-2*w - 3)*x^4 - 6*w*x^2 + (-40*w + 72)*x + 6*w - 9,
// (-12*w + 21)*x^4 + (8*w - 12)*x^3 + (6*w - 18)*x^2 + (-12*w + 12)*x - 10*w - 24

*/

function local_point_FldNum(quartic, p : prec:=50)
  K := CoefficientRing(quartic);
  Kv, KtoKv := Completion(K, p); 
  assert Precision(Kv) eq Infinity();
  Kv`DefaultPrecision := prec;
  Ov := Integers(Kv);
  kv, Kvtokv := ResidueClassField(Ov);
  quartic_v := Polynomial([KtoKv(c) : c in Coefficients(quartic)]);

  pi := UniformizingElement(p);
  piv := pi@KtoKv;

  // Initial reductions, 
  coeffvals := [Valuation(c,p) : c in Coefficients(quartic)];
  w := Min(coeffvals);
  if w notin {0,1} then 
    // reduce to that case by scaling y by s
    s := pi^(w div 2);
    quartic1 := quartic/s^2;
    xx, yy := Explode(local_point_FldNum(quartic1, p : prec:=prec));
    return [xx, s*yy];    
  elif coeffvals[1] lt Min(coeffvals[2..5]) then
    // don't want scaled poly to reduce to a constant, so swap around
    assert Degree(quartic) eq 4;
    quartic1 := Polynomial(Reverse(Coefficients(quartic)));
    while true do
      xx, yy := Explode(local_point_FldNum(quartic1, p : prec:=2*prec)); 
      if Valuation(xx,p) gt Ceiling(prec/4) then prec +:= 10; 
      else break; end if;
    end while;
    if Valuation( (yy/xx^2)^2 - Evaluate(quartic,1/xx), p) ge prec + w then
      return [1/xx, yy/xx^2];
    end if; // otherwise fall back on Mark's hints, below
  elif IsOdd(w) then  // w = 1
    // if integral, x must be congruent to a zero (BUT don't know which zero)
    roots := Roots(Polynomial([ Kvtokv(c/piv^w) : c in Eltseq(quartic_v) ]));
    if #roots gt 0 then // otherwise not solvable mod p (need denominator), fall back on Marks hints 
      r := Random(roots)[1] @@Kvtokv @@KtoKv;
      quartic1 := Evaluate(quartic, pi*x+r) where x is Parent(quartic).1;
      assert Min([Valuation(c,p) : c in Coefficients(quartic1)]) gt w; // substitution is correct
      xx, yy := Explode(local_point_FldNum(quartic1, p : prec:=prec));
      return [pi*xx+r, yy]; 
    end if;
  end if;

  even := IsEven(Norm(p));

  // Naive search with increasing denominator
  function naive_search(tries)
    depth := even select 10 else 5;
    for i := 1 to tries do
      xx := &+[ Random(kv)@@Kvtokv * piv^n : n in [0..depth]];
      if IsEven(i) and not IsWeaklyZero(xx) then
        xx := 1/xx;
      end if;
      yy2 := Evaluate(quartic_v, xx); 
      if Precision(yy2) lt 10 then 
        continue; 
      end if;
      issqr, yy := IsSquare(yy2);
      if issqr then 
        return true, [xx@@KtoKv, yy@@KtoKv]; 
      end if;
    end for;
    return false, _;
  end function;

  found, pt := naive_search(even select 10^4 else 10^3);
  if found then return pt; end if;

  unfound, pt := IsEmpty(HyperellipticCurve(quartic_v)(Kv));
  if not unfound then 
    assert IsWeaklyZero(pt[3]-1);
    return [pt[1]@@KtoKv, pt[2]@@KtoKv]; 
  end if;

  found, pt := naive_search(even select 10^6 else 10^4);
  if found then return pt; end if;

  error "\nFailed to find a local point on the quartic\n", quartic, 
        "\nPlease send this example to magma-bugs@maths.usyd.edu.au";
end function;

// For quartic over Q, find a random local solution, and return a rational approximation of it

function local_point(quartic, prime : prec:=20)
  p := Minimum(prime);
  e := (p eq 2) select 2 else 1;

  K := CoefficientRing(quartic);
  Kv, KtoKv := Completion(K, prime); assert Precision(Kv) eq Infinity();
  Kv`DefaultPrecision := prec;
  quartic_v := Polynomial([ KtoKv(c) : c in Coefficients(quartic) ]);

  // Initial reductions, 
  coeffvals := [ Valuation(c,prime) : c in Coefficients(quartic) ];
  w := Min(coeffvals);
  if w notin {0,1} then 
    // reduce to that case by scaling y by s
    s := p^(w div 2);
    quartic1 := quartic/s^2;
    xx, yy := Explode(local_point(quartic1, prime : prec:=prec));
    return [xx, s*yy];    
  elif coeffvals[1] lt Min(coeffvals[2..5]) then
    // don't want scaled poly to reduce to a constant, so swap around
    assert Degree(quartic) eq 4;
    quartic1 := Polynomial(Reverse(Coefficients(quartic)));
    while true do
      xx, yy := Explode(local_point(quartic1, prime : prec:=2*prec)); 
      if Valuation(xx) gt Ceiling(prec/4) then prec +:= 10; 
      else break; end if;
    end while;
    if Valuation( (yy/xx^2)^2 - Evaluate(quartic,1/xx) ) ge prec + w then
      return [1/xx, yy/xx^2]; end if; // otherwise fall back on Mark's hints, below
  elif IsOdd(w) then  // (w = 1)
    // if integral, x must be congruent to a zero (BUT don't know which zero)
    Ov := Integers(Kv);
    kv, Kvtokv := ResidueClassField(Ov);
    roots := Roots(Polynomial([ Kvtokv(c/p^w) : c in Eltseq(quartic_v) ]));
    if #roots gt 0 then // otherwise not solvable mod p (need denominator), fall back on Marks hints 
      r := Random(roots)[1] @@Kvtokv @@KtoKv;
      quartic1 := Evaluate(quartic, p*x+r) where x is Parent(quartic).1;
      assert Min([ Valuation(c,prime) : c in Coefficients(quartic1) ]) gt w; // substitution is correct
      xx, yy := Explode(local_point(quartic1, prime : prec:=prec));
      return [p*xx+r, yy]; end if;
  end if;

  for i := 1 to 200 do
    if i mod 50 eq 0 and p eq 2 or i mod 100 eq 0 then e +:= 1; end if;
    xx := KtoKv( Random(10^10)*p^Random([-e..e]) );
    yy2 := Evaluate(quartic_v, xx); if Precision(yy2) lt 4 then continue; end if;
    issqr, yy := IsSquare(yy2);
    if issqr then return [xx, yy]; end if;
  end for;

  // Points are hard to find, so ask for help ... 
  vd := Abs(Valuation(Discriminant(quartic), prime));
  bool, sol := GetLocalQuarticSolution(quartic, p, vd+50); assert bool;
  // need random answers, so perturb Mark's nice solution
  prec := 30 + Valuation(Discriminant(quartic), 2);
  Kv`DefaultPrecision := prec;
  sol := sol @KtoKv;
  for i in [1..prec], j in [1..5] do 
    xx := sol + Random(10^6)*p^i;
    yy2 := Evaluate(quartic, xx); 
    if Precision(yy2) lt 10 then continue; end if;
    bool, yy := IsSquare(yy2);
    if bool then return [xx, yy]; end if;
  end for; 

  /**** This is non-random, and doesn't work
  bool, pt := IsLocallySolvable(HyperellipticCurve(quartic), p);  assert bool;
  pt := LiftPoint(pt, 20 : Strict:=false);
  assert IsWeaklyEqual( pt[3], 1);
  xx := pt[1] @@KtoKv; 
  yy := pt[2] @@KtoKv; 
  if Valuation((yy@@KtoKv)^2 - Evaluate(quartic,xx@@KtoKv), prime) gt 10 then
    return [ pt[1] @@ KtoKv, pt[2] @@ KtoKv ]; 
  end if; 
  ****/

  error "Failed to find a local point on the quartic\n", quartic, 
        "\nPlease send this example to magma-bugs@maths.usyd.edu.au";
end function;

// rational approximation to a real point, for a quartic over the rationals 

function real_point(quartic : rand:=false )  // -> [ FldRatElt]
  prec := 50 + Ceiling(Max([Log(10,Abs(Norm(c))+1) : c in Coefficients(quartic)]));
  R := RealField(prec);

  if not rand then
    interval := [-20 .. 20];
    for xx in [i/2 : i in interval] cat [10*i : i in interval] do
      ysquared := Evaluate(quartic,xx);
      if ysquared ge 0 then
        yy := Round(Sqrt(R!ysquared)*10^prec)/10^prec;
        return [xx,yy];
      end if;
    end for;
  end if;

  roots := [ r[1] : r in Roots(quartic,R) ];
  if IsEmpty(roots) then roots := [0,100]; end if; // any interval works
  rand := Random([1..99]);
  if LeadingCoefficient(quartic) gt 0 then
    xx := Floor(Max(roots)) + rand;
  else
    xx := (rand*roots[2] + (100-rand)*roots[1]) / 100;
  end if;
  ysquared := Evaluate(quartic,xx);
  assert ysquared gt 0;
  rat := [ Round(c*10^prec)/10^prec : c in [xx, Sqrt(R!ysquared)] ];
  assert rat[2]^2 - Evaluate(quartic,rat[1]) lt 10^-20;
  return rat;
end function;

// "evaluate" a function field element at a "point" that is not (quite) on the curve!
// The function and point must be over the global field (or the point can be over Qp)

function plug_in(f, pt : max_val:=Infinity(), p:=0, conjugate:=0 )
  Qp := Universe(pt);
  padic := ISA( Type(Qp), FldPad );
  fixedprec := padic and Precision(Qp) ne Infinity();
  if padic and not fixedprec then
    // make sure Evaluate uses the right precision for coercion
    Qpdef := Qp`DefaultPrecision;
    Qp`DefaultPrecision := Max([ Precision(c) : c in pt ]); 
  end if;
  
  patch := FFPatchIndex(Scheme(Parent(f)));
  if patch ne 1 then 
    k := #pt + 2 - patch; // FF patch dehomogenised wrt kth projective variable
    if IsWeaklyZero(pt[k]) then 
      vprint CasselsTate, 3: "Patch index is", patch, "and point is not on patch, try again!";
      // (could express f homogeneously and plug in, but simpler to get a new point)
      return false,_;
    else
      pt := pt cat [1]; // projective point
      pt := [pt[i]/pt[k] : i in [1..#pt] | i ne k]; // affine point on FF patch
    end if;
  end if;
  PAA := OriginalRing(Parent(Numerator(f)));
  numf := PAA!Numerator(f);
  denf := PAA!Denominator(f);
  if conjugate ne 0 then
    assert Type(PAA) eq RngMPol;
    PR := PolynomialRing(RealField(), Rank(PAA));
    C,M := CoefficientsAndMonomials(numf);
    numf := &+[ Real(Conjugate(C[i],conjugate)) * Monomial(PR,Exponents(M[i])) : i in [1..#M]];
    C,M := CoefficientsAndMonomials(denf);
    denf := &+[ Real(Conjugate(C[i],conjugate)) * Monomial(PR,Exponents(M[i])) : i in [1..#M]];
  end if;
  num := Evaluate(numf, pt);
  den := Evaluate(denf, pt);

  if padic then
    if not fixedprec then Qp`DefaultPrecision := Qpdef; end if; // restore original setting
    if Valuation(num) ge max_val or Valuation(den) ge max_val then
      vprint CasselsTate, 3: "Too close to a pole or zero, try again!";
      return false,_;
    end if;
  elif p cmpne 0 then // pt over exact field, prime is p
    if Valuation(num,p) ge max_val or Valuation(den,p) ge max_val then
      vprint CasselsTate, 3: "Too close to a pole or zero, try again!";
      return false,_;
    end if;
  else // pt over reals 
    if Abs(num) lt 10^-max_val or Abs(den) lt 10^-max_val then
      vprint CasselsTate, 3: "Too close to a pole or zero, try again!";
      return false,_;
    end if;
  end if;

  return true, num/den;
end function;

