freeze;
// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!
/*************************************
 * Hyperelliptic/height.m            *
 *                                   *
 * Compute canonical heights and     *
 * the height constant               *
 *                                   *
 * Michael Stoll                     *
 *                                   *
 * started 25-Feb-1999               *
 *************************************/

import "../CrvHyp/places.m" : MakePlaceFunRatElt;
import "../CrvHyp/models.m" : IspMinimalfunction, 
			      pMinimalWeierstrassModelfunction;

/*------------------------------------------------------------------
  TO DO
  
    Improve FindOptimum -- use knowledge of where bad points are
  
  CHANGES
  
  M. Stoll, 2000-08-11
  
    New verbose flag JacHypHeight
  
13/7/01	nicole	Comment on Height and CanonicalHeigth synonym from kernel
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 Curve fix

  M. Stoll, 2001-10
  
    Introducing heights over rational function fields

17/04/03 Nicole Sutherland

    Small changes in CanonicalHeight to reflect change to rational places
    (and import statements)

2004-10, Michael Stoll
  Adapted a few things to make heights over F(t) work again.

27/05/05 Mike Harrison
  Made updates for new Real/Complex field structures.  

Feb 2006 Steve
  Minor fixes from Michael

Feb-March 2006 Steve
  I patched up Michael's patch 
  (see the section beginning
   "// Michael sent a patch replacing" ...)

11/03/2011 Jan Steffen Mueller
  General intrinsics moved to CrvHyp/height.m

  ------------------------------------------------------------------*/

// Declarations

declare verbose JacHypHeight, 3;

function MyVariety(I) 
    // For an ideal I in a multivariate polynomial ring over a finite 
    // field F, returns the set of all F-rational solutions.
    F := CoefficientRing(I);
    // require IsField(F) and IsFinite(F):
    //        "Coefficient ring must be a finte field.";
    P := Generic(I);
    r := Rank(P);
    dim := Dimension(I);
    if dim lt 0 then return []; end if;
    if dim eq 0 then return Variety(I); end if;
    // now dimension at least 1
    if r eq 1 then
      // rank = dim = 1 ==> I = 0, all points are solutions
      return [ <a> : a in F ];
    end if;
    I1 := EliminationIdeal(I, { P.i : i in [1..r-1] });
    P1 := PolynomialRing(F, r-1);
    vs := [ P1.i : i in [1..r-1] ];
    I1 := ideal< P1 | [Evaluate(a, vs cat [P1!0]) : a in Basis(I1)] >;
    var1 := MyVariety(I1);
    P0 := PolynomialRing(F);
    x := P0.1;
    var := [];
    B := Basis(I);
    for pt in var1 do
      f := GCD([P0 | Evaluate(b, pts cat [x]) : b in B])
           where pts := [ P0 | pt[i] : i in [1..r-1] ];
      if f eq 0 then
        var cat:= [ Append(pt, a) : a in F ];
      else
        var cat:= [ Append(pt, r[1]) : r in Roots(f) ];
      end if;
    end for;
    return var;
end function;

// The following procedure finds the optimal local height constant at
// an odd prime p.
// Method: We have to maximise
//   min{v_p(delta_j(x_1,x_2,x_3,x_4)) | j = 1,2,3,4}
// over the set of all (x_1,x_2,x_3,x_4) in Z_p with one of them = 1
// such that   kappa(x_1,x_2,x_3,x_4) = 0
//  and        t_1(x_1,x_2,x_3,x_4), t_2(x_1,x_2,x_3,x_4) are squares.

function FindOptimum(p, ds, k, ts, vars, bound)
  // p = prime, ds = [delta_1,...,delta_4], k = kappa, ts = [t_1, t_2],
  // vars = [x_1,x_2,x_3] (say, when x_4 = 1 is fixed);
  // vars =~ Generators(Parent(k)), Parent(k) is a polynomial ring over Z
  vprintf JacHypHeight, 2: "FindOptimum(%o)\n", p;
  P := Parent(k); // = Universe(ds) = Universe(ts)
  F := GF(p);
  PF := PolynomialRing(F, #vars);
  Fvars := [ PF.i : i in [1..#vars] ];
  // An auxiliary function
  function ValLt(poly)
    // poly in P, returns valuation of P and leading term
    cs := Coefficients(poly);
    ms := Monomials(poly);
    v := Min([ Valuation(c, p) : c in cs | c ne 0 ]);
    return v, PF!ExactQuotient(poly, p^v);
  end function;
  // Check if a partial solution lifts to a p-adic solution
  function CheckLift(k1)
    // Check if k1 = 0 lifts
    // simply return true for now
    return true;
  end function;
  // The recursive procedure that does the refinement
  function Search(ds1, k1, ts1)
    vprintf JacHypHeight, 3: " Search: ";
    // See if an improvement might be possible
    dsi := [ <v, l> where v, l := ValLt(d) : d in ds1 | d ne 0 ];
    vprintf JacHypHeight, 3: "%o, ", [a[1] : a in dsi];
    currv := Min([ a[1] : a in dsi ]);
    // the following expressions must be 0 mod p in order to get a better
    // value
    ids := [ a[2] : a in dsi | a[1] eq currv ];
    // kappa must vanish
    if k1 ne 0 then
      v, l := ValLt(k1);
      Append(~ids, l);
      vprintf JacHypHeight, 3: "%o, ", v; 
    end if;
    // now look at the t's
    tsi := [ <v, l, t> where v, l := ValLt(t) : t in ts1 | t ne 0 ];
    vprintf JacHypHeight, 3: "%o.\n", [a[1] : a in tsi];
    for a in tsi do
      if IsOdd(a[1]) then
        if TotalDegree(a[2]) eq 0 then
          // no chance to get a square here
          vprintf JacHypHeight, 3: "  ret: -1.\n";
          return -1;
        else
          Append(~ids, a[2]);
        end if;
      else
        if TotalDegree(a[2]) eq 0 then
          if IsSquare(MonomialCoefficient(a[2], PF!1)) then
            // always a square: can remove condition
            Exclude(~ts1, a[3]);
          else
            // never a square
            vprintf JacHypHeight, 3: "  ret: -1.\n";
            return -1;
          end if;
        else
          // do nothing
        end if;
      end if;
    end for;
    // Now see if we can get an improvement
    // vprintf JacHypHeight, 3: "  ideal:\n%o\n", ids;
    I := ideal< PF | ids>;
    currv :=  CheckLift(k1) select currv else -1;
    if currv eq bound then
      vprintf JacHypHeight, 3: "  bound %o is reached. ret %o.\n", bound, bound;
      return bound;
    end if;
    var := MyVariety(I);
    vprintf JacHypHeight, 3: "  variety size = %o.\n", #var;
    evv := [ [(Integers()!var[j,i]) + p*vars[i] : i in [1..#vars]]
              : j in [1..#var] ];
    for ev in evv do
      currv := Max(currv, Search([Evaluate(d, ev) : d in ds1],
                                 Evaluate(k1, ev),
                                 [Evaluate(t, ev) : t in ts1]));
      if currv eq bound then
        vprintf JacHypHeight, 3:
                "  bound %o is reached. ret %o.\n", bound, bound;
        return bound;
      end if;
    end for;
    return currv;
  end function;
  // Start the search
  return Search(ds, k, ts);
end function;

// Same for p = 2

function FindOptimum2(ds, k, ts, vars, bound)
  // ds = [delta_1,...,delta_4], k = kappa, ts = [t_1, t_2],
  // vars = [x_1,x_2,x_3] (say, when x_4 = 1 is fixed);
  // vars =~ Generators(Parent(k)), Parent(k) is a polynomial ring over Z
  vprintf JacHypHeight, 2: "FindOptimum(2)\n";
  P := Parent(k); // = Universe(ds) = Universe(ts)
  F := GF(2); Z4 := Integers(4); Z8 := Integers(8);
  PF := PolynomialRing(F, #vars);
  PZ4 := PolynomialRing(Z4, #vars);
  PZ8 := PolynomialRing(Z8, #vars);
  Fvars := [ PF.i : i in [1..#vars] ];
  Z4vars := [ PZ4.i : i in [1..#vars] ];
  Z8vars := [ PZ8.i : i in [1..#vars] ];
  // An auxiliary function
  function ValLt(poly)
    // poly in P, returns valuation of P and leading term
    cs := Coefficients(poly);
    ms := Monomials(poly);
    v := Min([ Valuation(c, 2) : c in cs | c ne 0 ]);
    polr := ExactQuotient(poly, 2^v);
    return v, PF!polr, PZ4!polr, PZ8!polr;
  end function;
  // Check if a partial solution lifts to a p-adic solution
  function CheckLift(k1)
    // Check if k1 = 0 lifts
    // simply return true for now
    return true;
  end function;
  // The recursive procedure that does the refinement
  function Search(ds1, k1, ts1)
    vprintf JacHypHeight, 3: " Search: ";
    // See if an improvement might be possible
    dsi := [ <v, l> where v, l := ValLt(d) : d in ds1 | d ne 0 ];
    vprintf JacHypHeight, 3: "%o, ", [a[1] : a in dsi];
    currv := Min([ a[1] : a in dsi ]);
    // the following expressions must be 0 mod p in order to get a better
    // value
    ids := [ a[2] : a in dsi | a[1] eq currv ];
    // kappa must vanish
    if k1 ne 0 then
      v, l := ValLt(k1);
      Append(~ids, l);
      vprintf JacHypHeight, 3: "%o, ", v; 
    end if;
    // now look at the t's
    ts1 := [ t : t in ts1 | t ne 0 ];
    tsi := [ <v, l2, l4, l8, t> where v, l2, l4, l8 := ValLt(t)
             : t in ts1 ];
    vprintf JacHypHeight, 3: "%o.\n", [a[1] : a in tsi];
    for a in tsi do
      if IsOdd(a[1]) then
        if TotalDegree(a[2]) eq 0 then
          // no chance to get a square here
          vprintf JacHypHeight, 3: "  ret: -1.\n";
          return -1;
        else
          Append(~ids, a[2]);
        end if;
      else
        if TotalDegree(a[4]) eq 0 then
          if MonomialCoefficient(a[4], PZ8!1) eq Z8!1 then
            // always a square: can remove condition
            Exclude(~ts1, a[3]);
          else
            // never a square
            vprintf JacHypHeight, 3: "  ret: -1.\n";
            return -1;
          end if;
        elif TotalDegree(a[3]) eq 0 then
          if MonomialCoefficient(a[3], PZ4!1) eq Z4!3 then
            // never a square
            vprintf JacHypHeight, 3: "  ret: -1.\n";
            return -1;
          end if;
        else
          // do nothing
        end if;
      end if;
    end for;
    // Now see if we can get an improvement
    // vprintf JacHypHeight, 3: "  ideal:\n%o\n", ids;
    I := ideal< PF | ids>;
    currv :=  CheckLift(k1) select currv else -1;
    if currv eq bound then
      vprintf JacHypHeight, 3: "  bound %o is reached. ret %o.\n", bound, bound;
      return bound;
    end if;
    var := MyVariety(I);
    vprintf JacHypHeight, 3: "  variety size = %o.\n", #var;
    evv := [ [(Integers()!var[j,i]) + 2*vars[i] : i in [1..#vars]]
              : j in [1..#var] ];
    for ev in evv do
      currv := Max(currv, Search([Evaluate(d, ev) : d in ds1],
                                 Evaluate(k1, ev),
                                 [Evaluate(t, ev) : t in ts1]));
      if currv eq bound then
        vprintf JacHypHeight, 3:
                "  bound %o is reached. ret %o.\n", bound, bound;
        return bound;
      end if;
    end for;
    return currv;
  end function;
  // Start the search
  return Search(ds, k, ts);
end function;

function LocalHeightConst(K, p, bound)
  // K = Kummer Surface, p = prime
  PZ4 := PolynomialRing(Integers(), 4);
  PZ3 := PolynomialRing(Integers(), 3);
  vars := [ PZ3.1, PZ3.2, PZ3.3 ];
  vss := [ [1, PZ3.1, PZ3.2, PZ3.3],
           [p*PZ3.1, 1, PZ3.2, PZ3.3],
           [p*PZ3.1, p*PZ3.2, 1, PZ3.3],
           [p*PZ3.1, p*PZ3.2, p*PZ3.3, 1]];
  ds4 := ChangeUniverse(K`Delta, PZ4);
  k4 := PZ4!DefiningPolynomial(K);
  ts4 := ChangeUniverse([K`AuxPolynomials[3], K`AuxPolynomials[5]], PZ4);
  v := 0;
  if IsOdd(p) then
    for vs in vss do
      v := Max(v, FindOptimum(p, [Evaluate(d, vs) : d in ds4],
                                 Evaluate(k4, vs),
                                 [Evaluate(t, vs) : t in ts4],
                                 vars, bound));
      if v eq bound then return v; end if;
    end for;
    return v;
  else
    for vs in vss do
      v := Max(v, FindOptimum2([Evaluate(d, vs) : d in ds4],
                               Evaluate(k4, vs),
                               [Evaluate(t, vs) : t in ts4],
                               vars, bound));
      if v eq bound then return v; end if;
    end for;
    return v;
  end if;
end function;

intrinsic HeightConstant(J::JacHyp : Effort := 0, Factor := false)
  -> FldReElt, FldReElt
{If J is the Jacobian of a gneus 2 curve defined over the rationals,
 of the form  y^2 = f(x)  with integral coefficients, this computes
 a real number c such that  h_K(P) le h(P) + c  for all P in J(Q),
 where h_K is the naive logarithmic height got from the Kummer surface
 and h is the canonical height on J. Effort is some specification
 as to how much effort should be put into getting a good bound.
 The second value returned is a bound for mu_infinity. If Factor is set
 to true, the discriminant will be factored, and its prime divisors
 will be considered individually. This usually results in an improvement
 of the bound. }
    // See M. Stoll: On the height constant for curves of genus two,
    // preprint 1998
    C := Curve(J);
    require Genus(C) eq 2 and CoefficientRing(C) cmpeq Rationals():
            "HeightConstant is only implemented",
            "for Jacobians of genus 2 curves over the rationals.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0 and &and[ Denominator(c) eq 1 : c in Coefficients(f)]:
            "HeightConstant needs a curve of the form  y^2 = f(x), ",
            "where f has integral coefficients.";
    require IsIntegral(Effort) and Effort ge 0 :
            "The Effort parameter must be a non-negative integer.";
    if assigned J`HeightConst and J`HeightConst[3] ge Effort 
        and (not Factor or J`HeightConst[4]) then
      return J`HeightConst[1], J`HeightConst[2];
    end if;
    K := KummerSurface(J);
    Factor := Factor or Effort ge 2;
    partitions := [ <[6,5,4],[3,2,1]>, <[6,5,3],[4,2,1]>, <[6,4,3],[5,2,1]>,
                    <[6,2,1],[5,4,3]>, <[6,5,2],[4,3,1]>, <[6,4,2],[5,3,1]>,
                    <[6,3,1],[5,4,2]>, <[6,3,2],[5,4,1]>, <[6,4,1],[5,3,2]>,
                    <[6,5,1],[4,3,2]> ];
    roots := [ r[1] : r in Roots(f /*inj(f)*/, ComplexField()) ];
    vprintf JacHypHeight, 1: "Find height constant for J =\n%o\n", J;
    vprintf JacHypHeight, 2: " Roots of f:\n";
    if GetVerbose("JacHypHeight") ge 2 then
      Cprt<i> := ComplexField(15);
      for r in roots do printf "   %o\n", Cprt!r; end for;
      delete Cprt;
    end if;
    lcf := Abs(LeadingCoefficient(f));
    // Find a bound for the local height constant at infinity
    a1 := 0; a2 := 0; a3 := 0; a4 := 0;
    for i := 1 to 10 do
      pi := partitions[i];
      p1 := pi[1]; p2 := pi[2];
      if Degree(f) eq 6 then
        u1 := roots[p1[1]] + roots[p1[2]];
        v1 := roots[p1[1]]*roots[p1[2]];
        s := [u1 + roots[p1[3]], u1*roots[p1[3]] + v1, v1*roots[p1[3]]];
        s0 := 1;
        res := &*[ roots[j1]-roots[j2] : j1 in p1, j2 in p2 ] * lcf^3;
      else
        s := [1, roots[p1[2]]+roots[p1[3]], roots[p1[2]]*roots[p1[3]]];
        s0 := 0;
        res := &*[ roots[j1]-roots[j2] : j1 in p1[[2,3]], j2 in p2 ] * lcf^3;
      end if;
      u2 := roots[p2[1]] + roots[p2[2]];
      v2 := roots[p2[1]]*roots[p2[2]];
      t := [u2 + roots[p2[3]], u2*roots[p2[3]] + v2, v2*roots[p2[3]]];
      b := Sqrt(lcf*(Modulus(s[3]*t[1] + s[1]*t[3])
                      + Modulus(s[3] + s0*t[3])
                      + Modulus(s[2] + s0*t[2]))
                 + 1);
      rr := Modulus(b/(4*res));
      a1 +:= rr*Modulus(s[1]-s0*t[1]);
      a2 +:= rr*Modulus(s[3]-s0*t[3] + s[2]*t[1]-s[1]*t[2]);
      a3 +:= rr*Modulus(s[3]*t[2]-s[2]*t[3]);
      a4 +:= rr*Modulus(s[1]*s[3]^2*t[2] - s0^2*s[2]*t[1]*t[3]^2
                         + s[1]*s[2]*t[1]*t[2]*(s[3] - s0*t[3])
                         - s[3]*t[3]*(s[1]*s[2] - s0^2*t[1]*t[2])
                         - s[1]*t[1]*(s[2]^2*t[3] - s0*s[3]*t[2]^2)
                         - s[1]^2*s[3]*t[2]^2 + s0*s[2]^2*t[1]^2*t[3]
                         + 4*s[1]*s[3]*t[1]*t[3]*(s[1] - s0*t[1])
                         + s[2]*t[2]*(s[1]^2*t[3] - s0*s[3]*t[1]^2)
                         - s0*(s[3]^2*t[1]*t[2] - t[3]^2*s[1]*s[2])
                         + s0*(4*s[3]*t[3]*(s[3] - s0*t[3])
                                + 4*s[2]*t[2]*(s[3]*t[2] - s[2]*t[3])
                                - 3*s[3]*t[3]*(s[2]*t[1] - s[1]*t[2])));
    end for;
    a1 *:= lcf; a2 *:= lcf; a3 *:= lcf; a4 *:= lcf^3;
    hc_inf := 2*Log(Max([a1,a2,a3,a4]));
    vprintf JacHypHeight, 1: " Bound for height constant at infinity:\n";
    vprintf JacHypHeight, 1: "   %o\n", hc_inf;
    // Now find a bound for the finite part
    disc := Integers()!Abs(Discriminant(C)/256); // this is |disc(F)|
    logdisc := Log(disc*16);
    c := GCD(ChangeUniverse(Eltseq(f), Integers()));
    disc1 := ExactQuotient(16*disc, c^6);
    hc_finite := Log(disc1);
    vprintf JacHypHeight, 1: " Bound for finite part of height constant:\n";
    vprintf JacHypHeight, 1: "   %o\n", hc_finite;
    if Effort ge 1 then
      // Use bound via R(S, S').
      // For a subset S of {1,2,3,4,5,6}, let F_S be the corresponding
      //  divisor of F (= homogenezation of f of degree 6).
      // Find the product over all (X - Disc(F_S) Disc(F_S')) where
      //  {S, S'} is a partition of {1,...,6} into two three-sets.
      //  This is a polynomial with integral coefficients.
      vprintf JacHypHeight, 1: "  Effort >= 1: Look at R(S,S')^2...\n";
      // First use the absolute values in order to estimate the
      //  precision needed.
      if Degree(f) eq 6 then
        ds := [ Modulus(lcf^4*dis(part[1])*dis(part[2])) : part in partitions ]
              where dis := func< p | (roots[p[1]]-roots[p[2]])^2
                                      * (roots[p[1]]-roots[p[3]])^2
                                      * (roots[p[2]]-roots[p[3]])^2 >;
      else // deg(f) = 5
        ds := [ Modulus(lcf^4*(roots[part[1][2]]-roots[part[1][3]])^2
                             *dis(part[2]))
                 : part in partitions ]
              where dis := func< p | (roots[p[1]]-roots[p[2]])^2
                                      * (roots[p[1]]-roots[p[3]])^2
                                      * (roots[p[2]]-roots[p[3]])^2 >;
      end if; // Degree(f) eq 6
      cs := Eltseq(&*[ PR.1 - d : d in ds ]) where PR is 
      					PolynomialRing(RealField());
      prec := Ceiling(Log(Max(cs)))+6;
      vprintf JacHypHeight, 2: "   Estimated precision: %o decimal digits.\n",
              prec;
      // Recompute the roots to the new precision
      roots := [ r[1] : r in Roots(f, ComplexField(prec)) ];
      // Now compute the polynomial we want
      PC := PolynomialRing(ComplexField(prec));
      if Degree(f) eq 6 then
        dp := &*[ PC.1 - lcf^4*dis(part[1])*dis(part[2]) : part in partitions ]
              where dis := func< p | (roots[p[1]]-roots[p[2]])^2
                                      * (roots[p[1]]-roots[p[3]])^2
                                      * (roots[p[2]]-roots[p[3]])^2 >;
      else // deg(f) = 5
        dp := &*[ PC.1 - lcf^4*(roots[part[1][2]]-roots[part[1][3]])^2
                              *dis(part[2])
                 : part in partitions ]
              where dis := func< p | (roots[p[1]]-roots[p[2]])^2
                                      * (roots[p[1]]-roots[p[3]])^2
                                      * (roots[p[2]]-roots[p[3]])^2 >;
      end if; // Degree(f) eq 6
      ds := Eltseq(dp);
      cs := [ Round(Real(c)) : c in ds ];
      require Max([Modulus(cs[i] - ds[i]) : i in [1..11]]) le 0.1 :
              "Insufficient precision in computation of resolvent polynomial.";
      // Check that suitable powers of disc divide the lower coeffs
      require (cs[1] eq disc^4) and (cs[2] mod disc^3 eq 0)
               and (cs[3] mod disc^2 eq 0) and (cs[4] mod disc eq 0) :
              "Insufficient precision in computation of resolvent polynomial.";
      // Now split off the primes that will contribute to improving the bound
      g := GCD(cs[[5..10]]);
      vprintf JacHypHeight, 2: "   `Small primes factor' = %o\n", g;
      if g eq 1 then
        vprintf JacHypHeight, 2: "   no improvement\n";
      else
        pl := [ a[1] : a in Factorization(g) ];
        vprintf JacHypHeight, 2: "   is divisible by primes ";
        if GetVerbose("JacHypHeight") ge 2 then
          for i := 1 to #pl do
            if i lt #pl
              then printf "%o, ", pl[i];
              else printf "%o\n", pl[i];
            end if;
          end for;
        end if; // GetVerbose("JacHypHeight") ge 2
        improve := 1;
        for p in pl do
          im_p := Min([Ceiling(Valuation(cs[i], p)/(11-i)) : i in [1..10]
                                                           | cs[i] ne 0]);
          vprintf JacHypHeight, 2: "   improvement by  %o log %o\n", im_p, p;
          improve *:= p^im_p;
        end for;
        disc1 := ExactQuotient(disc1, improve);
        hc_finite -:= Log(improve);
        vprintf JacHypHeight, 2: " New finite part is %o\n", hc_finite;
      end if; // g eq 1
    end if; // Effort ge 1
    if Factor then
      vprintf JacHypHeight, 2: " Factoring the finite bound...\n";
      fact := Factorization(disc1);
      vprintf JacHypHeight, 2: "  Factorization: %o\n", fact;
      for fp in fact do
        p := fp[1]; v := fp[2]; vd := Valuation(disc, p);
        vprintf JacHypHeight, 2: "  p = %o: v_%o(disc) = %o.\n", p, p, vd;
        if vd eq 1 then
          vprintf JacHypHeight, 2: "   v_%o = 1 --> can remove %o.\n", p, p;
          disc1 := ExactQuotient(disc1, p^v);
          v := 0;
        elif IsOdd(p) and vd le 4 then
          fred := PolynomialRing(GF(p))!ChangeUniverse(Eltseq(f), Integers());
          factred := [ a[2] : a in Factorization(fred) ];
          if Degree(f) lt 6 then factred cat:= [6 - Degree(f)]; end if;
          vprintf JacHypHeight, 2:
                  "   Exponents in factorization of f mod %o:\n   %o\n",
                  p, factred;
          // now factred is the sequence of exponents in the factorisation
          // of the homogenized f
          if Max(factred) eq vd + 1 then
            vprintf JacHypHeight, 2: 
                  "   Model is regular at %o, f mod %o has at least 2 roots,\n",
                  p, p;
            vprintf JacHypHeight, 2 :
                    "     with only one of them multiple --> can remove %o.\n",
                    p;
            disc1 := ExactQuotient(disc1, p^v);
            v := 0;
          end if; // Max(factred) eq vd + 1
        end if; // vd eq 1
        if Effort ge 2 and v gt 0 then
          v0 := LocalHeightConst(K, p, v);
          vprintf JacHypHeight, 1:
                  "  Optimal bound at %o : %o log %o.\n", p, v0, p;
          if v0 lt v then
            disc1 := ExactQuotient(disc1, p^(v-v0));
          end if;
        end if; // Effort ge 2 and Valuation(disc1, p) gt 0
      end for; // fp in fact
      hc_finite := Log(disc1);
      vprintf JacHypHeight, 1: " New finite part is %o\n", hc_finite;
    end if; // Factor
    vprintf JacHypHeight, 1: " Result (infinite + finite)/3 is\n  %o\n\n",
            (hc_finite + hc_inf)/3;
    // Determine upper bound for |delta(P)|/|P|^4 at infinity
    hc_inf_both := Max(hc_inf,
                       Log(Max([Abs(t) :
                                t in &cat[Coefficients(d) : d in K`Delta]])));
    J`HeightConst := <(hc_finite + hc_inf)/3, hc_inf_both/3, Effort, Factor>;
    return (hc_finite + hc_inf)/3, hc_inf_both/3;
end intrinsic;

intrinsic NaiveHeight(P::SrfKumPt) -> FldReElt
{Computes the logarithmic height on the Kummer surface. }
    TR := Type(CoefficientRing(Parent(P)));
    require TR in  {FldRat, FldFunRat}:
          "NaiveHeight is only implemented for the rationals or a",
          "rational function field of one variable as base field.";
    if TR eq FldRat then
      // This uses the normalization of SrfKumPts over the rationals!!
      return Log(Max([ Abs(c) : c in Eltseq(P) ]));
    elif TR eq FldFunRat then
      // This uses the normalization of SrfKumPts over rat'l function fields!!
      return m where m := Max([ Degree(c) : c in Eltseq(P) ]);
    else
      error "Problem in NaiveHeight(SrfKumPt)!!";
    end if;
end intrinsic;

intrinsic NaiveHeight(P::JacHypPt) -> FldReElt
{Computes the logarithmic naive height of P given by the mapping J -> K -> P^3.
 J must be a Jacobian of a genus 2 curve over the rationals. }
    J := Parent(P);
    require Genus(Curve(J)) eq 2:
            "NaiveHeight is only implemented for Jacobians of curves of",
            "genus 2.";
    return NaiveHeight(KummerSurface(J)!P);
end intrinsic;

//----------------------------------------------------------------------
// Compute Canonical Height.
//----------------------------------------------------------------------

// This is the algorithm described in
// E.V. Flynn, N.P. Smart: Canonical heights on the Jacobians of curves
//  of genus 2 and the infinite descent, Acta Arith. 79, 333-352 (1997)
// with improvements by myself
// M. Stoll: On the height constant for curves of genus two, II,
// to appear in Acta Arith., maybe 2002.

MyPrec := func<R | Precision(R)>;

intrinsic CanonicalHeight(P::SrfKumPt : Precision := 0) -> FldReElt
{Computes the canonical height of P.}
  // Some checks
  R := CoefficientRing(Parent(P));
  TR := Type(R);
  require TR eq FldRat or (TR eq FldFunRat and Type(Integers(R)) eq RngUPol):
          "NaiveHeight is only implemented for the rationals or a",
          "univariate rational function field as base field.";
  f := HyperellipticPolynomials(Curve(Jacobian(Parent(P))));
  require forall{c : c in Coefficients(f) | Denominator(c) eq 1}:
          "Defining polynomial of the curve must have integral coefficients.";
  vprint JacHypHeight: "CanonicalHeight: P =",P;
  K := Parent(P);
  if P eq K!0 then
    vprintf JacHypHeight:" P = 0, so height is zero.\n";
    return TR eq FldRat select RealField()!0 else 0;
  end if;
  D := K`Delta;
  if TR eq FldRat then
    eqn := DefiningPolynomial(K);
    Pol := PolynomialRing(RealField());
    x := Pol.1;
    P1s := ChangeUniverse(Eltseq(P), Integers());
    // Find the epsilon_p(n*P) for the bad primes
    P2s := [ Integers() | Evaluate(D[j], P1s) : j in [1..4]];
    g := GCD(P2s);
    bad := PrimeDivisors(g);
    vprintf JacHypHeight: " Bad primes: %o\n", bad;
    tables1 := [ <p, [0, Valuation(g,p)]> : p in bad ];
    tables := [];
    m := 1;
    mP := P;
    mP1 := K!0;
    mP3 := PseudoAdd(K!P2s, P, P); // (2*m+1)*P
    while not IsEmpty(tables1) do
      if IsDivisibleBy(m,10) then
        vprintf JacHypHeight, 3: "  m = %o\n", m;
      end if;
      // compute next multiple
      // here, mP = m*P, mP1 = (m-1)*P
      Ptemp := PseudoAdd(mP, P, mP1); // compute (m+1)*P
      mP1 := mP;
      mP := Ptemp;
      m +:= 1;
      // If m*P = 0, P is torsion and has height zero.
      if mP eq K!0 then
        vprintf JacHypHeight:" %o*P = 0, so height is zero.\n", m;
        return RealField()!0;
      end if;
      P2s := [Integers() | Evaluate(D[j], s) : j in [1..4]]
              where s := Eltseq(mP);
      g := GCD(P2s);
      P2s := [ a div g : a in P2s];
      mP2 := K!P2s;
      mP3 := PseudoAdd(mP2, P, mP3); // new (2*m+1)*P
      P3s := ChangeUniverse(Eltseq(mP3), Integers());
      if mP2 eq K!0 or mP3 eq K!0 then
        vprintf JacHypHeight: " P is torsion, so height is zero.\n";
        return RealField()!0;
      end if;
      flag := false; // indicates whether a table has been finished
      for i := 1  to #tables1 do
        p := tables1[i,1];
        v := Valuation(g, p);
        if v eq 0 then
          // table is complete; move it from tables1 to tables
          vprintf JacHypHeight, 2: "  p = %o: %o*P has epsilon_p = 0.\n", p, m;
          Append(~tables, tables1[i]);
          Undefine(~tables1, i);
          flag := true;
        elif P2s[1] mod p eq 0 and P2s[2] mod p eq 0 and P2s[3] mod p eq 0 then
          // 2mP is in kernel of reduction, can complete table
          vprintf JacHypHeight, 2: 
                  "  p = %o: 2*%o*P is in kernel of reduction.\n", p, m;
          table := tables1[i,2] cat [v];
          table := table cat [table[m-i+1] : i in [1..m-1]]; 
          Append(~tables, <p, table>);
          Undefine(~tables1, i);
          flag := true;
        elif P3s[1] mod p eq 0 and P3s[2] mod p eq 0 and P3s[3] mod p eq 0 then
          // (2m+1)P is in kernel of reduction, can complete table
          vprintf JacHypHeight, 2:
                  "  p = %o: (2*%o+1)*P is in kernel of reduction.\n", p, m;
          table := tables1[i,2] cat [v];
          table := table cat [table[m-i+2] : i in [1..m]]; 
          Append(~tables, <p, table>);
          Undefine(~tables1, i);
          flag := true;
        else
          // extend table
          Append(~tables1[i,2], v);
        end if;
      end for;
      if flag then
        tables1 := Setseq(Seqset(tables1)); // remove undefined entries
      end if;
      // printf "tables = %o\ntables1 = %o\n", tables, tables1;
    end while;
    if GetVerbose("JacHypHeight") ge 3 then
      print " Tables:";
      for entry in tables do
        printf "  p = %o --> %o\n", entry[1], entry[2];
      end for;
    end if;
    // Compute finite part
    sum := 0;
    for entry in tables do
      p := entry[1];
      table := entry[2];
      sum_p := 0;
      m_p := #table;
      r := Valuation(m_p, 2);
      for n := 0 to r-1 do
        sum_p +:= table[1 + (2^n mod m_p)]/4^(n+1);
      end for;
      n2_start := 2^r mod m_p;
      n2 := n2_start;
      c := 0;
      sum1 := 0;
      repeat
        sum1 +:= table[1 + (n2 mod m_p)]/4^c;
        c +:= 1;
        n2 := (2*n2) mod m_p;
      until n2 eq n2_start;
      // now c = ord(2) mod m_p/2^r
      sum_p := sum_p + 4^(-r-1)/(1 - 4^(-c))*sum1;
      vprintf JacHypHeight: 
              "  p = %o: contribution is %o*log(%o).\n", p, -sum_p, p;
      sum -:= sum_p*Log(p);
    end for;
    // compute infinite part
    if Precision gt 0 then
      Rs := RealField(Precision+2);
    else
      Rs := RealField(MyPrec(RealField())+2);
    end if;
    one := Rs!1;
    // Convert into (floating-point!) real numbers
    s := [one*t : t in P1s];
    // Normalize such that the sup-norm is 1
    norm := Max([Abs(t) : t in s]);
    for j := 1 to 4 do s[j] /:= norm; end for;
    // The following gives a slight speed improvement
    D := ChangeUniverse(D, ChangeRing(Parent(D[1]), Rs));
    D := [one*d : d in D];
    // The height (of P) is the naive height plus mu_infty(P) plus the finite 
    // part,
    // where mu_infty(Q) = sum_{n ge 0} eps_infty(2^n*Q)/4^(n+1)
    // where eps_infty(Q) is the local height constant at infinity at Q.
    ht := Log(norm);
    vprintf JacHypHeight: " Naive height = %o\n",ht;
    sum_inf := 0;
    pow4 := one;
    // Determine how many iterations are necessary
    prec := MyPrec(Rs);
    _, hc_inf := HeightConstant(Jacobian(K));
    bound := Ceiling((prec*Log(10) + Log(hc_inf))/Log(4));
    vprintf JacHypHeight, 2: " Current precision = %o decimal digits\n",prec-2;
    vprintf JacHypHeight, 2: " Bound for mu_infty = %o\n",hc_inf;
    vprintf JacHypHeight, 2: 
            "  ==> need %o iterations for infinite part.\n",bound;
    for n := 1 to bound do
      // double the point
      s := [Evaluate(D[j], s) : j in [1..4]];
      // keep it on K
      eqnIns:=Evaluate(eqn, [ Pol | s[1], s[2], s[3], x ]);
      if Degree(eqnIns) eq -1 then
        vprintf JacHypHeight, 2:
         " Multiple seems equal to 0, height must be 0\n.";
        return TR eq FldRat select RealField()!0 else 0;
      end if;
      // Michael sent a patch replacing
      // r := [ r[1] : r in Roots(eqnIns) ];
      // by
      // r := [ r[1] : r in Roots(eqnIns, ComplexField()) ];
      // This lead to other problems ... 
      // Patch by Steve:
      eqnIns /:= LeadingCoefficient(eqnIns); // Roots prefers monic (05-09, Steve)
      r := [ r[1] : r in Roots(eqnIns) ];
      if #r eq 0 then   
         // if there are no "real roots", 
         // then use the real part(s) of the complex roots
         r := [ Real(r[1]) : r in Roots(eqnIns, ComplexField(prec)) ];
      end if;
      if #r eq 1 then   
         s[4] := r[1];
      else 
         s[4] := Abs(s[4]-r[1]) lt Abs(s[4]-r[2]) select r[1] else r[2];
      end if;
      /*  old version
      case #[ rt : rt in r | IsReal(rt) ]:
        when 0: s[4] := Real(r[1]); // not so good... 
                vprintf JacHypHeight, 2:
                        "  Warning: Point left K (%o iterations).\n", n;
        when 1: s[4] := r[1];
        when 2: s[4] := Abs(s[4]-r[1]) lt Abs(s[4]-r[2]) select r[1] else r[2];
      end case;
      */
      // Normalize such that the sup-norm is 1
      norm := Max([Abs(t) : t in s]);
      // A safety measure:
      if norm eq 0 then
        print "CanonicalHeight: Precision loss! Result might not be accurate.";
        break;
      end if;
      for j := 1 to 4 do s[j] /:= norm; end for;
      // add eps_infty
      pow4 *:= 4;
      sum_inf +:= Log(norm) / pow4;
    end for;
    vprintf JacHypHeight: " infinite part = %o.\n", sum_inf;
    height := ht + sum_inf + sum;
    height := ((Precision gt 0) select RealField(Precision)
                            else RealField())!height;
    vprintf JacHypHeight: "height(P) = %o.\n", height;
    return height;
  elif TR eq FldFunRat then
    Pol := Integers(CoefficientRing(Parent(P)));
    P1s := ChangeUniverse(Eltseq(P), Pol);
    // Find the epsilon_p(n*P) for the bad primes
    P2s := [ Pol | Evaluate(D[j], P1s) : j in [1..4]];
    g := GCD(P2s);
    fact := Factorisation(g);
    bad := [ f[1] : f in fact ];
    vprintf JacHypHeight: " Bad primes: %o\n", bad;
    tables1 := [ <f[1], [0, f[2]]> : f in fact ];
    tables := [];
    m := 1;
    mP := P;
    mP1 := K!0;
    mP3 := PseudoAdd(K!P2s, P, P); // (2*m+1)*P
    // Substitute for Valuation
    val := function(pol, p)
             r := 0;
             while IsDivisibleBy(pol, p) do
               r +:= 1;
               pol := ExactQuotient(pol, p);
             end while;
             return r;
           end function; 
    while not IsEmpty(tables1) do
      if IsDivisibleBy(m,10) then
        vprintf JacHypHeight, 3: "  m = %o, naive height = %o\n",
                                 m, NaiveHeight(mP);
      end if;
      // compute next multiple
      // here, mP = m*P, mP1 = (m-1)*P
      Ptemp := PseudoAdd(mP, P, mP1); // compute (m+1)*P
      mP1 := mP;
      mP := Ptemp;
      m +:= 1;
      // If m*P = 0, P is torsion and has height zero.
      if mP eq K!0 then
        vprintf JacHypHeight:" %o*P = 0, so height is zero.\n", m;
        return 0;
      end if;
      P2s := [Pol | Evaluate(D[j], s) : j in [1..4]]
              where s := Eltseq(mP);
      g := GCD(P2s);
      P2s := [ ExactQuotient(a, g) : a in P2s];
      mP2 := K!P2s;
      mP3 := PseudoAdd(mP2, P, mP3); // new (2*m+1)*P
      P3s := ChangeUniverse(Eltseq(mP3), Pol);
      if mP2 eq K!0 or mP3 eq K!0 then
        vprintf JacHypHeight: " P is torsion, so height is zero.\n";
        return 0;
      end if;
      flag := false; // indicates whether a table has been finished
      for i := 1  to #tables1 do
        p := tables1[i,1];
        v := val(g, p);
        if v eq 0 then
          // table is complete; move it from tables1 to tables
          vprintf JacHypHeight, 2: "  p = %o: %o*P has epsilon_p = 0.\n", p, m;
          Append(~tables, tables1[i]);
          Undefine(~tables1, i);
          flag := true;
        elif IsDivisibleBy(P2s[1], p)
              and IsDivisibleBy(P2s[2], p)
              and IsDivisibleBy(P2s[3], p)
        then
          // 2mP is in kernel of reduction, can complete table
          vprintf JacHypHeight, 2: 
                  "  p = %o: 2*%o*P is in kernel of reduction.\n", p, m;
          table := tables1[i,2] cat [v];
          table := table cat [table[m-i+1] : i in [1..m-1]]; 
          Append(~tables, <p, table>);
          Undefine(~tables1, i);
          flag := true;
        elif IsDivisibleBy(P3s[1], p)
              and IsDivisibleBy(P3s[2], p)
              and IsDivisibleBy(P3s[3], p)
        then
          // (2m+1)P is in kernel of reduction, can complete table
          vprintf JacHypHeight, 2:
                  "  p = %o: (2*%o+1)*P is in kernel of reduction.\n", p, m;
          table := tables1[i,2] cat [v];
          table := table cat [table[m-i+2] : i in [1..m]]; 
          Append(~tables, <p, table>);
          Undefine(~tables1, i);
          flag := true;
        else
          // extend table
          Append(~tables1[i,2], v);
        end if;
      end for;
      if flag then
        tables1 := Setseq(Seqset(tables1)); // remove undefined entries
      end if;
      // printf "tables = %o\ntables1 = %o\n", tables, tables1;
    end while;
    if GetVerbose("JacHypHeight") ge 3 then
      print " Tables:";
      for entry in tables do
        printf "  p = %o --> %o\n", entry[1], entry[2];
      end for;
    end if;
    // Compute finite part
    sum := 0;
    for entry in tables do
      p := entry[1];
      table := entry[2];
      sum_p := 0;
      m_p := #table;
      r := Valuation(m_p, 2);
      for n := 0 to r-1 do
        sum_p +:= table[1 + (2^n mod m_p)]/4^(n+1);
      end for;
      n2_start := 2^r mod m_p;
      n2 := n2_start;
      c := 0;
      sum1 := 0;
      repeat
        sum1 +:= table[1 + (n2 mod m_p)]/4^c;
        c +:= 1;
        n2 := (2*n2) mod m_p;
      until n2 eq n2_start;
      // now c = ord(2) mod m_p/2^r
      sum_p := sum_p + 4^(-r-1)/(1 - 4^(-c))*sum1;
      sum_p *:= Degree(p);
      vprintf JacHypHeight: 
              "  p = %o: contribution is %o.\n", p, -sum_p;
      sum -:= sum_p;
    end for;
    vprintf JacHypHeight: "  Contribution of finite places is %o.\n", sum;
    // compute infinite part
    // change model to make it integral at infinity
    d := Max([Degree(c) : c in Coefficients(f)]);
    if IsOdd(d) then d +:= 1; end if;
    f1 := Parent(f)![ R!Pol![ Coefficient(Numerator(c), d-i) : i in [0..d] ]
                       : c in Coefficients(f) ];
    C1 := HyperellipticCurve(f1);
    J1 := Jacobian(C1);
    K1 := KummerSurface(J1);
    oldNaive := Max([Degree(c) : c in Eltseq(P) | c ne 0]);
    Psnew := [ Evaluate(P[1],1/t), Evaluate(P[2],1/t), Evaluate(P[3],1/t),
               t^d*Evaluate(P[4], 1/t) ] where t := R.1;
    newNaive := Max([Degree(s[i]) : i in [1..3] | s[i] ne 0]
                      cat (s[4] ne 0 select [-d+Degree(s[4])] else []))
                 where s := Eltseq(P);
    dif := newNaive - oldNaive;
    P1 := K1!Psnew;
    assert TR eq FldFunRat;
    pl0 := MakePlaceFunRatElt(R.1);
    if not IspMinimalfunction(C1, pl0) then
      vprintf JacHypHeight, 2: "  scaled curve is not minimal at infinity.\n";
      C2, tr2 := pMinimalWeierstrassModelfunction(C1, pl0);
      vprintf JacHypHeight, 3: "  minimal model at t = 0 (after t -> 1/t):\n";
      vprintf JacHypHeight, 3: "%o\n", C2;
//      mat, e := Eltseq(tr2);
//      ma,mb,mc,md := Explode(mat);
      d1,d2,d3 := Explode(DefiningPolynomials(tr2));
      P3 := Parent(d1);
      e := MonomialCoefficient(d2, P3.2);
      ma := MonomialCoefficient(d1, P3.1);
      mb := MonomialCoefficient(d1, P3.3);
      mc := MonomialCoefficient(d3, P3.1);
      md := MonomialCoefficient(d3, P3.3);

      J2 := Jacobian(C2);
      K2 := KummerSurface(J2);
      Pnew := K2!(Evaluate(tr2,Points(J1, P1)[1]));
      det := ma*md-mb*mc;
      Pn123 := [(md^2*P1[1] + mc*md*P1[2] + mc^2*P1[3])/det,
                (2*mb*md*P1[1] + (ma*md+mb*mc)*P1[2] + 2*ma*mc*P1[3])/det,
                (mb^2*P1[1] + ma*mb*P1[2] + ma^2*P1[3])/det];
      assert Pnew in Points(K2, Pn123);
      i := 1; while Pn123[i] eq 0 do i +:= 1; end while;
      dif0 := -Valuation(Pn123[i], pl0) + Valuation(Pnew[i], pl0)
               + 2*Valuation(e, pl0) - 3*Valuation(det, pl0);
      vprintf JacHypHeight, 3: "  additional shift = %o\n", dif0;
      dif +:= dif0;
      K1 := K2;
      P1 := Pnew;
      vprintf JacHypHeight, 3: "  new point is %o\n", P1;
    end if;
    D1 := K1`Delta;
    tab := [0];
    P1s := ChangeUniverse(Eltseq(P1), Pol);
    // Find the epsilon_p(n*P) for the bad primes
    P2s := [ Pol | Evaluate(D1[j], P1s) : j in [1..4]];
    g := GCD(P2s);
    m := 1;
    mP := P1;
    mP1 := K1!0;
    mP3 := PseudoAdd(K1!P2s, P1, P1); // (2*m+1)*P
    v := val(g, Pol.1);
    while v ne 0 do
      if IsDivisibleBy(m,10) then
        vprintf JacHypHeight, 3: "  m = %o, naive height = %o\n",
                                 m, NaiveHeight(mP);
      end if;
      Append(~tab, v);
      // compute next multiple
      // here, mP = m*P, mP1 = (m-1)*P
      Ptemp := PseudoAdd(mP, P1, mP1); // compute (m+1)*P
      mP1 := mP;
      mP := Ptemp;
      m +:= 1;
      // If m*P = 0, P is torsion and has height zero.
      if mP eq K1!0 then
        vprintf JacHypHeight:" %o*P = 0, so height is zero.\n", m;
        return 0;
      end if;
      P2s := [Pol | Evaluate(D1[j], s) : j in [1..4]]
              where s := Eltseq(mP);
      g := GCD(P2s);
      P2s := [ ExactQuotient(a, g) : a in P2s];
      mP2 := K1!P2s;
      mP3 := PseudoAdd(mP2, P1, mP3); // new (2*m+1)*P
      P3s := ChangeUniverse(Eltseq(mP3), Pol);
      if mP2 eq K1!0 or mP3 eq K1!0 then
        vprintf JacHypHeight: " P is torsion, so height is zero.\n";
        return 0;
      end if;
      v := val(g, Pol.1);
      if v eq 0 then
        // table is complete
        vprintf JacHypHeight, 2: "  p = inf: %o*P has epsilon_p = 0.\n", m;
      elif IsDivisibleBy(P2s[1], Pol.1)
            and IsDivisibleBy(P2s[2], Pol.1)
            and IsDivisibleBy(P2s[3], Pol.1)
      then
        // 2mP is in kernel of reduction, can complete table
        vprintf JacHypHeight, 2: 
                "  p = inf: 2*%o*P is in kernel of reduction.\n", m;
        tab := tab cat [v];
        tab := tab cat [tab[m-i+1] : i in [1..m-1]];
        v := 0;
      elif IsDivisibleBy(P3s[1], p)
            and IsDivisibleBy(P3s[2], p)
            and IsDivisibleBy(P3s[3], p)
      then
        // (2m+1)P is in kernel of reduction, can complete table
        vprintf JacHypHeight, 2:
                "  p = inf: (2*%o+1)*P is in kernel of reduction.\n", m;
        tab := tab cat [v];
        tab := tab cat [tab[m-i+2] : i in [1..m]]; 
        v := 0;
      end if;
    end while;
    vprintf JacHypHeight, 3: " Table: %o\n", tab;
    // Compute infinite part
    sum_inf := 0;
    m_inf := #tab;
    r := Valuation(m_inf, 2);
    for n := 0 to r-1 do
      sum_inf +:= tab[1 + (2^n mod m_inf)]/4^(n+1);
    end for;
    n2_start := 2^r mod m_inf;
    n2 := n2_start;
    c := 0;
    sum1 := 0;
    repeat
      sum1 +:= tab[1 + (n2 mod m_inf)]/4^c;
      c +:= 1;
      n2 := (2*n2) mod m_inf;
    until n2 eq n2_start;
    // now c = ord(2) mod m_inf/2^r
    sum_inf +:= 4^(-r-1)/(1 - 4^(-c))*sum1;
    sum_inf := d + dif - sum_inf;
    assert Type(sum_inf) in {RngIntElt, FldRatElt};
    vprintf JacHypHeight: " infinite part = %o.\n", sum_inf;
    ht := NaiveHeight(P);
    vprintf JacHypHeight: " naive height = %o.\n", ht;
    height := ht + sum_inf + sum;
    vprintf JacHypHeight: "height(P) = %o.\n", height;
    return height;  
  else
    error "Problem in CanonicalHeight(SrfKumPt)!!";
  end if;
end intrinsic;


//----------------------------------------------------------------------
// Compute Local Height.
//----------------------------------------------------------------------

// Try to be fairly general. We need something like a place
// (so far only for function fields of one variable and not terribly
// efficient -- should be there also for k(t) and number fields).
// We need:
// + the (additive) valuation function on the base field

intrinsic LocalHeight(K::SrfKum, s::SeqEnum, val::UserProgram) -> FldRatElt
{For internal use -- the local height of a point on a Kummer surface K,
 at the valuation given by the given function 'val'.}
    vprintf JacHypHeight, 1: "Local height of %o\n", s;
    pt := K!s;
    vprintf JacHypHeight, 1: "  normalised: %o\n", pt;
    i := 1;
    while s[i] eq 0 do i +:= 1; end while;
    dv := val(s[i]) - val(pt[i]); // correction term
    vprintf JacHypHeight, 1: "  correction term: %o.\n", -dv;
    return LocalHeight(pt, val) - dv;
end intrinsic;

intrinsic LocalHeight(pt::SrfKumPt, val::UserProgram) -> FldRatElt
{"} // "
    vprintf JacHypHeight, 1: "Local height of %o\n", pt;
    K := Parent(pt);
    ds := K`Delta;
    J := Jacobian(K);
    C := Curve(J);
    f := HyperellipticPolynomials(C);
    require forall{c : c in Coefficients(f) | c eq 0 or val(c) ge 0}:
            "Curve must be integral.";
    s := Eltseq(pt);
    naive := -Min([val(c) : c in s | c ne 0]);
    vprintf JacHypHeight: " Naive local height is %o.\n", naive;
    // initialise
    tab := [0];
    P1s := s;
    // Find the epsilon_p(n*P) for the bad primes
    P2s := [ Evaluate(ds[j], P1s) : j in [1..4]];
    v := Min([val(c) : c in P2s | c ne 0]);
    m := 1;
    mP := pt;
    mP1 := K!0;
    mP3 := PseudoAdd(K!P2s, pt, pt); // (2*m+1)*P
    while v ne 0 do
      if IsDivisibleBy(m,10) then
        vprintf JacHypHeight, 3: "  m = %o\n", m;
      end if;
      Append(~tab, v);
      // compute next multiple
      // here, mP = m*P, mP1 = (m-1)*P
      Ptemp := PseudoAdd(mP, pt, mP1); // compute (m+1)*P
      mP1 := mP;
      mP := Ptemp;
      m +:= 1;
      P2s := [Evaluate(ds[j], s) : j in [1..4]]
              where s := Eltseq(mP);
      v := Min([val(c) : c in P2s | c ne 0]);
      mP2 := K!P2s;
      P2s := Eltseq(mP2);
      mP3 := PseudoAdd(mP2, pt, mP3); // new (2*m+1)*P
      P3s := Eltseq(mP3);
      if v eq 0 then
        // table is complete
        vprintf JacHypHeight, 2: "  %o*P has epsilon_v = 0.\n", m;
      elif P2s[4] ne 0
            and (((P2s[1] eq 0 or val(P2s[1]) gt v4)
                   and (P2s[2] eq 0 or val(P2s[2]) gt v4)
                   and (P2s[3] eq 0 or val(P2s[3]) gt v4))
                   where v4 := val(P2s[4]))
      then
        // 2mP is in kernel of reduction, can complete table
        vprintf JacHypHeight, 2: 
                "  2*%o*P is in kernel of reduction.\n", m;
        tab := tab cat [v];
        tab := tab cat [tab[m-i+1] : i in [1..m-1]];
        v := 0;
      elif  P3s[4] ne 0
            and (((P3s[1] eq 0 or val(P3s[1]) gt v4)
                   and (P3s[2] eq 0 or val(P3s[2]) gt v4)
                   and (P3s[3] eq 0 or val(P3s[3]) gt v4))
                   where v4 := val(P3s[4]))
      then
        // (2m+1)P is in kernel of reduction, can complete table
        vprintf JacHypHeight, 2:
                "  (2*%o+1)*P is in kernel of reduction.\n", m;
        tab := tab cat [v];
        tab := tab cat [tab[m-i+2] : i in [1..m]]; 
        v := 0;
      end if;
    end while;
    vprintf JacHypHeight, 3: " Table: %o\n", tab;
    // Compute epsilon part
    sum := 0;
    m := #tab;
    r := Valuation(m, 2);
    for n := 0 to r-1 do
      sum +:= tab[1 + (2^n mod m)]/4^(n+1);
    end for;
    n2_start := 2^r mod m;
    n2 := n2_start;
    c := 0;
    sum1 := 0;
    repeat
      sum1 +:= tab[1 + (n2 mod m)]/4^c;
      c +:= 1;
      n2 := (2*n2) mod m;
    until n2 eq n2_start;
    // now c = ord(2) mod m_inf/2^r
    sum +:= 4^(-r-1)/(1 - 4^(-c))*sum1;
    sum := -sum;
    vprintf JacHypHeight: "  epsilon part = %o.\n", sum;
    // discriminant part
    vdisc := val(Discriminant(C));
    dp := vdisc/10;
    vprintf JacHypHeight: "  discriminant part = %o.\n", dp;
    loc := naive + sum + dp;
    vprintf JacHypHeight: " local height = %o.\n", loc;
    return loc;
end intrinsic;
