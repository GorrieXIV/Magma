freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!

/*******************************************
 * Hyperelliptic/chabauty.m                *
 *                                         *
 * Apply Chabuty's method to find all      *
 * rational points on a curve              *
 *                                         *
 * Michael Stoll                           *
 *                                         *
 * started 19-Mar-1999                     *
 *******************************************/

/*------------------------------------------------------------------

  CHANGES
  
  M. Stoll, 2000-08-11
  
    New verbose flag JacHypChabauty
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 HyperellipticCurve & Curve fix

   2003-04: Nils
   Various changes to get the thing to work with the new locals.

   2007_04: Steve
   Increase precision as much as necessary before doing PseudoAddMultiple
   to avoid the answer being congruent to (0:0:0:1), as this leads to 
   an attempt to do O(p^v)/O(p^v) in 'extract', and the division now 
   throws a runtime error. 
   The scope of the precision increase is just the calls to 
   PseudoAddMultiple and 'extract'. There are two separate occurences.

   Also post-process the final result to avoid the same (or overlapping)
   congruence classes being listed repeatedly, which can occur if there
   are several 'emergency stops' in these congruence classes.

  ------------------------------------------------------------------*/

// Declarations

declare verbose JacHypChabauty, 3;

// All this is for curves of genus 2 with Mordell-Weil rank at most 1.

intrinsic Chabauty0(J::JacHyp) -> SetIndx
   {Returns the rational points on the curve of which J is the 
   Jacobian, under the condition that J has Mordell-Weil rank zero.}

   G, m := TorsionSubgroup(J);
   K := KummerSurface(J);
   C := Curve(J);
   TK := { K | K!m(g) : g in G | g ne G!0 };
   f := HyperellipticPolynomials(C);
   points := {@ C | C![r[1],0] : r in Roots(f) @};
   points join:= PointsAtInfinity(C);
   for t in TK do
      if t[2]^2 eq 4*t[1]*t[3] and t[1] ne 0 then
         points join:= Points(C, t[2]/2/t[1]);
      end if;
   end for;
   return points;
end intrinsic;

intrinsic Chabauty(ptJ::JacHypPt, p::RngIntElt : Precision := 5) -> SetIndx
    {Given a point on the Jacobian of a hyperelliptic curve C,
    returns an indexed set of triples <x,z,v,k> such that there are 
    at most k pairs of rational points (X:Y:Z) on C with 
    (X:Z) congruent to (x:z) mod p^v, and such that there are no
    other rational points on C except the hyperelliptic points.
    J(Q) must have rank 1, and ptJ must have infinite order in J(Q).
    C must be in the simplified form  y^2 = f(x).}

//  Applies Chabauty's method to bound the number of rational points on
//  the curve C (where C = Curve(Parent(P))). P should be a generator
//  of J(Q) (J = Jacobian(C)) modulo torsion.
//  p is a prime number such that C has good reduction at p, and C must
//  be in simplified form  y^2 = f(x). The function returns an indexed set
//  of triples <x, z, v, k> such that there are at most k pairs of rational
//  points on C with x-coordinate mapping to x/z mod p^v, and such that
//  there are no non-Weierstrass points outside the union of these classes.
//  The Precision gives a lower bound for v above. }

    vprintf JacHypChabauty: "Chabauty:\n";
    // The usual checks
    J := Parent(ptJ);
    C := Curve(J);
    vprintf JacHypChabauty: "  Curve = %o\n", C;
    vprintf JacHypChabauty: "  Generator of J(Q)/Tors: %o.\n", ptJ;
    vprintf JacHypChabauty: "  Prime = %o.\n", p;
    require IsPrime(p): "p must be a prime number";
    require not IsDivisibleBy(Integers()!Discriminant(C), p):
            "The curve must have good reduction at p.";
    require Order(ptJ) eq 0: "ptJ must be of infinite order.";
    // 
    K := KummerSurface(J); // takes care of a few more checks
    Jp := BaseExtend(J, GF(p));
    Kp := KummerSurface(Jp);
    TG, Tmap := TorsionSubgroup(J);
    vprintf JacHypChabauty: " Invariants of torsion subgroup: %o.\n", Invariants(TG);
    T := { Tmap(t) : t in TG }; // the torsion points on J
    T1 := { Points(J, K!t)[1] : t in T }; // representatives mod +-1
    n := Order(Jp!ptJ); ptJ1 := ptJ;
    // Find generator of least possible order mod p
    for t in T do
      n1 := Order(Jp!(ptJ+t));
      if n1 lt n then ptJ1 := ptJ+t; n := n1; end if;
    end for;
    ptJ := ptJ1;
    ptK := K!ptJ;
    ptJp := Jp!ptJ;
    // E := n*ptJ; // This is in the kernel of reduction
    vprintf JacHypChabauty: " Generator %o has order %o mod %o.\n", ptJ, n, p;
    prec := Precision - 5;
    repeat
      prec +:= 5;
      W := pAdicField(p, prec); KW := BaseExtend(K, W);
      EW := n*KW!ptK;
      v := Min([Valuation(EW[j]) : j in [1,2,3]]);
    until v lt prec and IsEven(v);
    v := ExactQuotient(v, 2);
    vprintf JacHypChabauty: " Valuation of point in kernel of reduction = %o.\n", v;
    // Define function that deals with one point
    function OnePoint(n, v, t, k)
      // n : n*ptJ point in kernel of reduction, of valuation v
      // t = torsion point on J
      // k : look at point pt = t + k*ptJ
      vprintf JacHypChabauty: "  OnePoint(%o, %o, %o):\n", n, t, k;
      tK := K!t; ptK := K!ptJ; tmpK := K!(t - ptJ);
      // This function takes a point on the Kummer surface and a precision
      // and extracts the x-coordinate of the point on the curve (where
      // the Kummer point corresponds to twice the point on the curve
      // minus a canonical divisor).
      function extract(pt, pr)
        if GF(p)!Integers()!pt[1] ne 0 then
          // finite point mod p --> pt[1] = 1
          zp1 := 1;
          xp1 := pt[2]/2;
        elif GF(p)!Integers()!pt[3] ne 0 then
          // infinite Point mod p --> pt[3] = 1
          zp1 := pt[2]/2;
          xp1 := 1;
        else
          w := Min(Valuation(pt[1]), Valuation(pt[3]));
          if Valuation(pt[1]) eq w then
            zp1 := 1;
            xp1 := pt[2]/2/pt[1];
          else
            zp1 := pt[2]/2/pt[3];
            xp1 := 1;
          end if;
          pr -:= w;
        end if;
        return <Integers()!xp1, Integers()!zp1, pr>;
      end function;
      // function solve finds the (unique) p-adically integral zero m of the
      // power series with coefficients coeffs, then it computes 
      // pt + m^(1/exp)*E and extracts the point on C.
      function solve(coeffs, prec, min, exp)
        R := pAdicRing(p:Precision:= prec-min);
        pol := PolynomialRing(R)!
                 [Integers() | c/p^min : c in coeffs];
        pol := (-1 div Coefficient(pol,1))*pol + Parent(pol).1;
        m := R!0;
        for j := 1 to prec-min do
          m := Evaluate(pol, m);
        end for;
        if exp eq 2 then m := Sqrt(m); end if;
        m := Integers()!m;
       // Steve changed this
       /*
        pr := Min(prec, v*(prec-min));
        R := pAdicField(p, pr);
        KR := BaseExtend(K, R);
        pt := PseudoAddMultiple(KR!tK, KR!ptK, KR!tmpK, k + m*n);
        return extract(pt, pr);
       */
        myprec := Min(prec, v*(prec-min));
        while true do 
          R := pAdicField(p, myprec); KR := BaseExtend(K, R);
          pt := PseudoAddMultiple(KR!tK, KR!ptK, KR!tmpK, k + m*n);
          pt_ok := not &and[ IsWeaklyZero(pt[i]) : i in [1,3] ];
          if pt_ok then break; end if;
          myprec +:= 10;
        end while;
        return extract(pt, myprec);
      end function;
      // Find the power series to sufficient precision in order to
      // determine the relevant part.
      prec := Precision - 5;
      repeat
        prec +:= 5;
        pws := FindPowerSeriesForChabauty(p, [t, ptJ], n, k, prec, v);
        coeffs := Eltseq(pws);
        min, pos := Min(Reverse([ Valuation(c) : c in coeffs ]));
      until min lt prec;
      pos := #coeffs - pos;
      vprintf JacHypChabauty: "Power series coeffs are %o.\n", coeffs;
      vprintf JacHypChabauty: "Relevant part has degree %o.\n", pos;
      // pos is the degree of the relevant part.
      if prec ge 20+Precision then
        // emergency stop: Some degeneracy seems to be present
        // look at t + k*ptJ mod p^v; this must be ofthe required form
        vprintf JacHypChabauty: "Precision has grown too large: " * 
                                "some degeneracy seems to be present.\n";
       // Steve changed this
       /*
        R := pAdicField(p, v); KR := BaseExtend(K, R);
        pt := PseudoAddMultiple(KR!tK, KR!ptK, KR!tmpK, k);
        res := extract(pt, v);
       */
       myprec := v;
       while true do
         R := pAdicField(p, myprec); KR := BaseExtend(K, R);
         pt := PseudoAddMultiple(KR!tK, KR!ptK, KR!tmpK, k);
         pt_ok := not &and[ IsWeaklyZero(pt[i]) : i in [1,3] ];
         if pt_ok then break; end if;
         myprec +:= 10; 
       end while;
       res := extract(pt, myprec);
        anz := pos; 
        if t eq J!0 and (k eq 0 or 2*k eq n) then
          anz := (pos - 6) div 2;
        elif 2*t eq J!0 and (k eq 0 or 2*k eq n) then
          anz := pos div 2;
        end if;
        return {@ Append(res, anz) @};
      end if;
      if pos eq 0 then
        // no solution
        vprintf JacHypChabauty: "No solution.\n";
        return {@ @};
      elif pos eq 1 then
        // unique solution
        sol := solve(coeffs, prec, min, 1);
        vprintf JacHypChabauty: "Unique solution: %o.\n", sol;
        return {@ Append(sol, 1) @};
      elif t eq J!0 and k eq 0 and pos le 8 then
        if pos eq 6 then
          vprintf JacHypChabauty: "No solution.\n";
          return {@ @};
        else
          // if solution, then unique (mod sign).
          error if not forall{i : i in [1..pos by 2]
                                  | Valuation(coeffs[i+1]) ge prec},
                "Something is seriously wrong in chabauty.m, line 161!";
          if IsSquare(-coeffs[7]/coeffs[9]) then
            sol := solve([coeffs[i+1+6] : i in [0..#coeffs-7 by 2]], 
                         prec, min, 2);
            vprintf JacHypChabauty: "Unique solution: %o.\n", sol;
            return {@ Append(sol, 1) @};
          else
            vprintf JacHypChabauty: "No solution.\n";
            return {@ @};
          end if;
        end if;
      elif 2*t eq J!0 and k eq 0 and pos le 2 then
        // if solution, then unique (mod sign).
        error if not forall{i : i in [1..pos by 2]
                                | Valuation(coeffs[i+1]) ge prec},
              "Something is seriously wrong in chabauty.m, line 176!";
        if IsSquare(-coeffs[1]/coeffs[3]) then
          sol := solve([coeffs[i+1] : i in [0..#coeffs-1 by 2]], prec, min, 2);
          vprintf JacHypChabauty: "Unique solution: %o.\n", sol;
          return {@ Append(sol, 1) @};
        else
          vprintf JacHypChabauty: "No solution.\n";
          return {@ @};
        end if;
      else
        // possibly multiple solutions
        pol := PolynomialRing(GF(p))!
                [Integers()|c/p^min : c in coeffs[1..pos+1]];
        roots := Roots(pol);
        vprintf JacHypChabauty: "Several solutions possible.\n";
        vprintf JacHypChabauty: "Polynomial = %o,\n", pol;
        vprintf JacHypChabauty: " with roots: %o.\n", [r[1] : r in roots];
        if #roots eq 0 then
          return {@ @};
        else
          return &join[OnePoint(p*n, v+1, t, k+n*Integers()!r[1]): r in roots];
        end if;
      end if;
    end function;
    // Loop through torsion points
    result := {@ @};
    for t in T do
      vprintf JacHypChabauty: "Looking at torsion point t = %o...\n", t;
      // loop through multiples of ptJ
      for k := t in T1 select 0 else 1
          to IsEven(n) and t in T1 select n div 2 else (n-1) div 2 do
        if kpt[2]^2 eq 4*kpt[1]*kpt[3] where kpt := Kp!(Jp!t + k*ptJp)
        then
          vprintf JacHypChabauty: "t + %o*gen satisfies condition mod %o.\n", k, p;
          result join:= OnePoint(n, v, t, k);
        end if;
      end for;
    end for;

   // Deal with repeated points that sometimes arise from 
   // too many 'emergency stops'  (Steve added this bit)
   ans := {@ @};
   for tup in result do 
     if exists{tup1 : tup1 in ans | tup1[1] eq tup[1] and tup1[2] eq tup[2]} then
        continue; end if;
     tups := {tup1 : tup1 in result | tup1[1] eq tup[1] and tup1[2] eq tup[2]};
     vv := Min([ tup[3] : tup1 in tups ]);
     kk := Max([ tup[4] : tup1 in tups ]);
     Include( ~ans, <tup[1],tup[2],vv,kk> );
   end for;
   return ans;
end intrinsic;


intrinsic FindPowerSeries(p::RngIntElt, f::UserProgram, n::RngIntElt,
                          k::RngIntElt, d::RngElt)
                           -> RngSerPowElt
{ Given a function f such that f(z, n) = F(z) + O(p^n), where F is a
  power series with coefficients in the p-adic integers:
  F(z) = f_0 + f_1 z + f_2 z^2 + ...  with Valuation(f_m) >= d*m,
  where d is non-negative, this function finds the coefficients
  f_m up to O(p^n), for m up to k. }
    vprintf JacHypChabauty: "FindPowerSeries(%o, <func>, %o, %o, %o):\n", p, n, k, d;
    require IsPrime(p): "p must be a prime number.";
    require n ge 0 and k ge 0: "n and k must be non-negative.";
    d := Rationals()!d;
    require d gt 0: "d must be positive.";
    // Find N such that computations up to O(p^N) are sufficient.
    if d le 1/2 or (2*d - 1)*(k + 1) le n then
      N := Ceiling((k/2+1)*(n - k*(d-1/2)));
    else
      N := Ceiling((n - 2*d + 1)^2/(2*(2*d - 1)));
    end if;
    // This is rather primitive...
    N := Max(N, n);
    vmax := 0;
    vs := [];
    for m := 1 to k do
      v := Max(0,Ceiling(N/(m+2) - m/4 - d));
      vmax := Max(v + (k-1) div 2, vmax);
      Append(~vs, v);
      N := Max(N, n + m*v + Floor((m-1)^2/4));
    end for;
    if p eq 2 then N +:= 1; end if;
    vprintf JacHypChabauty: " Using precision %o.\n", N;
    // Now compute even and odd parts F_+(p^m), F_(p^m) for m up to vmax
    evens := [];
    odds := [];
    F0 := f(0, N);
    pm := 1;
    for m := 0 to vmax do
      Fplus := f(pm, N); Fminus := f(-pm, N);
      Append(~evens, ((Fplus + Fminus)/2 - F0)/pm^2);
      Append(~odds, (Fplus - Fminus)/2/pm);
      pm *:= p;
    end for;
    // Now find the coeffs recursively.
    R := pAdicField(p, n);
    zero := O(R.1^n);
    coeffs := [R | zero + F0];
    c := 2; a := 1; 
    for m := 1 to k do
      if IsOdd(m) then
        Append(~coeffs, zero + odds[vs[m]+1]/a);
        odds := [ (odds[i+1] - odds[i])/p^(2*i-2) : i in [1..#odds-1] ];
      else
        Append(~coeffs, zero + evens[vs[m]+1]/a);
        evens := [ (evens[i+1] - evens[i])/p^(2*i-2) : i in [1..#evens-1] ];
        a *:= (p^c - 1);
        c +:= 2;
      end if;
    end for;
    // Build the series
    P := PowerSeriesRing(R);
    return P!coeffs + O(P.1^(k+1));
end intrinsic;

intrinsic FindPowerSeriesForChabauty(p::RngIntElt, pts::[JacHypPt],
                                     M::RngIntElt, m::RngIntElt, 
                                     n::RngIntElt, v::RngElt)
                                      -> RngSerPowElt
{ For internal use only. }
    // Find the power series that, when evaluated at z in Z_p, gives
    // kpt[2]^2 - 4*kpt[1]*kpt[3], where kpt is the point on the
    // Kummer surface corresponding to pts[1] + (m + M*z)*pts[2].
    // The result is up to O(p^n). The point M*pts[2] must be in the
    // kernel of reduction; it has valuation v.
    vprintf JacHypChabauty: "   FindPowerSeries(%o, %o, %o, %o, %o, %o, %o):\n",
                   p, pts[1], pts[2], M, m, n, v;
    d := v - 1/(p-1);       // valuation of rth coeff will be gt d*r
    k := Ceiling(n/d) - 1;  // bound for r s.t. rth coeff is O(p^n) for r gt k
    // Find N such that computations up to O(p^N) are sufficient.
    if d le 1/2 or (2*d - 1)*(k + 1) le n then
      N := Ceiling((k/2+1)*(n - k*(d-1/2)));
    else
      N := Ceiling((n - 2*d + 1)^2/(2*(2*d - 1)));
    end if;
    // This is rather primitive...
    N := Max(N, n);
    vmax := 0;
    vs := [];
    for m := 1 to k do
      v := Max(0,Ceiling(N/(m+2) - m/4 - d));
      vmax := Max(v + (k-1) div 2, vmax);
      Append(~vs, v);
      N := Max(N, n + m*v + Floor((m-1)^2/4));
    end for;
    vprintf JacHypChabauty: " Using precision %o.\n", N;
    // Now compute even and odd parts F_+(p^r), F_(p^r) for r up to vmax
    R := pAdicField(p, N);
    J := Universe(pts);
    K := KummerSurface(J);
    KR := BaseExtend(K, R);
    kpt1 := KR!K!pts[1];
    kpt2 := KR!K!pts[2];
    kpt3 := KR!K!(pts[1]-pts[2]);
    kpt4 := KR!K!(pts[1]+pts[2]);
    // Find images of pts[1] + m*pts[2], M*pts[2], pts[1] + (m+-M)*pts[2]
    // on KR.
    Kpt1 := PseudoAddMultiple(kpt1, kpt2, kpt3, m);
    Kpt2 := M*kpt2;
    Kpt3 := PseudoAddMultiple(kpt1, kpt2, kpt3, m-M);
    Kpt4 := PseudoAdd(Kpt1, Kpt2, Kpt3);
    // This is the quadratic form on points on K.
    quad := func< pt | pt[2]^2 - 4*pt[1]*pt[3] >;
    // Collect values at powers of p for the even and odd parts of the power
    // series.
    evens := [];
    odds := [];
    F0 := quad(Kpt1);  // The constant term.
    pm := 1;
    for r := 0 to vmax do
      Fplus := quad(Kpt4); Fminus := quad(Kpt3);
      Append(~evens, ((Fplus + Fminus)/2 - F0)/pm^2);
      Append(~odds, (Fplus - Fminus)/2/pm);
      pm *:= p;
      if r lt vmax then
        Kpt3n := PseudoAddMultiple(Kpt1, Kpt2, Kpt4, p);
        Kpt4 := PseudoAddMultiple(Kpt1, Kpt2, Kpt3, p);
        Kpt2 := p*Kpt2;
        Kpt3 := Kpt3n;
      end if;
    end for;
    // Now find the coeffs recursively.
    R := pAdicField(p, n);
    zero := O(UniformizingElement(R)^n);
    coeffs := [R | zero + R!F0];
    c := 2; a := 1; 
    for r := 1 to k do
      if IsOdd(r) then
        Append(~coeffs, zero + R!(odds[vs[r]+1]/a));
        odds := [ (odds[i+1] - odds[i])/p^(2*i-2) : i in [1..#odds-1] ];
      else
        Append(~coeffs, zero + R!(evens[vs[r]+1]/a));
        evens := [ (evens[i+1] - evens[i])/p^(2*i-2) : i in [1..#evens-1] ];
        a *:= (p^c - 1);
        c +:= 2;
      end if;
    end for;
    // Build the series
    P := PowerSeriesRing(R);
    return P!coeffs + O(P.1^(k+1));
end intrinsic;

