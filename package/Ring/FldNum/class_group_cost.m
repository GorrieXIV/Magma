freeze;

///////////////////////////////////////////////////////////////////
//                                                                 
// Heuristic formulae for cost of relation search in ClassGroup
// 
// Steve Donnelly, August 2012 (rewritten)
//
// Still a lot more refinements to be made...
//                                                                 
///////////////////////////////////////////////////////////////////

declare verbose ClassGroupExpected, 3;

// Volume of the hyperbolic region inside standard box in R^n, 
// consisting of (x_1, ..., x_n) in R^n with 0 <= x_i <= 1, 
// and product x_1 ... x_n <= b.  
// Here b must satisfy 0 < b < 1.

function hvol(n, b)
  l := Log(b);
  s := 1;
  for k := 1 to n-1 do 
    s +:= (-l)^k / Factorial(k);
  end for;
  return b * s;
end function;


// For a field of degree d and discriminant D, this is a heuristic formula 
// for the expected number of tries needed to find each relation.

// We assume we are dealing with random elements in a region
// such that their norm is guaranteed to be bounded by sqrtD.
// We infer the distribution of the norms, and then integrate 
// this against the probability of smoothness.

function class_group_expected_tries(d, D, bound)

  assert bound ge 1;

  R := RealField(10);
  sqrtD := R! Sqrt(Abs(D));
  bound := R! bound;
  logbound := Log(bound);

  if d le 1 or bound ge sqrtD then
    return R! 1;
  end if;

  // Dickman is too slow for large values, and
  // DickmanRho(15.0) = 7.6 x 10^-20
  // so we cut off the sum at 15

  function riemann_summands(n, l, u)
    f := R! (u/l)^(1/n);    // increment by factor f
    x := R! l;
    lf := Log(f)/logbound;
    lx := Log(x)/logbound;
    V0 := hvol(d, x/sqrtD);
    X := [R| ];
    S := [R| ];

    vprintf ClassGroupExpected, 3 :
      "n = %o, l = %o, u = %o\n", n, l, u;

    for i := 1 to n do
      x *:= f;
      lx +:= lf;
      if lx gt 15 then 
         break;
      end if;
      V := hvol(d, x/sqrtD);
      v := V - V0;
      V0 := V;
      s := DickmanRho(lx);
      Append(~X, x);
      Append(~S, s*v);
      vprintf ClassGroupExpected, 3 : 
        "x = %o, V = %o, v = %o, s = %o, sv = %o\n", x, V, v, s, s*v;
    end for;

    return X, S;
  end function;

  terms := 100;
  xmin  := R! 1/2; // must be < bound
  xmax  := sqrtD;

  // Find the relevant range, by sampling only a few values

  X, S := riemann_summands(10, xmin, xmax);

  smax, i := Max(S);
  s := 10^-4 * smax;
  i0 := Min([j : j in [1..i] | S[j] ge s]);
  i1 := Max([j : j in [i..#S] | S[j] ge s]);
  x0 := i0 eq 1 select xmin else X[i0-1]; 
  x1 := X[i1]; 

  // Sum over [x0 .. x1] with a reasonable number of values,
  // check that the central summands are reasonably equal
  r := 0.8;
  w := 5;

  while true do
     _, S := riemann_summands(terms, x0, x1);
     smax, i := Max(S[2..#S]);
     i +:= 1;
     // &+S, i, S[i], S[Max(1,i-w)], S[Min(#S,i+w)];

     if i-w le 0 and x0 - xmin gt 0.5 then
        x0 := Max(xmin, x0/2);
     elif i+w gt #S and xmax - x1 gt 0.5 then
        x1 := Min(xmax, x1*2);
     elif i-w gt 0 and S[i-w]/S[i] ge r and 
          i+w le #S and S[i+w]/S[i] ge r then
        break;
     end if;

     terms *:= 2;
     vprintf ClassGroupExpected, 2 : 
       "Repeating Riemann sum with %o terms\n", terms;
  end while;

  sum := (&+ S);

  if sum lt 10^-20 then
    // calculation is meaningless, due to truncating Dickman
    return R! 10^20;
  end if;

  return 1/sum;

end function;


// cost = B/Log(B) * expected trials per prime
// time = const * cost where const is empirical
// April 2013: 
// for degree 3 or 4, around 10^4 trials per second

function class_group_expected_cost(d, D :
                                   bound := 0,
                                   const := d*3*10^-5);
  assert bound ge 0;
  if bound eq 0 then
    bound := Max(100, Round(Log(D)^2));
  end if;
  tries := class_group_expected_tries(d, D, bound);
  // P = number of primes in factor base
  P := RealField(6)! bound/Log(bound); 
  cost := P * tries;
  return cost, Round(tries), const * cost;
end function;


///////////////////////////////////////////////////////////////////////////////
// USER INTRINSICS 
// (also called by the new ClassGroup)
///////////////////////////////////////////////////////////////////////////////

intrinsic ClassGroupExpectedNumberOfTrials
          (O::RngOrd, B::RngIntElt) -> RngIntElt

{The expected number of trials to find each smooth element, 
in the class group computation for the order O using the 
factor base bound B}

  require IsAbsoluteOrder(O) : 
     "ClassGroup not implemented for relative extensions";

  return Ceiling(class_group_expected_tries
                 (Degree(O), Discriminant(O), B));
end intrinsic;


intrinsic ClassGroupSuggestedBound
          (O::RngOrd) -> RngIntElt, RngIntElt

{A suggested value for the factor base norm bound, for the 
class group computation for the order O.  Also returns the 
ClassGroupExpectedNumberOfTrials with that bound}

  return ClassGroupSuggestedBound(O, 0);
end intrinsic;

intrinsic ClassGroupSuggestedBound
          (O::RngOrd, Bmin::RngIntElt) -> RngIntElt, RngIntElt
{"} // "
  require IsAbsoluteOrder(O) : 
     "ClassGroup not implemented for relative extensions";

  Bmin := Max(Bmin, 50);

  d := Degree(O);
  D := Abs(Discriminant(O));
  logD := Ilog(2, D);

  // For easy fields, return fast
  // TO DO more
  B := 0;
  if logD le 10 then
     B := 50;
     E := 1;
  elif logD le 20 then
     B := 100;
     E := 1;
  elif d eq 2 then
     if logD le 25 then
        B := 100;
        E := 2;
     elif logD le 30 then
        B := 100;
        E := 3;
     elif logD le 50 then
        B := 100 + 30*(logD - 30);
        E := logD div 9;
     end if;
  end if;

  if B ge Bmin then
     return B, E;
  elif B gt 0 then
     E := Ceiling(class_group_expected_tries(d, D, Bmin));
     return Bmin, E;
  end if;

  // There is usually a wide plateau of values of B
  // whose cost varies only within a small factor r.

  function test(B)
     E := class_group_expected_tries(d, D, B);

     N := B/Log(B) where B is Parent(E)!B;

     // linear algebra cost guesstimate
     // (for hermite-no-trans; lll-kernel is cheaper)
     // allow O(N^4), in principle should be more like O(N^3)
     // using bound on elementary divisors (ie class number)
     L := (N/1000)^4 * 10^5;

     return <B, E, N*E + L, L>;
  end function;

  // We assume the cost behaves as a continuous function of c
  // with a single minimum, which we now try to locate.
  // In easy cases the optimal c is low, so start low.

  // Bmin should be one of the B-values 

  B0_ := Round(0.1*Log(D)^2);
  B0 := Bmin;
  while B0 lt B0_ do
     B0 := 2*B0;
  end while;

  T := [test(B0), test(2*B0)]; 

  // extend left until increase (take care with Bmin)
  while T[1,3] lt T[2,3] do
     if T[2,1] eq Bmin then
        return T[2,1], Max(1, Ceiling(T[2,2]));
     end if;
     B := T[1,1] div 2;
     assert B ge Bmin or T[1,1] eq Bmin;
     Insert(~T, 1, test(B));
  end while;

  // extend right until increase
  while T[#T,3] lt T[#T-1,3] do
     Append(~T, test(Round(2*T[#T,1])) );
  end while;

  // REFINE
  // include midpoint of intervals on each side of min
  // until B is determined within factor of rr
  rr := 1.05;

  while true do
     _, m := Min([t[3] : t in T]);
     assert m gt 1 and m lt #T;
     Bm := T[m,   1];
     Bl := T[m-1, 1];
     Br := T[m+1, 1];
     if Br le Bmin then
        break;
     end if;
     if Bl lt Bmin then
        Bl := Bmin;
     end if;
     if Bm lt Bmin then
        Bm := Bmin;
     end if;
     r, s := Max([ Bm/Bl, Br/Bm ]);
     assert r gt 1;
     if r lt rr then
        break;
     end if;
     if s eq 1 then
        // left
        B := Round(Bm / Sqrt(r));
        if B eq Bm or B eq Bl then
           break;
        end if;
        Insert(~T, m, test(B));
     else
        // right
        B := Round(Bm * Sqrt(r));
        if B eq Bm or B eq Bl then
           break;
        end if;
        Insert(~T, m+1, test(B));
     end if;
  end while;

  assert B ge Bmin;

  assert T eq Sort(T);

  _, a := Min([t[3] : t in T]);

  if IsVerbose("ClassGroupExpected", 1) then
     for t in T do 
        print t;
     end for;
     printf "Best:\n%o\n", T[a];
  end if;

  return T[a,1], Max(1, Ceiling(T[a,2]));

end intrinsic;


/////////////////////////////////////////////////////////////////
// Internal heuristics to be called from the class group routine
/////////////////////////////////////////////////////////////////

// Only need rough order of magnitude
// Returns 0 or 2^i * B for some i

intrinsic InternalClassGroupLP1Bound
  (d::RngIntElt, D::RngIntElt, B::RngIntElt, e::RngIntElt, f::RngIntElt)
-> RngIntElt 
{}
  vprint ClassGroupExpected: "Heuristic large prime bound";

  R     := RealField();
  logB  := Log(B);
  delta := Log(2)/logB;
  lDB   := Log( Sqrt(Abs(D))/2^d ) / logB;

  // Sqrt(Abs(D))/2^d  =  approx typical size of numbers
  // TO DO 2^r not 2^d ?

  vprintf ClassGroupExpected: "Smoothness exponent %o\n", lDB;

  if lDB lt 2 then
    return 0;
  end if;

  // use compatible estimate for ordinary relations and LP relations,
  // to get a fair comparison (what matters is relative size of # tries)

  vprintf ClassGroupExpected: "Given e = %o\n", e;
  e := Ceiling(1/DickmanRho(lDB));
  vprintf ClassGroupExpected: "Taking e = %o\n", e;

  E := R!0;
  N0 := e*f;

  vprintf ClassGroupExpected:
    "L = 0 (no LP)     1/rho = %o\ttries = %o\n", e, N0;

  imax := 28 - Ilog(2, B);
//time
  for i := 0 to imax do

    // large p : 2^i*B < p < 2^(i+1)*B

    L     := B * 2^i;
    gamma := 1 + i*delta;
    dg    := delta/gamma;

    rho := DickmanRho(lDB - gamma);

    // Expected # of matches = Ei * (# tries)^2 / 2
    Ei := dg / L * rho^2;
    E +:= Ei;

    // Solve for N = # tries:
    // # relations = N/e + N^2/2*E = f
    N := ( -1/e + Sqrt(1/e^2 + f*E) ) / E;

    // # single prime relations with p in this range
    LP := N * dg * rho;

    vprintf ClassGroupExpected:
      "L = 2^%o*B = %o 1/rho = %o\ttries = %o LPrels = %o\n",
      i+1, 2*L, Round(1/rho), Round(N), Round(LP);

    /* if not worthwhile to include the current interval, then return L
     *
     * c = (cost of processing and storing each LP) / (cost of each try)
     * note there is no processing until we find two with same p
     * TO DO: biff cost, just use 1 percent rule
     */
    c := 1;
    if c*LP gt N0 - N or N0/N lt 1.01 then
      break;
    elif i eq imax then
      L := 2*L;
      break;
    end if;

    N0 := N;

  end for;

  if L eq B then
    L := 0;
  end if;

  if IsVerbose("ClassGroupExpected") then
    if L eq 0 then
      print "Large prime bound = 0";
    else
      printf "Large prime bound = 2^%o*B = %o\n", Round(Log(2,L/B)), L;
    end if;
  end if;

  assert L lt 2^30;
  return L;

end intrinsic;

