freeze;

/***********************************************************************
*                 SOLVING CONICS OVER NUMBER FIELDS                    *
*                                                                      * 
*             Steve Donnelly, under ongoing development                *
*                                                                      * 
*  Acknowledgement: the basic algorithm is Denis Simon's idea          *
*                                                                      * 
*  Main functions: solve_diagonal_conic (called by HasRationalPoint)   *
*                  lagranges_method                                    * 
*                  simplify_neq_soln                                   * 
*                                                                      *       
************************************************************************

TO DO:

different method for quadratic K
(this code is bad for quadratic imaginary K, also for nonreal cubic K)

***********************************************************************/

debug := false;

dev := false; // if false, switch off experimental stuff

xverb := false;

import "points.m" : LLLBasis, small_element;

import "nice_qa.m" : reduced_z_basis;

import "../../Ring/FldNum/class_group_cost.m" : class_group_expected_cost;

rnd := func< x | x ge 1 select Round(x) else RealField(2)!x >;

//////////////////////////////////////////////////
// Toggle for the SUBFIELD METHOD :
// will be used iff degree of base field >= d
//////////////////////////////////////////////////

global_use_subfield := NewStore();

StoreSet(global_use_subfield, "d", Infinity());

intrinsic SetConicSubfieldMethodDegreeBound(value::RngIntElt)
{Do not use!!!  This method is dangerous!}
  StoreSet(global_use_subfield, "d", value);
end intrinsic;

intrinsic GetConicSubfieldMethodDegreeBound() -> RngIntElt
{For internal use}
   return StoreGet(global_use_subfield, "d");
end intrinsic;

///////////////////////////////////////////////////
// Approximate expected time for NormEquation over
// extension K(sqrt{a})/K
//  = (relation search time) + const * (unit size)
///////////////////////////////////////////////////

function neq_expected_time(a)
  ZK := Integers(Parent(a));
  d := 2*Degree(ZK);
  // discriminant of K(sqrt{a})  (upper bound)
  DK := Discriminant(ZK);
  D := DK^2 * Abs(Norm(a)); 
  // class group time 
  // (constant 1.5 times normal, because of subfield)
  _, _, t := class_group_expected_cost
             (d, D : const := d*5*10^-5);
  // r = new unit rank of K(sqrt{a}) / K
  r1, r2 := Signature(ZK);
  r11 := #[i : i in [1..r1] | Real(Conjugate(a,i)) gt 0];
  r := r11 + r2;
  // u = const * (unit size)    (upper bound)
  // (units are often smaller due to class group)
  if r eq 0 then 
    u := 0;
  else
    u := 10^-4 * Abs(D/DK) ^ (1/(2*r));
  end if;
  return t + u, t, u;
end function;

//////////////////////////////////////////////////
// SIMPLIFY SOLUTION
// Given an element l in a quadratic extension L/K, 
// returns a nice element with the same norm as l.
//////////////////////////////////////////////////

function simplify_via_nice_reps(l, n, Labs)
  L := NumberField(Parent(l));
  l2, s := NiceRepresentativeModuloPowers(Labs! l, 2);
  l2 := L! l2;
  s  := L! s;
  assert l2 eq l*s^2;
  ln := l2 / Norm(s);
  assert Norm(ln) eq n;
  return ln;
end function;

function equation_order(L)
  l := L.1;
  assert IsIntegral(l);
  assert IsAbsoluteField(L);
  return Order([l^i : i in [0..Degree(L)-1]] : Order:=true, Verify:=false);
end function;

function simplify_neq_soln(l, n : ZLabs:=0)
  verb := GetVerbose("Conic") ge 2 or GetVerbose("NormEquation") ge 2;
  verb3 := GetVerbose("Conic") ge 3 or GetVerbose("NormEquation") ge 3;

  L := Parent(l);
  K := BaseField(L);
  assert ISA(Type(K), FldNum) and BaseField(K) eq Rationals();
  assert Degree(L) eq 2; 
  assert Norm(l) eq n;
vprintf Conic, 3: "MaximalOrder of quadratic extension: "; 
vtime Conic, 3:
  ZL := Integers(L);

  if Type(ZLabs) eq RngIntElt then 
vprintf Conic, 3: "AbsoluteOrder of this maximal order: "; 
vtime Conic, 3:
    ZLabs := AbsoluteOrder(ZL);
  end if;
  Labs := NumberField(ZLabs);
  assert IsMaximal(Integers(Labs));

if 0 eq 1 then // TO DO is this as good?
_ := Factorization(l*Integers(Labs));
  return simplify_via_nice_reps(l, n, Labs);
end if;

  // can assume n has already been factored
  nprimes := [tup[1] : tup in Factorization(n*ZL)];

  if verb3 then printf "Original solution l = \n  %o\n", l; end if;
  l0 := l;
  previous := [];

  for i := 1 to 50 do // iterate several times, or until stable or getting worse!

    // Want to find b such that b^sigma/b*l is nice.
    // Let the ideal bb be the superfluous part of the numerator of l,
    // ie (l) = N*bb/bb^sigma where N has norm (n).
    // Then b will be chosen as some small element in bb.
    bb := 1*ZL;
    llni := 1*ZL;
    for P in nprimes do 
      eP := Valuation(l,P);
      llni *:= P^-eP;
      if eP gt 0 then
        fP := eP - Valuation(L!n,P);
        if fP gt 0 then 
          bb *:= P^fP;
        end if;
      end if;
    end for;
    // after removing primes appearing in the norm, ll = I/I^sigma for some I
    ll := l * llni;

    assert AbsoluteNorm(ll) eq 1;
    llden := (ll + 1*ZL)^-1; 
    llnum := ll * llden;
    if debug then
      assert llden + llnum eq 1*ZL; 
      assert Norm(llden) eq Norm(llnum);
    end if;
    bb *:= llnum;

    ////////////////////////////////////////////////////////////
    // new attempt: this gets a small element of bb, but doesn't 
    // try to make the absolute values of l small

    if bb eq 1*ZL then
      return l;
    end if;
    bb := ZLabs!! bb;
    b := small_element(bb); 
    assert b in bb; 
    b := ZL! b;
    Nb := Abs(AbsoluteNorm(b));
    Nbb := AbsoluteNorm(bb);
//printf "Current extra norm = %o,\n    new extra norm = %o\n", Nbb, Nb/Nbb;
//printf "Current height = %o,\n    new height = %o\n", Round(AbsoluteLogarithmicHeight( Labs!l )), 
//                                                      Round(AbsoluteLogarithmicHeight( Labs!(l*Norm(b)/b^2) ));
    if Nb ge Nbb^2 then // not an improvement
      return l;
    else
      l *:= Norm(b)/b^2; // = b^sigma/b
      continue;
    end if;
    ////////////////////////////////////////////////////////////

    d := Degree(Labs);
    FFLabs := FieldOfFractions(ZLabs);
    // We actually choose 1/b as an element of the frac ideal bb,
    // (using the inverses so we're not forcing any primes to appear in b)
    bb := (ZLabs!! bb)^-1;
    labs := Labs!l;
    size := Ilog(10, Max([ Abs(Numerator(coeff)) : coeff in Eltseq(labs) ]) );
    Append(~previous, <l, size>);  assert #previous eq i;
    if i gt 8 and &and [previous[i][2] ge previous[j][2] : j in [i-8..i-1]] then
      break i; // looks like we're getting nowhere
    end if; 

    prec := Max([100, GetKantPrecision(), size]);
    max_prec := 1000 + 200*i; // more than about 10^4 really slows it down!
    prec := Min(prec, max_prec);
prec := 200;
max_prec := 200*i;
    // TO DO : do we ever actually achieve any reduction when prec << size ??

    procedure increase(~p)
      p := Min(2*p, max_prec);
      if verb then
        print "simplify_neq_soln: increasing precision for conjugates to", p;
      end if;
    end procedure;
 
    while true do
    //bb_basis := Basis(bb);
      bb_basis := LLLBasis(bb);
      bb_basis_conjs := [ [ &+[ Eltseq(Labs!x)[i]*zz^(i-1) : i in [1..d]]
                          : zz in ChangeUniverse(Conjugates(Labs.1:Precision:=prec), ComplexField(prec))]
                        : x in bb_basis ];
      M := Matrix( ComplexField(prec), d,d, bb_basis_conjs);
      M_conj := Matrix(BaseRing(M), [[Conjugate(M[i,j]): j in [1..d]] : i in [1..d]]);
      labs_conjs := [&+[ Eltseq(labs)[i]*zz^(i-1) : i in [1..d]]
                       : zz in Conjugates(Labs.1:Precision:=prec)];
      D := DiagonalMatrix( RealField(prec), [Sqrt(Abs(x)): x in labs_conjs]);
      A := M*D*Transpose(M_conj);
           // Inner product on bb, where for each archimedean absolute value v,
           // the coordinate corresponding to v is weighted by Sqrt(|l|_v).
           // Therefore, short vectors will be elements 1/b in bb
           // for which |l*bconj/b|_v is likely to be small for all v.

      // Check if precision was sufficient (but just work approximately on the first few iterations)
      if prec lt max_prec and Max([Abs(Im(x)): x in Eltseq(A)]) gt 10^(-20) then
         increase(~prec); continue; end if;
      A := Matrix([[ Re(A[i,j]) : j in [1..d]] : i in [1..d]]);  // make A exactly real
      if prec lt max_prec and Max([Abs(x): x in Eltseq(A-Transpose(A))]) gt 10^(-20) then
         increase(~prec); 
         continue; 
      end if;
      A := 1/2*(A + Transpose(A)); // make A exactly symmetric
      if not IsPositiveDefinite(A) then
         if prec lt max_prec then
            increase(~prec); 
            continue; 
         else
            // TO DO: try to make A positive ???
         end if;
      end if;
      break; // we've increased precision as much as we're willing to, in this iteration
    end while;

    // Find short vectors under the quadratic form
    lat := LatticeWithGram(A : CheckPositive:=false); // we already checked (and possibly ignored,
                                                      // which means ShortestVectors might complain!) 
    try
      svs := ShortestVectors(lat : Max:=1);
      assert #svs eq 1;
      sv := svs[1];
      okay := true; 
    catch ERR 
      okay := false; 
      if verb then "ShortestVectors threw an error!"; end if;
    end try;
    if not okay then 
      continue i; 
    end if;
    binv := L! &+[ Round(sv[i])*bb_basis[i] : i in [1..d]];
    if verb3 then "b =", 1/binv; end if;
    bconj_over_b := binv^2/Norm(binv);
    l *:= bconj_over_b;
    if verb3 then printf "After %o iterations, new l = \n  %o\n", i, l; end if;
    if bconj_over_b in {1,-1} then
      break i; // stop iterating if stable
    end if;  
  end for; // i

  _,k := Min([tup[2] : tup in previous]);
  l := previous[k][1];

  if verb then 
    if l eq l0 then
      print "Did not simplify solution!";
    else
      printf "Simplified solution l = \n  %o\n", l; 
    end if;
  end if;

  return l;
end function;

// Find an ideal in each ideal class with smallest possible norm,
// by naively running over all ideals, ordered by norm.
// (Currently, only use ideals that are products of primes with prime norm.)

function small_ideal_class_reps(OK, Clmap : allowed_to_omit:=0, max:=Infinity())
  PI := PowerIdeal(OK);
  Cl := Domain(Clmap);
  Clreps := AssociativeArray(Cl);
  Clnorms := AssociativeArray(Cl);
  
  ideals_of_norm := [ {@ PI| @} ]; // the nth entry will contain the ideals of norm n
  count := 0;
  n := 1;
  while n lt max and count + allowed_to_omit lt #Cl do  
    n +:= 1;
    // get the ideals of norm n
    if IsPrime(n) then
      ideals_of_norm[n] := {@ PI| tup[1] : tup in Factorization(n*OK) | Norm(tup[1]) eq n @};
    else
      p := Max(PrimeDivisors(n));
      ideals_of_norm[n] := {@ PI| P*I : P in ideals_of_norm[p], I in ideals_of_norm[n div p] @};
    end if;
    // assign them as reps of relevant classes
    for I in ideals_of_norm[n] do
      cI := I @@ Clmap;
      if not IsDefined(Clreps, cI) then
        Clreps[cI] := I;
        Clnorms[cI] := n;
        count +:= 1;
      end if;
    end for;
    if #ideals_of_norm[n] gt 0 then
      vprintf Conic, 2: "%o ", count;
    end if;
  end while;

  return Clreps, Clnorms;
end function;

///////////////////////////////////////////////////
//  SOLVING DIAGONAL CONICS
///////////////////////////////////////////////////

forward lagranges_method;
forward naive_search;

// Given r,s,t in an absolute number field, try to solve r*x^2 + s*y^2 + t*z^2 = 0
// Returns a solution [x0,y0,z0] or false

function solve_diagonal_conic(rst : Primes:={}) 
  r,s,t := Explode(rst);

  K := Parent(r);  assert Parent(s) eq K and Parent(t) eq K;
  assert ISA(Type(K), FldAlg) and BaseField(K) eq Rationals(); 
  assert IsMonic(fK) and forall{c : c in Coefficients(fK) | IsIntegral(c)}
         where fK is DefiningPolynomial(K);

  OK := Integers(K);
  d := Degree(K);

  if not IsEmpty(Primes) then
    assert Type(Universe(Primes)) eq RngInt;
    Primes := &join [{tup[1] : tup in Decomposition(OK, p : Check:=true)} : p in Primes]; 
    // TO DO: Check:=false here seems not to work (leads to different, bad results? or just random?)
    StoreFactor([Minimum(P) : P in Primes]);
  end if;

  // Find all Primes appearing in the coeffs
  for x in [r,s,t] do
    Primes1 := {tup[1] : tup in Factorization(x*OK)}; 
    StoreFactor([Minimum(P) : P in Primes1]);
    Primes join:= Primes1;
  end for;

  // Reduce to integral coeffs [1, -a*da^2, -b*db^2]
  a := -s/r; 
  b := -t/r;
  Da := 1*OK;
  Db := 1*OK;
  for P in Primes do
    v := Valuation(a, P) div 2;
    if v ne 0 then
      Da *:= P^-v;
    end if;
    v := Valuation(b, P) div 2;
    if v ne 0 then
      Db *:= P^-v;
    end if;
  end for;
  da := small_element(Da);
  if Db eq Da then
    db := da;
  else
    db := small_element(Db);
  end if;

  vprint Conic: "Starting lagranges_method, over field of degree", d;
  vprint Conic, 2: "Coefficients of diagonal conic:", rst;
  time0 := Cputime();
  IndentPush();
  bool, sol := lagranges_method(a*da^2, b*db^2 : Primes:=Primes);
  IndentPop();
  vprintf Conic: "Conic over field of degree %o took %os\n", d, Cputime(time0);

  if bool then 
    x := sol[1];
    y := sol[2]*da;
    z := sol[3]*db;
    assert r*x^2 + s*y^2 + t*z^2 eq 0;
    return true, [x,y,z];
  else 
    return false, _;
  end if;
end function;

// Quick search for solutions to x^2 - a*y^2 = b*z^2

function naive_search(K, a, b, B)
  if IsSquare(Norm(-b/a)) then
    bool, y := IsSquare(-b/a);
    if bool then 
      vprint Conic: "Found a solution, -b/a = square!";
      return true, [K| 0,y,1]; 
    end if;
  end if;
  pairs := [[1,0], [0,1]] cat [[y,z] : y,z in [n: n in [1..B] | IsSquarefree(n)] | GCD(y,z) eq 1];
  vprintf Conic, 2: "Naive search (for solution in integers up to %o): ", B; 
  vtime Conic, 2:
  for yz in pairs do 
    y,z := Explode(yz);
    n := a*y^2+b*z^2;
    if IsSquare(Norm(n)) then 
      bool, x := IsSquare(n);
      if bool then 
        vprintf Conic: "Found an easy solution! \n"; 
        return true, [K| x,y,z];
      end if;
    end if;
  end for;
  return false, _;
end function;

// If a and b are in a subfield, and if a solution exists there, return one.

function is_solvable_over_subfield(K, a, b, subfields)
  for F in subfields do  // assume sorted by degree
    if a in F and b in F then
      if IsLocallySolvable(Conic([F| 1, -a, -b])) then
        vprint Conic: "Reduced to a solvable conic over subfield of degree", Degree(F);
        vprint Conic, 2: F;
        vprint Conic: "Calling lagranges_method over subfield:";
        IndentPush();
        bool, sol := lagranges_method(F!a, F!b); assert bool;
        IndentPop();
        return true, ChangeUniverse(sol, K);
      end if;
    end if;
  end for;
  return false, _;
end function;

// Experimental method: reduce to subfield of subdegree 2 
// The (first) boolean returned is false if either
//  -- there is no solution, or 
//  -- the method failed or was not attempted

function can_solve_using_subfield_method(a, b, K : F:=0)
  d := Degree(K);
  Z := Integers();

  if F cmpeq 0 then
    if IsOdd(d) or d lt GetConicSubfieldMethodDegreeBound() then
      return false, _;
    end if;
    if d eq 2 then
      sf := [Rationals()];
    else
      sf := [tup[1] : tup in Subfields(K:Proof:=0) | Degree(tup[1]) eq d/2];
    end if;
    if #sf eq 0 then
      return false, _;
    end if;
    // prefer F for which K/F has the fewest ramified infinite places
    r1 := Min([Signature(F) : F in sf]);
    sf := [F : F in sf | Signature(F) eq r1];
    if r1 gt 2*Signature(K) then 
      vprint Conic: "Not using subfield method (subfields have ramified infinite places)";
      return false, _; 
    end if;
    // now choose smallest discriminant
    F := sf[idx] where _, idx is Min([Discriminant(Integers(F)) : F in sf]);
  end if;

  vprint Conic: "Using subfield method: degree 2 subfield is", DefiningPolynomial(F);
  time0 := Cputime();
  IndentPush();
  bool, sol := HasRationalPointUsingSubfield(K!a, K!b, K, F); assert bool;
  IndentPop();
  if bool then
    vprintf Conic: "Solved conic via reduction to subfield of degree %o, took %os\n", Degree(F), Cputime(time0);
    return bool, sol;
  else
    return false, _;
  end if;
end function;

// Try to split the quaternion algebra by testing the min poly 
// of some elements in the Z-module Z_K[1, a, b]

// TO DO: don't use this, because it's actually equivalent to 
// testing if Norm(v*i+w*j) is square, ie just plugging into conic

function can_split_quaternion(K, a, b : NUM:=100)
  Pol := PolynomialRing(K); x := Pol.1;
  A<i,j> := QuaternionAlgebra< K | a, b >;
  ZB := [A| c*q : c in Basis(Integers(K)), q in [1,i,j]];
  ZB := reduced_z_basis(ZB);
  L := StandardLattice(Degree(K));
  svs := [Eltseq(tup[1]) : tup in ShortVectors(L, 2 : Max:=Ceiling(Sqrt(NUM)))]; 
  coords := [v1 cat v2 cat v3 : v1,v2,v3 in svs]; // avoids testing trivial elements (when ZB is not reduced)
  if #coords gt NUM then coords := coords[1..NUM]; end if;
  vprintf Conic: "Trying to split the quaternion algebra (testing %o small elements): ", #coords;
  vtime Conic:
  for v in coords do
    q := &+ [A| v[i]*ZB[i] : i in [1..#ZB]];
    if q in K then 
      continue; 
    end if;
    t := Trace(q);
    n := Norm(q);
    bool, rt := HasRoot(x^2 - t*x + n);
    if bool then
      vprintf Conic: "\nFOUND SOLUTION by splitting the quaternion algebra\n";
      z := q - rt;
      s := Eltseq(A!z); 
      assert s[1]^2 - a*s[2]^2 - b*s[3]^2 eq 0;
      return true, s[1..3];
    end if;
  end for;  
  return false, _;
end function;

// helper
function solution_from_zero_divisor(A, z)
  if z[4] eq 0 then 
    sol := Eltseq(z);
  else
    Mat2, AtoMat2 := MatrixRing(A, z);
    zz := (Mat2![0,1,0,0]) @@ AtoMat2;      
    sol := Eltseq(zz*A.3);                  
    assert sol[4] eq 0; 
  end if;
  return sol[1..3];
end function;

function reduce_via_quaternion_and_recurse(K, a, b : trans_data:=0, max_order:=false)
  na := Abs(Norm(a));
  nb := Abs(Norm(b));
  assert na le nb; 
  A<i,j> := QuaternionAlgebra< K | a, b >;
  O := Order([A| 1, i, j, i*j]);
CheckOrder(O);

  if trans_data cmpne 0 then
    // construct larger order by including element obtained from previous reduction step
    x,y,z, swapped := Explode(trans_data);
    if not IsIntegral(x) or not IsIntegral(y) then
      den := Denominator(ideal<Integers(K)|x,y>);
      x *:= den; y *:= den; z *:= den;
    end if;
    if not swapped and z eq 1 then
      // x^2 - a*y^2 = b*b0*z^2 where b0 was the previous b
      b0 := (x^2-a*y^2)/(b*z^2); 
      j0 := (x-i*y)/(b*z) * j; 
      assert IsIntegral(b0);
      assert Trace(j0) eq 0 and Norm(j0) eq -b0;
      O := Order([A| 1, i, j, i*j, j0, i*j0]);
    elif z eq 1 then 
      // same, except a and b were also swapped after reduction
      // x^2 - b*y^2 = a*a0*z^2 where a0 was the previous b 
      a0 := (x^2-b*y^2)/(a*z^2); 
      i0 := (x-j*y)/(a*z) * i; 
      assert IsIntegral(a0);
      assert Trace(i0) eq 0 and Norm(i0) eq -a0;
      O := Order([A| 1, i, j, i*j, i0, i0*j]);
    end if;  
CheckOrder(O);
  end if;
  if max_order then
    vprintf Conic, 2: "MaximalOrder in quaternion algebra: ";
    vtime Conic, 2:
    O := MaximalOrder(O);
CheckOrder(O);
  end if;

  zb := ZBasis(O);
  A1, AtoA1 := NicerQuaternionAlgebra(A : elements:=zb, reduce_a);
  if ISA(Type(A1), AlgMat) then
    z := (A1![0,1,0,0]) @@ AtoA1;      
    assert Trace(z) eq 0 and Norm(z) eq 0;
    sol := Eltseq(z*A.3);
    assert sol[4] eq 0;
    return true, sol[1..3];
  end if;
  a1 := -Norm(A1.1);
  b1 := -Norm(A1.2);
  assert IsIntegral(a1) and IsIntegral(b1);
  na1 := Abs(Norm(a1));
  nb1 := Abs(Norm(b1));
  if na1 lt na then
    vprintf Conic: "REDUCED 'a' using the quaternion algebra, new a has norm %o\n", na1;
    vprint Conic, 2: "    old a =", K!a, "    new a =", K!a1; 
    vprint Conic: "Now calling lagranges_method recursively";
    bool, sol1 := lagranges_method(a1, b1); assert bool;
    z1 := A1! (sol1 cat [0]);               
    z := z1 @@ AtoA1;                       
    return true, solution_from_zero_divisor(A, z);
  else
    return false, _;
  end if;
end function;

function fact_to_string(seq)
  s := "";
  for i := 1 to #seq do 
    if i gt 1 then
      s *:= " * ";
    end if;
    tup := seq[i];
    s *:= IntegerToString(tup[1]);
    if tup[2] gt 1 then
      s *:= "^" * IntegerToString(tup[2]);
    end if;
  end for;
  return s;
end function;

// Given integral a, b in an absolute number field, try to solve x^2 - a*y^2 = b*z^2
// Returns true, [x0,y0,z0] or false, _

// TO DO
// LagrangesMethod intrinsic
// HasRationalPoint vararg LagrangesMethodEffort

function lagranges_method(a, b : Primes:={}, Nice:=true, Effort:=1.0)

  assert Effort gt 0;

  Cl := 0;
  Clmap := 0;
  Clreps := 0;
  Clnorms := 0;

  Z := Integers();
  K := Parent(a);  
  assert ISA(Type(K), FldAlg) and BaseField(K) eq Rationals(); 
  OK := Integers(K);
  a := OK!a;  
  b := OK!b;
  d := Degree(K);
  D := Discriminant(OK);
  r1, r2 := Signature(K);

  vprintf Conic: "Base field has discriminant %o = %o\n%o real places and %o complex places\n", 
                  fact_to_string(Factorization(D)), D, r1, r2;

  a0 := a;  b0 := b;            // remember original conic
  trans := IdentityMatrix(K,3); // transformation back to original conic, so [x,y,z]*trans = [x0,y0,z0]
  swap := Matrix(K,3,3, [1,0,0, 0,0,1, 0,1,0]); // swaps a and b

  /********  All return statements should go via one of the following two functions  *********/

  function transform_soln(a, b, xyz, trans)  // saves writing the checks at every return point
    okay := xyz[1]^2 - a*xyz[2]^2 - b*xyz[3]^2 eq 0;
    sol0 := Eltseq( Vector(K,xyz) * trans );
    x0, y0, z0 := Explode(sol0);
    okay and:= x0^2 - a0*y0^2 - b0*z0^2 eq 0;

    // try to simplify the transformed solution
    bool, asqrt := IsSquare(a0);
    if bool then
      sol := [K| asqrt, 1, 0];
    elif Nice and not IsIdentity(trans) then
      L := ext<K| Polynomial([K| -a0, 0, 1]) >;
      l := (x0 + y0*L.1)/z0; 
      if debug then assert Norm(l) eq b0; end if;

if xverb then
xxx := FieldOfFractions(LLL(Integers(AbsoluteField(L)))) ! l;
printf "Size before %o (%o)\n", #Sprint(xxx), Ilog(10, Denominator(xxx));
end if; 
      vprintf Conic: "Simplifying transformed solution: "; 
      vtime Conic:
      l1 := simplify_neq_soln(l, b0); 
if xverb then
xxx := FieldOfFractions(LLL(Integers(AbsoluteField(L)))) ! l1;
printf "Size after %o (%o)\n", #Sprint(xxx), Ilog(10, Denominator(xxx));
end if;
      x1, y1 := Explode(Eltseq(L!l1));
      okay and:= x1^2 - a0*y1^2 - b0 eq 0;
      sol := [K| x1, y1, 1];

if IsVerbose("Conic") then
 // Check how well we simplified
 gcd0 :=  Norm(ideal< OK | x0, y0, z0 >)^-1;
 norms0 := [Integers()| Norm(x0)*gcd0, Norm(y0)*gcd0, Norm(y0)*gcd0];
 Nden1 :=  Norm(ideal< OK | x1, y1, 1 >)^-1;
 norms1 := [Integers()| Norm(x1)*Nden1, Norm(y1)*Nden1, Nden1];
 D_bound := Round(3*Log(Abs(D)));
 ab_bound := Round(Log(Abs(Norm(a0*b0))));
 print  "Heights: original =", Round(Log(Abs(&* norms0)));
 print  "       simplified =", Round(Log(Abs(&* norms1)));
 printf "        heuristic = %o = %o + %o\n", D_bound + ab_bound, D_bound, ab_bound;
//printf "  HeightOnAmbient = %o\n", Round(Log(HeightOnAmbient(Conic([K|1,-a0,-b0])!sol)));
end if; // verbose

    else
      sol := sol0;
    end if;

    error if not okay, "lagranges_method came up with an incorrect solution";

    return true, sol, sol0;
  end function;

  // Settings for the first run through
  effort := 0.1;
  use_class_group := false; 
  use_units := false;
  try_subfield_method := false; // if true, try it after doing some reduction
  MAX_weightings := 10;
  neq_time := Infinity();
  history := [* *];
  modular_sqrts := [[OK|1,0], [OK|1,0]]; // initially contains no info
  // The first sequence [X0,Y0] satisfies (X0/Y0)^2 = a modulo part of b,
  // the second sequence likewise for b modulo part of a

  // After each reduction, check if problem is reduced to a subfield
  subfields := [tup[1] : tup in Subfields(K:Proof:=0) | Degree(tup[1]) notin [1,d]];
  Sort(~subfields, func< F1,F2 | Degree(F1)-Degree(F2) >);

  while true do  // iteratively reduce a and b

    if Abs(Norm(a)) gt Abs(Norm(b)) then  // ensure a smaller than b
      temp := a; a := b; b := temp;
      trans := swap * trans; 
      Reverse(~modular_sqrts);
    end if;

    bool, xyz := naive_search(K, a, b, 10);
    if bool then return transform_soln(a, b, xyz, trans); end if;

    bool, xyz := is_solvable_over_subfield(K, a, b, subfields);
    if bool then return transform_soln(a, b, xyz, trans); end if;

    if use_units then 
      assert assigned units; 
      adjusted_by_unit := false;
      // Use units to reduce height of a or b, if possible 
      // TO DO: search in lattice instead of doing this cheap + vulgar thing
      vprintf Conic, 2: "Try adjusting coefficients by square units: "; 
      vtime Conic, 2:
      repeat
        // try to adjust a
        u := 1; 
        hau := AbsoluteLogarithmicHeight(a);
        for uu in units do 
          hauu := AbsoluteLogarithmicHeight(a*uu^2);
          if hauu lt hau then u := uu; hau := hauu; end if;
        end for;
        // try to adjust b
        v := 1; 
        hbv := AbsoluteLogarithmicHeight(b);
        for vv in units do
          hbvv := AbsoluteLogarithmicHeight(b*vv^2);
          if hbvv lt hbv then v := vv; hbv := hbvv; end if;
        end for;
        if u ne 1 or v ne 1 then 
          adjusted_by_unit := true;
          vprintf Conic,2: ". ";
          a *:= u^2;
          b *:= v^2;
          trans := DiagonalMatrix([K| 1,u,v]) * trans;
          modular_sqrts[1,1] *:= u;
          modular_sqrts[2,1] *:= v;
        end if;
      until u eq 1 and v eq 1;
    end if; // use_units
    
    if use_units and adjusted_by_unit then
      bool, xyz := naive_search(K, a, b, 10);
      if bool then return transform_soln(a, b, xyz, trans); end if;

      bool, xyz := is_solvable_over_subfield(K, a, b, subfields);
      if bool then return transform_soln(a, b, xyz, trans); end if;
    end if;

    norma := Z! Norm(a);
    normb := Z! Norm(b);
    vprintf Conic: "TRYING TO REDUCE, coeffs have norms %o and %o\n", norma, normb;

    if neq_time lt Infinity() then
      neq_time, neq_t, neq_u := neq_expected_time(a);
      vprintf Conic: "(Expected time for current NormEquation: %o sec)\n", rnd(neq_time);
      Append(~history, [* < neq_time, neq_t, neq_u >, a, b, trans *] );
    end if;
    
    // Construct an OK-submodule M < K+K s.t that for (x,y) in M, b divides x^2-a*y^2
    // We define M := {(x,y) in K + K | x in I, y in J, and x - A*y in R} 
    // where I, J, R are (fractional) ideals of OK, and A is in OK

    // TO DO: in the case v_P(b) is odd and v_P(a) is nonzero and even, should really 
    // have a square root condition instead of just valuation conditions on x and y,
    // so that the values can have valuation v_P(b) instead of v_P(b) + 1

    // We will take A = X0/Y0 modulo b2, where we write (b) = b1*b2 with
    // b2 coprime to b1, b2 coprime to a*Y0, and b2 dividing X0^2 - a*Y0^2
    X0, Y0 := Explode(modular_sqrts[1]);
    b2 := b*OK;
    aY0 := (a*Y0)*OK;
    bad := aY0 + b2;
    while Minimum(bad) ne 1 do
      b2 := OK!! (b2/bad);
      bad := aY0 + b2;
    end while;
    N0 := X0^2 - a*Y0^2;
    // pull out all prime-powers of b2 which do not divide N0
    remains := b2/(b2+N0*OK);
    bad := remains;
    while Minimum(bad) ne 1 do 
      b2 := OK!! (b2/bad);
      bad := remains + b2;
    end while;
    b1 := OK!! (b*OK/b2);

    // Put denominators in J at primes that appear more than once in 'a'
    // (In practice these primes won't be large, even in step 1 where all primes are stored anyway)
    a_fact_easy := &cat [Factorization(ideal<OK| a, tup[1]>) : tup in 
                         Factorization(norma : ECMLimit:=2000, MPQSLimit:=0, Proof:=false)];
    a_vals := [Valuation(a,tup[1]) : tup in a_fact_easy];
    Jdenom := 1*OK;
    for tup in a_fact_easy do
      v := Valuation(a, tup[1]);
      if v ge 2 then
        Jdenom *:= tup[1] ^ (v div 2);
      end if;
    end for;
    J := Jdenom ^ -1;

    I := 1*OK;
    if Minimum(b2) eq 1 then
      Acongruences := [OK| ];
      Rfactors := [];
    else
      A0 := X0 * Modinv(Y0, b2);
      assert A0^2 - a in b2;
      Acongruences := [A0];
      Rfactors := [<b2, 1>];
    end if;

    // Factorize b1 (in step 1 the primes are known, in later steps they should be small)
    b1fact := [];
    for P in Primes do 
      e := Valuation(b1, P);
      if e gt 0 then 
        Append(~b1fact, <P,e>); 
        Include(~Primes, P);
      end if;
    end for;
    if IsEmpty(b1fact) then
      b1fact := Factorization(b1);
    else
      b1factx := Factorization( b1 / &*[tup[1]^tup[2] : tup in b1fact] );
      b1fact cat:= b1factx;
//assert forall{tup: tup in b1factx | Norm(tup[1]) lt 10^20};
    end if;

    for tup in b1fact do 
      P := tup[1];
      va := Valuation(a,P);
      if va gt 0 then  
        // impose minimum condition so that x^2 and a*y^2 have valuation >= tup[2]
        I *:= P ^ Ceiling( tup[2]/2 );
        J *:= P ^ Ceiling( (tup[2] - va - 2*Valuation(J,P)) / 2 );
      else  
        e := tup[2] div 2;
        I *:= P^e;  
        J *:= P^e;
        if IsOdd(tup[2]) then
          k, modP := ResidueClassField(P);
          bool, AmodP := IsSquare(a @modP);
          if bool then 
            Append(~Acongruences, AmodP @@modP );
            Append(~Rfactors, <P, e+1>);
          else
            error "Conic is not locally soluble -- should have checked this earlier";
          end if;
        end if;
      end if;
    end for;

    // Get a Z-module basis of M. 
    // Work with matrices over Q, in terms of the basis of K.
    Ibas := Matrix([ Eltseq(K!x) : x in Basis(I) ]);  
    Jbas := Matrix([ Eltseq(K!x) : x in Basis(J) ]);  
    Mmat := BlockMatrix([[Ibas, zero], [zero, Jbas]]) where zero is ZeroMatrix(Rationals(),d,d);
    if debug then 
      Kbasis_det := Determinant(Matrix([ Eltseq(FieldOfFractions(OK)! b) : b in Basis(K) ]));
      assert Abs(Determinant(Mmat)*Kbasis_det^2) eq Abs(Norm(I)*Norm(J)); 
    end if;
    if not IsEmpty(Rfactors) then
      Rcomponents := [ tup[1]^tup[2] : tup in Rfactors ];
      R := &*Rcomponents;
      A := ChineseRemainderTheorem( Acongruences cat [0], 
                                    Rcomponents  cat [Jdenom^2] );  
      assert &and [A^2 - a in rf[1] : rf in Rfactors];
      modular_sqrts[1] := [OK| A, 1]; // this is at least as good as what was here before
      Rbas := Matrix([ Eltseq(K!x) : x in Basis(R) ]);  
      mA := RepresentationMatrix(K!A);
      // Impose the condition that x - A*y in R.
      // ie determine which Z-linear combinations of rows of Ibas and -mA*Jbas 
      // are equal to some Z-linear combinations of rows of Rbas.
      VJ := VerticalJoin([ Ibas, -Jbas*mA, Rbas ]);  
      VJ := ChangeRing(den*VJ, Z)  // make VJ integral 
                 where den is LCM([Denominator(c) : c in Eltseq(VJ)]);
      Kmat := KernelMatrix(VJ);  assert Nrows(Kmat) eq 2*d and Ncols(Kmat) eq 3*d;
      xymat := EchelonForm(Submatrix(Kmat, 1,1, 2*d,2*d ));  // project to the (x,y) component
      assert Abs(Determinant(xymat)) eq Abs(&*[Norm(tup[1]) : tup in Rfactors]);
      Mmat := xymat * Mmat;  
    end if;

    Mbas := [ [K!row[1..d], K!row[d+1..2*d]] where row is Eltseq(Mmat[r]) : r in [1..2*d] ];
    if debug then 
      assert &and[ mb[1]^2 - a*mb[2]^2 in b*OK : mb in Mbas ]; 
    end if;

reassign_Kweightings := true;

    timeout := false;
    reduction_time0 := Cputime();

    for prec_const := 1 to 101 by 2 do  // increase precision when things go wrong
      error if prec_const gt 100, "Something is going wrong in lagranges_method"; 
      
      // Create the lattice inside (K tensor R) + (K tensor R) given by the images of Mbas, where 
      // the coords are the real embeddings followed by the real and imag parts of the complex embeddings

//"Heights:", Round(AbsoluteLogarithmicHeight(a)), Round(AbsoluteLogarithmicHeight(b));
      prec := 100 + Round(AbsoluteLogarithmicHeight(a)) + Round(AbsoluteLogarithmicHeight(b));
      prec *:= prec_const;
      if prec_const gt 1 then
        vprint Conic,2: "\nIncreased precision to", prec;
      end if;

      M := Matrix([ Conjugates(xy[1] : Precision:=prec) cat Conjugates(xy[2] : Precision:=prec) : xy in Mbas ]);

if reassign_Kweightings then
      // If a and b have norm 1, don't try hard (low chance of success)
      if Abs(Norm(b)) eq 1 then 
        mw := 1;
        if MAX_weightings gt mw then 
          vprintf Conic, 2: "Setting MAX_weightings = %o\n", mw; 
          MAX_weightings := mw;
        end if;
      end if;

      // Define weighted norm on the lattice, designed be small when |x^2| and |a*y^2| are small for each embedding
      // The idea is to make the height of x^2-a*y^2 as small as possible.
      // We vary the weights, keeping their product constant, in order to explore into the cusps!
      // Currently weight the valuations of K, could also weight |x +/- sqrt(a)*y| (but more work to set up). 
      // Note: I realised that for the case [1,1,...], using |x +/- sqrt(a)*y| isn't better than |x| and |y|.
      // First, collect some weightings (with product 1) of the infinite places of K.
      Kweightings := [* [1 : i in [1..d]] *];
      inds := [* <[j], [jj]> : j in [1..r1], jj in [1..r1] | j ne jj *] cat                     // two real places
              [* <[j,j+1], [jj,jj+1]> : j in [1..r1-1], jj in [r1+1..d by 2] *] cat             // two real, one complex pair
              [* <[j,j+1], [jj,jj+1]> : j in [r1+1..d by 2], jj in [r1+1..d by 2] | j ne jj *]; // two complex pairs
      if not assigned Ws then 
        Ws := [2,4];
      end if;
      for W in Ws do
        for js in inds do 
          w := [Rationals()| 1 : i in [1..d]]; 
          for j in js[1] do w[j] := W; end for;
          for j in js[2] do w[j] := 1/W; end for;
          Append(~Kweightings, w);
        end for; 
      end for; 
      if #Kweightings gt MAX_weightings then
        Kweightings := [* Kweightings[i] : i in [1 .. MAX_weightings] *];
      end if;
end if;

      MAX := Ceiling( 5000 * effort * Sqrt(Effort) );
      // Compensate somewhat when not enough weightings are available 
      // (in particular, when K is imaginary quadratic there is only one)
      if MAX_weightings gt 4 * #Kweightings then 
        MAX := Ceiling( MAX * MAX_weightings / #Kweightings / 4 );
        MAX := Min(MAX, 10^6);
      end if;
      // TO DO: MAX is probably too big

      vprintf Conic, 3: "Conjugates: "; 
      vtime Conic, 3:
      conjs := Conjugates(a : Precision:=prec);

      for ww in Kweightings do 
        vprintf Conic, 2: "Weights %o : ", ww; 
if xverb then
        vprintf Conic, 2: " (MAX=%o) ", MAX; 
end if;
        weights := wts cat [wts[i] * Abs(conjs[i])^(1/2) : i in [1..d]] 
                       where wts is ChangeUniverse(ww, RealField(prec));
        MW := M * DiagonalMatrix(weights);
        MWstar := Matrix([[ ComplexConjugate(MW[j,i]) : j in [1..2*d]] : i in [1..2*d]]); // conjugate transpose
        MWgram := MW * MWstar;
        if &or[ Abs(Imaginary(m)) gt 10^-20 : m in Eltseq(MWgram) ] then 
          continue prec_const; // clearly we're not working with enough precision, so start again
        end if;
        MWgram := Matrix(RealField(prec), 2*d, 2*d, [Real(m) : m in Eltseq(MWgram)]);
        MWgram := 1/2*( MWgram + Transpose(MWgram) ); // make sure it's exactly symmetric
        MWgramred, lll := LLLGram(MWgram);
        MWgramred := 1/2*( MWgramred + Transpose(MWgramred) ); // make sure it's exactly symmetric
        if not IsPositiveDefinite(MWgramred) then
          continue prec_const; // clearly we're not working with enough precision, so start again
        end if;
        L := LatticeWithGram(MWgramred);
        Mbasred := [[ &+[K| lll[i][j]*Mbas[j][k] : j in [1..2*d]] : k in [1,2]] : i in [1..2*d]]; // Mbasred = lll*Mbas 

        // Try short vectors.  
        // TO DO: for very large degree, instead just take small combinations of the LLL basis
        NUM := 0;
        // problem with Determinant for real lattices? (bad memory blowout)
        // HIGH := Max(1, Floor( 1/10*Abs(Determinant(L))^(1/(4*d)) ) ); 
if d le 15 then
        LOW := 0;
        HIGH := 1;
else
        // want to only call ShortVectors once, so it doesn't have to search exhaustively
      //Ldet := Determinant(L); assert Ldet gt 0;
        NormR := &* [Z| Norm(tup[1]) : tup in Rfactors];
        Ldet := Norm(I)*Norm(J)*NormR * Abs(D); // TO DO: is this close to correct?
        LOW := 0;
        HIGH := Floor(Sqrt(MAX)) * Floor(Ldet ^ (1/d));
end if;
        reduced := false;

//ProStart();
        ww_time0 := Cputime();
        svcount  := 0;
        sfcount1 := 0;
        sfcount2 := 0;
        while not reduced and not timeout and NUM lt MAX do  
          sv_time0 := Cputime();
          svs := LOW eq 0 select ShortVectors(L, HIGH : Max:=MAX-NUM) // TO DO: Prune
                           else  ShortVectors(L, LOW, HIGH : Max:=MAX-NUM); 
          sv_time := Cputime(sv_time0);
if sv_time ge 1 then vprintf Conic, 2: " (SV:%o:%os) ", #svs, Round(sv_time); end if;
          NUM +:= #svs;
          LOW := HIGH;
          HIGH := 2*LOW;

if NUM ge MAX/2 and #[sv : sv in svs | &and[sv[1][i] eq 0 : i in [1+d..2*d]] ] gt #svs/2 then
  // TO DO: Too many short vectors with y=0 ... should this happen ?
  if prec_const eq 1 then 
    continue prec_const;
  elif prec_const le 50 and prec lt 1000 then 
    // increase precision and continue running through Kweightings starting from ww
    wwidx := Min([ i : i in [1..#Kweightings] | ww eq Kweightings[i] ]);
    Kweightings := [Kweightings[j] : j in [wwidx .. #Kweightings]];
    reassign_Kweightings := false;
    continue prec_const;  
end if; end if;

          // Note: the first few short vectors often have yy = 0.  It's important not to
          // discard these, because they are needed to pull squares out of b near the start.
          for sv in svs do 
            svcount +:= 1;

            coords := [Round(x) : x in Eltseq(sv[1])];
            xx := &+[ coords[i]*Mbasred[i][1] : i in [1..2*d]]; 
            yy := &+[ coords[i]*Mbasred[i][2] : i in [1..2*d]]; 
            n := xx^2 - a*yy^2;
            normbnew := Z! (Norm(n)/normb);  

            // Check for trivial solutions
            if IsSquare(normbnew) then 
              bnew := OK! (n/b);  
              bool, zz := IsSquare(bnew);
              if bool then 
                vprintf Conic: "\nFOUND SOLUTION: reduced conic has b = square (tried %o short vectors)\n", Index(svs,sv);
                return transform_soln(a, b, [xx,yy,zz], trans);
            end if; end if;
            if IsSquare((-1)^d*normbnew/norma) then
              bnew := OK! (n/b);  
              bool, s := IsSquare(-bnew*a); // quicker to test order element
              if bool then 
                s := K! (s/a); // s^2 = -bnew/a
                vprintf Conic: "\nFOUND SOLUTION: reduced conic has -b/a = square (tried %o short vectors)\n", Index(svs,sv);
                return transform_soln(a, b, [a*s*yy, s*xx, bnew], trans);
            end if; end if;

            // The main reduction thing
            if Abs(normbnew) lt Abs(normb) then 
              bnew := OK! (n/b);  
              vprintf Conic, 2: "\n";
              vprintf Conic: "REDUCED 'b' (tried %o short vectors), new b has norm %o\n", Index(svs,sv), Abs(normbnew);
              vprint Conic, 3: "old b =", OK!b, "new b =", bnew;
              b := bnew;
              T := Matrix(K, 3,3, [xx,yy,0, a*yy,xx,0, 0,0,bnew]);
              trans := T * trans;
              dyy := Denominator(yy);
              modular_sqrts := [[OK|xx*dyy,yy*dyy], [OK|xx*Y0,X0]] where X0,Y0 is Explode(modular_sqrts[2]);
              reduced := true; 
              break prec_const;  // try to reduce again
            end if;

            if use_class_group and yy ne 0 then
              // Try to reduce by pulling a square factor out of bnew

              // sf = Squarefree(normbnew), using not much more than trial division
              fact, sgn, unfact := Factorization(normbnew : Proof := false, 
                                   SQUFOFLimit:=15, PollardRhoLimit:=0, ECMLimit:=0, MPQSLimit:=0);
              sf := sgn * &* [Z| tup[1]^(tup[2] mod 2) : tup in fact]; 
              if assigned unfact then
                sf *:= &* unfact;
              end if;

              if Abs(sf) lt Abs(normb) then
                sfcount1 +:= 1;
                vprintf Conic, 3: ".";
                bnew := OK! (n/b);
                S := &*[ PowerIdeal(OK) | tup[1] ^ (tup[2] div 2) : tup in Factorization(bnew*OK) ];
                if Abs(Norm(bnew)/Norm(S)^2) lt Abs(normb) then 
                  sfcount2 +:= 1;
                  vprintf Conic, 3: "%o:%o ", Round(Abs(Norm(bnew)/normb)), Norm(S)^2;
                  // get class group rep for S
                  cS := S @@ Clmap;
                  if IsDefined(Clreps, cS)
                    and Abs(Norm(bnew)/Norm(S)^2*Clnorms[cS]^2) lt Abs(normb)
                  then
                    bool, zz := IsPrincipal(S/Clreps[cS]);
                    assert bool and Abs(Norm(zz)) eq Norm(S)/Clnorms[cS];
                    bnew := OK! (bnew/zz^2);
                    normbnew := Norm(bnew);
                    assert Abs(normbnew) lt Abs(normb);
                    vprintf Conic, 2: "\n";
                    vprintf Conic: "REDUCED 'b', new b has norm %o\n", normbnew;
                    vprint Conic, 3: "old b =", OK!b, "new b =", bnew;
                    b := bnew;
                    T := Matrix(K, 3,3, [xx,yy,0, a*yy,xx,0, 0,0,bnew*zz]);
                    trans := T * trans;
                    dyy := Denominator(yy);
                    dzz := Denominator(zz);
                    modular_sqrts := [[OK|xx*dyy,yy*dyy], [OK|xx*dzz*Y0,zz*dzz*X0]] where X0,Y0 is Explode(modular_sqrts[2]);
                    reduced := true; 
                    break prec_const;
                  end if;
                end if;
              end if;
            end if;

            // Give up when likely to be easier to solve the norm equation
            // Considerations:
            //  neq is often easier than estimated, because disc < D*Norm(a)^2,
            //  hard reductions typically reduce neq time only by a small fraction,
            //  extra reduction may lead to a nicer solution in the end

            // On break, continue if one of the candidates works, otherwise quit
            if svcount mod 100 eq 0 then
              reduction_time := Cputime(reduction_time0);
              if effort eq 0.1 and reduction_time gt 1  // initial run
                 or reduction_time gt Effort * effort * neq_time / 2
              then 
                timeout := true; 
                break;
              end if;
            end if;

          end for; // sv in svs
        end while; // NUM lt MAX
//ProShow(20);

        vprintf Conic, 2: "Time: %o\n", Cputime(ww_time0);
        if use_class_group then
          vprintf Conic, 2: "# candidates for square factors: %o, %o\n", sfcount1, sfcount2;
        end if;

        if timeout then
          vprintf Conic: "Exiting loop after %os\n", reduction_time;
          break;
        end if;

      end for; // ww in Kweightings
      break;
    end for; // prec_const

    if reduced then
      if not assigned zz then zz := 1; end if;
      trans_data := <xx, yy, zz, false>; // used only in reduce_via_quaternion_and_recurse

      if Abs(Norm(a)) gt Abs(Norm(b)) then // ensure a smaller than b
        temp := a; a := b; b := temp;
        trans := swap * trans; 
        trans_data[4] := true;
        Reverse(~modular_sqrts);
      end if;

      // TO DO: at which stage should this be tried?
      if dev and d le 20 and Abs(Norm(b)) le 10^20 then 
        vprintf Conic: "Trying to reduce using the quaternion algebra: "; 
        vtime Conic:
        bool, xyz := reduce_via_quaternion_and_recurse(K, a, b : trans_data:=trans_data, max_order:=true);
        if bool then return transform_soln(a, b, xyz, trans); end if;
      end if;

      /* TO DO: combine this into reduce_via_quaternion, or omit completely
      if Abs(Norm(b)) lt 10^5 then 
        bool, xyz := can_split_quaternion(K, a, b);
        if bool then return transform_soln(a, b, xyz, trans); end if;
      end if;
      */

      continue; // try to reduce again
    end if; 

    if try_subfield_method then
      bool, xyz := can_solve_using_subfield_method(a, b, K);
      if bool then return transform_soln(a, b, xyz, trans); end if;
      try_subfield_method := false; // no point trying more than once 
    end if;

    // If coeffs are units, don't run reduction loop any more, as there's only 
    // a small chance of finding a solution (we've already given it a short run) 
    if Abs(Norm(b)) eq 1 and assigned Cl then
      assert Abs(Norm(a)) eq 1; 
      break; 
    end if; 

    try_again := false; // unless we find a reason 

    if effort lt 0.3 then
      effort := 0.3;
      try_again := true;
    elif effort lt 1 then
      effort := 1;
      try_again := true;
    end if;

    if neq_time eq Infinity() then
      neq_time, neq_t, neq_u := neq_expected_time(a);
      try_again := true;
      Append(~history, [* < neq_time, neq_t, neq_u >, a, b, trans *] );
    end if;

    // TO DO: maybe go straight to NormEquation in cases we think it can handle
    //       (rather than trying too hard to reduce further)

    // Start to use_class_group?
    if not use_class_group then

      if Cl cmpeq 0 then
        vprintf Conic: "Computing class group of the base field: "; 
        vtime Conic:
        if ISA(Type(OK), RngQuad) then
          Cl, Clmap := ClassGroup(OK);
        else 
          Cl, Clmap := ClassGroup(OK : Proof:="GRH");
        end if;
        vprintf Conic: "Class group has order %o\n", #Cl;
      end if;

      ur := UnitRank(K);
      if ur gt 0 and Abs(D) gt #Cl^2 * 10^(8*ur) then
        // elements obtained via IsPrincipal will be too large
        effort := 1;
      else
        use_class_group := effort eq 1 or 
                           #Cl lt 1000 and #Cl - 100 lt neq_time;
        if use_class_group then
          vprintf Conic: "\nFinding class group representatives with small norm: ";
          vtime Conic:
          Clreps, Clnorms := small_ideal_class_reps(OK, Clmap : 
                             allowed_to_omit := Max(0, #Cl div 5 - 10), 
                             max := Min(10^6, neq_time) );
          effort := 1;
          try_again := true;

          // use units to reduce? (not very important)
          if ur gt 0 and ur le 10 and Abs(D) le #Cl^2 * 10^(6*ur) then
            vprintf Conic: "Computing independent units in the base field: "; 
            vtime Conic:
            U, Umap := IndependentUnits(K);
            assert Ngens(U) eq 1 + ur;
            Ugens := [ U.i @ Umap : i in [2..Ngens(U)] ];
            // use a few of the shortest combinations
            if ur eq 1 or ur gt 6 then
              units := Ugens;
            else
              svs := ShortVectors(StandardLattice(ur), 2);
              combs := [ Eltseq(tup[1]) : tup in svs ];
              units := [ PowerProduct(Ugens, c) : c in combs ];
            end if;
            units cat:= [OK| 1/u : u in units];
            use_units := true;
          end if;
        end if;
      end if;
    end if;

    // Use more weight?
    // 'Effort' contributes to MAX and MAX_weightings
    MAX_weightings := Ceiling( Sqrt(Effort) * neq_time/10 ); 
    if effort lt 1 then
      MAX_weightings := Min(MAX_weightings, Round(effort*100));
    end if;
    vprint Conic, 2: "Setting MAX_weightings =", MAX_weightings;

    jump := Max(1, #inds div 4); // inds = weight combinations for each W
    bigWs := [2^n : n in [2 .. 100*jump by jump]]; // TO DO: more ways to randomise
    if not bigWs subset Ws then
      Ws := Sort(Setseq(Seqset( Ws cat bigWs )));
      try_again := true;
    end if;

    if try_again then 
      // repeat loop through short vectors, using weightings of the infinite places by all Ws,
      // and trying to take out square factors if use_class_group is true 
      // TO DO: this stupidly runs through the old weights first, even if no reduction occurred in the previous loop 
      continue; 
    end if;
    
    break;
  
  end while; // main reduction loop
 
  bool, xyz := naive_search(K, a, b, 1 + 100 div d);
  if bool then return transform_soln(a, b, xyz, trans); end if;

  // Exhausted all attempts to reduce ==> call NormEquation.

  /* TO DO:
  Note neq_u depends very heavily on the signature of the quadratic extension.
  Should select an 'a' of smallest norm among those with the best signature.
  Without working that out, a fairly simple improvement would be: when neq_u
  is too large, continue the loop and check neq_time for "near-reductions"
  (where Norm(a) increases a bit) until a good enough value of 'a' is found.
  Currently, we just take the best one that we've happened to save.
  */

  if not IsEmpty(history) then
    _, best := Min([ h[1,1] : h in history ]);
    neq_tup, a, b, trans := Explode(history[best]);
    neq_time, neq_t, neq_u := Explode(neq_tup);
  end if;
  
  // ensure really have a smaller than b
  na := Norm(a);
  nb := Norm(b);
  assert Abs(na) le Abs(nb);

  vprint Conic:    "\nGIVING UP !!!!";
  vprintf Conic:   "Norms are %o and %o\n", na, nb;
  vprintf Conic,2: "a = %o \nb = %o\n", K!a, K!b;

  vprintf Conic: "Getting nice representative for a in K*/(K*)^2: ";
  vtime Conic:
  a, sa := NiceRepresentativeModuloPowers(K!a, 2 : Effort:=1);
  T := Matrix(K, 3,3, [1,0,0, 0,sa,0, 0,0,1]);
  trans := T * trans;

  // lagranges_method assumes the calling function checked local solubility, 
  // so something is wrong if NormEquation finds no solution.
  // We check the solution, so the result is rigorous even 
  // if the class group done in NormEquation is non-rigorous.

if neq_time lt Infinity() then
// TO DO missing assignment in some case, eg (sometimes) libs/test/Descent/8
  vprintf Conic: "Calling NormEquation, expected time: %o ( = %o + %o ) sec\n",
                  rnd(neq_time), rnd(neq_t), rnd(neq_u);
end if;
  IndentPush();
  L := ext< K | Polynomial([K| -a,0,1]) >; 
  vblevel := GetVerbose("NormEquation");
  SetVerbose("NormEquation", Max(vblevel, GetVerbose("Conic")) );
  bool, solns := NormEquation(L, K!b); assert bool; 
  SetVerbose("NormEquation", vblevel);
  IndentPop();

  // simplify solution by multiplying by suitable element of norm 1 in L
  ZLabs := Integers(AbsoluteField(L)); // has already been created during NormEquation
if xverb then
xxx := FieldOfFractions(LLL(Integers(AbsoluteField(L)))) ! solns[1];
printf "[lagrange] Size before %o (%o)\n", #Sprint(xxx), Ilog(10, Denominator(xxx));
end if;
  vprintf Conic: "Simplifying solution produced by NormEquation: "; 
  vtime Conic:
  alpha := simplify_neq_soln(L!solns[1], b : ZLabs:=ZLabs); 
if xverb then
xxx := FieldOfFractions(LLL(Integers(AbsoluteField(L)))) ! alpha;
printf "[lagrange] Size after %o (%o)\n", #Sprint(xxx), Ilog(10, Denominator(xxx));
end if;

  xyz := Eltseq(alpha) cat [1];
  return transform_soln(a, b, xyz, trans);
  
end function;

