freeze;

/*******************************************
 *                                         *
 * 8-descent on elliptic curves            *
 *                                         *
 * Sebastian Stamminger, 06-Nov-2005       *
 *                                         *
 * Substantially revised by Tom Fisher     *
 *                                         *
 * Last modified: April 2010, S Donnelly   *
 *                                         *
 *******************************************/

declare attributes Crv: EtaleAlgebra;

declare verbose EightDescent, 4;

import "FourDesc/local_quartic.m": LocalImageOfC2; 
import "../CrvG1/g1invariants.m" : TransformationToMap;

/********** CHANGE LOG -- please record all changes here ***********
  
  Sept 2007 for release in V2.14-1, Steve:

    + Return sequence of curves, followed by sequence of maps 

    + Added real solubility testing.

    + Removed the Pari option (for accessing Simon's conic solver), 
      and instead call LegendresMethod.

    + Don't set Bound in ClassGroup, this should now be controlled 
      by the user via SetClassGroupBounds.

    + Hack around in ImageOfOnePointAtVeryBadOrSmallPrime to get 
      a point that LiftPoint accepts (and catch errors from LiftPoint)

  Sept 2008, Steve:

    + Now solve conic by calling HasPoint, which calls my new routines 
      for diagonalization and Lagrange's method. 
      Commented out PointOnConic and other functions no longer called.
   
  March 2010, Tom :

    + Added options NormalCurve and Union to EightDescent
 
    + EtaleAlgebra changed to use GenusOneModels. The use of 
      MatrixFromQF in FourDesc/utils.m was potentially confusing 
      since it clears denominators. (For a minimised QI the
      denominators can only be 1 or 2.)

    + new version of ImageOfOneLocalPoint, making many previous
      functions redundant

    + added LocalImageAtRealPlace 

    + version taking genus one model as input

    + EightDescent now starts by minimising and reducing the C4

  April 2010, Steve:

    + Added fallback case in ThirdQuadric to handle examples where 
      the 8 points are not disctinct (but these examples seem to 
      fail later anyway, when getting the 20 quadrics)

    + Rewritten HasRealPoint to work more generally 
      (previously gave up when coordinate projections can't be used)

    + Using Mark's FastRoots in ReductionCovariant

****************************************************************/

/*******************************************************************
Real solubility testing 
Steve Donnelly, April 2010
********************************************************************/

// IsolateRoots handles squarefree polys.
// This factors f and refines until intervals are disjoint

function isolate_roots(f : fact:=[], prec:=20)
  f := PolynomialRing(Rationals())! f;
  if IsEmpty(fact) then fact := Factorization(f); end if;

  intervals := &cat [IsolateRoots(tup[1], 10^-prec) : tup in fact];
  Sort(~intervals, func<i1,i2| i1[1]-i2[1]> );
  // are intervals disjoint?
  if exists{i : i in [1..#intervals-1] | intervals[i][2] ge intervals[i+1][1] } then
    return isolate_roots(f : fact:=fact, prec:=2*prec); end if;
  return intervals;
end function;

// Try random directions until we find a birational plane projection
function proj_to_P2(X)
  deg := Degree(X);
  A := Ambient(X);
  assert IsProjective(A) and Dimension(A) eq 3 and BaseRing(A) cmpeq Rationals();

  L := StandardLattice(4);
  N := 0;
  found := false;
  while not found do 
    N +:= 1;
    SV := ShortVectors(L, N, N);
    for tup in SV do 
      pt := A!Eltseq(tup[1]);
      if pt in X then continue; end if;
      X1, pi := Projection(X, pt);
      if Degree(X1) eq deg then
        found := true;
        break;
      end if;
    end for;
  end while;
  X1 := Curve(X1);
  pi := map< X -> X1 | DefiningEquations(pi) >;
  bool, pii := IsInvertible(pi); assert bool;
  return X1, pi, pii;
end function;

// TO DO: this only decides existence of smooth real points

function HasRealPoint(X : Precision:=0, ReturnPoint:=true )

  error if BaseRing(X) ne Rationals(), "The curve should be over Q";

  error if not IsProjective(X) or Dimension(X) ne 1,
       "Currently only implemented for projective curves in P^2 or P^3";

  d := Dimension(Ambient(X));
  error if not d in {2,3},
       "Currently only implemented for projective curves in P^2 or P^3";

  if d eq 3 then
    X1, pi, pii := proj_to_P2(X); // project to plane curve

    coeffs := &cat[Coefficients(f): f in Equations(X)];
    coeffs1 := Coefficients(Equation(X1));
    b1 := Maximum([Abs(Numerator(c)): c in coeffs]);
    b2 := Maximum([Abs(Denominator(c)): c in coeffs]);
    b3 := Maximum([Abs(Numerator(c)): c in coeffs1]);
    b4 := Maximum([Abs(Denominator(c)): c in coeffs1]);
    extra_prec := 3*Ilog(10,Maximum([b1,b2,b3,b4,10]));

    bool, pt1 := HasRealPoint(X1 : Precision := Precision + extra_prec,
                                   ReturnPoint := ReturnPoint);
    // pull back point (approximately) 
    // if it's a base point of pii, throw an error (TO DO)
    pt := [Evaluate(eqn,pt1) : eqn in DefiningEquations(pii)];
    ptmax := Max([Abs(x) : x in pt]);
    okay := ptmax ne 0;
    if okay then
      pt := [x/ptmax : x in pt]; 
      okay := forall{eqn : eqn in Equations(X)
                         | Abs(Evaluate(eqn,pt)) lt 10^(20-Precision)};
    end if;
    error if not okay, "HasRealPointError1";

    if bool and ReturnPoint then
      return true, pt;
    else
      return bool, _;
    end if;
  end if;

  // d = 2
  // We check real solubility of f(x,y) = 0 in intervals, 
  // along the x-axis (just like in one-variable calculus).
  // There are finitely many intervals to consider, separated by
  // critical points, ramification points, etc

  eqns := DefiningEquations(X); assert #eqns eq 1;
  F := eqns[1];

  size := Max([ Round(Log(10, Abs(c) )) : c in Coefficients(F) ]); 
  prec := Max(Precision, size + 50);
  R := RealField(prec);
  Q := Rationals();

  // find smallest degree variable
  degs := [Degree(F,k) : k in [1..3]];

  // special case - if an odd deg poly in one var then OK
  if not ReturnPoint and &or[IsOdd(d) : d in degs] then 
    return true; 
  end if;
  
  deg, j := Min([d eq 0 select Infinity() else d : d in degs]); // smallest nonzero degree
  l, m := Explode(Exclude([1,2,3], j));
  assert {j,l,m} eq {1,2,3};
  
  // Dehomogenize
  K := BaseRing(Parent(F));  assert K eq Rationals();
  P<x,y> := PolynomialRing(K,2);
  subs := [P| 0 : k in [1..3]];  
  subs[j] := y;  
  subs[l] := 1;
  subs[m] := x;
  f := Evaluate(F,subs);

  // get the discriminant poly of f (wrt y) and real roots
  df := UnivariatePolynomial(Resultant(f,Derivative(f,2),2));
  intervals := isolate_roots(df);
  n := #intervals;
  D := 10; r := Random([1..D-1]); 
  xs := (n eq 0) select [Q| r]
                  else  [Q| intervals[1][1] - r] cat
                        [Q| (r*intervals[i][2] + (D-r)*intervals[i+1][1])/D : i in [1..n-1]] cat
                        [Q| intervals[n][2] + r];

  // search for real roots of f(a,y) for a in xs
  t := PolynomialRing(Q).1;
  for a in xs do
    fa := Evaluate(f, [a,t]);
    rootsfa := RealRoots(fa, RealField(prec+10), 10^-prec);
    if #rootsfa gt 0 then 
      if ReturnPoint then 
        r1 := rootsfa[1];
        pt := [Parent(r1)|0,0,0];
        pt[j] := r1;  
        pt[l] := 1;
        pt[m] := a;  
        return true, pt;
      else
        return true, _; 
      end if;
    end if;
  end for;
  return false, _;
end function;


// Make polynomial integral with small content

import "../CrvCon/points.m" : small_element;

function _IntegralModel(X)
  assert #DefiningPolynomials(X) eq 1;
  f := DefiningPolynomials(X)[1];
  K := BaseRing(Parent(f));

  if Type(K) eq FldRat then
    cs := Coefficients(f);
    d := LCM([Denominator(c) : c in cs]);
    s := GCD([Integers()| d*c : c in cs]) / d;
  else 
    assert ISA(Type(K), FldAlg);
    C := ideal< Integers(K) | Set(Coefficients(f)) >;
         // RHS must not be a single sequence (ambiguous)
    s := small_element(C^-1 : class);
  end if;

  sf := s*f;
  assert forall{c : c in Coefficients(sf) | IsIntegral(c)};
  return Scheme(Ambient(X), sf);
end function;


/*************************
The etale algebra of C4.
*************************/

function EtaleAlgebra(C4)
  // C4 is the intersection of two quadrics produced by a 4-descent.
  QT := PolynomialRing(Rationals()); T := QT.1;
  M := Matrices(GenusOneModel(C4));
  // bool, M := IsQuadricIntersection(C4); (this does does re-scaling)
  // M[1] and M[2] are the corresponding symmetric matrices.
  g := Determinant(T*M[1] + M[2]);
  // g = HyperellipticPolynomials(AssociatedHyperellipticCurve(C4));
  if assigned C4`EtaleAlgebra then
    return C4`EtaleAlgebra, C4`EtaleAlgebra`AbsoluteMap, g;
  else
    Q := Rationals();
    A<theta> := quo<PolynomialRing(Q) | g >;
    Aabs, iso := AbsoluteAlgebra(A); 
    //The decomposition of A into number fields.
    C4`EtaleAlgebra := A; // We store A with C4.
    return A, iso, g;
  end if;
end function;

/***************************************************************
The quadric (hypersurface) corresponding to a symmetric matrix.
It would be nice to have this as a Magma-Intrinsic.
****************************************************************/

function Quadric(M);
  // M is an (n+1)x(n+1) symmetric matrix.
  // Return the corresponding quadric.
  K := CoefficientRing(M);
  n := NumberOfColumns(M)-1;
  Pn<[x]> := ProjectiveSpace(K,n);
  Kx := CoordinateRing(Pn);
  xvec := Matrix([x]);
  // q := x*M*Transpose(x); //the quadratic form.
  q := (xvec*ChangeRing(M,Kx)*Transpose(xvec))[1,1]; 
  return Scheme(Pn,q);
end function;


/***********************************
The singular quadrics in the pencil.
************************************/

function SingularQuadricsInThePencil(C4)
//  bool, M := IsQuadricIntersection(C4);
  M := Matrices(GenusOneModel(C4));
  A := C4`EtaleAlgebra;
  iso := A`AbsoluteMap;
  // A.1 is a generic zero of g.
  thetas := iso(A.1); 
  // thetas are the zeros of g in the number fields, 
  // one for each Galois orbit.
  Msing := <theta*M[1] + M[2] : theta in thetas>;
  return <Quadric(M) : M in Msing>;
end function;    


/**********************************************
The conic corresponding to a singular quadric 
produced by projection from the singular point.
***********************************************/

function ConicOfSingularQuadric(Qsing)
  // Qsing is a singular quadric.
  pt := SingularPoints(Qsing)[1];
  C<[z]>, projection := Projection(Qsing,pt); 
  // This is a conic and the projection P3 -> P2.
  return _IntegralModel(C), projection; 
//  return (C), projection; 
end function;


/***************************************************************************
                  TangentPlaneAt(Qsing)
It computes a tangent plane to a singular quadric Qsing in the pencil of
C4. First we compute the conic underlying Qsing. Then we have to find a 
point on this conic. For that we bring it into diagonal form. Then we use 
general conic-solving machinery to find a point. This is the most expensive
step. If the parameter Point is given, it is used as a point on the conic.
Next we compute a tangent line to this point and take its preimage under 
the projection map to get a tangent plane to the singular quadric.
*****************************************************************************/

function TangentPlaneAt(Qsing : Point:=[])
  // Qsing is a singular quadric in the pencil.
  C, projection := ConicOfSingularQuadric(Qsing);
  vprintf EightDescent: "Projection from the singularity leads to a " *
                        "conic given by %o\n", DefiningPolynomial(C);
  vprintf EightDescent: "Solving conic over %o of discriminant %o\n", 
                        BaseField(C), Discriminant(Integers(BaseField(C)));
  bool, C := IsConic(C);  assert bool;
  bool, pt := HasPoint(C);  
  line := TangentLine(pt);
  vprintf EightDescent, 1 : "The tangent line to this point is \n%o, ", 
                             DefiningPolynomial(line);
  t := line @@ projection; // t is the tangent plane.
  t := _IntegralModel(t);  // Make it integral
  vprintf EightDescent, 1 : "\n which lifts under the projection to the " *
                            "tangent plane \n%o.\n\n", DefiningPolynomial(t);
  return t;
end function;


/**********************************************************************
DifferentTangentPlane computes a different tangent plane to the
singular quadric using parametrization of the points on the conic.
**********************************************************************/

function DifferentTangentPlane(Qsing1, L1 : PointOnP1:=[])
  // Qsing1 a singular quadric in the pencil with tangent plane L1.
  // We parametrize the conic, take a different point on it, and
  // compute the corresponding tangent plane.
  K := BaseField(Qsing1);
  C, pr := ConicOfSingularQuadric(Qsing1); // recomputed (doesn't matter).
  pt := Points(pr(Scheme(Qsing1,L1)))[1]; // The original point.
  param := Parametrization(Curve(C),pt);
  if PointOnP1 eq [] then
    PointOnP1 := [Random(K,10),1];
  end if;
  newpt := param(PointOnP1);
  line := TangentLine(newpt);
  t11 := line @@ pr;

  return DefiningPolynomial(_IntegralModel(t11));
end function;  


/******************************************************************
Given a tangent plane to one of the singular quadrics, compute the 
product of all four (resp. two) conjugates of it.
(L1 = DefiningPolynomial(t1)).
********************************************************************/

function ProductOfConjugates(L1)
  Kx := Parent(L1); 
  _, m := SwapExtension(Kx);
  return Norm(m(L1));
end function;


/**********************************************************************
OnePointInEachGaloisOrbit takes a zero-dimensional affine scheme Z over 
a number field (not only Q), and computes one point in each Galois orbit
of Z over suitable extensions of the base field.
This is much faster than working over the algebraic closure.

TO DO: the GroebnerBasis can be bad here   -- Steve
************************************************************************/

function OnePointInEachGaloisOrbit(Z)
  vprint EightDescent,3: "Computing one point in each Galois orbit.";
  // Z is a zero dimensional affine scheme over a number field.
  // We want to find one point in each Galois orbit of Z(Qbar).
  L := BaseField(Z);
  Gr := GroebnerBasis(Z);
  g := Gr[#Gr]; // We take the last element.
  if g eq 1 then return []; end if; // If Z is empty.
  bool, g := IsUnivariate(g);
  assert bool; // g should be univariate, since Z is zero dimensional.
  fact := Factorization(g);
  // The roots of g in suitable number fields:
  fields := <NumberField(f[1] : DoLinearExtension) : f in fact>;
  d := Rank(Ideal(Z));
  // Now the d-th coordinate of our point is L.1.
  if d eq 1 then return [* <L.1> : L in fields *]; end if; 
  // terminating condition.
  // Recursion:
  pts := < <OnePointInEachGaloisOrbit(
             Scheme(Spec(P), [Evaluate(h, x cat [L.1]) : h in Gr])), L.1>  
            where x := [P.i : i in [1..d-1]] 
            where P := PolynomialRing(L, d-1)  
         :  L in fields >;
  points := [* <Append(tup, pt[2]) : tup in pt[1]>[1] : pt in pts *]; 
  // Turn the tuples into sequences:
  return [* [pt[i] : i in [1..#pt]] : pt in points *];
end function;


/*****************************************************************
We know a point P. We want to find a quadric Q defined over the 
rationals which vanishes at P, i.e. Q(P) = 0.
The equation Q(P) = 0 gives some constraints on the possible 
coefficients of Q, which are computed by the following function.
The output of the following function is a matrix, and the 
coefficients of Q must then be in the kernel of this matrix.
******************************************************************/

function ConstraintsOnQuadricsThrough(P)
  vprintf EightDescent,3: 
  "Computing the constraints on quadrics through the point... \n";
  // P is a point on C4 over some number field. 
  // We search a quadric Q over the rationals
  // which goes through P.
  P := Eltseq(P); 
  L := Universe(P);
  Labs := AbsoluteField(L);
  Lc<[c]> := PolynomialRing(Labs,10);
  // c[1],...,c[10] are the coefficients of Q.
  Lcx := PolynomialRing(Lc,4);
  xx := MonomialsOfDegree(Lcx,2);
  // xx = {x1^2, x1*x2, ..., x3*x4, x4^2}
  Q := &+[c[i]*xx[i] : i in [1..10]];
  // Q is the unknown quadric.
  QP := Evaluate(Q,P); // = Q(P).
  coeffs := [Eltseq(MonomialCoefficient(QP,c[i])) : i in [1..10]];
  return Matrix(coeffs);
end function;


/**************************************************************************
ThirdQuadric computes the third quadric through the 8 points where C4 meets
the four tangent planes.
**************************************************************************/

function ThirdQuadric(C4,L)
  vprint EightDescent,3: 
        "Computing the vector space of quadrics through the eight points.";
  ts := [Scheme(Proj(Parent(Li)),Li) : Li in L];
  Zs := [Scheme(t,DefiningPolynomials(C4)) : t in ts];
  allpts := [* *];
  for Z in Zs do 
    for i in [4,3,2,1] do 
      ZZ := Scheme(Z, [Z.j: j in [i+1..4]]);
      if Dimension(ZZ) lt 0 then 
        break i;
      end if;
      Zaff := AffinePatch(ZZ,5-i); // dehomogenise by setting Z.i = 1
      pts := OnePointInEachGaloisOrbit(Zaff);
      pts := [* Insert(pt, i, 1) : pt in pts *]; // projective points
      allpts cat:= pts;
    end for;
  end for;
  Ms := <ConstraintsOnQuadricsThrough(P) : P in allpts>;
  Mat := HorizontalJoin(Ms);
  vprint EightDescent,3: "Computing the kernel of the constraints matrix.";
  Ker := KernelMatrix(Mat);

  if Nrows(Ker) gt 3 then
    // This can happen when there some repeated points, where two of the
    // (possibly conjugate) four linear forms intersect.   
    // Then ConstraintsOnQuadricsThrough may give too few constraints.
    // Maybe(?) this only happens when these are rational points on C4.
    // It's handled here, but we seem to get more problems later anyway.
    // Example: the 8-coverings of 15a1.
    // Here we compute Q3 using more general machinery (the first bit 
    // is copied from TheConstant, so gets done twice).
    //  --- April 2010, SRD
//"\n\nNEW CASE !!!!!!!!\n";
    Qx := CoordinateRing(Ambient(C4));
    I := Ideal(C4);
    norms := [Qx!ProductOfConjugates(Li) : Li in L];
    FourPlanes := &*norms;
    D := Divisor(C4, Scheme(C4, FourPlanes)); 
    supp, mults := Support(D); 
    assert Degree(D) eq 16;
    assert forall{m: m in mults | IsEven(m)};
    D8 := Divisor([<supp[i], mults[i] div 2> : i in [1..#supp]]);
    bool, Q3 := IsHypersurfaceDivisor(D8);
    Q3 *:= LCM([Denominator(c) : c in Coefficients(Q3)]);
    return Q3;
  end if;

  L := Lattice(Ker);
  L1 := PureLattice(L);
  // We mod out by Q1 and Q2.
  xx := MonomialsOfDegree(CoordinateRing(Ambient(C4)),2);
  L2, qmap := quo<L1 | [[MonomialCoefficient(Q,xx[i]) : i in [1..10]] 
                       : Q in DefiningPolynomials(C4)]>;
  L3 := TorsionFreeSubgroup(L2);
  assert Ngens(L3) ge 1; //space of quadrics mod <Q1,Q2> is at least 1-dim.
  c := Eltseq(L3.1 @@ qmap); // The coefficients of Q3.
  Q3 := &+[c[i]*xx[i] : i in [1..10]]; 
  return Q3;
end function;


/************************************************************************
The constant c in the equation L1*L2*L3*L4 = c*Q^2 (the "norm condition").
*************************************************************************/

// TO DO: this gets called many times on same arguments

function TheConstant(C4,L,Q3)
  Qx := CoordinateRing(Ambient(C4));
  I := Ideal(C4);
  norms := [Qx!ProductOfConjugates(Li) : Li in L];
  FourPlanes := &*norms;
  NFP := NormalForm(FourPlanes,I);
  NQ3 := NormalForm(Q3^2,I);
  bool, c := IsCoercible(Rationals(), NFP/NQ3); assert bool;
  return c;
end function;


/*****************************************************************
Computes the gamma in L1*L1' = gamma*H^2.
******************************************************************/

function PlaneThrough(ThreePoints)
  // Given three points in P3 over K.
  // Return the plane over K through the three points.
  P3<[x]> := Ambient(Scheme(Rep(ThreePoints)));
  K := BaseField(P3);
  Kc<[c]> := PolynomialRing(K,4);
  // c[1],...,c[4] will be the coefficients of H.
  KcX<[X]> := PolynomialRing(Kc,4);
  H := &+[c[i]*X[i] : i in [1..4]];
  // the unknown plane.
  HPs := [Evaluate(H,Eltseq(P)) : P in ThreePoints];
  // H(P) must be zero for P in ThreePoints.
  coeffs := [[MonomialCoefficient(HP,c[i]) : i in [1..4]] : HP in HPs];
  Ker := Kernel(Transpose(Matrix(coeffs)));
  vprintf EightDescent,3: "Number of possible planes: %o. Expected 1.\n",
                           Dimension(Ker);
  c := Eltseq(Basis(Ker)[1]);
  H := &+[c[i]*x[i] : i in [1..4]];
  return H;
end function;

function TheGamma(C4,L1,L11,Qsing)
  // L1/L1' = gamma*q^2 on C4. This function computes the gamma.
  // Or: L1*L1' = gamma*H^2. (q = H^2/L1'^2)
  // Notation: L1' = L11. 
  vprint EightDescent,3: "Computing gamma...";
  P3<[x]> := Ambient(Qsing);
  K := BaseField(P3);
  Kx := CoordinateRing(P3);
  L1 := Kx!L1;
  L11 := Kx!L11;
  Q1,Q2 := Explode(ChangeUniverse(DefiningPolynomials(C4),Kx));
  pt1 := SingularPoints(Qsing)[1];
  i := 1; // If pt1[i] = 0, then we take a different i.
  while pt1[i] eq 0 do i+:=1; end while;
  ThreePoints := {pt1} join Points(Scheme(Qsing,[L1,x[i]])) 
                       join Points(Scheme(Qsing,[L11,x[i]]));
  vprint EightDescent,3: "Computing the plane through the three points.";
  vtime EightDescent,3: 
  H := PlaneThrough(ThreePoints);
  I := ideal<Kx | DefiningPolynomials(C4)>;
  vprintf EightDescent,3: "The plane H with L1 L1' = gamma H^2 is\n%o\n", H;
  // Now gamma:
  return K!( NormalForm(L1*L11,I)/NormalForm(H^2,I) );
end function;

/************************************************************************
BadPrimes
*************************************************************************/

function PrimesDividingTheNormsOfAllCoefficients(L1)
  // we assume L1 is integral.
  coeffs := Coefficients(L1);
  norms := [Norm(c) : c in coeffs];
  bad := GCD(ChangeUniverse(norms,Integers()));
  return Set(PrimeDivisors(bad));
end function;

function ProjectionToSpecZ(X)
  // X is a scheme over Z.
  vprint EightDescent,3: "Projecting to Spec(Z)";
  if IsAffine(X) then  
    I := Ideal(X);
    idl := EliminationIdeal(I,{}); // eliminating all variables.
    bool, n := IsPrincipal(idl); assert bool;
    n := Integers()!n;
    if n ne 0 then return n; else return 1; end if;
  else // X is projective.
    d := Dimension(Ambient(X));
    return LCM([ProjectionToSpecZ(AffinePatch(X,i)) : i in [1..d]]);
  end if;
end function;

function BadPrimesUnfactored(C4,L,Q3) 
  // Discriminant(g) is taken extra.
  c := TheConstant(C4,L,Q3);
  badc := Numerator(c)*Denominator(c); 
  // Bad primes (unfactored) from coeffs:
  badcoeffs := LCM([GCD([Integers()!Norm(c) : c in Coefficients(Li)]) : Li in L]);
  // Bad primes from P8:
  P8 := ChangeRing(Scheme(C4,Q3),Integers());
  badP8 := ProjectionToSpecZ(SingularSubscheme(P8));
  vprintf EightDescent,4: "badP8 = %o.\n", badP8;
  bad := LCM([badc,badcoeffs,badP8]);
  return bad;
end function;

function MyBadPrimes(C4,L,Q3 : BadPrimesHypothesis := BadPrimesHypothesis)
  g := Modulus(C4`EtaleAlgebra); 
  d := LCM([Denominator(c): c in Coefficients(g)]);
  g := ChangeRing(g*d,Integers());
  c := TheConstant(C4,L,Q3);
  // Here we could check, whether c is to big for factorization.
  // If so, we could start again with different tangent planes
  // until c is nice enough.
  vprintf EightDescent,2: "Factoring the constant c ... ";
  vtime EightDescent,2:
  fc := Factorization(Numerator(c))*Factorization(Denominator(c));
  vprintf EightDescent,2: "Factorization of c: %o\n",fc;
  S1 := Set(PrimeDivisors(SquareFree(fc))) join Set(PrimeDivisors(Discriminant(g)));
  vprint EightDescent,3: "Bad primes from the coefficients of Li...";
  S2 := &join{PrimesDividingTheNormsOfAllCoefficients(Li) : Li in L};
  vprint EightDescent,3: S2;
  vprintf EightDescent,3: 
         "Under BadPrimesHypothesis S = %o\n",{2} join S1 join S2;
  if BadPrimesHypothesis then
    S3 := {};
  else
    vprint EightDescent,3: 
          "Projection of the singular subscheme of P_8 to Spec(Z):";
    P8 := ChangeRing(Scheme(C4,Q3),Integers());
    badP8 := ProjectionToSpecZ(SingularSubscheme(P8));
    vprint EightDescent,3: "Bad primes from singular subscheme of P_8 divide \n  ", badP8;
    // if badP8 is to big (60 digits or more), we try to make it smaller:
    if Log(badP8)/Log(10) ge 60 then
      //Rem: we could try several different tangent planes.
      vprint EightDescent,3: "Trying to reduce the set of bad primes.";
      Qsing := SingularQuadricsInThePencil(C4)[1];
      L11 := DifferentTangentPlane(Qsing,L[1]);
      vprintf EightDescent,3: "The different tangent plane is L1' = \n%o.\n",L11;
      Lnew := L; Lnew[1] := L11; 
      // We only change the first one. 
      // Evtl. better results when changing both in the split case,
      // but then TheGamma has to be computed for both.
      Q31 := ThirdQuadric(C4, Lnew); 
      vprintf EightDescent,3: "The quadric Q3' is \n%o.\n",Q31;
      bad1 := BadPrimesUnfactored(C4,Lnew,Q31);
      vprintf EightDescent,4: "Computed bad primes for L1': %o\n", bad1;
      gamma := TheGamma(C4,L[1],Lnew[1],Qsing);
      vprintf EightDescent,3: "gamma = %o.\n",gamma;
      Ngamma := Norm(gamma);
      badP8 := GCD(badP8, bad1*Numerator(Ngamma)*Denominator(Ngamma));
    end if;
    vprintf EightDescent,3: "Factoring %o...\n", badP8;
    S3 := Set(PrimeDivisors(badP8));
    S := {2} join S1 join S2 join S3;
    if S eq {2} join S1 join S2 then
      vprintf EightDescent,3: "We proved now:\
      \nBadPrimesHypothesis is true.\n";
    end if;
  end if;
  return {2} join S1 join S2 join S3;
end function;  
  

/***************************************************************************
The local image
****************************************************************************/

// The map F: C4(Q) -> A^*/A^*2. 
// We replace the domain of F by the set of sequences for technical reasons.

/*
function TheMapF(C4,L)
// L = <L[1]> or <L[1],L[2]>.
  C4seq := PowerSequence(Integers());
  A := C4`EtaleAlgebra; iso := A`AbsoluteMap;
  R4<[x]> := PolynomialRing(A,4);
  MC := MonomialCoefficient;
  coeffs := [<MC(L[i],Parent(L[i]).j): i in [1..#L]>@@iso : j in [1..4]];
  print coeffs;
  F := map<C4seq -> A | pt :-> <Evaluate(L[i],pt) : i in [1..#L]>@@iso >;
  return F;
end function;
*/

function LinearFormOverEtaleAlgebra(C4,L)
// L = <L[1]> or <L[1],L[2]>.
  A := C4`EtaleAlgebra; 
  iso := A`AbsoluteMap;
  R4<x1,x2,x3,x4> := PolynomialRing(A,4);
  MC := MonomialCoefficient;
  coeffs := [<MC(L[i],Parent(L[i]).j): i in [1..#L]>@@iso : j in [1..4]];
  return &+[coeffs[i]*R4.i: i in [1..4]];
end function;

/**************************************
At very bad primes or small primes:
***************************************/

function MakeIntegral(pt)
  // pt is a p-adic point on a projective scheme.
  // We just scale it and
  // return an integral point (as sequence) whith j-th coordinate = 1.
  min, j := Min([Valuation(pt[i]) : i in [1..#Eltseq(pt)]]);
  integralpt := [pt[i]/pt[j] : i in [1..#Eltseq(pt)]];
  assert integralpt in Scheme(pt);
  integralpt := ChangeUniverse(integralpt,Integers(Parent(pt[1]))); //in Zp
  return integralpt, j;
end function;

/*
function InverseOfProjection(C4)
  C,pr := Projection(C4);
  phi := map<C4->C|DefiningEquations(pr) : Check:=false>;
  bool, inv := IsInvertible(phi);
  error if not bool, "Projection from (1:0:0:0) doesn't induce a 
  birational map between C4 and its projection to the plane. 
  We would have to project from a different point.";
  return inv;
end function;
*/

// Local solvability test by projecting to P2 and taking the preimage.

/*
function tryLiftPoint(pt, prec : Strict:=false)
  try
    liftedpt := LiftPoint(pt, prec : Strict:=Strict);
    return true, liftedpt; 
  catch err
    vprint EightDescent,2: "LiftPoint threw a failure";
  end try;
  return false, _;
end function;
*/

/*
function IsLocallySolvableByProjectionToPlaneCurve(C4,p)
  C := Curve(Projection(C4));
  bool, pt := IsLocallySolvable(C,p : Smooth);  assert bool;
  // the Smooth parameter does not guarantee that pt is a nonsingular point 
  // -- it means that pt lifts to a rational point on the desingularization.
  bool, pt := tryLiftPoint(pt,50 : Strict:=false);
  if not bool then 
    return false,_; end if;
  inv := InverseOfProjection(C4);
  liftedpt := [Evaluate(f, Eltseq(pt)) : f in DefiningEquations(inv)];
  // same as inv(pt) (but over local field).
  return liftedpt in C4;  // creates point on C4 or gives false
end function;
*/

/*
function tryHasRoot(f,R)  // R is a local ring or field
  try 
    return HasRoot(f,R);
  catch err
    vprint EightDescent,2: "HasRoot threw a failure, trying Factorization instead";
  end try;
  try
    fact := Factorization(f,R);
  catch err 
    vprint EightDescent,2: "Factorization threw a failure, giving up";
    return false, _;
  end try;
  if exists(ff){tup[1] : tup in fact | Degree(tup[1]) eq 1} then
    rt := -c[1]/c[2] where c is Coefficients(ff);
    return true, rt;
  else
    return false, _;
  end if;
end function;
*/

// Using new version of IsLocallySolvable for genus one models.

function ImageOfOneLocalPoint(C4,L,p : prec:=50)
  C4seq := PowerSequence(Integers());
  phi4 := GenusOneModel(C4);
  flag,pt := IsLocallySolvable(phi4,p:Precision:=prec,Random); 
  error if not flag,"Quadric intersection is not locally soluble";
//  got_liftedpt, liftedpt := tryLiftPoint(pt, prec);
  liftedpt := pt;
  pti := MakeIntegral(liftedpt);
  liftedprec := Min([Precision(pti[i]) : i in [1..#pti]]);
  Fpti := Evaluate(L,C4seq!pti);
  v := Valuation(Integers()!Norm(Fpti),p); 
  if (p eq 2) and (v gt liftedprec-10) or 
     (p ne 2) and (v ge liftedprec) then 
    error if prec ge 10^3, "Error in 8 descent: " *
         "Lifted", p,"-adic point to precision", liftedprec, "which was not enough."; 
    prec +:= 10;
    vprintf EightDescent, 2: "Trying again with precision %o in " *
                             "ImageOfOneLocalPoint\n", prec;
    return ImageOfOneLocalPoint(C4,L,p : prec:=prec);
  end if;
  return Fpti, pti;
end function;

/*
function ImageOfOnePointAtVeryBadOrSmallPrime(C4,F,p : prec:=50)
  // large prec indicates many recursive attempts, 
  // so go straight to perturbation method
  got_liftedpt := false;
  if p ne 3 and prec le 50 then  
    got_liftedpt, liftedpt := IsLocallySolvableByProjectionToPlaneCurve(C4,p);
    // might get smashed by the way we take the preimge under the projection.
    if not got_liftedpt then 
      vprint EightDescent,1: "!!!!! IsLocallySolvableByProjectionToPlaneCurve" 
                            *" didn't work, using the original curve instead";
    end if;
  end if;
  if not got_liftedpt and prec le 50 then
    bool, pt := IsLocallySolvable(C4,p);  assert bool;
    got_liftedpt, liftedpt := tryLiftPoint(pt, prec);
  end if;
  if not got_liftedpt then
    // hack around with perturbations to get a better point
    x := PolynomialRing(Rationals()).1;
    Qp := pAdicField(p);
    for i := 1 to 10^4 do 
      bool, pt := IsLocallySolvable(C4,p);  assert bool;
      ptcoords := [Rationals()!cc : cc in Eltseq(pt)];
      precs := [AbsolutePrecision(cc) : cc in Eltseq(pt)];
      ptcoords1 := [ptcoords[i]+Random([1..p])*p^Random([precs[i]-1..precs[i]+3]) : i in [1..4]];
      j := Random([1..4]); k := Random(Exclude([1..4],j));  // two "random" coordinates
      pols := DefiningEquations(C4);
      for l in [1..4] do 
        if l notin [j,k] then pols := [Evaluate(pols[i],l,ptcoords1[l]) : i in [1..2]]; end if;
      end for;
      pol := Resultant(pols[1], pols[2], j);
      pol := Evaluate(pol, [Parent(x)| l eq k select x else 0 : l in [1..4]]);
      bool, rtk := tryHasRoot(pol, Qp);
      if bool then 
        pol := Evaluate(pols[1], k, Rationals()!rtk);
        pol := Evaluate(pol, [Parent(x)| l eq j select x else 0 : l in [1..4]]);
        bool, rtj := tryHasRoot(pol, Qp);
        if bool then 
          ChangeUniverse(~ptcoords1, Qp);
          ptcoords1[j] := rtj;  ptcoords1[k] := rtk;
          for l := 1 to 4 do 
             ptcoords1[l] +:= (l in [j,k]) select O(Qp!p^(precs[l]+5)) 
                                            else  O(Qp!p^Random([precs[l]..precs[l]+5]));
          end for;
          bool, pt1 := IsCoercible(C4(Qp), ptcoords1);
          if bool then
            got_liftedpt, liftedpt := tryLiftPoint(pt1, prec);
            if got_liftedpt then break i; end if;
          end if;
        end if;
      end if;
    end for; // i
  end if;
  error if not got_liftedpt, "Error in IsLocallySolvableByProjectionToPlaneCurve:"
                            *" Failed to come up with a liftable point";

 pti := MakeIntegral(liftedpt);
  liftedprec := Min([Precision(pti[i]) : i in [1..#pti]]);
  Fpti := F(pti);
  v := Valuation(Integers()!Norm(Fpti),p); 
  if (p eq 2) and (v gt liftedprec-10) or 
     (p ne 2) and (v ge liftedprec) then 
    error if prec ge 10^3, "Error in 8 descent: " *
         "Lifted", p,"-adic point to precision", liftedprec, "which was not enough."; 
    prec +:= 10;
    vprintf EightDescent, 2: "Trying again with precision %o in " *
                             "ImageOfOnePointAtVeryBadOrSmallPrime\n", prec;
    return ImageOfOnePointAtVeryBadOrSmallPrime(C4,F,p : prec:=prec);
  end if;
  return Fpti, pti;
end function;
*/


/**********************************************************************
My own code for computing the image of one local point, which is faster
than IsLocallySolvable.
***********************************************************************/

/*
function RandomPoint(C)
  // C is an affine curve over Fp in A3.
  vprintf EightDescent,3: "Computing a random F_p-point";
  assert Dimension (C) eq 1;
  Fp := BaseField(C);
  pts := {};
  while IsEmpty(pts) do 
    vprintf EightDescent,3: "."; 
    // The number of dots is the number of trials, wich is
    // expected to be less than 4 on average.
    x := Random(Fp);
    Z := Scheme(C, C.1 - x); 
    //some hyperplane section (C.1 must have some value x).
    pts := Points(Z); // Z is 0-dim.
  end while;
  vprintf EightDescent,3: "\n";
  return Random(pts);
end function;
*/

/*
function NextLevel(C,pt_p)
  // C an affine scheme over the integers.
  // pt_p a point mod p.
  Fp := Parent(pt_p[1]);
  p := Characteristic(Fp);
  pt := ChangeUniverse(Eltseq(pt_p),Integers());
  newpols := [Evaluate(f,[pt[i] + p*C.i : i in [1..3]]) div p : f in 
  DefiningPolynomials(C)];
  return Scheme(Ambient(C),newpols);
end function;
*/

/*
function OldImageOfOneLocalPoint(C4,F,p)
  if p le 7  or  Dimension(SingularSubscheme(ChangeRing(C4,GF(p)))) ge 1 
             or  #SingularPoints(ChangeRing(C4,GF(p))) ge 2 then
   //    return ImageOfOnePointAtVeryBadOrSmallPrime(C4,F,p);
    return ImageOfOneLocalPoint(C4,F,p:newcode:=false);
  else
    Fp := GF(p);
    C_i := AffinePatch(ChangeRing(C4,Integers()),1); 
    // Might be a bad affine patch (e.g. at p=2).
    error if Dimension(C_i) lt 1, 
         "Error in MyImageOfOneLocalPoint: We took the wrong affine patch.";
    pt := [0,0,0]; 
    for i in [0..1000] do
      C_i_Fp := BaseChange(C_i,Fp);
      if Dimension(SingularSubscheme(C_i_Fp)) ge 1  or
      #SingularPoints(C_i_Fp) ge 2 then // hand over to IsLocallySolvable.
//       return ImageOfOnePointAtVeryBadOrSmallPrime(C4,F,p); 
      return ImageOfOneLocalPoint(C4,F,p:newcode:=false); 
      end if;
      pt_i := RandomPoint(C_i_Fp); 
      // If pt_i is smooth, it lifts. Thus we take only smooth points.
      while IsSingular(pt_i) do pt_i := RandomPoint(C_i_Fp); end while;
      C_i := NextLevel(C_i,pt_i);
      pt := [pt[j] + p^i*Integers()!pt_i[j] : j in [1..3]] cat [1];
      v := Valuation(Integers()!Norm(F(pt)),p); 
      if v lt i then
        //If v lt i, then the precision i is enough to determine F(pt) mod A^*2.
        return F(pt), pt, i; 
      end if;
    end for;
    error "Error in 8 descent: precision 1000 was not enough to compute the local image.";
  end if;
end function;
*/

// The whole local image

function LocalImage(C4,L,p,g) 
  g := ChangeRing(g,Rationals()); // needed for local image of C2.
  Fpt := ImageOfOneLocalPoint(C4,L,p);
  A := C4`EtaleAlgebra;
  kgens, res_p := LocalImageOfC2(g,p : EtaleAlgebra:=A );
  xi_p := res_p(Fpt);
  // The local image of F is the coset xi*U, where U is generated by kgens.
  _, quomap := quo<Codomain(res_p)|kgens>;
  localimage := <quomap, quomap(xi_p)>;
  return localimage, res_p;
end function;

////////////////////////////////////////////////////////////////

// Local image at real place (added 2010)

// A modification of the function in FourDesc/local_quartic.m
function RealLabels(eps,prec)
  // TO DO: don't repeat all this on every call?
  A := Universe(eps);
  f := Modulus(A); // degree 4 polynomial
  R := RealField(prec);
  rts := Roots(PolynomialRing(R)!f); 
  assert &and[t[2] eq 1 : t in rts]; // check it really does have 4 roots
  ar := Sort([R!Real(t[1]) : t in rts]); 

  homs := [hom<A -> R | a> : a in ar];
  he := [[h(e) : h in homs] : e in eps];
  bool := forall{x : x in seq, seq in he | Abs(x) gt 10^(-prec/3)};
  GF2 := GF(2);
  labels := [ [GF2| x lt 0 select 1 else 0 : x in seq] : seq in he];
  return labels, bool;
end function;

function LocalImageOfC2AtRealPlace(g,A,prec)
  R := RealField(prec);
  P := PolynomialRing(R); 
  D := Discriminant(g);
  if D gt 0 then 
    if #Roots(P!g) gt 0 then 
      HR := AbelianGroup([2,2,2,2]);
      if LeadingCoefficient(g) gt 0 then
        kgens := [HR![1,1,0,0],HR![0,0,1,1]];
      else
        kgens := [HR![1,0,0,1],HR![0,1,1,0]];
      end if;
    else
      HR := AbelianGroup([]);
      kgens := [HR|];
    end if;
  else
    HR := AbelianGroup([2,2]);
    kgens := [HR![1,1]];
  end if;
  vprintf EightDescent,2 : "Quartic has %o real roots\n",NumberOfGenerators(HR);
  res_infty := map< A -> HR | x :-> HR!(RealLabels([x],prec)[1]) >;
  return kgens,res_infty;
end function;

function ImageOfOneRealPoint(C4,L,prec)
  bool,realpt := HasRealPoint(C4 : Precision:=prec);
  assert bool; // C4 should have real points
  A := C4`EtaleAlgebra;
  R := Universe(realpt);
  P := PolynomialRing(R); 
  AR := quo<P|P!Modulus(A)>;
  MC := MonomialCoefficient;
  coeffs := [MC(L,Parent(L).i): i in [1..4]];
  Fpt := &+[AR|(P!coeffs[i])*realpt[i]: i in [1..4]];
  return Fpt;
end function;

function LocalImageAtRealPlace(C4,L,g,prec)
  g := ChangeRing(g,Rationals());
  // ensure labels are not too close to zero, so result is rigorous
  // (okay, in theory should also ensure prec is sufficient for round-off)
  repeat
    Fpt := ImageOfOneRealPoint(C4,L,prec);
    A := C4`EtaleAlgebra;
    kgens, res_infty := LocalImageOfC2AtRealPlace(g,A,prec);
    HR := Codomain(res_infty);
    labels, bool := RealLabels([Fpt],prec);
    prec +:= 1;
  until bool; 
  xi_infty := HR!labels[1];
  _, quomap := quo<Codomain(res_infty)|kgens>;
  localimage := <quomap, quomap(xi_infty)>;
  return localimage,res_infty;
end function;

/**************************************************************
The set H of elements fulfilling the norm condition. We call it
H, since it should correspond to (a coset in) the cohomology 
group H^1(Q,E[8];S), or H^1(Q,E[2];S).
***************************************************************/

function TheSetH(C4,c,S);
  A := C4`EtaleAlgebra;
  // S must be a set of prime ideals in QNF.
  S_QNF := {p*MaximalOrder(BaseRing(A)) : p in S};
  vprintf EightDescent, 2: "Construction of A(S,2)\n";
  vtime EightDescent, 2: 
  AS2,A_to_AS2,toVec,bU := pSelmerGroup(A,2,S_QNF:Raw);
  vprintf EightDescent, 2: "Computing the image of S in A(S,2), to get A(S,2)/Q(S,2).\n";
  vtime EightDescent, 2: 
  ImageOfS := {A_to_AS2(t) : t in {-1} join Set(S)};
  AS2Q, modQstar := quo<AS2 | ImageOfS>;
  A_to_AS2Q := A_to_AS2 * modQstar;
  vprintf EightDescent, 2: "Construction of the norm\n";
  bU := Eltseq(bU);
  t := Cputime();
  NbU := [Norm(b) : b in bU];
// two new lines
   QNF := NumberField(Polynomial([0,1]) : DoLinearExtension);
  S_QNF := {p*MaximalOrder(QNF) : p in S};
  QS2,Q_to_QS2 := pSelmerGroup(2,S_QNF);
  BruinNorm := hom<AS2 -> QS2 | [Q_to_QS2(PowerProduct(NbU,[c mod 2 : c in Eltseq(toVec(g))])) :
                                 g in OrderedGenerators(AS2)]>;
  MyNorm := hom<AS2Q -> QS2 | [BruinNorm(a@@modQstar) : a in OrderedGenerators(AS2Q)]>;
  // MyNorm: A(S,2)/Q(S,2) -> Q(S,2).
  vprintf EightDescent, 2: "%o\n", Cputime(t);
  vprintf EightDescent, 2: "Computing the premiage of c under the norm.\n";
  t := Cputime();
  bool, c1 := HasPreimage(Q_to_QS2(c), MyNorm);
  if bool then
    Ker := Kernel(MyNorm);
    vprintf EightDescent, 2: "%o\n", Cputime(t);
    vprintf EightDescent, 2: "Bound on #Sel after norm condition: 2^%o.\n", 
    Round(Log(#Ker)/Log(2));
    // Representation of the coset c1+Ker:
    _, quomap := quo<AS2Q | Ker>;
    H := <quomap, {quomap(c1)} >;
  else
    vprint EightDescent, 2: "Sel was killed by the norm condition.";
    H := <{},{}>; 
  end if;
  return H, A_to_AS2Q, toVec, bU;
end function;


/***************************************
FakeSelmerSet
Intersection of local images.
****************************************/

function FakeSelmerSet(C4,L,g,Q3,S,H,A_to_AS2Q,toVec,bU)
  // Preliminaries:
  Zx := PolynomialRing(Integers(),4);
  // F := TheMapF(C4,L);
  LL := LinearFormOverEtaleAlgebra(C4,L);
  c := TheConstant(C4,L,Q3); 
  Q1,Q2 := Explode(DefiningPolynomials(C4));
  EightPts := Scheme(Proj(Zx),[Q1,Q2,Q3]);
  // Now we start:
  Sel := H;
  realprecision := 200;  // TO DO : set sensibly
  for p in S do
    if not IsFinite(p) then
      vprintf EightDescent, 2: "\nComputing local image at real place.\n";
      vtime EightDescent, 2: 
        localimage, res_p := LocalImageAtRealPlace(C4,LL,g,realprecision);
    else
      vprintf EightDescent, 2: "\nComputing local image at prime p = %o.\n",p;
      vtime EightDescent, 2: 
        localimage, res_p := LocalImage(C4,LL,p,g);
    end if;
    vprintf EightDescent, 2: 
    "Setting up res_p:A(S,2)/Q(S,2)->Q(S,2) as a homomorphism.\n";
    t := Cputime();
    if not IsFinite(p) then
      // could call res_p here, but this would mean computing the 
      // real roots of the quartic #bU times!
      rl := RealLabels(bU,realprecision);
      // if elements of bU are large, might want to increase real precision 
      lbU := [Codomain(res_p) | x : x in rl];
    else
      lbU := [res_p(b) : b in bU];
    end if;
    AS2Q := Codomain(A_to_AS2Q);
    modQstar := Components(A_to_AS2Q)[2]; // A_to_AS2Q = A_to_AS2 * modQstar.
    // Now Res_p = res_p, but as a homomorphism A(S,2)/Q(S,2) -> Q(S,2).
    Res_p := hom< AS2Q -> Codomain(res_p)| 
      [ &+[v[i]*lbU[i] : i in [1..#v]] where v := Eltseq(toVec(a @@ modQstar)) 
              : a in OrderedGenerators(AS2Q)]>;
    vprintf EightDescent, 2: "%o\n", Cputime(t);
    vprintf EightDescent, 2: 
    "Computing the preimage of the local image under res_p:\n";
    t := Cputime();
    modU := localimage[1]; 
    // modU is the quotient map with the information about the subgroup.
    xi_p := localimage[2]; //the coset representative.
    modURes_p := hom<AS2Q->Codomain(modU) | [modU(Res_p(a)) 
              : a in OrderedGenerators(AS2Q)]>;
    bool, xi := HasPreimage(xi_p, modURes_p);
    if not bool then
      vprintf EightDescent, 1: 
      "Local image doesn't have a preimage under res_p,\
      \ni.e. the preimage is not unramified outside S.\n";
      return {}, _;
    end if;
    V := Kernel(modURes_p);
    // We use the following representation of the coset xi+V:
    _, quomap := quo<AS2Q | V>;
    xiV := <quomap, {quomap(xi)}>; 
    vprintf EightDescent, 2: "%o\n", Cputime(t);
    vprintf EightDescent, 2: "and intersecting with Sel.\n";
    vtime EightDescent, 2: 
    Sel := CosetIntersection(Sel,xiV);
    vprintf EightDescent, 2: "Bound on #Sel now: 2^%o.\
    \nCoset representative: %o\n", Round(Log(#Kernel(Sel[1]))/Log(2)), Sel[2];
    if IsEmpty(Sel[2]) then
      return {}, _;
    end if;
  end for;
  // Sel is a coset, represented as Sel = <quomap,{zeta}>.
  // We want to have it as an actual set.
  quomap, setzeta := Explode(Sel);
  assert #setzeta eq 1; //Only one coset. (not empty: checked before)
  zeta := Rep(setzeta);
  z := zeta @@ quomap;
  U := Kernel(quomap);
  Sel := {z + u : u in U};
  //vprintf EightDescent, 0: "\nWARNING!! Did not check p = infinity.\n\n";
  return Sel, A_to_AS2Q;
end function;


/**********************************************************************
Representation as 2-coverings of C4.
**********************************************************************/

/****************************************************
CorrespondingSubstitution computes the quadriatic 
forms r_i in the equations 
  x_1 = r_1(y_1,...,y_4),
  ... 
  x_4 = r_4(y_1,...,y_4), 
coming from F(P) = xi*y^2.
*****************************************************/

function TheMatrix(L)
  // The matrix M of the coefficients.
  Ms := [Matrix([Eltseq(MonomialCoefficient(Li,Parent(Li).i)) : i in [1..4]])
  : Li in L];
  return HorizontalJoin(Ms);
end function;

function CorrespondingSubstitution(L,xi)
  // L = <L[1],L[2]> or <L[1]>.
  // xi = <xi[1],xi[2]> or <xi[1]> in K1 (x K2).
  // we compute "(xi*y^2) * M^-1" in the following sense:
  M := TheMatrix(L);
  error if not IsInvertible(M), //Should be checked before.
  "ERROR: M is not invertible. Choose a different point on the conic!";
  // The following is like SwapExtension, but over the product of 1 or 2 fields.
  Ks := <BaseRing(Parent(Li)) : Li in L>;
  gs := <DefiningPolynomial(K) : K in Ks>;
  Qy<[y]> := PolynomialRing(Rationals(),4);
  Qyths := [quo<PolynomialRing(Qy) | g/LeadingCoefficient(g)> : g in gs];
  m := [hom<Ks[i] ->Qyths[i] | Qyths[i].1 > : i in [1..#L]];
  gen := <&+[y[i+2*j-1]*Qyths[j].1^i : i in [0..Degree(Ks[j])-1]] : 
  j in [1..#L]>;
  // generic element of K1 (x K2) = y = y_1 + y_2 theta_1 + ...
  rhs := [Eltseq(m[i](xi[i])*gen[i]^2) : i in [1..#L]];
  rhs := Matrix([ChangeUniverse(&cat rhs, Qy)]); // as matrix.
  subst := Eltseq(rhs * ChangeRing(M^-1,Qy)); 
  // We return in addition Norm(y), since we have it already.
  return subst, &*[Norm(gen[i]) : i in [1..#L]];
end function;


/************************************************************************
ThreeQuartics1,2,3 computes the covering maps phi8plus : C8plus -> C4 and 
phi8minus : C8minus -> C4 where the C8plus (resp. C8minus) is given by 
three quartics in P3.
*************************************************************************/

function ThreeQuartics(C4,L,Q3,xi)
  // C4 is the 4-descendent.
  // L are the linear forms defining the tangent planes.
  // Q3 is the third quadric through the 8 points. 
  Qx<[x]> := CoordinateRing(AmbientSpace(C4));
  vprintf EightDescent, 2: 
  "\nComputing the substitution corresponding to xi = %o.\n",xi;
  subst, NormOfy := CorrespondingSubstitution(L,xi);
  vprintf EightDescent, 2: "Computing the first two quartics.\n";
  G1, G2 := Explode([Evaluate(f,subst) : f in DefiningPolynomials(C4)]);
  // G1 and G2 are two quartics, which define C8'. 
  // C8' consists of the two components C8plus and C8minus.
  // They are separated by a third quartic, which comes from 
  // the norm condition (L1L2L3L4 = c*Q3^2).
  // Since L1L2L3L4 = Norm(xi*y^2), this is equiv. to 
  // Norm(xi)*(Norm(y))^2 = c*Q3^2, and since Norm(xi) = c*a^2 for some a,
  // equiv. to a*Norm(y) = +/- Q3(subst).
  c := TheConstant(C4,L,Q3);
  b := &*[Norm(xi[i]) : i in [1..#xi]]/c;
  vprintf EightDescent, 2: "Computing the square root of Norm(xi)/c.\n";
  bool, a := IsSquare(b);
  assert bool; // Norm(xi) = c*a^2.
  vprintf EightDescent, 2: "Computing the third quartic.\n";
  G3plus := a*NormOfy + Evaluate(Q3,subst);
  vprintf EightDescent, 3: "Magma is checking that C8plus is a curve...\n";
  vtime EightDescent, 3: 
  C8plus := Curve(AmbientSpace(C4),[Qx|G1,G2,G3plus]);
  G3minus := a*NormOfy - Evaluate(Q3,subst);
  vprintf EightDescent, 3: "Magma is checking that C8minus is a curve...\n";
  vtime EightDescent, 3: 
  C8minus := Curve(AmbientSpace(C4),[Qx|G1,G2,G3minus]);
  C8plus`Reduced := true; C8minus`Reduced := true; 
  C8plus`GeometricallyIrreducible := true; C8minus`GeometricallyIrreducible := true; 
  C8plus`Nonsingular := true; C8minus`Nonsingular := true;
  phi1 := map<C8plus ->C4 | subst : Check:=false>;
  phi2 := map<C8minus->C4 | subst : Check:=false>;
  return [phi1,phi2];
end function;


/****************************************************************************
Putting everything together: EightDescent
****************************************************************************/

intrinsic EightDescent(C4::Crv : StopWhenFoundPoint:=false, 
                                 BadPrimesHypothesis:=false, 
		                 DontTestLocalSolvabilityAt:={},
 		                 NormalCurve:=true,
 		                 Union:=false)
       -> SeqEnum, SeqEnum
{Performs a 2-descent on an intersection of two quadrics C4 (as obtained by a FourDescent). Returns all the locally solvable 2-coverings of C4}
  
  // StopWhenFoundPoint: 
  // When turned on, stops if it happens to find a 
  // point on C4 during the 8-descent, and returns this point.
  
  // BadPrimesHypothesis:
  // If set to true, then the program assumes that the set of bad
  // primes consists just of 
  // S1 = prime divisors of 2*c*disc(g), and 
  // S2 = primes dividing the norms of all coefficients of L1 (and L2).
  // The primes coming from projection of the singular subscheme of P_8
  // to Spec(Z) are disregarded.

  // DontTestLocalSolvabilityAt:
  // A set of primes, at which local solvability is not tested.
  // You can test the resulting curves in the end for local solvability
  // if you want. E.g. with IsLocallySolvable(Projection(C8):Smooth);

  // NormalCurve:
  // Computes 20 quadrics defining a genus one normal curve in P^7,
  // and then minimises and reduces. (If false, computes 3 quartics 
  // defining an essentially random projection of this curve to P^3,
  // and makes no attempt at minimisation and reduction.)

  // Union:
  // Computes the union of C8^+ and C8^- instead of each of the
  // curves individually

//////

  require IsQuadricIntersection(C4) : 
         "The given curve must be an intersection of quadrics in P^3";
  P3<[x]> := Ambient(C4); // for nicer output.
  Original_C4 := C4;
  if BaseRing(C4) cmpeq Integers() then 
    C4 := ChangeRing(C4,Rationals()); 
  end if;
  require BaseRing(C4) cmpeq Rationals() :
         "The given curve must defined over the rationals";
  model0 := GenusOneModel(C4);
  model1,tr1 := Minimise(model0);
  model2,tr2 := Reduce(model1);
  tr := tr2*tr1;
  C4 := Curve(model2);
  A<theta>, iso, g := EtaleAlgebra(C4);
  require g/LeadingCoefficient(g) eq Parent(g)!Modulus(A) :
         "Something is wrong with the etale algebra.";
  vprintf EightDescent,1: 
         "The etale algebra is A = Q[T]/(g(T)) where g = %o\n", g;
  g := ChangeRing(g,Integers());
  require not HasRoot(g, Rationals()) :
         "The 2-covering below the given 4-covering has a Q-rational Weierstrass point."*
         "\nEightDescent is not implemented in this situation";

  // for nicer output we assign the names theta_1 and theta_2:
  K1<theta_1> := Codomain(iso)[1];
  vprintf EightDescent,1: "It is isomorphic to ";
  if #iso(theta) eq 2 then
    K2<theta_2> := Codomain(iso)[2];
    vprintf EightDescent,1: 
    "K_1\\times K_2 where K_1 = Q[T]/(%o) and K_2 = Q[T]/(%o).\n",
    DefiningPolynomial(K1), DefiningPolynomial(K2);
  else
    vprintf EightDescent,1: "K_1 where K_1 = Q[T]/(%o).\n",
    DefiningPolynomial(K1);
  end if;
  Qsing := SingularQuadricsInThePencil(C4);
  vprintf EightDescent,1: "The singular quadrics in the pencil are \n%o ", 
  DefiningPolynomial(Qsing[1]);
  if #Qsing eq 2 then
    vprintf EightDescent,1: "and\n%o ", DefiningPolynomial(Qsing[2]);
  end if;
  vprintf EightDescent,1: "and their conjugates.\n";
  vprintf EightDescent,4: "As symmetric matrices: \n%o\n",
                          <SymmetricMatrix(DefiningPolynomial(C)) : C in Qsing>;
  vprintf EightDescent,2: "\nComputation of the tangent planes.\n";
  ts := [TangentPlaneAt(Q) : Q in Qsing];
  L := <DefiningPolynomial(t) : t in ts>; // The linear forms for the map F.
  if not IsInvertible(TheMatrix(L)) and StopWhenFoundPoint then
    vprintf EightDescent,2: 
           "Checking the intersection of the four planes with C4 for Q-rational points.\n";
    trivialpts := Points(Scheme(C4, &*[Qx!ProductOfConjugates(Li) : Li in L]))
                                        where Qx := CoordinateRing(Ambient(C4));
    if not IsEmpty(trivialpts) then
      vprintf EightDescent,1: "Tangent planes meet C4 in a rational point:\n";
      return trivialpts, _;
    end if;
  end if;
  while not IsInvertible(TheMatrix(L)) do
    vprint EightDescent, 2 : "M is not invertible.";
    L := <DifferentTangentPlane(Qsing[i],L[i]) : i in [1..#L]>;
    vprintf EightDescent, 2 : "We chose a different point. \nNow L = %o\n", L;
  end while;
  vprintf EightDescent,2: "Computing the third quadric ... \n";
  vtime EightDescent,2: 
  Q3 := ThirdQuadric(C4,L); 
  vprintf EightDescent,1: "The third quadric in the pencil is \n%o.\n", Q3;
  vprintf EightDescent,4: "As symmetric matrix: \n%o\n", SymmetricMatrix(Q3);
  c := TheConstant(C4,L,Q3); 
  vprintf EightDescent,1: "The constant in L_1L_2L_3L_4 = c*Q3^2 is \nc = %o.\n", c;
  vprintf EightDescent,1: "\nComputing the bad primes (and factoring c) ...\n";
  t := Cputime();
  S := MyBadPrimes(C4,L,Q3 : BadPrimesHypothesis := BadPrimesHypothesis);
  vprintf EightDescent,1: "Time: %o for computing the set of bad primes.\n", Cputime(t);
  vprintf EightDescent,1: "The set of bad primes is %o.\n", S; 
  vprintf EightDescent,1: 
       "\nComputing the subset H of A(S,2)/Q(S,2), fulfilling the norm condition.\n";
  t := Cputime();
  H,A_to_AS2Q,toVec,bU := TheSetH(C4,c,S);
  vprintf EightDescent,1: "Time: %o for computing the set H.\n", Cputime(t);
  // if H is empty then we can stop.
  if IsEmpty(H[2]) then
    return [], [];
  end if;
  vprintf EightDescent,1: "\nComputing the intersection of the local images\n"; 
  S := S diff DontTestLocalSolvabilityAt;
  if not IsEmpty(DontTestLocalSolvabilityAt) then
    vprintf EightDescent,1: 
      "Not testing local solvability at %o.\n", DontTestLocalSolvabilityAt;
  end if;
  S := Sort(SetToSequence(S)) cat [Infinity()]; 
  t := Cputime();
  Sel, mSel := FakeSelmerSet(C4,L,g,Q3,S,H,A_to_AS2Q,toVec,bU); 
  vprintf EightDescent,1: 
         "Time: %o for computing the intersection of the local images\n", Cputime(t);
  Xi := {iso(xi @@ mSel) : xi in Sel};
  vprintf EightDescent,1: "The fake Selmer set has cardinality %o\n", #Xi;
  vprintf EightDescent,2: "The fake Selmer set consists of \n%o\n", Xi;

// Added new NormalCurve option
  if NormalCurve then 
    maps := EightCoverings(C4,L,Xi,Qsing,Union); // "8coverings.m"
  else
    maps := &cat[ThreeQuartics(C4,L,Q3,xi) : xi in Xi];
  end if;

  // basic sanity check
  error if not (#maps eq 0 or 2^Ilog(2,#maps) eq #maps),
       "EightDescent: number of covers obtained is not a power of 2";

  // going back to original C4
  iso := TransformationToMap(model0,model2,tr
		:Domain := C4,Codomain := Original_C4);
  maps := [mp*iso: mp in maps];

  return [Domain(mp) : mp in maps], maps;
end intrinsic;

intrinsic EightDescent(model::ModelG1 : StopWhenFoundPoint:=false, 
                                 BadPrimesHypothesis:=false, 
		                 DontTestLocalSolvabilityAt:={},
 		                 NormalCurve:=true,
 		                 Union:=false)
       -> SeqEnum, SeqEnum
{"} //"
  require Degree(model) eq 4 : "Genus one model should have degree 4";
  return EightDescent(Curve(model) : 
    StopWhenFoundPoint:=StopWhenFoundPoint,
    BadPrimesHypothesis:=BadPrimesHypothesis, 
    DontTestLocalSolvabilityAt:=DontTestLocalSolvabilityAt,
    NormalCurve:=NormalCurve,
    Union:=Union);
end intrinsic;

/*********************************
How to get the 20 quadrics in P^7.
**********************************/

// function TwentyQuadrics(C8) 
//   // Another good name would be QuadricIntersection.
//   // C8 is the eightdescendent given by three quartics
//   D := Divisor(C8, Scheme(C8,C8.1));
//   phi_D := DivisorMap(D);
//   C20<[y]> := Image(phi_D);
//   return C20, phi_D;
// end function;
