freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!
/*******************************************
 * Hyperelliptic/reduce.m                  *
 *                                         *
 * SL_2(Z)-reduction of binary forms       *
 *                                         *
 * Michael Stoll                           *
 *                                         *
 * started 17-Sep-1999                     *
 *******************************************/

 /*

   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
   (nothing to do)

   Michael Stoll, 2001-09-18

     Fixed a couple of typos in the comments, plus
     a bug in Covariant -- the polynomial has to be made monic.

   Michael Stoll, 2002-03-07

     Replaced IsSquarefree(pol) by Discriminant(pol) ne 0 in
     Covariant for pols over the reals (IsSquarefree leads to
     trashing on my machine in this case...)

  Nicole Sutherland 2008-12-12

     Replaced use of FldPrElt by FldComElt

  Steve Donnelly, 2009-03

     Use step length < 1 in the Newton iteration in Covariant
     where necessary to get convergence.  Otherwise infinite loop for
     -31*x^6 + 276*x^5 - 12*x^4 - 3982*x^3 + 108*x^2 + 20808*x + 20277


  Michael Stoll, 2016-05-25

    Prompted by a bug report from Andrew Sutherland:

    Introduced PreliminaryReduction, which performs an ad-hoc preliminary
    partial reduction by trying to get the roots well-distributed.

    PreliminaryReduction is called by Covariant (unless explicitly
    told not to via the Preliminary optional argument)
    and by Reduce as a first step in the process.

    Covariant uses Q_0-reduction to get the initial value for
    the iteration unless an explicit initial value is given.

    Covariant signals an error if no convergence is obtained
    after 100 iterations.

    Some cleaning up in Reduce.

  ------------------------------------------------------------------*/


// Declarations

declare verbose CrvHypReduce, 3;

// Given a (squarefree) binary form in 2 variables of degree d,
//  F(x,z) = a_0 x^d + a_1 x^(d-1) z + ... + a_d z^d,
// with integral (or rational or real) coefficients,
// we would like to find a transform
//  G(x,z) = F(ax + bz, cx + dz) with (a,b; c,d) in SL_2(Z)
// of F, which is as `small' as possible.

// In order to achieve this, we associate to F a positive
// definite covariant quadratic form (up to a constant factor),
//  Phi(F)(x,z) = a(F) x^2 + b(F) x z + c(F) z^2,
// where `covariant' means that (with G as above)
//  Phi(G)(x,z) = (const) Phi(F)(ax + bz, cx + dz) .
// We then use the well-known reduction theory for pos. def.
// quadratic forms (i.e. we are shifting its root in the
// upper half-plane into the well-known fundamental domain
// of SL_2(Z)).

// We define a first Phi_0(F) as follows.
// If a_0 is nonzero, we write F(x,1) = a_0 f(x) and put
//  Phi_0(F) = SUM_r (x - r z)(x - r' z)/|f'(r)|^(2/(d/2))
// where the sum is over the (complex) roots r of f and
// where r' denotes the complex conjugate of r.
// If a_0 = 0, we must have a_1 /= 0; we write
// F(x,1) = a_1 f(x) and put
//  Phi_0(F) = z^2 + SUM_r (x - r z)(x - r' z)/|f'(r)|^(2/(d/2))
// with the same notation as before.

// A better Phi (``Julia's covariant'') is described in
//  M. Stoll, J.E. Cremona: On the reduction theory of binary forms,
//  J. reine angew. Math. 565, 79-99 (2003)


function FindZero(f, x0, x1, eps)
  vprintf CrvHypReduce, 3:
          "FindZero: x0 = %o, x1 = %o, eps = %o\n", x0, x1, eps;
  f0 := f(x0); f1 := f(x1);
  x2 := 0.5*(x0+x1); f2 := f(x2);
  while Abs(f2) gt eps and Abs(x0 - x1) gt eps do
    if f0*f2 gt 0 then
      x0 := x2; f0 := f2;
    else
      x1 := x2; f1 := f2;
    end if;
    x2 := 0.5*(x0+x1); f2 := f(x2);
    vprintf CrvHypReduce, 3: "  x = %o, f(x) = %o\n", x2, f2;
  end while;
  return x2;
end function;

function Distinctify(A)
  B:=[ComplexField()|];
  for x in A do
    for i in [1..x[2]] do
      Append(~B,x[1]);
    end for;
  end for;
  return B;
end function;

// Michael Stoll, 2016-05-25:
// The following function does some preliminary reduction steps;
// it transforms the polynomial by an element of SL(2,Z) such
// that the roots are reasonably evenly distributed.
// It returns the partially reduced polynomial and the transformation matrix.
function PreliminaryReduction(d, pol)
  vprintf CrvHypReduce, 2: "Preliminary reduction...\n";
  // keep track of transformations
  G := SL(2, Integers());
  transmat := G!1;
  repeat
    changed := false;
    roots := Distinctify(Roots(pol, ComplexField()));
    // Maximum absolute Value of a root
    maxroot := Max([Modulus(r) : r in roots]);
    // Find mean of the roots, rounded to nearest integer
    rootmean := Round(Real(&+roots)/#roots);
    // Maximum distance of a root from the rounded mean
    maxdist := Max([Modulus(r-rootmean) : r in roots]);
    if maxdist lt maxroot then
      // shift
      pol := Evaluate(pol, Parent(pol).1 + rootmean);
      vprintf CrvHypReduce, 3: "shift by %o -->\n%o\n", rootmean, pol;
      transmat := transmat*G![1, rootmean, 0, 1];
      maxroot := maxdist;
      changed := true;
    end if;
    if maxroot lt 0.99 then
      // invert: pol -> +-x^d pol(-1/x)
      pol := Parent(pol)![(-1)^n*Coefficient(pol, d-n) : n in [0..d]];
      vprintf CrvHypReduce, 3: "invert -->\n%o\n", pol;
      transmat := transmat*G![0, -1, 1, 0];
      changed := true;
    end if;
  until not changed;
  return pol, transmat;
end function;

function moebius(mat, x)
  return (mat[1,1]*x + mat[1,2])/(mat[2,1]*x + mat[2,2]);
end function;

intrinsic Covariant(d::RngIntElt, pol::RngUPolElt
                    : Simple := false, Init := [], Preliminary := true) -> FldComElt, FldComElt
{Given a degree d binary form F(x,z) with real coefficients,
 represented by d and pol = F(x,1) such that F is squarefree,
 returns its covariant in the upper half-plane. If Simple is set,
 the easier to compute Q_0-covariant is returned. Otherwise, the value
 of theta(pol) is returned as a second value.}
    require Degree(pol) in {d, d-1} : "";
    vprintf CrvHypReduce, 2:
            "%o-Covariant of degree %o form given by\n %o\n",
            Simple select "Q_0" else "Julia", d, pol;
    if Preliminary then
      // Do some preliminary reduction.
      pol, transmat := PreliminaryReduction(d, pol);
    else
      transmat := SL(2, Integers())!1;
    end if;
    // Work over the reals
    PR := PolynomialRing(RealField() : Global := false); x := PR.1;
    pol := PR!Eltseq(pol);
    lcf := LeadingCoefficient(pol);
    // normalize pol
    pol *:= 1/lcf;
    polD := Derivative(pol);
    // get complex roots as a sequence of Degree(pol) elements
    roots := Distinctify(Roots(pol, ComplexField()));
    vprintf CrvHypReduce, 2: " Roots: %o\n", roots;
    if Simple or IsEmpty(Init) then
      // Compute the Q_0-invariant (see Stoll&Cremona)
      cov := &+[ (x^2 - 2*Real(r)*x + Modulus(r)^2)
                  * 1/Modulus(Evaluate(polD, r))^(2/(d-2)) : r in roots ];
      // Take root at infinity into account when degree is less than d
      if Degree(pol) lt d then cov +:= PR!1; end if;
      a := Coefficient(cov, 2);
      b := Coefficient(cov, 1);
      c := Coefficient(cov, 0);
      // covariant is root if the quadratic in the upper half plane
      cov := (-b + (ComplexField().1)*Sqrt(Abs(b*b-4*a*c)))/(2*a);
      if Simple then
        vprintf CrvHypReduce, 2: "==> Covariant = %o\n", cov;
        return moebius(transmat, cov), _;
      else
        // Use the simple covariant as starting point,
        // when no initial value is given
        Init := [Real(cov), Imaginary(cov)^2];
      end if;
    else
      // Transform given initial value according to transmat
      init := ComplexField()![Init[1], Sqrt(Init[2])];
      init := moebius(transmat^-1, init);
      Init := [Real(init), Imaginary(init)^2];
    end if;
    // Now compute Julia's covariant
    eps := 1.0e-10; // tolerance for norm of gradient and for decrease of value
    rr := [ RealField() | r : r in roots | IsReal(r) ]; // the real roots
    rc := [ r : r in roots | not IsReal(r) ];           // the genuine complex roots
    rc := [ rc[j] : j in [1..#rc by 2] ]; // representatives mod conjugation
    PR2<t,u> := PolynomialRing(RealField(), 2);
    polr := &*[ PR2 | (t - r)^2 + u : r in rr ];
    polc := &*[ PR2 | t^2 - 2*Real(r)*t + Modulus(r)^2 + u : r in rc ];
    // Let F = polr*polc^2 = prod_r ((t - r)(t - bar(r)) + u) (r in roots).
    // Then pol1 = dF/dt and pol2 = u^(d/2+1)*d/du(F*u^(-d/2)).
    // We want to find (t,u) such that pol1(t,u) = pol2(t,u) = 0.
    pol1 := (Derivative(polr,1)*polc + 2*Derivative(polc,1)*polr)*polc;
    pol2 := (u*(Derivative(polr,2)*polc + 2*Derivative(polc,2)*polr)
             - d/2*polr*polc)*polc;
    // Find second derivatives for Newton's method
    pol11 := Derivative(pol1,1);
    pol12 := Derivative(pol2,1);
    pol22 := u*Derivative(pol2,2) - (d/2+1)*pol2;

    // Find minimum of polr*polc^2/u^(d/2) in R x R_+
    // Use Newton iteration if possible
    vprintf CrvHypReduce, 2: "  starting iteration...\n", pol;
    tu := Init; // given initial value or coming from Q_0-covariant
    val0 := Evaluate(polr, tu)*Evaluate(polc, tu)^2/tu[2]^(d/2);
    loopcount := 0;
    repeat
      // Evaluate second derivatives of F/u^(d/2) at (t,u)
      df11tu := Evaluate(pol11, tu)/tu[2]^(d/2);
      df12tu := Evaluate(pol12, tu)/tu[2]^(d/2+1);
      df21tu := df12tu;
      df22tu := Evaluate(pol22, tu)/tu[2]^(d/2+2);
      det := df11tu*df22tu - df12tu*df21tu;
      // Evaluate first derivatives
      f1tu := Evaluate(pol1, tu)/tu[2]^(d/2);
      f2tu := Evaluate(pol2, tu)/tu[2]^(d/2+1);
      // Find shift: dftu^(-1) * ftu
      d1tu := (df22tu*f1tu - df12tu*f2tu)/det;
      d2tu := (-df21tu*f1tu + df11tu*f2tu)/det;
      // New approximation
      // (try step length = 1/s in case of divergence -- SRD)
      for s in [1,2,4,10] do
        tu1 := [ tu[1] - d1tu/s, tu[2] - d2tu/s ];
        val := tu1[2] gt 0
               select Evaluate(polr, tu1)*Evaluate(polc, tu1)^2/tu1[2]^(d/2)
               else 0;
        if tu1[2] gt 0 and val lt val0 then
          if s ne 1 then loopcount -:= 1; end if; // don't count small steps
          break;
        end if;
      end for;
      vprintf CrvHypReduce, 3: "  New approx: %o\n", tu;
      vprintf CrvHypReduce, 3: "   val = %o\n", val;
      vprintf CrvHypReduce, 3: "   grad = %o\n", [f1tu, f2tu];
      if tu1[2] le 0 or val gt val0*(1.0+eps) then
        vprintf CrvHypReduce, 3: "   Divergence!\n";
//         loopcount := 0; // keep counting, to be on the safe side...
        fun := func<x | f1tu*ft + f2tu*fu
                        where ft := Evaluate(pol1,tu0)/tu0[2]^(d/2)
                        where fu := Evaluate(pol2,tu0)/tu0[2]^(d/2+1)
                        where tu0 := [tu[1] - x*f1tu, tu[2] - x*f2tu] >;
        // find zero of fun; first find sign change
        fun0 := fun(0.0);
        if f2tu le 0.0 then
          x1 := 1.0;
          while fun(x1)*fun0 gt 0 do
            x1 +:= 1.0;
            vprintf CrvHypReduce, 3: "*";
            end while;
          vprintf CrvHypReduce, 3: "\n";
        else
          x1m := tu[2]/f2tu;
          x1 := 0.5*x1m;
          while fun(x1)*fun0 gt 0 do
            x1 := 0.5*(x1 + x1m);
            vprintf CrvHypReduce, 3: "*";
          end while;
          vprintf CrvHypReduce, 3: "\n";
        end if;
        xn := FindZero(fun, 0.0, x1, eps);
        tu := [tu[1] - xn*f1tu, tu[2] - xn*f2tu];
        val0 := Evaluate(polr, tu)*Evaluate(polc, tu)^2/tu[2]^(d/2);
        vprintf CrvHypReduce, 3: "    New approx: %o\n", tu;
        vprintf CrvHypReduce, 3: "    val = %o\n", val0;
        d1tu := 1.0+eps;
      else
        tu := tu1;
        val0 := val;
        loopcount +:= 1;
      end if;
    until Max(Abs(d1tu), Abs(d2tu)) lt eps or loopcount gt 100;
    error if loopcount gt 100, "Covariant: No convergence reached.\n";
    cov := tu[1] + Sqrt(-tu[2]);
    vprintf CrvHypReduce, 2: "==> Covariant = %o\n", cov;
    return moebius(transmat, cov), Modulus(lcf)^2*val0;
end intrinsic;


intrinsic Reduce(d::RngIntElt, pol::RngUPolElt : Simple := false)
  -> RngUPolElt, GrpMatElt
{Given a degree d binary form F(x,z) with real coefficients,
 represented by pol = F(x,1) of degree d such that F is squarefree,
 returns a GL_2(Z)-equivalent form (in dehomogenized form) and
 the transformation matrix (an element of GL_2(Z)).
 If Simple is set, Q_0-reduction is used.}
    require Degree(pol) in {d, d-1} :
            "Data must specify a squarefree binary form.";
    require d ge 3: "The degree must be at least 3.";
    // If degree is at most 4, both notions of reduction are the same.
    if d le 4 then Simple := true; end if;

    // first do preliminary reduction
    pol, transmat := PreliminaryReduction(d, pol);

    // Using real precision 100 seems to avoid division by zero in Covariant
    external_real_field := GetDefaultRealField();
    if Precision(external_real_field) lt 100 then
      SetDefaultRealField(RealField(100));
    end if;

    eps := 1.0e-20;
    vprintf CrvHypReduce:
            "%o-Reduce(%o, %o):\n", Simple select "Q_0" else "Julia", d, pol;
    G := SL(2, Integers());
    P := Parent(pol); X := P.1;
    P2 := PolynomialRing(CoefficientRing(P), 2);
    x := P2.1; z := P2.2;
    // Homogenize the polynomial
    polh := &+[ Coefficient(pol, k)*x^k*z^(d-k) : k in [0..d] ];
    // Initialize transformation matrix
    mat := G!transmat;
    // Compute covariant
    cov := Covariant(d, Evaluate(polh, [X, 1])
                      : Simple := Simple, Preliminary := false);
    count := 5;
    repeat
      if count eq 0 then
        // Recompute covariant every five steps, to counter precision loss
        cov := Covariant(d, Evaluate(polh, [X, 1])
                          : Simple := Simple, Preliminary := false,
                            Init := [ Real(cov), Imaginary(cov)^2 ]);
        count := 5;
      else
        count -:= 1;
      end if;
      vprintf CrvHypReduce:
              "  %o-cov = %o\n", Simple select "Q_0" else "Julia", cov;
      // do a shift to bring the real part into interval [-1/2, 1/2]
      s := Round(Real(cov));
      cov -:= s;
      m := G![1, s, 0, 1];
      polh := Evaluate(polh, [x + s*z, z]);
      mat := mat*m;
      vprintf CrvHypReduce: "  shift = %o -->\n   pol = %o\n   mat = %o\n",
                            s, polh, Eltseq(mat);
      // do an inversion if necessary
      if Modulus(cov) lt 1 then
        m := G![0, -1, 1, 0];
        cov := -1/cov;
        polh := Evaluate(polh, [-z, x]);
        mat := mat*m;
        vprintf CrvHypReduce: "  invert -->\n   pol = %o\n   mat = %o\n",
                              polh, Eltseq(mat);
      end if;
      if 2*Abs(Real(cov)) le 1 and Modulus(cov) ge 1
          and not(2*Abs(Real(cov)) lt 0.99 and Modulus(cov) gt 1.01)
      then
        // Recompute covariant if near boundary
        cov := Covariant(d, Evaluate(polh, [X, 1])
                          : Simple := Simple, Preliminary := false,
                            Init := [ Real(cov), Imaginary(cov)^2 ]);
        count := 5;
      end if;
    until 2*Abs(Real(cov)) le 1+eps and Modulus(cov) ge 1-eps;

    SetDefaultRealField(external_real_field);

    return Evaluate(polh, [X, 1]), mat;
end intrinsic;

intrinsic Reduce(pol::RngUPolElt, d::RngIntElt : Simple := false) -> RngUPolElt, GrpMatElt
{"} // "
    return Reduce(d, pol : Simple := Simple);
end intrinsic;

intrinsic Reduce(pol::RngUPolElt : Simple := false) -> RngUPolElt, GrpMatElt
{"} // "
    return Reduce(Degree(pol), pol : Simple := Simple);
end intrinsic;

