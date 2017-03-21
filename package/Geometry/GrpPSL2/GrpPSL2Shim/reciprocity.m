freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Shimura reciprocity law
// May 2006, June 2007, John Voight
//
//////////////////////////////////////////////////////////////////////////////

declare attributes AlgAssVOrd : SplitNegativeUnit;

import "2F1.m" : HypergeometricReversion;
import "../../CrvEll/heegnernew.m" : recognise_polynomial_over_Q;

intrinsic ShimuraConjugates(mu::AlgAssVOrdElt) -> SeqEnum
  {Returns the set of conjugates of mu under the Shimura reciprocity law.}

  O := Parent(mu);
  A := Algebra(O);
  require Type(A) eq AlgQuat : 
    "Argument must be an element of a quaternionic order";

  // Should check here if mu is primitive!
  Z_F := BaseRing(O);
  F := BaseField(A);
  Z_K := ext<Z_F | MinimalPolynomial(mu)>;
  K := NumberField(Z_K);
  f := Conductor(Z_K);
  G, m := RingClassGroup(K, Z_F!!Norm(f));
  
  conjs := [<G ! 0, A ! 1>];

  for sigma in G do
    if sigma ne G ! 0 then
      frakq := m(sigma);
      q := Abs(Norm(Norm(frakq)));

      iotaK := hom<K -> A | mu>;
      I := rideal<O | [iotaK(g) : g in Generators(frakq)]>;
      Gamma := FuchsianGroup(O);
      bl, xi := IsPrincipal(I, Gamma : Strict := true);
      if not bl then
        error "Principal ideal not found?!";
      end if;

      Append(~conjs,<sigma,xi>);
    end if;
  end for;

  return conjs;
end intrinsic;

RecognizeConjugates := function(conjs);
  CC := Parent(conjs[1]);
  PCC := PolynomialRing(CC);
  fMu := &*[ PCC.1 - conjs[i] : i in [1..#conjs]];
  fMues := Eltseq(fMu);
  fMuesrat := [];
  for i := 1 to #fMues do
    cf := Convergents(ContinuedFraction(Re(fMues[i])));
    fMuesrat[i] := cf[1,1]/cf[2,1];
  end for;
  return PolynomialRing(Rationals()) ! fMuesrat;
end function;

intrinsic CMPoints(G::GrpPSL2, mu::AlgAssVOrdElt : Precision := 0) -> RngUPolElt, SeqEnum
  {Returns the minimal polynomial of the Galois conjugates of the CM points 
   corresponding to mu and their complex values.  The polynomial returned
   is not guaranteed; the coefficients are rational approximations.}

  muconjs := ShimuraConjugates(mu);
  if Precision eq 0 then
    Precision := 100*#muconjs;
  end if;
  G`MatrixRepresentation := FuchsianMatrixRepresentation(Algebra(BaseRing(G)) : 
                                 Precision := Precision);
  U, _, m := Group(G);
  H := UpperHalfPlane();
  D := Universe(G`ShimFDDisc);
  D`prec := Precision;
  prootH := FixedPoints(G!m(U.1), H)[1];
  qrootH := FixedPoints(G!m(U.2), H)[1];
  rrootH := FixedPoints(G!m(U.3), H)[1];
  G`TriangleHRoots := [prootH, qrootH, rrootH];
  G`TriangleDRoots := [PlaneToDisc(D, z) : z in G`TriangleHRoots];

  z := FixedPoints(G!mu, UpperHalfPlane())[1];
  zs := [(G!(xi[2]^(-1)))*z : xi in muconjs];

  js := HypergeometricReversion(G, zs);

  if #js eq 1 and Abs(js[1]) gt 10^Precision(Parent(js[1])) then
    return 1/PolynomialRing(Rationals()).1, js;
  end if;

  CC := Parent(js[1]);
  PCC := PolynomialRing(CC);
  fMu := &*[ PCC.1 - j : j in js];
  bl, fMu := recognise_polynomial_over_Q(fMu);  
  if not bl then
    fMu := RecognizeConjugates(js);
  end if;

  // One possible sanity check: For the first 100 applicable primes,
  // check that the polynomial has the right splitting behavior.
  // We content ourselves with simply verifying that the polynomial
  // has smooth discriminant. 
  if Degree(fMu) eq 1 then
    df := Roots(fMu, Rationals())[1][1];
    df := Numerator(df)*Denominator(df);
  else
    df := Numerator(disc)*Denominator(disc) where disc is Discriminant(fMu);
  end if;
  Fdf, _, unfactored := Factorization(df : ECMLimit := 0, MPQSLimit := 0);
  if assigned unfactored then // df was not smooth enough 
    error "Minimal polynomial is not recognizable--increase precision";
  end if;

  return fMu, js;
end intrinsic;
