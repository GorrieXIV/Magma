freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//   INTEGRAL POINTS ON ELLIPTIC CURVES OVER NUMBER FIELDS        //
//                                                                //
//   Steve Donnelly, November 2013                                //
//                                                                //
////////////////////////////////////////////////////////////////////

// TO DO
// remove checks when overQ
// torsion


import "sintpoints.m" :
        best_delta,
        CheckPointsWithBoundedHeight;


//////////////////////////////////////////////////////////////////////
// Utility
//////////////////////////////////////////////////////////////////////

intrinsic IsSIntegral(P::PtEll[FldAlg], S::Setq) -> BoolElt
{True iff P is not the identity and has S-integral (affine) coordinates}

   if P[3] eq 0 then
      return false;
   end if;
   assert P[3] eq 1;

   ZF := Integers(Ring(Parent(P)));

   if IsEmpty(S) then
      return P[1] in ZF and P[2] in ZF;
   else
error "Not implemented";
      S := LCM(S);
   end if;
end intrinsic;


//////////////////////////////////////////////////////////////////////
// Bounds
//////////////////////////////////////////////////////////////////////

function reduce_height_bound_one_step_at_v
         (E, Omega, height_pairing, t, tlogs, canon_height_bound, v)

overQ, CQ := CanChangeUniverse(Coefficients(E), Rationals());
if overQ then
EQ := EllipticCurve(CQ);
end if;

    // Lattice 
    // Z^(r+1) = {[P,n] : P in gens, n in Z}
    // with
    // norm([P,n]) = Height(P) + C*|Log(P)/Omega + n/t|^2

    // TO DO: in calling function
    r := Nrows(height_pairing);
    R := BaseRing(height_pairing);
assert IsIdentical(R, Parent(tlogs[1,v]));
    M := MatrixRing(R, r+1) ! 1;
    M[r+1,r+1] := 1/t;
    for i in [1..r] do
      M[i,r+1] := tlogs[i,v]/t;  // = Log(P_i)/Omega
    end for;

    delta := best_delta(M, height_pairing, canon_height_bound);
    delta *:= Omega;

    // Convert lower bound on delta = Log(P) to upper bound on Log(x(P))
    if delta lt 10^-20 then
       // EllipticExponential throws silly bug when too close to 0
       xbound := 1000 + Round(1/delta^2);
    else
       deltaC := ComplexField(Precision(Parent(delta)))! delta;
       xbound := Real(EllipticExponential(E, v, deltaC)[1]);
if overQ then
assert 
 Abs(xbound - Real(EllipticExponential(EQ, deltaC)[1]))
 lt 10^(-Precision(BaseRing(height_pairing)) div 2);
end if;
    end if;
 
    return Log(Max(1, xbound));

end function;


function reduced_canonical_height_bound(E, gens, bound0, S)

overQ, CQ := CanChangeUniverse(Coefficients(E), Rationals());
if overQ then
EQ := EllipticCurve(CQ);
end if;

  F := BaseField(E);
  rF, sF := Signature(F);
assert sF eq 0;

  r := #gens;
assert #S eq 0;

  // This prec is needed for the first reduction step (??)
  // TO DO: it can be reduced for the subsequent steps
  prec := 2*(r+1)*Ilog(10, bound0) + 100;
  assert prec ge 100;
  R  := RealField(prec);
  RR := RealField(6);

  height_pairing := HeightPairingMatrix(gens : Precision:=prec); // TO DO: sensible prec
  eigenvalues := [tup[1] : tup in Eigenvalues(height_pairing)];
  assert #eigenvalues eq r;

  lambda := Min(eigenvalues);
  lambda := lambda * 0.99; // for roundoff error
  assert lambda gt 0;

  cps_l, cps_u := CPSHeightBounds(E);  // TO DO: enough precision for correct bounds
  canon_minus_naive := R! -cps_l * Degree(F);
  naive_minus_canon := R!  cps_u * Degree(F);
assert canon_minus_naive ge 0;
assert naive_minus_canon ge 0;
  vprintf IntegralPoints: "Height difference bounds: %o, %o\n", 
                           RR! canon_minus_naive,
                           RR! naive_minus_canon;

  canon_height_bound := bound0;
  naive_height_bound := canon_height_bound + naive_minus_canon;

  // handle egg (trivially)
  t := 2;
  a1,a2,a3,a4,a6 := Explode(Coefficients(E));
  xpol := [1/4*a3^2 + a6, 1/2*a1*a3 + a4, 1/4*a1^2 + a2, 1];
  b_egg := [R| ];
  for v in [1..rF] do
    xpolv := Polynomial([Conjugate(c, v) : c in xpol]);
    max_rt := Max([Abs(tup[1]) : tup in Roots(xpolv)]);
    b_egg[v] := Max(0, Log(max_rt));
  end for;

  // TO DO : torsion

  // Logs of gens

  eps := 10 ^ (-prec div 2);

  Omega_R := [R| ];
  for i := 1 to rF do
    pi := Periods(E, i : Precision:=prec)[1];
    assert Abs(Im(pi)) lt eps;
    pi := Real(pi); 
    assert pi gt 0;
    Omega_R[i] := pi;
  end for;

if overQ then
Omega := RealPeriod(EQ : Precision:=prec);
assert forall{omega : omega in Omega_R | Abs(Omega - omega) lt eps};
end if;

  tlogs_R := [ [] : P in gens];

  for i in [1..r] do 
    tP := t * gens[i];
    assert tP[3] eq 1;
    for v in [1..rF] do
      l := EllipticLogarithm(tP, v : Precision:=prec) / Omega_R[v];
if t ne 1 then      
l1 := t*EllipticLogarithm(gens[i], v : Precision:=prec) / Omega_R[v];
assert Abs(ldiff - Round(ldiff)) lt 10^-10 where ldiff := Real(l - l1);
end if;
      assert Abs(Im(l)) lt 10^-10;
      tlogs_R[i,v] := Real(l);
    end for;
  end for;

  // Reduction loop

  naive_bounds := [naive_height_bound : i in [1..rF]];

  while true do

    vprint IntegralPoints: "Current bound on canonical height =", RR! canon_height_bound;

    if r eq 1 and false then
      // TO DO
      // refine canon_height_bound to be the height of the largest point that satisfies it
      vprint IntegralPoints: "Current bound on canonical height =", RR! canon_height_bound;
    end if;

    if canon_height_bound lt lambda then
      // the only S-integral points are torsion points
      return 0, 0, height_pairing;
    end if;

    for v := 1 to rF do
      b := reduce_height_bound_one_step_at_v
           (E, Omega_R[v], height_pairing, t, tlogs_R, canon_height_bound, v);

      b := Max(b, b_egg[v]);

      naive_bounds[v] := b;
    end for;

    vprint IntegralPoints: "==> bounds on contributions to naive height:", 
                                ChangeUniverse(naive_bounds, RR);

    naive_height_bound := &+ naive_bounds;

    if canon_height_bound gt naive_height_bound + canon_minus_naive + 10^-2 then
       canon_height_bound := naive_height_bound + canon_minus_naive;
    else
       return canon_height_bound, 0, height_pairing;
    end if;

  end while;
end function;

//////////////////////////////////////////////////////////////////////////
// Interface
//////////////////////////////////////////////////////////////////////////

intrinsic IntegralPoints(E::CrvEll[FldNum] : FBasis:=[], SafetyFactor:=2)
       -> SeqEnum
{Given an elliptic curve over a number field, returns a sequence containing
the integral points on E (up to sign: only one of P and -P is listed)}

   F := BaseRing(E);
   S := [];
   basis := FBasis;

   require forall{ai: ai in aInvariants(E) | IsIntegral(ai)} :
          "The given curve must have integral coefficients";

   require not IsEmpty(FBasis) :
          "The parameter FBasis must be provided and must be nonempty";

   require SafetyFactor ge 1 :
          "The SafetyFactor must not be less than 1";

   require IsAbsoluteField(F) and IsSimple(F) :
          "The base field must be a direct extension of Q " *
          "(an extension by a single polynomial)";

   require IsTotallyReal(F) :
          "Currently implemented only over totally real fields";

   require #TorsionSubgroup(E) eq 1 : 
          "Not implemented yet for curves with nontrivial torsion";


   height_bound_0 :=
     InternalIntegralPointsInitialBound
       (Coefficients(E), basis, S, [1..Degree(F)]);
// height_bound_0 := 10^100;

   height_bound, naive_height_bounds, height_pairing :=
     reduced_canonical_height_bound(E, basis, height_bound_0, S);


  // Search region with volume SafetyFactor times as large
  // (up to height_bound + extra)
  if SafetyFactor eq 1 then
    extra := 0;
  else
    if height_bound eq 0 then  // important to test this case 
      height_bound := 10;      // (typical size)
    end if;
    SF := SafetyFactor^(2/#basis) - 1;
    extra := SF * height_bound;
  end if;

  tors := [Id(E)]; // TO DO

  assert Precision(BaseRing(height_pairing)) ge 100;
  height_pairing := ChangeRing(height_pairing, RealField(30));

  pts := CheckPointsWithBoundedHeight
         (E, basis, tors, height_pairing, height_bound, S : extra:=extra);

  xpts := [P[1] : P in pts];
  ParallelSort(~xpts, ~pts);

  return pts, height_bound;

end intrinsic;

