freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!

/*****************************************************
 * Hyperelliptic/jacobian.m                          *
 *                                                   *
 * Functions for Jacobians of hyperelliptic curves   *
 *                                                   *
 * Michael Stoll                                     *
 *                                                   *
 * started 22-Jun-1998                               *
------------------------------------------------------


 CHANGE LOG:  ***Please record all changes here***


 modified by Paulette Lieby 1999
 
  changes:
  --------

  Attribute changes:
  ******************
 
  AddFunction, NegateFunction, RandomFunction, Zero  
           disappear
 
  Type, Generators and Points are now internal attributes
    (Type is set when the jacobian is created and 
     therefore cannot be set by the user --
     however Generators and Points must be set by the user)

  Bound is a new attribute, which is internal as well
    (because formerly we had the (external) attribute
    Points = < points, bound > when ring == Rationals())


  ==> no need to declare Type, Generators, Points and Bound anymore


  Function changes:
  *****************

  SetType(J) disappears

  the CantorComposition and Reduction functions disappear
  as well as CantorAdd and Even 
 
  however there is now a CantorComposition1 & 2  (in kernel now)
  made   available at the Magma level 
  (since it is needed in RandomFunction)

  all Random functions  disappear


  Intrinsic changes:
  ******************

  Zero               no need, there is already one provided
  IsZero         --> in kernel
  DivisorToPoint --> in kernel (internal)
  JacobianPoint  --> in kernel: to create a point,
    one can coerce as in J![a,b] or
    create as in elt<J | a, b> or elt<J | a, b, d>

  +, *, and -    --> in kernel

  Random         --> in kernel
  AbelianGroup   --> in kernel

------------------------------------------------------
 
Modifications by David Kohel, June 2000

BaseExtend, BaseChange, ChangeRing for changing base field
JacobianPoint (moved to function)
Point (undocumented, called from kernel coercion function)
ReducePoint (moved to function)

   '-'(P1::CrvHypPt, P2::CrvHypPt)
      -> replaced by kernel intrinsic call to more general 
         magma function J![[P1..Pt],[Q1..Qt]]
Point counting moved to take field:

   EulerFactor(J,p) -> EulerFactor(J,K)
   // Commented out -- create the parent struture.
   AbelianGroup(J,p) -> AbelianGroup(J,K) 

--for consistency with elliptic curves

  -----------------------------------------------------------------
  
  CHANGES
  
  Changed by Michael Stoll, 2000-03-24, merged with version 2.7-1 2000-08-08:
  
    Cleaned up the code
    
    Improvement in Order(JacHypPt)
    
  2000-03-29/2000-08-08:
  
    Removed some comments referring to pieces of code that had
      been removed earlier
    
    Added some comments on attributes.
    
    Added (Rational)Points(J, a, d) for genus 2 Jacobians, giving the
      indexed set of rational points on J of the form <a,b,d>.
  
  2000-08-16:
  
    Moved BadPrimes here from selmer.m
  
  2000-08-17:
    
    Improvement in EulerFactor(J, F) (no need to factor the discriminant)
    
   2000-08-25:
   
     In BaseExtend/BaseChange -- allow Rng type (instead of Fld)
	 (reason: Laurent series fields are NOT of type Fld!)

	 2001-02-28

	 IsPoint: a better coercion intrinsic

   2001-05:  Paulette Lieby 	    

    remove pSubgroup and replace it by the kernel Sylow(J, p)
 
	     
   2001-06:
 
   Scheme merge.

   13/07/01: Nicole Sutherland

   return type
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 HyperellipticCurve & Curve fix
		 and CrvHypPtOld

		 AND (finally!) get rid of these calls to
		 CrvHypPtOld ('-' and JacobianPoint)

   2001-07: Paulette
   IsOrder renamed as HasOrder
   
   2001-12: David Kohel
   JacobianPoint(P1,P2) corrected for genus one in which P1 = -P2.

   2004-03: Mike Harrison
   Changed EulerFactor to call through the new ZetaFunction(C)
   (rather than the reverse!).

   2006-01: Steve 
    Implemented JacobianPoint(J::JacHyp, D::DivCrvElt) -> JacHypPt
    which converts a divisor on the curve to a point on the Jacobian.
    This involves some reduction to a simpler Mumford representation,
    which can then be fed into Magma using elt< J | a,b,d >.
    The reduction already implemented in the C code
    is only what is required for adding 2 points that are
    already in reduced representation. 
    I've done my own reduction inside the new intrinsic (in this file).  

   2011-02-11: Jan Steffen Mueller
    Points(J::JacHyp : Bound := 0) now works for general models of 
    genus 2 curves 
  
   -----------------------------------------------------------------
  
  TO DO:
  
    ReducePoint for arbitrary genus and maybe for number fields
    
    (Rational)Points(J, a, d) for general Jacobians
    
    Use Baby step/Giant step to improve computation of #J
 

******************************************************/

forward ReducePoint;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Attribute declarations                                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare attributes JacHyp:
    // the following attributes are assigned when needed (K = base field)
    EulerFactor,         // the Euler factor (for K finite). Set by EulerFactor.
    Order,               // the group order (for K finite). Set by EulerFactor.
    FactoredOrder,       // the group order in factored form (for K finite).
                         // Set by FactoredOrder.
    Group,               // the abstract abelian group isomorphic to J(K)
                         //  (for K finite). Set by AbelianGroup.
    TwoTorsion,          // specifies the 2-torsion subgroup.
                         // Set by TwoTorsionSubgroup (in torsion.m).
    TorsionGroup,        // J_tors(Q) as an abstract group (K = Q, genus = 2).
    TorsionMap,          // map from abstract group to J_tors(Q).
                         // Both set by TorsionSubgroup.
    TorsionBound,        // a bound on the size of the rational torsion
                         //  subgroup (for K = Rationals()). Precise format:
                         //   < bound, n, [<p, b>] >
                         //  with bound the current bound,
                         //       n the number of good primes looked at,
                         //       [<p,b>] a list of the primes together
                         //         with the size of J(F_p).
                         // Set by TorsionBound.
    HeightConst;         // a triple <hc, hc_infty, eff> giving the
                         // result of HeightConstant(J) with Effort = eff.
                         // Set by HeightConstant (in height.m).

// Internal attributes:
//  Type        -- type of the Jacobian, see below. Set upon creation.
//  Generators  -- generators of J(K) corresponding to the group gens
//                 (the (abstract) group is given by the Group attribute).
//                 Set by AbelianGroup(J).
//  Points      -- Indexed set of rational points found so far. 
//                 Set by (Rational)Points(J [: Bound := ...]).
//  Bound       -- (Naive Kummer) height bound for rational points
//                 found so far. Set by (Rational)Points(J : Bound := ...).

// type says which kind of algorithms to use for +, -, Random.
// The following types are currently implemented.
// type  0: this the default type when none of the cases below applies.
//          Installs addition and negation functions that signal an error.
// type  1: curve has form  y^2 = f(x), deg(f) odd.
// type  2: curve has form  y^2 = f(x), deg(f) even, genus is even
//          and there are no rational points at infinity.
// type  3: curve has form  y^2 = f(x), deg(f) even, and genus is 2.
// type 11: curve has 1 point at infinity. 
// type 12: curve has no rational points at infinity and genus is even.
// type 13: curve has 2 rational points at infinity and genus is 2.


////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Attribute access                                                  //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Dimension(J::JacHyp) -> RngIntElt
   {The dimension of the jacobian J as a variety.}
   return Genus(Curve(J));
end intrinsic;

intrinsic BadPrimes(J::JacHyp : Badness := 1) -> SeqEnum
{Returns the sequence of primes where the given model of the curve of J
  has bad reduction. J must be defined over a number field, and the defining 
  polynomials of its curve must have integral coefficients. }
  return BadPrimes(Curve(J) : Badness := Badness);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Base field                                                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic BaseField(J::JacHyp) -> Rng
    {The base field of the Jacobian J. }
    return BaseField(Curve(J));
end intrinsic;

intrinsic BaseRing(J::JacHyp) -> Rng
    {The base field of the Jacobian J. }
    return BaseRing(Curve(J));
end intrinsic;


////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Base extension                                                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

// NOTE: BaseChange = BaseExtend at bind level, so do not define both here!

intrinsic BaseExtend(J::JacHyp, F::Rng) -> JacHyp
    {Extends the base field of the Jacobian J to F.}
    C := Curve(J);
    return Jacobian(ChangeRing(C, F));
end intrinsic;

intrinsic BaseExtend(J::JacHyp, j::Map) -> JacHyp
    {Extends the base field of the Jacobian J by applying j.}
    return Jacobian(BaseExtend(Curve(J), j));
end intrinsic;

intrinsic BaseExtend(J::JacHyp, n::RngIntElt) -> JacHyp
    {Extends the finite base field of the Jacobian J to 
    its degree n extension.}
    return Jacobian(BaseExtend(Curve(J),n));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Points on the Jacobian                                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//
// A point on the Jacobian J of the curve H is given by three components:
//  a -- a monic polynomial of degree at most g (= genus of H);
//  b -- a polynomial of degree at most g+1 such that
//       a divides b^2 + h*b - f, where h and f are the defining
//       polynomials of H;
//  d -- a positive integer with deg(a) <= d <= g.
//       The degree of b^2 + h*b - f must be <= g+1 - (d-deg(a)).
// We interpret a and b as homogeneous polynomials (in x and z) 
// of degrees d and g+1, resp.
// Then <a,b,d> represents the divisor of degree d given by:
//  + its image in P^1 is defined by a;
//  + the point in the support above a point in P^1 that is
//    a zero of a is given by  y = b(x,z).
// In short, we have the divisor that is the gcd of the divisors
// defined by a(x,z) and y - b(x,z).
// If d is even or H has only one point at infinity (the odd degree
// case), then we get an element of J by subtracting a suitable
// multiple of the point(s) at infinity.
//
// In the odd degree case, we then can always take d = deg(a). 
// In the even degree case, we need to take d even. This implies
// that the genus has to be even in order to get unique representatives.
//
// Normalizations:
//  + If d = deg(a), we can reduce b mod a, so deg(b) < deg(a).
//  + If a = 1 (the opposite case), we can assume that deg(b(1,z)) = d.
//  + In general, we get a unique representative by requiring
//    that the coefficient of x^k in b is zero for k in 
//    [deg(a) .. deg(a) + g+1 - d].
//
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Coercion : curve divisor to jacobian point                        //
//  (note: internal coercion calls this)                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic JacobianPoint(J::JacHyp, D::DivCrvElt) -> JacHypPt
{The point on the Jacobian J (of a hyperelliptic curve C) 
associated to the divisor D on C. If D does not have degree 0,
then a suitable multiple of the divisor at infinity is subtracted.
When the divisor at infinity on C has even degree, D is required to have even degree.}

// The intrinsic works for any divisor such that the corresponding point
// is definable in Magma, and otherwise an error results.
// Not implemented in characteristic 2.
  
   debug := false;
   C := Curve(D);
   F := BaseField(C);
   require J eq Jacobian(C): "The first argument should be the Jacobian
          of a curve C and the second argument should be a divisor on C";
   require Characteristic(BaseField(C)) ne 2:
      "Not implemented in characteristic 2.
       If this is needed, please email Magma.";
   P<X,Y,Z> := CoordinateRing(Ambient(C));
   g := Genus(C);
   f, h := HyperellipticPolynomials(C);
   
   // Reduce to the case where C has the form y^2 = f(x)
   if h ne 0 then
      Csim :=  HyperellipticCurve(f+h^2/4);
      CtoCsim := map< C -> Csim | [X, Y+Z^(g+1)*Evaluate(h,X/Z)/2, Z] >;
      D := Pullback( Inverse(CtoCsim), D);
      pt := Jacobian(Csim)!D;   
      return elt< J | pt[1], pt[2]+h/2, pt[3] >;
   end if;
   
   PAI := PointsAtInfinity(C);
   if #PAI eq 2 then
      TwoPtsAtInf := true;
      _, s := IsSquare(LeadingCoefficient(f));
      Pinf1 := C![1,s,0];
      Pinf2 := C![1,-s,0];
      DivAtInfty := Divisor(C, ideal < P | Z >);
      assert PAI eq {@ Pinf1, Pinf2 @};
   elif #PAI eq 1 then
      DivAtInfty := Divisor(PAI[1]);      
      PlaceAtInf := Support(DivAtInfty)[1];
      TwoPtsAtInf := false;
   else
      DivAtInfty := Divisor(C, ideal < P | Z >);
      PlaceAtInf := Support(DivAtInfty)[1];
      TwoPtsAtInf := false;
   end if;
   if Degree(DivAtInfty) eq 2 then
      require IsEven(Degree(D)): 
         "D must have even degree when the divisor at infinity has degree 2";
   end if;

   // Get the zeros and poles of D, and separate off the infinite and Weierstrass parts too.
   // For the Weierstrass places, we may reduce the multiplicities mod 2.
   TupUniv := CartesianProduct(Places(C),Integers());
   DivWeierstrass := Divisor(C, ideal<P | Y, Z^Degree(f)*Evaluate(f, X/Z)>);
   InfW := Support(DivAtInfty) cat Support(DivWeierstrass);
   Dnum := Divisor(C, [ TupUniv | d : d in Decomposition(D)  
                      |  d[1] notin InfW and  d[2] gt 0] );
   Dden := -Divisor(C, [ TupUniv | d : d in Decomposition(D)  
                      |  d[1] notin InfW and  d[2] lt 0] );
   Dinf := Divisor(C, [ TupUniv | d : d in Decomposition(D)  
                      |  d[1] in Support(DivAtInfty) ] );
   DW   := Divisor(C, [ TupUniv | <d[1], d[2] mod 2> : d in Decomposition(D)  
                      |  d[1] in Support(DivWeierstrass) ] );
   assert Support(D - (Dnum-Dden+Dinf)) subset Support(DivWeierstrass);
   // Replace the pole divisor by its reflection (with positive multiplicity). 
   // Doing this doesn't change the parity of deg D,
   // and it doesn't change the divisor class that is being represented.
   DdenReflected := Pullback( HyperellipticInvolution(C), Dden );
   Dnoninf := Dnum + DW + DdenReflected;   // Effective divisor such that 
                                           // Dnoninf + Dinf gives what we want
   I := Ideal(Dnoninf);
   if debug then
      print "Dnum, Dden, Dinf, DW are\n ", Support(Dnum), Support(Dden), Support(Dinf), Support(DW);
   end if;
   
   // Keep track of the infinite contributions, only in the case TwoPtsAtInf. 
   // (In other cases, divisors at infinity are trivial anyway).
   // The imbalance between Pinf1 and Pinf2 in D is recorded in v,
   // and this will be added at the end.
   if TwoPtsAtInf then
      v := Valuation(Dinf, Pinf1) - Valuation(Dinf, Pinf2);
      if debug then print "v is ",v; end if;
   end if;
   
   // Now we want an equation of the form c(x)*y = b(x).
   // We get this from a Groebner basis for I using lex order, with x smaller than y
   Pxy<y,x> := PolynomialRing(BaseRing(P),2, "lex");
   f := Evaluate(f, x);
   I := ideal< Pxy | [Evaluate(pol, [x,y,1]) : pol in Basis(I)] >;
   Ix := EliminationIdeal(I,{x});  
   a := Basis(Ix)[1];
   // remove factors from the ideal corresponding to "vertical" divisors 
   // (since they are trivial).
   for fa in Factorisation(a) do
      Ifa := ideal< Pxy | fa[1], y^2-f >;  // "vertical" divisor supported at the roots of fa
      while I subset Ifa do
         Inew := ColonIdeal(I, Ifa);  // should be able to take exact ideal quotients here
         assert Inew*Ifa+ideal<Pxy | y^2-f>  eq I;   // really working in Pxy/(y^2-f)
         I := Inew;
      end while;
   end for;
   if I eq Pxy then   // ideal is now trivial, so return the infinite contribution, if any.
      if TwoPtsAtInf then
         return (v div 2)*(Pinf1-Pinf2);
      else 
         return J!0;
      end if;
   end if;
   Ix := EliminationIdeal(I,{x});  
   a := Basis(Ix)[1];
   // Now get an equation of the form c(x)*y = b(x).
   // Remember that I has lex order, with x smaller than y
   GB := GroebnerBasis(I);
   assert #GB eq 2;
   assert a eq GroebnerBasis(I)[2];
   CyeqB := GroebnerBasis(I)[1];
   assert Degree(CyeqB, y) eq 1;
   b := -Evaluate(CyeqB, [0,x]);    // Beware: the variables are in the order y, x
   c := Evaluate(CyeqB + b, [1,x]);
   assert CyeqB eq c*y-b;
   assert GCD(a,c) eq 1;   // common factors should have been removed as "vertical" divisors
   
   // Reduce b(x)/c(x) mod a(x), so we obtain y-b(x) with deg b < deg a.
   Pu := PolynomialRing(BaseRing(P)); u := Pu.1;   // Univ poly ring, for div or quo.
   au, bu, cu, fu := Explode([ Evaluate(pol,[0,u]) : pol in [a,b,c,f] ]);
      // Recall a,b,c,f are polys in variables y, x, in that order.
   gcd, M, N := XGCD(au, cu);   // N should equal 1/c mod a
   assert gcd eq 1;
   bu := bu*N mod au;
   // Reduction: Replace a by (b^2-f)/a and reduce b mod a ... until deg a <= g+1.
   while Degree(au) gt Degree(fu)/2 do    // it goes down to g or g+1
      // Replace (a,y-b) by a linear equivalent divisor,
      // using the fact that the divisor given by y-b is trivial.
      // More precisely, the homogenisation z^k*y-b(x,z), 
      // where k = deg(b(x)) - (g+1) when this is positive.
      // Contribution at infinity in z^k*y-b(x,z): 
      //    * We only care if TwoPtsAtInf.
      //    * Only possible when k = 0 and deg(b(x)) = g+1.
      //    * In this case, the point (1:s:0) appears (for s = 1 or -1)
      //      iff s is the leading coeff of b(x), 
      //      and the multiplicity is 2g+2 - deg( b(x)^2-f ).
      if TwoPtsAtInf and Degree(bu) eq g+1 then   // maybe a contribution at infinity
         multinf :=  2*g+2 - Degree(bu^2-fu);
         if multinf gt 0 then 
            blc := LeadingCoefficient(bu);
            assert blc eq s or blc eq -s;    // s^2 = LeadingCoeff(fu)
            sInt := blc eq s select 1 else -1;   // looks silly, but needed if s is in GF(p).
            v +:= - sInt*multinf;   // add Pinf1 this many times to the running total
               // Recall v is the amount multiplicity(Pinf1) exceeds multiplicity(Pinf2).
               // The minus sign is because we need the reflection of the point. 
            if debug then print "v is now ",v; end if;
         end if;
      end if;
      au := ExactQuotient(bu^2-fu,au);
      au := au/LeadingCoefficient(au);   // keep au monic (why not?)
      bu := - bu mod au;   // reflect the points, to get the inverse in Pic^0(C)
   end while;
   if debug then print "au is and bu are now",au, bu; end if;

   if IsOdd(Degree(au)) then  // this should only happen when there's 
                              // at least one rational point at infinity,
      if TwoPtsAtInf then   // this should only have happenned if Pinf1 
         assert IsOdd(v);   // appears an odd number of times in the running total.
                            // We will now absorb one Pinf1 into (a,y-b). 
         v -:= 1;
         if debug then print "absorbing Pinf1, v is now ",v; end if;
         if Degree(au) lt g+1 then   
            // simply put Pinf1 = (1:s:0) in the divisor.
            // Homogeneously, replace a(x,z) and b(x,z) by 
            //     z*a(x,z) and b(x,z) + s*x^k*a(x,z),
            // (the second of these equals b(x) when a=0 and z=1, 
            // and equals s when z=0, since a is monic).
            k := g+1 - Degree(au);
            bu := bu + s*u^k*au;   
            d := Degree(au) + 1;
            abJ := elt< J | [au,bu], d >;
         else   
            if debug then print "Awkward case, deg(au) = g+1"; end if;
            // deg(au) = g+1, and we find an equivalent divisor 
            // of degree (g+1) containing Pinf1 = (1:s:0).
            // Since deg b < g+1 and a is monic of deg g+1,
            // the trivial divisor of degree 2g+2 cut by  
            //     y + z^l*b(x,z) + s*a(x,z)
            // contains (1:-s:0) and the divisor (a,y+b),
            // i.e. the reflection of (1:s:0) + (a,y-b).
            // Therefore the remaining part of it, which has degree g, 
            // will be linearly equivalent to (1:s:0) + (a,y-b).
            DD := Divisor(C, ideal<P | Y + Z^(g+1)*(Evaluate(bu,X/Z)+s*Evaluate(au,X/Z)) >);
            DD := DD - Divisor(Pinf2) 
                     - Divisor(C, ideal< P |  Z^(g+1)*Evaluate(au,X/Z),
                                            Y+Z^(g+1)*Evaluate(bu,X/Z)> );
            if debug then print "    ... DD is ", Support(DD); end if;
            assert IsEffective(DD); 
            abJ := JacobianPoint(J, DD);   
                // Recursive call should work with no reduction required.
         end if;
      else 
         require Degree(DivAtInfty) eq 1: 
            "Error: degree became odd while finding the reduced representation";
         abJ := J![au,bu];
      end if;
   else 
      abJ := J![au,bu];
   end if;
   if debug then print "ready to return ", au, bu, abJ; end if;

   if TwoPtsAtInf then    // Put in the infinite bit using addition on J.
      return abJ + (v div 2)*(Pinf1-Pinf2);   
   else
      return abJ; 
   end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Point Coercion to the reduction of J mod p                        // 
//    (retained for kernel)                                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Point(J::JacHyp, pt::JacHypPt) -> JacHypPt
   {For internal use only}
   // INTERNAL: Returns the image of pt on J, where J is the 
   // reduction of the parent of pt at a good prime, or when 
   // pt is over a finite field and J comes from a base field 
   // extension.
   // N.B.: This intrinsic is also called via jac_hc_coerce

   F := BaseField(J);
   PF := PolynomialRing(F);
   Jpt := Parent(pt);
   if BaseField(Jpt) cmpeq Rationals() and IsFinite(F) then
      require J eq BaseExtend(Jpt, F):
         "Argument 1 is not the base change of the parent of argument 2.";
      pt1 := ReducePoint(pt, Characteristic(F));
      if Degree(F) gt 1 then
        pt1 := elt< J | PF!pt1[1], PF!pt1[2], pt1[3] >;
      end if;
      return pt1;
   elif J eq BaseExtend(Jpt, F) then
      return elt< J | PF!pt[1], PF!pt[2], pt[3] >;
   else 
      require false: 
         "Argument 1 is not a base change of the parent of argument 2";
   end if;
end intrinsic;

intrinsic IsPoint(J::JacHyp, pt::JacHypPt) -> BoolElt, JacHypPt
    {True iff pt is coercible into Jacobian J; if true, also return J!pt }
    // INTERNAL: Returns the image of pt on J, where J is the 
    // reduction of the parent of pt at a good prime, or when 
    // pt is over a finite field and J comes from a base field 
    // extension.
    // N.B.: This intrinsic is also called via jac_hc_coerce
    //
    // Based on the "Point" intrinsic by Michael Stoll.  Modified to
    // return a boolean when coercion is impossible.
    
    F := BaseField(J);
    PF := PolynomialRing(F);
    Jpt := Parent(pt);
 
    // coercion Pt over Rationals -> Jac over finite field
    if BaseField(Jpt) cmpeq Rationals() and IsFinite(F) then
        if J ne BaseExtend(Jpt, F) then
            // Argument 1 is not the base change of the parent of argument 2.
            return false, _;
        end if;
        pt1 := ReducePoint(pt, Characteristic(F));
        if Degree(F) gt 1 then
            pt1 := elt< J | PF!pt1[1], PF!pt1[2], pt1[3] >;
        end if;
        return true, pt1;
    else
    // generic coercion
        test, coer_pt1 := IsCoercible(PF, pt[1]);
        if test then
            test, coer_pt2 := IsCoercible(PF, pt[2]);
            if test then
                return true, elt< J | coer_pt1, coer_pt2, pt[3] >;
            end if;
        end if;
        return false, _;
    end if;
end intrinsic;


function ReducePoint(pt,p) // (pt::JacHypPt, p::RngIntElt) -> JacHypPt
   // {Given a point on a Jacobian of a genus 2 curve over the rationals 
   // and a prime p of good reduction, returns the image of the point on 
   // the reduction mod p of the Jacobian.}

   J := Parent(pt);
   // require BaseField(J) cmpeq Rationals():
   //        "The point must lie on a Jacobian over the rationals.";
   // require Genus(Curve(J)) eq 2:
   //        "The point must lie on a Jacobian of a genus 2 curve.";
   Jp := BaseExtend(J, GF(p));
   a := pt[1]; b := pt[2]; d := pt[3];
   PZ := PolynomialRing(Integers());
   PF := PolynomialRing(GF(p));
   a := PZ!(LCM([Integers() | Denominator(c) : c in Coefficients(a)])*a);
   bden := LCM([Integers() | Denominator(c) : c in Coefficients(b)]);
   b := PZ!(bden*b);
   if IsDivisibleBy(bden, p) then
      as := Eltseq(a) cat [ 0 : i in [Degree(a)..1] ];
      mat := Matrix(4, as cat [0, 0] cat as);
      matp := ChangeRing(mat, GF(p));
      V := KSpace(GF(p), 4);
      VZ := RSpace(Integers(), 2);
      n := Valuation(bden, p);
      while n gt 0 do
        bs := Eltseq(b) cat [ 0 : i in [Degree(b)..2] ];
        flag, sol := IsConsistent(matp, V!bs);
        if not flag then return Jp!0; end if;
        b -:= PZ!Eltseq((VZ!sol)*mat);
        b := ExactQuotient(b, p);
        bden := ExactQuotient(bden, p);
        n -:= 1;
      end while;
   end if;
   return DivisorToPoint(Jp, PF!a, (GF(p)!bden)^-1*PF!b, d);
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Enumeration of Points                                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic RationalPoints(J::JacHyp : Bound := 0, ReturnAll := false) -> SetIndx
   {Returns all rational points on the Jacobian J over a 
   finite field, or all points on a Jacobian of a genus 2 curve of the 
   form y^2 = f(x), defined over the rationals, up to a bound on the 
   naive Kummer surface height set by the parameter Bound.}

   R := CoefficientRing(J);
   if R cmpeq Rationals() then
      require Dimension(J) eq 2 : 
         "Argument must the Jacobian of a genus 2 curve.";
   elif Type(R) ne FldFin then
      require false : 
         "Argument must defined over the rationals or a finite field.";
   end if;
   return Points(J : Bound := Bound, ReturnAll:=ReturnAll);
end intrinsic;

intrinsic Points(J::JacHyp : Bound := 0, ReturnAll := false) -> SetIndx
{"} // "

   R := CoefficientRing(J);
   if R cmpeq Rationals() then
      require Dimension(J) eq 2 : 
         "Argument must be the Jacobian of a genus 2 curve.";
      C := Curve(J);
      require IsIntegral(C) :
         "Argument must be the Jacobian of a curve given by an integral model.";
      K := KummerSurface(J);
      if not ReturnAll and assigned J`Points and Bound le J`Bound then
          points := J`Points;
          ht := func< pt | Max([Abs(c) : c in Eltseq(K!pt)]) >;
          return {@ pt : pt in points | ht(pt) le Bound @};
      end if;

      require Bound gt 0:
         "A positive parameter Bound must be specified.";

      f, h := HyperellipticPolynomials(C);
      if h ne 0 then
        // need to search for points on the Jacobian of C1 : y^2 = 4f(x) + h(x)^2
        C1, phi := SimplifiedModel(C);
        J1 := Jacobian(C1);
        psi := Inverse(phi);
        // we have ht(phi(P)) < Bound1 => ht(P) < Bound 
        Bound1 := Ceiling(Max(1, 1/2*(1/2 + Abs(h0*h2) + Abs(h0*h3) + Abs(h1*h3)))*Bound)
        where h0 := Coefficient(h, 0)
        where h1 := Coefficient(h, 1)
        where h2 := Coefficient(h, 2)
        where h3 := Coefficient(h, 3);
      else   
        J1 := J;
        Bound1 := Bound;
      end if;
      K1 := KummerSurface(J1);

      // search for points on J1 up to height Bound1
      str1 := jPoints(J1, Bound1 : ReturnAll:=ReturnAll);

      n := #str1 div 4;
      // include the origin
      points1 := {@ J1!0 @};
      // now add the other points
      for i := 1 to n do
        points1 join:= Points(J1, K1!str1[4*i-3..4*i]);
      end for;
      // map points back to J
      J`Points := h eq 0 select points1 else {@ Evaluate(psi, P) : P in points1 @};
      J`Bound := Bound;
      return J`Points;
   end if;
   // Here, the base field is not the rationals.
   if assigned J`Points then 
      return J`Points; 
   end if;
   require IsFinite(R):
       "Set of rational points is only implemented for Jacobians",
       "of curves over finite fields or the rationals.";
   A, m := AbelianGroup(J);
   points := {@ m(a) : a in A @};
   J`Points := points;
   return points;
end intrinsic;

intrinsic RationalPoints(J::JacHyp, a::RngUPolElt, d::RngIntElt) -> SetIndx
{Find all points on J with first component a and degree d. 
  So far only for genus 2 and curve of the form y^2 = f(x).}
    return Points(J, a, d);
end intrinsic;

intrinsic Points(J::JacHyp, a::RngUPolElt, d::RngIntElt) -> SetIndx
{Find all points on J with first component a and degree d. 
  So far only for genus 2 and curve of the form y^2 = f(x).}
  require Degree(a) le d: "The degree of a may not be larger than d.";
  require d le Genus(Curve(J)): "d may not be larger than the genus.";
  if d eq 0 then return {@ J!0 @}; end if;
  K := KummerSurface(J);
  ptsK := Points(K, [Coefficient(a,2), -Coefficient(a,1), Coefficient(a,0)]);
  return &join[ Points(J, ptK) : ptK in ptsK ];
end intrinsic;


////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Constructing points on J from points on C                         //                          //                                                                    //
////////////////////////////////////////////////////////////////////////

// Compatibility function -- unknown whether this is used in the 
// package code ... now advertised in the handbook, though.

intrinsic '-'(P1::PtHyp, P2::PtHyp) -> JacHypPt
    {Returns the divisor class [P1 - P2] as a point on the Jacobian.}
    return JacobianPoint(P1,P2);
end intrinsic;


// Internal function -- called by Jacobian point constructor.

intrinsic JacobianPoint(S::[PtHyp], T::[PtHyp]) -> JacHypPt
    {For internal use only}
    require #S eq #T : "Arguments must have the same length.";
    return &+[ JacobianPoint(S[i],T[i]) : i in [1..#S] ]; 
end intrinsic;

intrinsic JacobianPoint(P1::PtHyp, P2::PtHyp) -> JacHypPt
    {The difference of the two points in the Jacobian (for internal
    use only).}
    C := Curve(P1);
    require C eq Curve(P2) and Ring(Parent(P1)) cmpeq BaseRing(C) :
       "Arguments must be points on the same curve over its base ring.";
    J := Jacobian(C);
    g := Genus(C);
    if g eq 0 then
	return J!0;
    elif P1 eq P2 then
	return J!0;
    end if;
    // Use that [P1 - P2] = [P1 + P2^- - M] where M is any divisor of the
    // form P + P^- (with P |-> P^- the hyperelliptic involution).
    f, h := HyperellipticPolynomials(C);
    PR := Parent(f); X := PR.1;
    P2m := -P2;
    if P1[3] eq 0 then
	// P1 is at infinity
	if P2m[3] eq 0 then
	    // both are at infinity and equal (even degree model)
	    y := P1[2]/P1[1]^(g+1);
	    h0 := Coefficient(h, g+1); 
	    h1 := Coefficient(h, g);
	    f1 := Coefficient(f, 2*g+1);
	    return elt< J | PR!1, y*X^(g+1) + (f1-h1*y)/(h0+2*y)*X^g, 2 >;
	else
	    // P1 is at infinity and P2m is not
	    y1 := P1[2]/P1[1]^(g+1);
	    x2 := P2m[1]/P2m[3]; 
	    y2 := P2m[2]/P2m[3]^(g+1);
	    d := 2 - (Degree(C) mod 2);
	    return elt< J | X-x2, y1*(X^(g+1)-x2^(g+1))+y2, d >;
	end if;
    elif P2m[3] eq 0 then
	// P2m is at infinity and P1 is not
	x1 := P1[1]/P1[3]; 
	y1 := P1[2]/P1[3]^(g+1);
	y2 := P2m[2]/P2m[1]^(g+1);
	d := 2 - (Degree(C) mod 2);
	return elt< J | X-x1, y2*(X^(g+1)-x1^(g+1))+y1, d >;
    elif P1 eq P2m then
	// Twice the same point -> use tangent line
	// If genus = 1 then the divisor must be reduced.
	if g eq 1 then
	    require #PointsAtInfinity(C) eq 1 :
   	       "Genus one Jacobian point constructor implemented " * 
	       "only for curves with one point at infinity.";
	    x1 := P1[1]/P1[3];
	    y1 := P1[2]/P1[3]^(g+1);
	    return 2 * elt< J | X-x1, y1*(X^(g+1)-x1^(g+1))+y1, 1 >;
	end if;
	x1 := P1[1]/P1[3]; y1 := P1[2]/P1[3]^(g+1);
	slope := ( Evaluate(Derivative(f),x1) -
	           Evaluate(Derivative(h),x1)*y1 )/(2*y1+Evaluate(h,x1));
	return J ! [ (X-x1)^2, slope*(X-x1)+y1 ];
    else
	// generic case: Two distinct finite points
	if g eq 1 then
	    Infty := PointsAtInfinity(C);
	    require #Infty ge 1 :
   	       "Genus one Jacobian point constructor implemented " * 
	       "only for curves with points at infinity.";
	    O := Infty[1];
	    x1 := P1[1]/P1[3]; y1 := P1[2]/P1[3]^2;
	    x2 := P2[1]/P2[3]; y2 := P2[2]/P2[3]^2;
	    d := 2 - (Degree(C) mod 2);
	    return elt< J | X-x1, y1, d > - elt< J | X-x2, y2, d >;
	end if;
	x1 := P1[1]/P1[3]; y1 := P1[2]/P1[3]^(g+1);
	x2 := P2m[1]/P2m[3]; y2 := P2m[2]/P2m[3]^(g+1);
	slope := (y2-y1)/(x2-x1);
	return J ! [ (X - x1)*(X - x2), slope*(X-x1)+y1 ];
    end if;
end intrinsic;



////////////////////////////////////////////////////////////////////////
//                                                                    //
//  Group invariants for Jacobians                                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

// Find the Euler factor of the Jacobian over a finite field

intrinsic EulerFactor(J::JacHyp) -> RngUPolElt
{The Euler factor of a Jacobian over a finite field, i.e. the 
reciprocal characteristic polynomial of Frobenius acting on H^1(J).}
    if assigned J`EulerFactor then return J`EulerFactor; end if;
    C := Curve(J);
    R := CoefficientRing(C);
    require IsFinite(R): "Base field of Jacobian must be finite.";
    // The Euler factor is  E(T) := product of (T - a_i)  (i = 1,...,2g)
    // with  sum a_i^k = q^k + 1 - #curve(extension of R of degree k).
    // We have the functional equation  q^g E(T) = T^(2g) E(q/T) ,
    // so we only need to compute the power sums up to k = g.
    f := PolynomialRing(Integers())!Numerator(ZetaFunction(C));
    J`EulerFactor := f;
    // We have #J = EulerFactor(J)(1)
    J`Order := &+Coefficients(f);
    return f;
end intrinsic;

intrinsic EulerFactor(J::JacHyp, K::FldFin) -> RngUPolElt
{The Euler factor of the base extension of J to K, where the base 
field of J is the rationals.}
    require BaseField(J) cmpeq Rationals():
       "Argument 1 must have the rationals as its base field.";
    require Valuation(Discriminant(Curve(J)), Characteristic(K)) eq 0: 
       "Argument 1 must have good reduction over argument 2";
    return EulerFactor(BaseExtend(J, K));
end intrinsic;

// Count points on the Jacobian over a finite field

intrinsic '#'(J::JacHyp) -> RngIntElt
{The number of rational points on the Jacobian over a finite field.}
    if assigned J`Order then return J`Order; end if;
    require IsFinite(CoefficientRing(Curve(J))):
            "Base field of Jacobian must be finite.";
    return Order(J);
end intrinsic;


intrinsic FactoredOrder(J::JacHyp) -> SeqEnum
{The order of the group of rational points of J, over a finite
field, in factored form.}
    if assigned J`FactoredOrder then return J`FactoredOrder; end if;
    require IsFinite(CoefficientRing(Curve(J))):
            " Base field of Jacobian must be finite.";
    size := #J;
    J`FactoredOrder := [ <a[1], a[2], size div (a[1]^a[2]) > :
                          a in Factorization(size) ];
    return J`FactoredOrder;
end intrinsic;

intrinsic TorsionBound(J::JacHyp, n::RngIntElt) -> RngIntElt
{A bound on the size of the rational torsion subgroup by
looking at the first n good primes, where the base field 
of J is the rationals:
The best known result based on the first n primes of
good reduction AND any previously computed torsion bound}
// Note: plist must only contain primes of good reduction
// (Order assumes this)
    if assigned J`TorsionBound and 
       (J`TorsionBound[2] ge n or J`TorsionBound[1] eq 1) then
      return J`TorsionBound[1];
    end if;
    C := Curve(J);
    require CoefficientRing(C) cmpeq Rationals():
            "Base field must be the rationals.";
    f, h := HyperellipticPolynomials(C);
    require &and[ Denominator(c) eq 1 : c in Eltseq(h) cat Eltseq(f) ]:
            "Coefficients of defining polynomials must be integers.";
    require n ge 1: "Need at least one prime.";
    disc := Integers()!Discriminant(C);
    if assigned J`TorsionBound then
      bound := J`TorsionBound[1];
      plist := J`TorsionBound[3];
      p := plist[#plist][1];
      s := J`TorsionBound[2]+1;
    else
      bound := 0;
      plist := [];
      p := 1;
      s := 1;
    end if;
    for i := s to n do
      p := NextPrime(p);
      while disc mod p eq 0 do p := NextPrime(p); end while;
      size := #BaseExtend(J,FiniteField(p));
      bound := Gcd(bound, size);
      Append(~plist, <p, size>);
      if bound eq 1 then break; end if;
    end for;
    J`TorsionBound := <bound, #plist, plist>;
    return bound;
end intrinsic;

intrinsic Order(pt::JacHypPt) -> RngIntElt
{The order of the point on the Jacobian, over a finite field or 
the rationals. Returns 0 if the point has infinite order.}
    J := Parent(pt);
    if IsFinite(CoefficientRing(Curve(J))) then
      fs := FactoredOrder(J);
      order := 1;
      zero := Zero(J);
      for tr in fs do
        q := tr[3]*pt;
        e := 0;
        while q ne zero do q := tr[1]*q; e +:= 1; end while;
        order *:= tr[1]^e;
      end for;
      return order;
    else
      bound := TorsionBound(J, 5);
      if bound gt 50 then bound := TorsionBound(J, 10); end if;
      // the bound is hopefully small...
      if bound eq 1 then return (pt eq Zero(J)) select 1 else 0; end if;
      //*** Modification MS 2000-03-24
      // Try to use information on various reductions first,
      // in order to avoid multiplications with large integers if possible
      plist := J`TorsionBound[3];
      ord := Order(ReducePoint(pt, plist[1,1]));
      // order of pt is ord if finite (J(Q)_tors -> J(F_p) is injective for odd p)
      for i := 2 to #plist do
        if Order(ReducePoint(pt, plist[i,1])) ne ord then
          // if pt is torsion, its image under reduction mod any p must have same order
          return 0;
        end if;
      end for;
      // now check if pt really has order ord
      return IsZero(ord*pt) select ord else 0;
    end if;
end intrinsic;

intrinsic HasOrder(P::JacHypPt,n::RngIntElt) -> BoolElt
    {Returns true iff n is the order of the Jacobian point P.
    Maybe expensive over infinite fields when n is large.}
    require n gt 0: "Argument n must be positive.";
    pf := PrimeDivisors(n);
    O := Parent(P)!0;
    return n*P eq O and forall{p : p in pf | (n div p)*P ne O};
end intrinsic;

