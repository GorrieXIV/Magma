freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!

/***********************************************************************
 * README for igusa.m   (by Everett W. Howe)                           *
 ***********************************************************************

It is important to note the following:

Igusa invariants can be defined for genus 2 *curves* over every field
and for *polynomials* of degree at most 6 over fields of characteristic
not 2.  The Igusa invariants of a genus 2 curve  y^2 + h*y = f
are equal to the Igusa invariants of the polynomial h^2 + 4*f except
in characteristic 2, where the latter are not defined.  In fact, this
package will not calculate the Igusa invariants of a polynomial unless
2 is a *unit* in the coefficient ring.  However, Igusa invariants of
*curves* are calculated for all coefficient rings.  (Well, almost all.
See below.)

Igusa invariants are given by a sequence [J2, J4, J6, J8, J10] of 5
elements of the coefficient ring of the polynomials defining the curve.
This sequence should be thought of as living in weighted projective
space, with weights 2, 4, 6, 8, and 10.

Warning:
Many of the people who work with genus 2 curves over the complex numbers
seem not to like the real Igusa invariants, and instead they tend to
work with some related numbers that I call the Igusa-Clebsch invariants
[I2, I4, I6, I10] of the curve.  (Once again, these live in weighted
projective space.)  The Igusa-Clebsch invariants of a polynomial are 
defined in terms of certain nice symmetric polynomials in its roots,
and (in characteristic zero) you get the J-invariants from the
I-invariants by some simple homogenous transformations.  In fact, many
of the genus-2-curves-over-the-complex-numbers people refer to the 
elements i1 := I2^5/I10  and  i2 := I2^3*I4/I10  and  i3 := I2^2*I6/I10
as the "invariants" of the curve.  The problem with the Igusa-Clebsch
invariants is that they do not work in characteristic 2; that is the
whole reason Igusa defined his J-invariants in the first place.


========================================================================


The package igusa.m contains the following intrinsics:
/***  this has changed as of 26/07/01 -- see update below  ***



IgusaInvariants(C): CrvHyp -> SeqEnum 
JInvariants(C): CrvHyp -> SeqEnum 

  Gives the Igusa invariants of a hyperelliptic curve C of genus 2.


IgusaInvariants(f,h): RngUPolElt, RngUPolElt -> SeqEnum 
JInvariants(f,h): RngUPolElt, RngUPolElt -> SeqEnum 

  Gives the Igusa invariants of the curve y^2 + h*y = f, where
  h is a polynomial of degree at most 3 and f is a polynomial
  of degree at most 6.  The coefficient ring R of the polynomial
  must either
    have characteristic 2
  or 
    be a ring in which Magma can apply the operator
    ExactQuotient( , 2).

  So for instance, R can be an arbitrary field, or Z, or a polynomial 
  ring over a field or over Z, and so forth.  However, R can not be
  a p-adic ring.  (There's no reason ExactQuotient( ,2) shouldn't
  work in a p-adic ring, but for some reason it doesn't.)
  If your favorite coefficient ring doesn't meet these conditions,
  use ScaledIgusaInvariants instead (see below), and scale the
  results by the appropriate powers of 2.


IgusaInvariants(f): RngUPolElt -> SeqEnum
JInvariants(f): RngUPolElt -> SeqEnum

  Gives the Igusa invariants of the *polynomial* f.  The integer 2
  must be a unit in the coefficient ring of f.


ScaledIgusaInvariants(f,h): RngUPolElt, RngUPolElt -> SeqEnum 

  Computes the Igusa J-invariants of the curve y^2 + h*y - f = 0,
  scaled by [16, 16^2, 16^3, 16^4, 16^5].  The polynomial h must have
  degree at most 3, the polynomial f must have degree at most 6, and 
  the characteristic of the base ring should not be 2.
  

ScaledIgusaInvariants(f): RngUPolElt -> SeqEnum

  Computes the Igusa J-invariants of a polynomial of degree at most 6,
  scaled by [16, 16^2, 16^3, 16^4, 16^5].  The coefficient ring
  must not have characteristic 2.


IgusaClebschInvariants(f): RngUPolElt -> SeqEnum

  Computes the Igusa-Clebsch invariants I2, I4, I6, I10 of a polynomial
  of degree at most 6.  The integer 2 must be a unit of the coefficient
  ring.


IgusaClebschInvariants(f,h): RngUPolElt, RngUPolElt -> SeqEnum 

  Computes the Igusa-Clebsch invariants of the curve y^2 + h*y - f = 0.
  The polynomial h must have degree at most 3, and the polynomial f must
  have degree at most 6.  These will be all be zero in characteristic 2.


IgusaClebschInvariants(C): CrvHyp -> SeqEnum 

  Computes the Igusa-Clebsch invariants of a genus 2 curve over a field.
  These will be all be zero in characteristic 2.


========================================================================

The following functions are "quick" versions of some of the functions
described above.  They only work over fields in which 30 is not 0.

(The Clebsch invariants are some invariants of binary sextics that
were computed by Clebsch; they are computed as a first step in finding
the Igusa-Clebsch invariants.  I don't know of anyone who uses them
(except as a stepping stone to the Igusa-Clebsch invariants), but as
long as I was calculating them I figured I would make them available 
in the package.)

QuickClebschInvariants(f): RngUPolElt -> SeqEnum
QuickIgusaClebschInvariants(f): RngUPolElt -> SeqEnum
QuickIgusaInvariants(f): RngUPolElt -> SeqEnum
QuickJInvariants(f): RngUPolElt -> SeqEnum

QuickClebschInvariants(C): CrvHyp -> SeqEnum
QuickIgusaClebschInvariants(C): CrvHyp -> SeqEnum
QuickIgusaInvariants(C): CrvHyp -> SeqEnum
QuickJInvariants(C): CrvHyp -> SeqEnum
***********************************************************************/

/*--------------------------------------------------------------------*/
/*            COMPUTATION OF INVARIANTS OF GENUS-2 CURVES             */
/*--------------------------------------------------------------------*/

/* 

This MAGMA package is based on some gp routines written by
Fernando Rodriguez-Villegas as part of the Computational
Number Theory project funded by a TARP grant.  The gp routines
may be found at 

       http://www.ma.utexas.edu/users/villegas/cnt/inv.gp

Rodriguez-Villegas's routines are based on a paper of Mestre:

   Jean-Francois Mestre:
   Construction de courbes de genre 2 a partir de leurs modules,
   pp. 313--334 in:
   Effective methods in algebraic geometry (T. Mora & C. Traverso, eds),
   Progr. Math. 94,
   Birkhauser, Boston, 1991.

The first part of Mestre's paper summarizes work of Clebsch and Igusa,
and is based on the classical theory of invariants.

This package has routines to compute three types of invariants of
quintic and sextic polynomials f (or, perhaps more accurately, of
binary sextic forms):

   The "Clebsch invariants" A, B, C, D of f, defined on p. 317
   of Mestre;

   The "Igusa-Clebsch invariants" A', B', C', D' of f, defined
   on p. 319 of Mestre; and

   The "Igusa invariants" (or "Igusa J-invariants", or "J-invariants")
   J_2, J_4, J_6, J_8, J_10 of f, defined on p. 324 of Mestre.

The routines to calculate these invariants are called
"ClebschInvariants", "IgusaClebschInvariants", and "JInvariants",
respectively.  For convenience, we use "IgusaInvariants" as a 
synonym for "JInvariants".  Some people might prefer that
"IgusaInvariant" be a synonym for "IgusaClebschInvariant" instead.

The coefficient ring of the polynomial f must be an algebra over a
field of characteristic not 2 or 3.

   -- Everett W. Howe, 19 Jan 2001

*/

/*------------------------------------------------------------------
  
  Changed by Michael Stoll 2001-01-23:

    Removed `ii' prefix of local functions (they are not visible outside).
    
    Made ClebschInvariants, IgusaClebschInvariants, JInvariants and
      IgusaInvariants into intrinsics.
    
    Added signature to above intrinsic, so they can be applied to
      a genus 2 curve.
   
    Replaced ConstantTerm with MonomialCoefficient(_, 1) (to get
      invariants in the coefficient ring).
    
    Added functionality to make it work when invariants are defined,
      but 2, 3 or 5 are not units in the base ring.
    
    Added Integral{J|Igusa}Invariants - scaled-up versions of the J_i
      with integral coefficients.

  2001-02-15:

    Changed comment at the beginning of the package to include
      Villegas's funding source and to update the URL of his gp code.
*/


/*------------------------------------------------------------------

  Changed by Everett Howe 2001-02-22:

    Revised package to reflect Igusa's paper more than Mestre's.
      (Jun-Ichi Igusa: Arithmetic variety of moduli for genus two,
      Ann. of Math. 72 (1960) 612--649.)
      The main conceptual change: *Invariants applied to a
      curve y^2 + h*y = f  is equal to *Invariants applied to the 
      polynomial h^2 + 4*f, except in characteristic 2, when the 
      former is defined but the latter isn't.

    Removed Integral{J|Igusa}Invariants -- they are no longer needed.
      The JInvariants of a curve are now automatically integral,
      and to get a scaled integral version of the J-invariants of
      a polynomial you can use Scaled{J|Igusa}Invariants.

    IgusaInvariants and JInvariants are now computed via
      universal polynomials.  The output is a sequence of 
      five elements of the base ring of the parent of the 
      polynomials given as input to the function; this sequence
      should be viewed as living in weighted projective space.

    IgusaClebschInvariants are now computed in terms of the 
      IgusaInvariants function, instead of vice versa.

    The old functions are retained under different names:
      Quick{Igusa|IgusaClebsch|Clebsch}Invariants.
      They are generally faster than the new functions,
      but they are only designed to work for curves or polynomials
      over fields of characteristic not 2, 3, or 5.

    Added two variants: Scaled{Igusa|J}Invariants.  These give
      the J-invariants scaled by [16, 16^2, 16^3, 16^4, 16^5].
      The point of this is to deal with polynomials over rings
      in which ExactQuotient doesn't work, for instance p-adic
      rings.  This is necessary because IgusaInvariants first
      calculates the scaled invariants and then divides by
      the appropriate powers of 16.

    Changed Uberschiebung to Ueberschiebung.

    NOTE:  *Invariants applied to a curve y^2 + h*y = f
      is equal to *Invariants applied to the polynomial h^2 + 4*f,
      except in characteristic 2, when the latter is undefined.

/*------------------------------------------------------------------

 
        **** Paulette Lieby: 2001-03-16:
 
        AbsoluteInvariants
 
        **** Pierrick Gaudry: 2001-03-19:
 
        IgusaToIgusaClebsch
        IgusaClebschToIgusa
 
        **** Pierrick Gaudry: 2001-03-20:
 
        better names for the 2 previous functions:
           ClebschToIgusaClebsch
	   IgusaClebschToClebsch


	**** Paulette Lieby: 2001-06-27:
	   
	Scheme merge   

 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)

   2001-07: Paulette
   The Scaled and some of the Quick intrinsics have disappeared
   (replaced by functions) -- Scaled and Quick are now varargs
   in the more general functions

   The only exception to this being QuickClebschInvariants
   (no general ClebschInvariants existed before that)
   :: this is now ClebschInvariants
   
   So now we have:

   intrinsic ClebschInvariants(ff::RngUPolElt)
   intrinsic ClebschInvariants(C::CrvHyp) 
   intrinsic IgusaInvariants(h::RngUPolElt, f::RngUPolElt : Scaled)
   intrinsic IgusaInvariants(f::RngUPolElt : Scaled, Quick)
   intrinsic IgusaInvariants(C::CrvHyp : Quick)
   intrinsic JInvariants(h::RngUPolElt, f::RngUPolElt)
   intrinsic JInvariants(f::RngUPolElt : Quick)
   intrinsic JInvariants(C::CrvHyp : Quick)
   intrinsic IgusaClebschInvariants(f::RngUPolElt : Quick)
   intrinsic IgusaClebschInvariants(h::RngUPolElt, f::RngUPolElt)
   intrinsic IgusaClebschInvariants(C::CrvHyp : Quick)
   intrinsic AbsoluteInvariants(C::CrvHyp)

   2001-07: Paulette
   Got it wrong (again!): must reinstall the
   ScaledIgusaInvariants (two protos)

   --------------------------------------------------------------------*/

// forward declarations

forward QuickIgusaInvariantsCurve; 
forward QuickIgusaInvariants; 
forward QuickJInvariantsCurve; 
forward QuickJInvariants; 
forward QuickIgusaClebschInvariants;
forward QuickIgusaClebschInvariantsCurve;



// Given an element f of a 2-variable polynomial ring over some ring K
// and two non-negative integers m and n, compute the (m,n)-th partial
// derivative of f.

function DoublePartialDerivative(f,m,n)
    return Derivative(Derivative(f,m,1),n,2);
end function;


/*--------------------------------------------------------------------*/
// Given two binary forms f and g of (nominal) degrees m and n (which
// forms we take to be elements of a 2-variable polynomial ring over
// some base ring K) and an integer k, compute the "Ueberschiebung"
// (fg)_k, as defined on p. 315 of Mestre.  Return the Ueberschiebung
// and its (nominal) degree.

function Ueberschiebung(f,g,m,n,k)
    K := BaseRing(Parent(f));
    h := Parent(f)!0;
    for j in [0..k] do
	h +:= (-1)^j * Binomial(k,j)
                     * DoublePartialDerivative(f, j, k-j)
                     * DoublePartialDerivative(g, k-j, j);
    end for;
    coef := Factorial(m-k)*Factorial(n-k)/Factorial(m)/Factorial(n);
    h := (K!coef) * h;
    return h, m + n - 2*k;
end function;


/*--------------------------------------------------------------------*/
// Given a single-variable polynomial f of degree at most 6 over a
// ring K, return the associated binary sextic form.

function Homogenization(f)
    T<y,z> := PolynomialRing(BaseRing(Parent(f)),2);
    return &+[ Coefficient(f,j)*y^j*z^(6-j) : j in [0..6]];
    // Numerator(z^6*Evaluate(f,y/z));
end function;


/*--------------------------------------------------------------------*/
// Given a polynomial of degree at most 6, compute the Clebsch
// invariants A, B, C, D (as on p. 317 of Mestre).  This entails
// computing the invariants i, delta, y1, y2, and y3 as well.

intrinsic ClebschInvariants(ff::RngUPolElt) -> SeqEnum
    {Given a polynomial of degree at most 6, compute the Clebsch
    invariants A, B, C, D (as on p. 317 of Mestre) in characteristic 
    other than 2, 3, or 5.}
    require Degree(ff) le 6: "Polynomial must have degree at most 6.";
    R := CoefficientRing(Parent(ff));
    require IsUnit(R!30) : "30 must be invertible in the base ring.";
          
    f := Homogenization(ff);
    fdeg := 6;
    i,     ideg     := Ueberschiebung(f,  f, fdeg,  fdeg, 4);
    delta, deltadeg := Ueberschiebung(i,  i, ideg,  ideg, 2);
    y1,    y1deg    := Ueberschiebung(f,  i, fdeg,  ideg, 4);
    y2,    y2deg    := Ueberschiebung(i, y1, ideg, y1deg, 2);
    y3,    y3deg    := Ueberschiebung(i, y2, ideg, y2deg, 2);
    CT := func< poly | MonomialCoefficient(poly, Parent(poly)!1) >;
    return [CT(Ueberschiebung( f,     f,  fdeg,     fdeg, 6)),
            CT(Ueberschiebung( i,     i,  ideg,     ideg, 4)),
            CT(Ueberschiebung( i, delta,  ideg, deltadeg, 4)),
            CT(Ueberschiebung(y3,    y1, y3deg,    y1deg, 2))];
end intrinsic;

intrinsic ClebschInvariants(C::CrvHyp) -> SeqEnum
    {Compute the Clebsch invariants of a genus 2 curve in 
    characteristic other than 2, 3, or 5.}
    require Genus(C) eq 2: "Curve must be of genus 2.";
    return ClebschInvariants(h^2 + 4*f)
        where f, h := HyperellipticPolynomials(C);
end intrinsic;



/*--------------------------------------------------------------------*/
// Given a polynomial of degree at most 6, compute the Igusa-Clebsch
// invariants A', B', C', D' (as on p. 319 of Mestre).


function QuickIgusaClebschInvariants(f) 
    // Given a polynomial of degree at most 6, compute 
    // the Igusa-Clebsch invariants A', B', C', D'
    // (as on p. 319 of Mestre).

    if not (Degree(f) le 6) then
	vprint Igusa : "Warning: Polynomial must have degree at most 6.";
    end if;

    A, B, C, D := Explode(ClebschInvariants(f));
    return [-120*A,
            -720*A^2 + 6750*B,
             8640*A^3 - 108000*A*B + 202500*C,
            -62208*A^5 + 972000*A^3*B + 1620000*A^2*C 
            - 3037500*A*B^2 - 6075000*B*C - 4556250*D];
end function;

function QuickIgusaClebschInvariantsCurve(C) 
    // Compute the Igusa-Clebsch invariants of a genus 2 curve.

    if not (Genus(C) eq 2) then
	vprint Igusa : "Warning: Curve must be of genus 2.";
    end if;

    return QuickIgusaClebschInvariants(h^2 + 4*f)
         where f, h := HyperellipticPolynomials(C);
end function;


/*--------------------------------------------------------------------*/
// Given a polynomial of degree at most 6, compute the J-invariants
// J_2, J_4, J_6, J_8, J_10 (as on p. 324 of Mestre).

// NOTE: The value should really live in a weighted projective space
//       (with weights 2,4,6,8,10)


function QuickJInvariants(f)
    // Given a polynomial of degree at most 6, compute the 
    // J-invariants J_2, J_4, J_6, J_8, J_10 of the polynomial
    // (as on p. 324 of Mestre).

    if not (Degree(f) le 6) then
	print "Polynomial must have degree at most 6.";
    end if;

    K   := BaseRing(Parent(f));

    if not (IsUnit(K!30)) then
	vprint Igusa : "Warning: 30 must be invertible in the base ring.";
    end if;

    v   := QuickIgusaClebschInvariants(f);
    J2  := (K!(1/8))*v[1];
    J4  := (K!(1/96))*(4*J2^2 - v[2]);
    J6  := (K!(1/576))*(8*J2^3 - 160*J2*J4 - v[3]);
    J8  := (K!(1/4))*(J2*J6 - J4^2);
    J10 := (K!(1/4096))*v[4];
    return [J2, J4, J6, J8, J10];
end function;

function QuickIgusaInvariants(f) 
    // Given a polynomial of degree at most 6, compute the J-invariants
    // J_2, J_4, J_6, J_8, J_10 of the polynomial (as on p. 324 of Mestre).
    return QuickJInvariants(f);
end function;

function QuickJInvariantsCurve(C) 
    //Compute the J-invariants J_2, J_4, J_6, J_8, J_10 of a genus 2 curve
    // over a field of characteristic not 2, 3, or 5.
    if not (Genus(C) eq 2) then
	print "Curve must be of genus 2.";
    elif (Characteristic(BaseField(C)) in {2,3,5}) then
	print "Characteristic of base field must not be 2, 3, or 5.";
    end if;
    return QuickJInvariants(h^2 + 4*f)
        where f, h := HyperellipticPolynomials(C);
end function;

function QuickIgusaInvariantsCurve(C)
    //Compute the J-invariants J_2, J_4, J_6, J_8, J_10 of a genus 2 curve
    // over a field of characteristic not 2, 3, or 5.}
    return QuickJInvariantsCurve(C);
end function;


/*--------------------------------------------------------------------*/
// The functions below compute invariants using universal polynomials.

function IgusaInvariantsCharacteristicTwo(f,h)
  // The J-invariants of y^2 + h*y = f over a ring of characteristic 2.
  a0,a1,a2,a3 := Explode([ Coefficient(h,i) : i in [0..3] ]);
  b0,b1,b2,b3,b4,b5,b6 := Explode([ Coefficient(f,i) : i in [0..6] ]);
  return [
  a0^2*a3^2 + a1^2*a2^2,
  a0^4*a3^2*b6 + a0^3*a1*a3^2*b5 + a0^3*a2^2*a3*b5 + a0^3*a3^3*b3 + 
   a0^2*a1^2*a2^2*b6 + a0^2*a1^2*a3^2*b4 + a0^2*a1*a2^3*b5 + 
   a0^2*a1*a2*a3^2*b3 + a0^2*a2^3*a3*b3 + a0^2*a2^2*a3^2*b2 + 
   a0^2*a2*a3^3*b1 + a0^2*a3^4*b0 + a0^2*a3^2*b3^2 + a0*a1^4*a3*b5 + 
   a0*a1^3*a2^2*b5 + a0*a1^3*a3^2*b3 + a0*a1^2*a2^2*a3*b3 + a0*a1^2*a3^3*b1 +
   a0*a1*a2^4*b3 + a0*a2^4*a3*b1 + a1^5*a2*b5 + a1^4*a2^2*b4 + 
   a1^4*a2*a3*b3 + a1^3*a2^3*b3 + a1^3*a2*a3^2*b1 + a1^2*a2^4*b2 + 
   a1^2*a2^3*a3*b1 + a1^2*a2^2*a3^2*b0 + a1^2*a2^2*b3^2 + a1*a2^5*b1,
  a0^6*a3^2*b6^2 + a0^4*a1^2*a2^2*b6^2 + a0^4*a1^2*a3^2*b5^2 + 
   a0^4*a2^4*b5^2 + a0^4*a3^4*b3^2 + a0^2*a1^4*a2^2*b5^2 + 
   a0^2*a1^4*a3^2*b4^2 + a0^2*a2^6*b3^2 + a0^2*a2^4*a3^2*b2^2 + 
   a0^2*a2^2*a3^4*b1^2 + a0^2*a3^6*b0^2 + a0^2*a3^2*b3^4 + a1^8*b5^2 + 
   a1^6*a2^2*b4^2 + a1^6*a3^2*b3^2 + a1^4*a2^4*b3^2 + a1^4*a3^4*b1^2 + 
   a1^2*a2^6*b2^2 + a1^2*a2^4*a3^2*b1^2 + a1^2*a2^2*a3^4*b0^2 + 
   a1^2*a2^2*b3^4 + a2^8*b1^2,
  a0^8*a3^4*b6^2 + a0^8*a3^2*b6^3 + a0^8*b6^4 + a0^7*a1*a3^2*b5*b6^2 + 
   a0^7*a2^2*a3^3*b5*b6 + a0^7*a2^2*a3*b5*b6^2 +  a0^7*a2*a3^4*b5^2 + 
   a0^7*a3^5*b4*b5 + a0^7*a3^3*b3*b6^2 + a0^7*a3^3*b5^3 + 
   a0^6*a1^2*a2^2*b6^3 + a0^6*a1^2*a3^2*b4*b6^2 + a0^6*a1^2*a3^2*b5^2*b6 + 
   a0^6*a1*a2^3*a3^2*b5*b6 + a0^6*a1*a2^3*b5*b6^2 + a0^6*a1*a2^2*a3^3*b5^2 + 
   a0^6*a1*a2*a3^4*b4*b5 + a0^6*a1*a2*a3^2*b3*b6^2 + a0^6*a1*a2*a3^2*b5^3 + 
   a0^6*a1*a3^5*b3*b5 + a0^6*a2^6*b6^2 + a0^6*a2^5*a3*b5*b6 + 
   a0^6*a2^4*a3^2*b4*b6 + a0^6*a2^4*a3^2*b5^2 + a0^6*a2^3*a3^3*b3*b6 + 
   a0^6*a2^3*a3*b3*b6^2 + a0^6*a2^2*a3^4*b2*b6 + a0^6*a2^2*a3^4*b3*b5 + 
   a0^6*a2^2*a3^2*b2*b6^2 + a0^6*a2*a3^5*b2*b5 + a0^6*a2*a3^5*b3*b4 + 
   a0^6*a2*a3^3*b1*b6^2 + a0^6*a2*a3^3*b3*b5^2 + a0^6*a3^6*b1*b5 + 
   a0^6*a3^6*b2*b4 + a0^6*a3^6*b3^2 + a0^6*a3^4*b0*b6^2 + a0^6*a3^4*b2*b5^2 +
   a0^6*a3^4*b3^2*b6 + a0^6*a3^2*b3^2*b6^2 + a0^5*a1^4*a3^3*b5*b6 + 
   a0^5*a1^4*a3*b5*b6^2 + a0^5*a1^3*a2^2*b5*b6^2 + a0^5*a1^3*a3^2*b3*b6^2 + 
   a0^5*a1^3*a3^2*b5^3 +  a0^5*a1^2*a2^3*a3^2*b5^2 + 
   a0^5*a1^2*a2^2*a3^3*b4*b5 + a0^5*a1^2*a2^2*a3*b3*b6^2 + 
   a0^5*a1^2*a2*a3^4*b3*b5 + a0^5*a1^2*a3^5*b2*b5 + a0^5*a1^2*a3^3*b1*b6^2 + 
   a0^5*a1^2*a3^3*b3*b5^2 + a0^5*a1*a2^6*b5*b6 + a0^5*a1*a2^5*a3*b5^2 + 
   a0^5*a1*a2^4*a3^2*b4*b5 + a0^5*a1*a2^4*b3*b6^2 + a0^5*a1*a2^3*a3^3*b3*b5 +
   a0^5*a1*a2^2*a3^4*b1*b6 + a0^5*a1*a2^2*a3^4*b3*b4 + 
   a0^5*a1*a2^2*a3^2*b3*b5^2 + a0^5*a1*a2*a3^5*b1*b5 + a0^5*a1*a2*a3^5*b3^2 +
   a0^5*a1*a3^6*b1*b4 + a0^5*a1*a3^6*b2*b3 + a0^5*a1*a3^4*b1*b5^2 + 
   a0^5*a1*a3^4*b3^2*b5 + a0^5*a2^7*b5^2 + a0^5*a2^6*a3*b3*b6 + 
   a0^5*a2^6*a3*b4*b5 + a0^5*a2^5*a3^2*b3*b5 + a0^5*a2^4*a3^3*b3*b4 + 
   a0^5*a2^4*a3*b1*b6^2 + a0^5*a2^3*a3^4*b1*b5 + a0^5*a2^2*a3^5*b1*b4 + 
   a0^5*a2^2*a3^3*b1*b5^2 + a0^5*a2^2*a3^3*b3^2*b5 + a0^5*a2*a3^6*b1*b3 + 
   a0^5*a3^7*b1*b2 + a0^5*a3^5*b3^3 + a0^4*a1^5*a2*a3^2*b5*b6 + 
   a0^4*a1^5*a2*b5*b6^2 + a0^4*a1^5*a3^3*b5^2 + a0^4*a1^4*a2^2*b4*b6^2 + 
   a0^4*a1^4*a2^2*b5^2*b6 + a0^4*a1^4*a2*a3^3*b3*b6 + 
   a0^4*a1^4*a2*a3*b3*b6^2 + a0^4*a1^4*a3^4*b2*b6 + a0^4*a1^4*a3^4*b3*b5 + 
   a0^4*a1^4*a3^4*b4^2 + a0^4*a1^4*a3^2*b4^2*b6 + a0^4*a1^4*a3^2*b4*b5^2 +
   a0^4*a1^4*b5^4 + a0^4*a1^3*a2^3*a3^2*b4*b5 + a0^4*a1^3*a2^3*b3*b6^2 + 
   a0^4*a1^3*a2^2*a3^3*b3*b5 + a0^4*a1^3*a2*a3^4*b2*b5 + 
   a0^4*a1^3*a2*a3^2*b1*b6^2 + a0^4*a1^3*a2*a3^2*b3*b5^2 + 
   a0^4*a1^3*a3^5*b1*b5 + a0^4*a1^2*a2^6*b4*b6 + a0^4*a1^2*a2^5*a3*b4*b5 + 
   a0^4*a1^2*a2^4*a3^2*b3*b5 + a0^4*a1^2*a2^4*a3^2*b4^2 + 
   a0^4*a1^2*a2^4*b2*b6^2 + a0^4*a1^2*a2^3*a3^3*b3*b4 +
   a0^4*a1^2*a2^3*a3*b1*b6^2 + a0^4*a1^2*a2^2*a3^4*b0*b6 + 
   a0^4*a1^2*a2^2*a3^4*b3^2 + a0^4*a1^2*a2^2*a3^2*b0*b6^2 + 
   a0^4*a1^2*a2^2*a3^2*b2*b5^2 + a0^4*a1^2*a2^2*b3^2*b6^2 + 
   a0^4*a1^2*a2*a3^5*b0*b5 + a0^4*a1^2*a2*a3^5*b2*b3 + 
   a0^4*a1^2*a2*a3^3*b1*b5^2 + a0^4*a1^2*a3^6*b0*b4 + 
   a0^4*a1^2*a3^6*b1*b3 + a0^4*a1^2*a3^4*b3^2*b4 + 
   a0^4*a1^2*a3^2*b3^2*b5^2 + a0^4*a1*a2^7*b3*b6 + a0^4*a1*a2^7*b4*b5 + 
   a0^4*a1*a2^5*a3^2*b3*b4 + a0^4*a1*a2^5*b1*b6^2 + a0^4*a1*a2^4*a3^3*b3^2 +
   a0^4*a1*a2^3*a3^4*b1*b4 + a0^4*a1*a2^3*a3^2*b1*b5^2 + 
   a0^4*a1*a2^3*a3^2*b3^2*b5 + a0^4*a1*a2^2*a3^5*b1*b3 + 
   a0^4*a1*a2*a3^6*b1*b2 + a0^4*a1*a2*a3^4*b3^3 + a0^4*a1*a3^7*b1^2 + 
   a0^4*a2^8*b4^2 + a0^4*a2^7*a3*b1*b6 + a0^4*a2^7*a3*b2*b5 + 
   a0^4*a2^7*a3*b3*b4 + a0^4*a2^6*a3^2*b0*b6 + a0^4*a2^6*a3^2*b2*b4 + 
   a0^4*a2^6*a3^2*b3^2 + a0^4*a2^5*a3^3*b0*b5 + a0^4*a2^5*a3^3*b1*b4 + 
   a0^4*a2^5*a3*b3^2*b5 + a0^4*a2^4*a3^4*b0*b4 + a0^4*a2^4*a3^4*b1*b3 +
   a0^4*a2^4*a3^4*b2^2 + a0^4*a2^4*a3^2*b2^2*b6 + a0^4*a2^4*a3^2*b3^2*b4 + 
   a0^4*a2^3*a3^3*b3^3 + a0^4*a2^2*a3^4*b2*b3^2 + a0^4*a2*a3^5*b1^2*b5 + 
   a0^4*a2*a3^5*b1*b3^2 + a0^4*a3^8*b0^2 + a0^4*a3^6*b0^2*b6 + 
   a0^4*a3^6*b0*b3^2 + a0^4*a3^6*b1^2*b4 + a0^4*a3^4*b1^2*b5^2 + 
   a0^4*a3^4*b3^4 + a0^4*a3^2*b3^4*b6 + a0^3*a1^6*a2^2*a3*b5*b6 + 
   a0^3*a1^6*a2*a3^2*b5^2 + a0^3*a1^6*a3^3*b4*b5 + a0^3*a1^6*a3*b5^3 + 
   a0^3*a1^5*a2^2*a3^2*b3*b6 + a0^3*a1^5*a2^2*b5^3 + 
   a0^3*a1^5*a2*a3^3*b3*b5 + a0^3*a1^5*a3^4*b1*b6 + a0^3*a1^5*a3^4*b2*b5 + 
   a0^3*a1^5*a3^2*b3*b5^2 + a0^3*a1^5*a3^2*b4^2*b5 + 
   a0^3*a1^4*a2^3*a3^2*b3*b5 + a0^3*a1^4*a2^2*a3^3*b1*b6 + 
   a0^3*a1^4*a2^2*a3^3*b2*b5 + a0^3*a1^4*a2^2*a3*b3*b5^2 + 
   a0^3*a1^4*a2^2*a3*b4^2*b5 + a0^3*a1^4*a2*a3^4*b3^2 + 
   a0^3*a1^4*a3^5*b2*b3 + a0^3*a1^4*a3^3*b1*b5^2 + a0^3*a1^4*a3^3*b3*b4^2 + 
   a0^3*a1^3*a2^6*b3*b6 + a0^3*a1^3*a2^5*a3*b3*b5 + 
   a0^3*a1^3*a2^4*a3^2*b3*b4 + a0^3*a1^3*a2^3*a3^3*b3^2 +
   a0^3*a1^3*a2^2*a3^4*b2*b3 + a0^3*a1^3*a2*a3^5*b1*b3 + 
   a0^3*a1^3*a3^6*b0*b3 + a0^3*a1^3*a3^4*b3^3 + a0^3*a1^2*a2^7*b3*b5 + 
   a0^3*a1^2*a2^6*a3*b1*b6 + a0^3*a1^2*a2^6*a3*b2*b5 + 
   a0^3*a1^2*a2^4*a3^3*b0*b5 + a0^3*a1^2*a2^4*a3^3*b1*b4 + 
   a0^3*a1^2*a2^3*a3^4*b1*b3 + a0^3*a1^2*a2^2*a3^5*b1*b2 + 
   a0^3*a1^2*a2*a3^6*b1^2 + a0^3*a1^2*a3^7*b0*b1 + a0^3*a1^2*a3^5*b1^2*b5 +
   a0^3*a1^2*a3^5*b1*b3^2 + a0^3*a1*a2^8*b1*b6 + a0^3*a1*a2^8*b2*b5 + 
   a0^3*a1*a2^8*b3*b4 + a0^3*a1*a2^7*a3*b3^2 + a0^3*a1*a2^6*a3^2*b2*b3 + 
   a0^3*a1*a2^6*b3^2*b5 + a0^3*a1*a2^5*a3^3*b1*b3 + 
   a0^3*a1*a2^4*a3^4*b0*b3 + a0^3*a1*a2^4*a3^2*b2^2*b5 + 
   a0^3*a1*a2^2*a3^4*b1^2*b5 + a0^3*a1*a3^6*b0^2*b5 + a0^3*a1*a3^6*b1^2*b3 +
   a0^3*a1*a3^2*b3^4*b5 + a0^3*a2^9*b3^2 + a0^3*a2^8*a3*b0*b5 + 
   a0^3*a2^8*a3*b1*b4 + a0^3*a2^8*a3*b2*b3 + a0^3*a2^7*a3^2*b1*b3 + 
   a0^3*a2^6*a3^3*b1*b2 + a0^3*a2^6*a3*b2^2*b5 + a0^3*a2^6*a3*b3^3 + 
   a0^3*a2^5*a3^4*b1^2 + a0^3*a2^4*a3^5*b0*b1 + a0^3*a2^4*a3^3*b1^2*b5 + 
   a0^3*a2^4*a3^3*b2^2*b3 + a0^3*a2^2*a3^5*b0^2*b5 + 
   a0^3*a2^2*a3^5*b1^2*b3 + a0^3*a2^2*a3*b3^4*b5 + a0^3*a3^7*b0^2*b3 + 
   a0^3*a3^7*b1^3 + a0^3*a3^3*b3^5 + a0^2*a1^8*a2^2*b6^2 + 
   a0^2*a1^8*a2*a3*b5*b6 + a0^2*a1^8*a3^2*b4*b6 + a0^2*a1^8*a3^2*b5^2 + 
   a0^2*a1^7*a2^3*b5*b6 + a0^2*a1^7*a2^2*a3*b5^2 + a0^2*a1^7*a2*a3^2*b4*b5 +
   a0^2*a1^7*a2*b5^3 + a0^2*a1^7*a3^3*b3*b5 + a0^2*a1^6*a2^3*a3*b3*b6 + 
   a0^2*a1^6*a2^2*a3^2*b3*b5 + a0^2*a1^6*a2^2*b4^2*b6 + 
   a0^2*a1^6*a2^2*b4*b5^2 + a0^2*a1^6*a2*a3^3*b3*b4 + 
   a0^2*a1^6*a2*a3*b3*b5^2 + a0^2*a1^6*a3^4*b0*b6 + a0^2*a1^6*a3^4*b2*b4 + 
   a0^2*a1^6*a3^4*b3^2 + a0^2*a1^6*a3^2*b3^2*b6 + a0^2*a1^6*a3^2*b4^3 + 
   a0^2*a1^5*a2^3*a3^2*b1*b6 + a0^2*a1^5*a2^3*a3^2*b2*b5 + 
   a0^2*a1^5*a2^3*b3*b5^2 + a0^2*a1^5*a2^3*b4^2*b5 + 
   a0^2*a1^5*a2*a3^4*b2*b3 + a0^2*a1^5*a2*a3^2*b1*b5^2 + 
   a0^2*a1^5*a2*a3^2*b3*b4^2 + a0^2*a1^5*a3^5*b1*b3 + 
   a0^2*a1^4*a2^6*b2*b6 + a0^2*a1^4*a2^5*a3*b2*b5 + 
   a0^2*a1^4*a2^4*a3^2*b1*b5 + a0^2*a1^4*a2^4*a3^2*b2*b4 + 
   a0^2*a1^4*a2^4*b3^2*b6 + a0^2*a1^4*a2^3*a3^3*b2*b3 + 
   a0^2*a1^4*a2^3*a3*b1*b5^2 + a0^2*a1^4*a2^3*a3*b3*b4^2 + 
   a0^2*a1^4*a2^2*a3^4*b1*b3 + a0^2*a1^4*a2^2*a3^4*b2^2 + 
   a0^2*a1^4*a2^2*a3^2*b0*b5^2 + a0^2*a1^4*a2^2*a3^2*b2*b4^2 + 
   a0^2*a1^4*a2^2*b3^2*b5^2 + a0^2*a1^4*a2*a3^5*b1*b2 + 
   a0^2*a1^4*a2*a3^3*b1*b4^2 + a0^2*a1^4*a3^6*b0*b2 + a0^2*a1^4*a3^6*b1^2 +
   a0^2*a1^4*a3^4*b0*b4^2 + a0^2*a1^4*a3^4*b2*b3^2 + 
   a0^2*a1^4*a3^2*b3^2*b4^2 + a0^2*a1^3*a2^7*b1*b6 + a0^2*a1^3*a2^7*b2*b5 + 
   a0^2*a1^3*a2^5*a3^2*b0*b5 + a0^2*a1^3*a2^5*a3^2*b1*b4 + 
   a0^2*a1^3*a2^4*a3^3*b1*b3 + a0^2*a1^3*a2^3*a3^4*b1*b2 + 
   a0^2*a1^3*a2^2*a3^5*b1^2 + a0^2*a1^3*a2*a3^6*b0*b1 + 
   a0^2*a1^3*a2*a3^4*b1^2*b5 + a0^2*a1^3*a2*a3^4*b1*b3^2 + 
   a0^2*a1^2*a2^8*b0*b6 + a0^2*a1^2*a2^8*b2*b4 + a0^2*a1^2*a2^7*a3*b2*b3 + 
   a0^2*a1^2*a2^6*a3^2*b1*b3 + a0^2*a1^2*a2^6*b2^2*b6 + 
   a0^2*a1^2*a2^6*b3^2*b4 + a0^2*a1^2*a2^5*a3^3*b0*b3 + 
   a0^2*a1^2*a2^4*a3^2*b1^2*b6 + a0^2*a1^2*a2^4*a3^2*b2^2*b4 + 
   a0^2*a1^2*a2^2*a3^4*b0^2*b6 + a0^2*a1^2*a2^2*a3^4*b1^2*b4 + 
   a0^2*a1^2*a2^2*b3^4*b6 + a0^2*a1^2*a2*a3^5*b1^2*b3 + 
   a0^2*a1^2*a3^6*b0^2*b4 + a0^2*a1^2*a3^2*b3^4*b4 + a0^2*a1*a2^9*b0*b5 + 
   a0^2*a1*a2^9*b1*b4 + a0^2*a1*a2^9*b2*b3 + a0^2*a1*a2^7*a3^2*b1*b2 + 
   a0^2*a1*a2^7*b2^2*b5 + a0^2*a1*a2^7*b3^3 + a0^2*a1*a2^6*a3^3*b1^2 + 
   a0^2*a1*a2^5*a3^4*b0*b1 + a0^2*a1*a2^5*a3^2*b1^2*b5 + 
   a0^2*a1*a2^5*a3^2*b2^2*b3 + a0^2*a1*a2^3*a3^4*b0^2*b5 + 
   a0^2*a1*a2^3*a3^4*b1^2*b3 + a0^2*a1*a2^3*b3^4*b5 + 
   a0^2*a1*a2*a3^6*b0^2*b3 + a0^2*a1*a2*a3^6*b1^3 + a0^2*a1*a2*a3^2*b3^5 + 
   a0^2*a2^10*b2^2 + a0^2*a2^9*a3*b0*b3 + a0^2*a2^9*a3*b1*b2 + 
   a0^2*a2^8*a3^2*b0*b2 + a0^2*a2^8*a3^2*b1^2 + a0^2*a2^7*a3*b1*b3^2 + 
   a0^2*a2^7*a3*b2^2*b3 + a0^2*a2^6*a3^2*b0*b3^2 + a0^2*a2^6*a3^2*b2^3 + 
   a0^2*a2^6*b3^4 + a0^2*a2^5*a3^3*b1^2*b3 + a0^2*a2^5*a3^3*b1*b2^2 + 
   a0^2*a2^4*a3^4*b0*b2^2 + a0^2*a2^4*a3^4*b1^2*b2 + 
   a0^2*a2^4*a3^2*b2^2*b3^2 + a0^2*a2^3*a3^5*b0^2*b3 + a0^2*a2^3*a3^5*b1^3 +
   a0^2*a2^3*a3*b3^5 + a0^2*a2^2*a3^6*b0^2*b2 + a0^2*a2^2*a3^6*b0*b1^2 + 
   a0^2*a2^2*a3^4*b1^2*b3^2 + a0^2*a2^2*a3^2*b2*b3^4 + 
   a0^2*a2*a3^7*b0^2*b1 + a0^2*a2*a3^3*b1*b3^4 + a0^2*a3^8*b0^3 + 
   a0^2*a3^6*b0^2*b3^2 + a0^2*a3^4*b0*b3^4 + a0^2*a3^2*b3^6 + 
   a0*a1^10*a3*b5*b6 + a0*a1^9*a2^2*b5*b6 + a0*a1^9*a2*a3*b5^2 + 
   a0*a1^9*a3^2*b3*b6 + a0*a1^9*a3^2*b4*b5 + a0*a1^8*a2^2*a3*b3*b6 + 
   a0*a1^8*a3^3*b1*b6 + a0*a1^8*a3^3*b2*b5 + a0*a1^8*a3^3*b3*b4 + 
   a0*a1^8*a3*b4^2*b5 + a0*a1^7*a2^4*b3*b6 + a0*a1^7*a2^3*a3*b3*b5 + 
   a0*a1^7*a2^2*a3^2*b3*b4 + a0*a1^7*a2^2*b4^2*b5 + a0*a1^7*a2*a3^3*b3^2 +
   a0*a1^7*a3^4*b0*b5 + a0*a1^7*a3^4*b1*b4 + a0*a1^7*a3^4*b2*b3 + 
   a0*a1^7*a3^2*b3^2*b5 + a0*a1^7*a3^2*b3*b4^2 + a0*a1^6*a2^4*a3*b1*b6 + 
   a0*a1^6*a2^2*a3^3*b0*b5 + a0*a1^6*a2^2*a3^3*b1*b4 + 
   a0*a1^6*a2^2*a3*b3^2*b5 + a0*a1^6*a2^2*a3*b3*b4^2 + a0*a1^6*a3^5*b0*b3 +
   a0*a1^6*a3^5*b1*b2 + a0*a1^6*a3^3*b1*b4^2 + a0*a1^6*a3^3*b3^3 +
   a0*a1^5*a2^6*b1*b6 + a0*a1^5*a2^5*a3*b1*b5 + a0*a1^5*a2^4*a3^2*b1*b4 +
   a0*a1^5*a2^4*b1*b5^2 + a0*a1^5*a2^4*b3^2*b5 + a0*a1^5*a2^4*b3*b4^2 +
   a0*a1^5*a2^3*a3^3*b1*b3 + a0*a1^5*a2^2*a3^4*b1*b2 +
   a0*a1^5*a2*a3^5*b1^2 + a0*a1^5*a3^6*b0*b1 + a0*a1^5*a3^4*b1*b3^2 +
   a0*a1^4*a2^7*b1*b5 + a0*a1^4*a2^6*a3*b0*b5 + a0*a1^4*a2^4*a3*b1*b4^2 +
   a0*a1^4*a2^4*a3*b2^2*b5 + a0*a1^4*a2^4*a3*b3^3 + a0*a1^4*a3^5*b0^2*b5 +
   a0*a1^4*a3*b3^4*b5 + a0*a1^3*a2^8*b0*b5 + a0*a1^3*a2^8*b1*b4 + 
   a0*a1^3*a2^7*a3*b1*b3 + a0*a1^3*a2^6*a3^2*b0*b3 + a0*a1^3*a2^6*b2^2*b5 +
   a0*a1^3*a2^6*b3^3 + a0*a1^3*a2^4*a3^2*b1^2*b5 + 
   a0*a1^3*a2^4*a3^2*b2^2*b3 + a0*a1^3*a2^2*a3^4*b0^2*b5 +
   a0*a1^3*a2^2*b3^4*b5 + a0*a1^3*a3^6*b0^2*b3 + a0*a1^3*a3^2*b3^5 +
   a0*a1^2*a2^9*b1*b3 + a0*a1^2*a2^8*a3*b0*b3 + a0*a1^2*a2^7*a3^2*b1^2 + 
   a0*a1^2*a2^6*a3^3*b0*b1 + a0*a1^2*a2^6*a3*b1*b3^2 +
   a0*a1^2*a2^6*a3*b2^2*b3 + a0*a1^2*a2^4*a3^3*b1^2*b3 +
   a0*a1^2*a2^4*a3^3*b1*b2^2 + a0*a1^2*a2^2*a3^5*b0^2*b3 +
   a0*a1^2*a2^2*a3*b3^5 + a0*a1^2*a3^7*b0^2*b1 + a0*a1^2*a3^3*b1*b3^4 +
   a0*a1*a2^10*b0*b3 + a0*a1*a2^10*b1*b2 + a0*a1*a2^9*a3*b1^2 +
   a0*a1*a2^8*a3^2*b0*b1 + a0*a1*a2^8*b1*b3^2 + a0*a1*a2^8*b2^2*b3 +
   a0*a1*a2^6*a3^2*b1^2*b3 + a0*a1*a2^4*a3^4*b0^2*b3 + a0*a1*a2^4*b3^5 + 
   a0*a2^11*b1^2 + a0*a2^10*a3*b0*b1 + a0*a2^8*a3*b1*b2^2 +
   a0*a2^6*a3^3*b1^3 + a0*a2^4*a3^5*b0^2*b1 + a0*a2^4*a3*b1*b3^4 +
   a1^12*b6^2 + a1^11*a2*b5*b6 + a1^11*a3*b5^2 + a1^10*a2^2*b4*b6 +
   a1^10*a2*a3*b3*b6 + a1^10*a2*a3*b4*b5 + a1^10*a3^2*b4^2 +
   a1^9*a2^3*b3*b6 + a1^9*a2^2*a3*b3*b5 + a1^9*a2*a3^2*b1*b6 +
   a1^9*a2*a3^2*b2*b5 + a1^9*a2*a3^2*b3*b4 + a1^9*a2*b4^2*b5 +
   a1^9*a3^3*b3^2 + a1^8*a2^4*b2*b6 + a1^8*a2^3*a3*b1*b6 +
   a1^8*a2^3*a3*b2*b5 + a1^8*a2^2*a3^2*b0*b6 + a1^8*a2^2*a3^2*b2*b4 +
   a1^8*a2^2*b3^2*b6 + a1^8*a2^2*b4^3 + a1^8*a2*a3^3*b0*b5 + 
   a1^8*a2*a3^3*b1*b4 + a1^8*a2*a3^3*b2*b3 + a1^8*a2*a3*b3^2*b5 +
   a1^8*a2*a3*b3*b4^2 + a1^8*a3^4*b2^2 + a1^8*b4^4 + a1^7*a2^5*b1*b6 +
   a1^7*a2^4*a3*b1*b5 + a1^7*a2^3*a3^2*b0*b5 + a1^7*a2^3*a3^2*b1*b4 +
   a1^7*a2^3*b3^2*b5 + a1^7*a2^3*b3*b4^2 + a1^7*a2^2*a3^3*b1*b3 +
   a1^7*a2*a3^4*b0*b3 + a1^7*a2*a3^4*b1*b2 + a1^7*a2*a3^2*b1*b4^2 + 
   a1^7*a2*a3^2*b3^3 + a1^7*a3^5*b1^2 + a1^6*a2^6*b0*b6 + 
   a1^6*a2^5*a3*b0*b5 + a1^6*a2^4*a3^2*b0*b4 + a1^6*a2^4*b0*b5^2 +
   a1^6*a2^4*b2*b4^2 + a1^6*a2^4*b3^2*b4 + a1^6*a2^3*a3^3*b0*b3 +
   a1^6*a2^3*a3*b1*b4^2 + a1^6*a2^3*a3*b3^3 + a1^6*a2^2*a3^4*b0*b2 + 
   a1^6*a2^2*a3^2*b0*b4^2 + a1^6*a2^2*a3^2*b2*b3^2 + a1^6*a2^2*b3^2*b4^2 +
   a1^6*a2*a3^5*b0*b1 + a1^6*a2*a3^3*b1*b3^2 + a1^6*a3^6*b0^2 +
   a1^6*a3^2*b3^4 + a1^5*a2^7*b0*b5 + a1^5*a2^5*b1*b4^2 +
   a1^5*a2^5*b2^2*b5 + a1^5*a2^5*b3^3 + a1^5*a2*a3^4*b0^2*b5 +
   a1^5*a2*b3^4*b5 + a1^4*a2^8*b0*b4 + a1^4*a2^7*a3*b0*b3 +
   a1^4*a2^6*b1^2*b6 + a1^4*a2^6*b2^2*b4 + a1^4*a2^6*b2*b3^2 +
   a1^4*a2^5*a3*b1^2*b5 + a1^4*a2^5*a3*b1*b3^2 + a1^4*a2^5*a3*b2^2*b3 + 
   a1^4*a2^4*a3^2*b0*b3^2 + a1^4*a2^4*b1^2*b5^2 + a1^4*a2^2*a3^4*b0^2*b4 +
   a1^4*a2^2*b3^4*b4 + a1^4*a2*a3^5*b0^2*b3 + a1^4*a2*a3*b3^5 +
   a1^3*a2^9*b0*b3 + a1^3*a2^7*a3^2*b0*b1 + a1^3*a2^7*b1*b3^2 +
   a1^3*a2^7*b2^2*b3 + a1^3*a2^5*a3^2*b1^2*b3 + a1^3*a2^5*a3^2*b1*b2^2 +
   a1^3*a2^3*a3^4*b0^2*b3 + a1^3*a2^3*b3^5 + a1^3*a2*a3^6*b0^2*b1 + 
   a1^3*a2*a3^2*b1*b3^4 + a1^2*a2^10*b0*b2 + a1^2*a2^9*a3*b0*b1 +
   a1^2*a2^8*a3^2*b0^2 + a1^2*a2^8*b0*b3^2 + a1^2*a2^8*b2^3 +
   a1^2*a2^7*a3*b1*b2^2 + a1^2*a2^6*a3^2*b0*b2^2 + a1^2*a2^6*a3^2*b1^2*b2 +
   a1^2*a2^6*b2^2*b3^2 + a1^2*a2^5*a3^3*b1^3 + a1^2*a2^4*a3^4*b0^2*b2 + 
   a1^2*a2^4*a3^4*b0*b1^2 + a1^2*a2^4*a3^2*b1^2*b3^2 + a1^2*a2^4*b2*b3^4 +
   a1^2*a2^3*a3^5*b0^2*b1 + a1^2*a2^3*a3*b1*b3^4 + a1^2*a2^2*a3^6*b0^3 +
   a1^2*a2^2*a3^4*b0^2*b3^2 + a1^2*a2^2*a3^2*b0*b3^4 + a1^2*a2^2*b3^6 +
   a1*a2^11*b0*b1 + a1*a2^9*b1*b2^2 + a1*a2^7*a3^2*b1^3 +
   a1*a2^5*a3^4*b0^2*b1 + a1*a2^5*b1*b3^4 + a2^12*b0^2 + a2^8*b2^4 +
   a2^4*a3^4*b1^4 + a3^8*b0^4 + b3^8,
  a0^10*a3^4*b6^3 + a0^9*a1*a3^4*b5*b6^2 + a0^9*a2*a3^4*b5^2*b6 +
   a0^9*a3^5*b3*b6^2 + a0^9*a3^5*b4*b5*b6 + a0^9*a3^5*b5^3 +
   a0^9*a3^3*b5^3*b6 + a0^8*a1^2*a3^4*b4*b6^2 + a0^8*a1*a2*a3^4*b3*b6^2 +
   a0^8*a1*a2*a3^4*b4*b5*b6 + a0^8*a1*a2*a3^2*b5^3*b6 +
   a0^8*a1*a3^5*b3*b5*b6 + a0^8*a1*a3^5*b4*b5^2 + a0^8*a1*a3^3*b5^4 +
   a0^8*a2^2*a3^4*b4^2*b6 + a0^8*a2^2*b5^4*b6 + a0^8*a2*a3^5*b1*b6^2 +
   a0^8*a2*a3^5*b2*b5*b6 + a0^8*a2*a3^5*b3*b4*b6 + a0^8*a2*a3^5*b4^2*b5 +
   a0^8*a2*a3^3*b3*b5^2*b6 + a0^8*a2*a3*b5^5 + a0^8*a3^6*b0*b6^2 +
   a0^8*a3^6*b1*b5*b6 + a0^8*a3^6*b2*b4*b6 + a0^8*a3^6*b2*b5^2 +
   a0^8*a3^6*b3^2*b6 + a0^8*a3^6*b3*b4*b5 + a0^8*a3^6*b4^3 +
   a0^8*a3^4*b2*b5^2*b6 + a0^8*a3^4*b3^2*b6^2 + a0^8*a3^4*b3*b5^3 +
   a0^8*a3^4*b4^2*b5^2 + a0^8*a3^2*b4*b5^4 + a0^8*b5^6 +
   a0^7*a1^3*a3^4*b3*b6^2 + a0^7*a1^2*a2^2*a3*b5^3*b6 +
   a0^7*a1^2*a2*a3^4*b3*b5*b6 + a0^7*a1^2*a2*a3^2*b5^4 +
   a0^7*a1^2*a3^5*b1*b6^2 + a0^7*a1^2*a3^5*b2*b5*b6 +
   a0^7*a1^2*a3^5*b3*b5^2 + a0^7*a1^2*a3^3*b4*b5^3 + a0^7*a1^2*a3*b5^5 +
   a0^7*a1*a2^2*a3^4*b1*b6^2 + a0^7*a1*a2^2*a3^4*b2*b5*b6 +
   a0^7*a1*a2^2*a3^4*b3*b4*b6 + a0^7*a1*a2^2*a3^2*b3*b5^2*b6 +
   a0^7*a1*a2*a3^5*b1*b5*b6 + a0^7*a1*a2*a3^5*b2*b5^2 +
   a0^7*a1*a2*a3^5*b3^2*b6 + a0^7*a1*a2*a3^5*b3*b4*b5 +
   a0^7*a1*a2*a3^3*b3*b5^3 + a0^7*a1*a3^6*b1*b4*b6 +
   a0^7*a1*a3^6*b2*b3*b6 + a0^7*a1*a3^6*b2*b4*b5 + a0^7*a1*a3^6*b3*b4^2 +
   a0^7*a1*a3^4*b1*b5^2*b6 + a0^7*a1*a3^4*b2*b5^3 + a0^7*a1*a3^2*b3*b5^4 +
   a0^7*a2^3*a3^4*b3^2*b6 + a0^7*a2^2*a3^5*b0*b5*b6 +
   a0^7*a2^2*a3^5*b1*b4*b6 + a0^7*a2^2*a3^5*b2*b3*b6 +
   a0^7*a2^2*a3^5*b3^2*b5 + a0^7*a2^2*a3^3*b1*b5^2*b6 +
   a0^7*a2^2*a3^3*b3^2*b5*b6 + a0^7*a2*a3^6*b0*b5^2 + a0^7*a2*a3^6*b1*b3*b6 +
   a0^7*a2*a3^6*b1*b4*b5 + a0^7*a2*a3^6*b2*b3*b5 + a0^7*a2*a3^6*b3^2*b4 +
   a0^7*a2*a3^4*b1*b5^3 + a0^7*a3^7*b0*b4*b5 + a0^7*a3^7*b1*b2*b6 +
   a0^7*a3^7*b1*b3*b5 + a0^7*a3^7*b1*b4^2 + a0^7*a3^7*b2^2*b5 +
   a0^7*a3^7*b2*b3*b4 + a0^7*a3^7*b3^3 + a0^7*a3^5*b0*b5^3 +
   a0^7*a3^5*b2*b3*b5^2 + a0^7*a3^5*b3^2*b4*b5 + a0^7*a3^3*b1*b5^4 +
   a0^7*a3^3*b3^2*b5^3 + a0^6*a1^4*a2^4*b6^3 + a0^6*a1^4*a3^4*b2*b6^2 +
   a0^6*a1^4*b5^4*b6 + a0^6*a1^3*a2^3*b5^3*b6 + a0^6*a1^3*a2^2*a3*b5^4 +
   a0^6*a1^3*a2*a3^4*b1*b6^2 + a0^6*a1^3*a2*a3^4*b2*b5*b6 +
   a0^6*a1^3*a2*a3^2*b4*b5^3 + a0^6*a1^3*a2*b5^5 + a0^6*a1^3*a3^5*b1*b5*b6 +
   a0^6*a1^3*a3^5*b2*b5^2 + a0^6*a1^3*a3^3*b3*b5^3 +
   a0^6*a1^2*a2^3*a3*b3*b5^2*b6 + a0^6*a1^2*a2^2*a3^4*b0*b6^2 +
   a0^6*a1^2*a2^2*a3^4*b2*b4*b6 + a0^6*a1^2*a2^2*a3^2*b3*b5^3 +
   a0^6*a1^2*a2*a3^5*b0*b5*b6 + a0^6*a1^2*a2*a3^5*b2*b3*b6 +
   a0^6*a1^2*a2*a3^5*b2*b4*b5 + a0^6*a1^2*a2*a3^3*b3*b4*b5^2 +
   a0^6*a1^2*a2*a3*b3*b5^4 + a0^6*a1^2*a3^6*b0*b4*b6 +
   a0^6*a1^2*a3^6*b0*b5^2 + a0^6*a1^2*a3^6*b1*b3*b6 +
   a0^6*a1^2*a3^6*b1*b4*b5 + a0^6*a1^2*a3^6*b2*b4^2 +
   a0^6*a1^2*a3^4*b0*b5^2*b6 + a0^6*a1^2*a3^4*b2*b4*b5^2 +
   a0^6*a1^2*a3^4*b3^2*b5^2 + a0^6*a1*a2^3*a3^4*b0*b5*b6 +
   a0^6*a1*a2^3*a3^4*b1*b4*b6 + a0^6*a1*a2^3*a3^4*b2*b3*b6 +
   a0^6*a1*a2^3*a3^2*b1*b5^2*b6 + a0^6*a1*a2^3*a3^2*b3^2*b5*b6 +
   a0^6*a1*a2^2*a3^5*b0*b5^2 + a0^6*a1*a2^2*a3^5*b1*b4*b5 +
   a0^6*a1*a2^2*a3^5*b2*b3*b5 + a0^6*a1*a2^2*a3^3*b1*b5^3 +
   a0^6*a1*a2^2*a3^3*b3^2*b5^2 + a0^6*a1*a2*a3^6*b0*b4*b5 +
   a0^6*a1*a2*a3^6*b1*b2*b6 + a0^6*a1*a2*a3^6*b1*b4^2 +
   a0^6*a1*a2*a3^6*b2^2*b5 + a0^6*a1*a2*a3^6*b2*b3*b4 + 
   a0^6*a1*a2*a3^4*b0*b5^3 + a0^6*a1*a2*a3^4*b2*b3*b5^2 +
   a0^6*a1*a2*a3^4*b3^2*b4*b5 + a0^6*a1*a2*a3^2*b1*b5^4 +
   a0^6*a1*a2*a3^2*b3^2*b5^3 + a0^6*a1*a3^7*b0*b3*b5 +
   a0^6*a1*a3^7*b1^2*b6 + a0^6*a1*a3^7*b1*b2*b5 + a0^6*a1*a3^7*b1*b3*b4 +
   a0^6*a1*a3^7*b2*b3^2 + a0^6*a1*a3^5*b1*b3*b5^2 + a0^6*a1*a3^5*b3^3*b5 +
   a0^6*a2^4*a3^4*b2^2*b6 + a0^6*a2^3*a3^5*b0*b3*b6 +
   a0^6*a2^3*a3^5*b1*b2*b6 + a0^6*a2^3*a3^5*b2^2*b5 +
   a0^6*a2^3*a3^3*b3^3*b6 + a0^6*a2^2*a3^6*b0*b2*b6 +
   a0^6*a2^2*a3^6*b0*b3*b5 + a0^6*a2^2*a3^6*b1^2*b6 +
   a0^6*a2^2*a3^6*b1*b2*b5 + a0^6*a2^2*a3^6*b2^2*b4 +
   a0^6*a2^2*a3^4*b1^2*b6^2 + a0^6*a2^2*a3^4*b2^2*b5^2 +
   a0^6*a2^2*a3^4*b2*b3^2*b6 + a0^6*a2^2*a3^4*b3^3*b5 +
   a0^6*a2*a3^7*b0*b2*b5 + a0^6*a2*a3^7*b0*b3*b4 + a0^6*a2*a3^7*b1*b2*b4 +
   a0^6*a2*a3^7*b2^2*b3 + a0^6*a2*a3^5*b0*b3*b5^2 + a0^6*a2*a3^5*b1^2*b5*b6 +
   a0^6*a2*a3^5*b1*b2*b5^2 + a0^6*a2*a3^5*b2*b3^2*b5 + a0^6*a2*a3^5*b3^3*b4 +
   a0^6*a2*a3^3*b3^3*b5^2 + a0^6*a3^8*b0^2*b6 + a0^6*a3^8*b0*b1*b5 +
   a0^6*a3^8*b0*b2*b4 + a0^6*a3^8*b0*b3^2 + a0^6*a3^8*b1^2*b4 +
   a0^6*a3^8*b1*b2*b3 + a0^6*a3^8*b2^3 + a0^6*a3^6*b0*b2*b5^2 +
   a0^6*a3^6*b1^2*b4*b6 + a0^6*a3^6*b1*b3^2*b5 + a0^6*a3^6*b2*b3^2*b4 +
   a0^6*a3^6*b3^4 + a0^6*a3^4*b1^2*b5^2*b6 + a0^6*a3^4*b2*b3^2*b5^2 +
   a0^6*a3^4*b3^4*b6 + a0^5*a1^5*a2^4*b5*b6^2 + a0^5*a1^5*a3^4*b1*b6^2 +
   a0^5*a1^5*b5^5 + a0^5*a1^4*a2^5*b5^2*b6 + a0^5*a1^4*a2^4*a3*b3*b6^2 +
   a0^5*a1^4*a2^4*a3*b4*b5*b6 + a0^5*a1^4*a2^4*a3*b5^3 +
   a0^5*a1^4*a2^3*b5^4 + a0^5*a1^4*a2^2*a3*b4*b5^3 +
   a0^5*a1^4*a2*a3^4*b1*b5*b6 + a0^5*a1^4*a2*a3^2*b3*b5^3 +
   a0^5*a1^4*a3^5*b0*b5*b6 + a0^5*a1^4*a3^5*b1*b5^2 +
   a0^5*a1^4*a3^3*b2*b5^3 + a0^5*a1^4*a3*b3*b5^4 +
   a0^5*a1^3*a2^4*b3*b5^2*b6 + a0^5*a1^3*a2^3*a3*b3*b5^3 +
   a0^5*a1^3*a2^2*a3^4*b0*b5*b6 + a0^5*a1^3*a2^2*a3^4*b1*b4*b6 +
   a0^5*a1^3*a2^2*a3^2*b3*b4*b5^2 + a0^5*a1^3*a2^2*b3*b5^4 +
   a0^5*a1^3*a2*a3^5*b0*b5^2 + a0^5*a1^3*a2*a3^5*b1*b3*b6 +
   a0^5*a1^3*a2*a3^5*b1*b4*b5 + a0^5*a1^3*a2*a3^3*b3^2*b5^2 +
   a0^5*a1^3*a3^6*b0*b3*b6 + a0^5*a1^3*a3^6*b0*b4*b5 +
   a0^5*a1^3*a3^6*b1*b4^2 + a0^5*a1^3*a3^4*b0*b5^3 +
   a0^5*a1^3*a3^4*b1*b4*b5^2 + a0^5*a1^3*a3^4*b2*b3*b5^2 +
   a0^5*a1^2*a2^4*a3*b1*b5^2*b6 + a0^5*a1^2*a2^4*a3*b3^2*b5*b6 +
   a0^5*a1^2*a2^3*a3^4*b1*b3*b6 + a0^5*a1^2*a2^3*a3^2*b1*b5^3 +
   a0^5*a1^2*a2^3*a3^2*b3^2*b5^2 + a0^5*a1^2*a2^2*a3^5*b0*b3*b6 +
   a0^5*a1^2*a2^2*a3^5*b1*b3*b5 + a0^5*a1^2*a2^2*a3^3*b1*b4*b5^2 +
   a0^5*a1^2*a2^2*a3^3*b3^2*b4*b5 + a0^5*a1^2*a2^2*a3*b1*b5^4 +
   a0^5*a1^2*a2^2*a3*b3^2*b5^3 + a0^5*a1^2*a2*a3^6*b1^2*b6 +
   a0^5*a1^2*a2*a3^6*b1*b2*b5 + a0^5*a1^2*a2*a3^6*b1*b3*b4 +
   a0^5*a1^2*a2*a3^4*b3^3*b5 + a0^5*a1^2*a3^7*b0*b1*b6 +
   a0^5*a1^2*a3^7*b0*b2*b5 + a0^5*a1^2*a3^7*b0*b3*b4 +
   a0^5*a1^2*a3^7*b1*b3^2 + a0^5*a1^2*a3^5*b0*b3*b5^2 +
   a0^5*a1^2*a3^5*b1^2*b5*b6 + a0^5*a1^2*a3^5*b1*b2*b5^2 +
   a0^5*a1^2*a3^5*b2*b3^2*b5 + a0^5*a1*a2^4*a3^4*b0*b3*b6 +
   a0^5*a1*a2^4*a3^4*b1*b2*b6 + a0^5*a1*a2^4*a3^2*b3^3*b6 +
   a0^5*a1*a2^3*a3^5*b0*b3*b5 + a0^5*a1*a2^3*a3^5*b1^2*b6 +
   a0^5*a1*a2^3*a3^5*b1*b2*b5 + a0^5*a1*a2^3*a3^3*b3^3*b5 +
   a0^5*a1*a2^2*a3^6*b0*b1*b6 + a0^5*a1*a2^2*a3^6*b0*b3*b4 +
   a0^5*a1*a2^2*a3^6*b1*b2*b4 + a0^5*a1*a2^2*a3^4*b0*b3*b5^2 +
   a0^5*a1*a2^2*a3^4*b1^2*b5*b6 + a0^5*a1*a2^2*a3^4*b1*b2*b5^2 +
   a0^5*a1*a2^2*a3^4*b1*b3^2*b6 + a0^5*a1*a2^2*a3^4*b3^3*b4 +
   a0^5*a1*a2^2*a3^2*b3^3*b5^2 + a0^5*a1*a2*a3^7*b0*b1*b5 +
   a0^5*a1*a2*a3^7*b0*b3^2 + a0^5*a1*a2*a3^7*b1^2*b4 +
   a0^5*a1*a2*a3^7*b1*b2*b3 + a0^5*a1*a2*a3^5*b1*b3^2*b5 +
   a0^5*a1*a2*a3^5*b3^4 + a0^5*a1*a3^8*b0^2*b5 + a0^5*a1*a3^8*b0*b1*b4 +
   a0^5*a1*a3^8*b0*b2*b3 + a0^5*a1*a3^8*b1*b2^2 + a0^5*a1*a3^6*b0*b1*b5^2 +
   a0^5*a1*a3^6*b1^2*b3*b6 + a0^5*a1*a3^6*b1^2*b4*b5 +
   a0^5*a1*a3^6*b1*b3^2*b4 + a0^5*a1*a3^6*b2*b3^3 + a0^5*a1*a3^4*b1^2*b5^3 +
   a0^5*a1*a3^4*b1*b3^2*b5^2 + a0^5*a1*a3^4*b3^4*b5 +
   a0^5*a2^5*a3^4*b1^2*b6 + a0^5*a2^4*a3^5*b0*b1*b6 +
   a0^5*a2^4*a3^5*b1^2*b5 + a0^5*a2^4*a3^3*b1^2*b5*b6 +
   a0^5*a2^4*a3^3*b1*b3^2*b6 + a0^5*a2^3*a3^6*b0*b1*b5 +
   a0^5*a2^3*a3^6*b1^2*b4 + a0^5*a2^3*a3^4*b1*b3^2*b5 +
   a0^5*a2^2*a3^7*b0^2*b5 + a0^5*a2^2*a3^7*b0*b1*b4 +
   a0^5*a2^2*a3^7*b1^2*b3 + a0^5*a2^2*a3^5*b0*b1*b5^2 +
   a0^5*a2^2*a3^5*b1^2*b3*b6 + a0^5*a2^2*a3^5*b1^2*b4*b5 +
   a0^5*a2^2*a3^5*b1*b3^2*b4 + a0^5*a2^2*a3^3*b1^2*b5^3 +
   a0^5*a2^2*a3^3*b1*b3^2*b5^2 + a0^5*a2^2*a3^3*b3^4*b5 +
   a0^5*a2*a3^8*b0*b1*b3 + a0^5*a2*a3^8*b1^2*b2 + a0^5*a2*a3^6*b1^2*b3*b5 +
   a0^5*a2*a3^6*b1*b3^3 + a0^5*a3^9*b0^2*b3 + a0^5*a3^9*b0*b1*b2 +
   a0^5*a3^9*b1^3 + a0^5*a3^7*b1^3*b6 + a0^5*a3^7*b1^2*b3*b4 +
   a0^5*a3^7*b1*b2*b3^2 + a0^5*a3^5*b1^2*b3*b5^2 + a0^5*a3^5*b3^5 +
   a0^4*a1^6*a2^4*b4*b6^2 + a0^4*a1^6*a3^4*b0*b6^2 + a0^4*a1^6*b4*b5^4 +
   a0^4*a1^5*a2^5*b3*b6^2 + a0^4*a1^5*a2^5*b4*b5*b6 +
   a0^4*a1^5*a2^4*a3*b3*b5*b6 + a0^4*a1^5*a2^4*a3*b4*b5^2 +
   a0^4*a1^5*a2^3*b4*b5^3 + a0^4*a1^5*a2^2*a3*b3*b5^3 +
   a0^4*a1^5*a2*a3^4*b0*b5*b6 + a0^4*a1^5*a2*a3^2*b2*b5^3 +
   a0^4*a1^5*a2*b3*b5^4 + a0^4*a1^5*a3^5*b0*b5^2 +
   a0^4*a1^5*a3^3*b1*b5^3 + a0^4*a1^4*a2^6*b4^2*b6 +
   a0^4*a1^4*a2^5*a3*b1*b6^2 + a0^4*a1^4*a2^5*a3*b2*b5*b6 +
   a0^4*a1^4*a2^5*a3*b3*b4*b6 + a0^4*a1^4*a2^5*a3*b4^2*b5 +
   a0^4*a1^4*a2^4*a3^2*b0*b6^2 + a0^4*a1^4*a2^4*a3^2*b1*b5*b6 +
   a0^4*a1^4*a2^4*a3^2*b2*b4*b6 + a0^4*a1^4*a2^4*a3^2*b2*b5^2 +
   a0^4*a1^4*a2^4*a3^2*b3^2*b6 + a0^4*a1^4*a2^4*a3^2*b3*b4*b5 +
   a0^4*a1^4*a2^4*a3^2*b4^3 + a0^4*a1^4*a2^4*b2*b5^2*b6 +
   a0^4*a1^4*a2^4*b3^2*b6^2 + a0^4*a1^4*a2^4*b4^2*b5^2 +
   a0^4*a1^4*a2^3*a3*b3*b4*b5^2 + a0^4*a1^4*a2^2*a3^4*b0*b4*b6 +
   a0^4*a1^4*a2^2*a3^2*b3^2*b5^2 + a0^4*a1^4*a2^2*b2*b5^4 +
   a0^4*a1^4*a2*a3^5*b0*b3*b6 + a0^4*a1^4*a2*a3^5*b0*b4*b5 +
   a0^4*a1^4*a2*a3^3*b2*b3*b5^2 + a0^4*a1^4*a2*a3*b1*b5^4 +
   a0^4*a1^4*a3^6*b0*b4^2 + a0^4*a1^4*a3^4*b0*b4*b5^2 +
   a0^4*a1^4*a3^4*b1^2*b6^2 + a0^4*a1^4*a3^4*b1*b3*b5^2 +
   a0^4*a1^4*a3^2*b0*b5^4 + a0^4*a1^4*b3^2*b5^4 + a0^4*a1^3*a2^5*b1*b5^2*b6 +
   a0^4*a1^3*a2^5*b3^2*b5*b6 + a0^4*a1^3*a2^4*a3*b1*b5^3 +
   a0^4*a1^3*a2^4*a3*b3^2*b5^2 + a0^4*a1^3*a2^3*a3^4*b0*b3*b6 +
   a0^4*a1^3*a2^3*a3^2*b1*b4*b5^2 + a0^4*a1^3*a2^3*a3^2*b3^2*b4*b5 +
   a0^4*a1^3*a2^3*b1*b5^4 + a0^4*a1^3*a2^3*b3^2*b5^3 +
   a0^4*a1^3*a2^2*a3^5*b0*b3*b5 + a0^4*a1^3*a2^2*a3^3*b1*b3*b5^2 +
   a0^4*a1^3*a2^2*a3^3*b3^3*b5 + a0^4*a1^3*a2*a3^6*b0*b1*b6 +
   a0^4*a1^3*a2*a3^6*b0*b2*b5 + a0^4*a1^3*a2*a3^6*b0*b3*b4 +
   a0^4*a1^3*a2*a3^4*b0*b3*b5^2 + a0^4*a1^3*a2*a3^4*b1^2*b5*b6 +
   a0^4*a1^3*a2*a3^4*b1*b2*b5^2 + a0^4*a1^3*a2*a3^4*b2*b3^2*b5 +
   a0^4*a1^3*a3^7*b0*b3^2 + a0^4*a1^3*a3^5*b1*b3^2*b5 +
   a0^4*a1^2*a2^5*a3*b3^3*b6 + a0^4*a1^2*a2^4*a3^4*b0*b2*b6 +
   a0^4*a1^2*a2^4*a3^2*b3^3*b5 + a0^4*a1^2*a2^3*a3^5*b0*b1*b6 +
   a0^4*a1^2*a2^3*a3^5*b0*b2*b5 + a0^4*a1^2*a2^3*a3^3*b3^3*b4 +
   a0^4*a1^2*a2^3*a3*b3^3*b5^2 + a0^4*a1^2*a2^2*a3^6*b0^2*b6 +
   a0^4*a1^2*a2^2*a3^6*b0*b2*b4 + a0^4*a1^2*a2^2*a3^4*b0*b2*b5^2 +
   a0^4*a1^2*a2^2*a3^4*b0*b3^2*b6 + a0^4*a1^2*a2^2*a3^4*b1^2*b4*b6 +
   a0^4*a1^2*a2^2*a3^4*b3^4 + a0^4*a1^2*a2*a3^7*b0^2*b5 +
   a0^4*a1^2*a2*a3^7*b0*b1*b4 + a0^4*a1^2*a2*a3^7*b0*b2*b3 +
   a0^4*a1^2*a2*a3^5*b0*b1*b5^2 + a0^4*a1^2*a2*a3^5*b0*b3^2*b5 +
   a0^4*a1^2*a2*a3^5*b1^2*b3*b6 + a0^4*a1^2*a2*a3^5*b1^2*b4*b5 +
   a0^4*a1^2*a2*a3^5*b2*b3^3 + a0^4*a1^2*a3^8*b0*b2^2 +
   a0^4*a1^2*a3^6*b0^2*b5^2 + a0^4*a1^2*a3^6*b0*b3^2*b4 +
   a0^4*a1^2*a3^6*b1^2*b4^2 + a0^4*a1^2*a3^6*b1*b3^3 +
   a0^4*a1^2*a3^4*b0*b3^2*b5^2 + a0^4*a1^2*a3^4*b1^2*b4*b5^2 +
   a0^4*a1^2*a3^4*b3^4*b4 + a0^4*a1*a2^5*a3^4*b0*b1*b6 +
   a0^4*a1*a2^5*a3^2*b1^2*b5*b6 + a0^4*a1*a2^5*a3^2*b1*b3^2*b6 +
   a0^4*a1*a2^4*a3^5*b0*b1*b5 + a0^4*a1*a2^4*a3^3*b1^2*b5^2 +
   a0^4*a1*a2^4*a3^3*b1*b3^2*b5 + a0^4*a1*a2^3*a3^6*b0^2*b5 +
   a0^4*a1*a2^3*a3^6*b0*b1*b4 + a0^4*a1*a2^3*a3^4*b0*b1*b5^2 +
   a0^4*a1*a2^3*a3^4*b1^2*b3*b6 + a0^4*a1*a2^3*a3^4*b1^2*b4*b5 +
   a0^4*a1*a2^3*a3^4*b1*b3^2*b4 + a0^4*a1*a2^3*a3^2*b1^2*b5^3 +
   a0^4*a1*a2^3*a3^2*b1*b3^2*b5^2 + a0^4*a1*a2^3*a3^2*b3^4*b5 +
   a0^4*a1*a2^2*a3^7*b0*b1*b3 + a0^4*a1*a2^2*a3^5*b1*b3^3 +
   a0^4*a1*a2*a3^8*b0^2*b3 + a0^4*a1*a2*a3^8*b0*b1*b2 +
   a0^4*a1*a2*a3^6*b1^3*b6 + a0^4*a1*a2*a3^6*b1^2*b3*b4 +
   a0^4*a1*a2*a3^6*b1*b2*b3^2 + a0^4*a1*a2*a3^4*b1^2*b3*b5^2 +
   a0^4*a1*a2*a3^4*b3^5 + a0^4*a1*a3^9*b0*b1^2 + a0^4*a1*a3^7*b1^3*b5 +
   a0^4*a2^6*a3^4*b0^2*b6 + a0^4*a2^6*b3^4*b6 + a0^4*a2^5*a3^5*b0^2*b5 +
   a0^4*a2^5*a3^3*b1^2*b3*b6 + a0^4*a2^5*a3*b3^4*b5 +
   a0^4*a2^4*a3^6*b0^2*b4 + a0^4*a2^4*a3^4*b0^2*b5^2 +
   a0^4*a2^4*a3^4*b1^2*b2*b6 + a0^4*a2^4*a3^4*b1^2*b3*b5 +
   a0^4*a2^4*a3^2*b3^4*b4 + a0^4*a2^4*b3^4*b5^2 + a0^4*a2^3*a3^7*b0^2*b3 +
   a0^4*a2^3*a3^5*b1^3*b6 + a0^4*a2^3*a3^5*b1^2*b2*b5 +
   a0^4*a2^3*a3^5*b1^2*b3*b4 + a0^4*a2^3*a3^3*b1^2*b3*b5^2 +
   a0^4*a2^3*a3^3*b3^5 + a0^4*a2^2*a3^8*b0^2*b2 + a0^4*a2^2*a3^6*b0*b1^2*b6 +
   a0^4*a2^2*a3^6*b1^2*b2*b4 + a0^4*a2^2*a3^6*b1^2*b3^2 +
   a0^4*a2^2*a3^4*b1^2*b2*b5^2 + a0^4*a2^2*a3^4*b1^2*b3^2*b6 +
   a0^4*a2^2*a3^4*b2*b3^4 + a0^4*a2*a3^9*b0^2*b1 + a0^4*a2*a3^7*b0*b1^2*b5 +
   a0^4*a2*a3^7*b1^3*b4 + a0^4*a2*a3^5*b1^3*b5^2 +
   a0^4*a2*a3^5*b1^2*b3^2*b5 + a0^4*a2*a3^5*b1*b3^4 + a0^4*a3^10*b0^3 +
   a0^4*a3^8*b0^2*b3^2 + a0^4*a3^8*b0*b1^2*b4 + a0^4*a3^8*b1^3*b3 +
   a0^4*a3^8*b1^2*b2^2 + a0^4*a3^6*b0*b1^2*b5^2 + a0^4*a3^6*b0*b3^4 +
   a0^4*a3^6*b1^2*b3^2*b4 + a0^4*a3^4*b1^2*b3^2*b5^2 + a0^4*a3^4*b3^6 +
   a0^3*a1^7*a2^4*b3*b6^2 + a0^3*a1^7*b3*b5^4 + a0^3*a1^6*a2^5*b3*b5*b6 +
   a0^3*a1^6*a2^4*a3*b1*b6^2 + a0^3*a1^6*a2^4*a3*b2*b5*b6 +
   a0^3*a1^6*a2^4*a3*b3*b5^2 + a0^3*a1^6*a2^3*b3*b5^3 +
   a0^3*a1^6*a2^2*a3*b2*b5^3 + a0^3*a1^6*a2*a3^2*b1*b5^3 +
   a0^3*a1^6*a3^3*b0*b5^3 + a0^3*a1^6*a3*b1*b5^4 +
   a0^3*a1^5*a2^6*b1*b6^2 + a0^3*a1^5*a2^6*b2*b5*b6 +
   a0^3*a1^5*a2^6*b3*b4*b6 + a0^3*a1^5*a2^5*a3*b1*b5*b6 +
   a0^3*a1^5*a2^5*a3*b2*b5^2 + a0^3*a1^5*a2^5*a3*b3^2*b6 +
   a0^3*a1^5*a2^5*a3*b3*b4*b5 + a0^3*a1^5*a2^4*a3^2*b1*b4*b6 +
   a0^3*a1^5*a2^4*a3^2*b2*b3*b6 + a0^3*a1^5*a2^4*a3^2*b2*b4*b5 +
   a0^3*a1^5*a2^4*a3^2*b3*b4^2 + a0^3*a1^5*a2^4*b1*b5^2*b6 +
   a0^3*a1^5*a2^4*b2*b5^3 + a0^3*a1^5*a2^4*b3*b4*b5^2 +
   a0^3*a1^5*a2^3*a3*b3^2*b5^2 + a0^3*a1^5*a2^2*a3^2*b2*b3*b5^2 +
   a0^3*a1^5*a2*a3^3*b1*b3*b5^2 + a0^3*a1^5*a3^4*b0*b3*b5^2 +
   a0^3*a1^4*a2^7*b3^2*b6 + a0^3*a1^4*a2^6*a3*b0*b5*b6 +
   a0^3*a1^4*a2^6*a3*b1*b4*b6 + a0^3*a1^4*a2^6*a3*b2*b3*b6 +
   a0^3*a1^4*a2^6*a3*b3^2*b5 + a0^3*a1^4*a2^5*a3^2*b0*b5^2 +
   a0^3*a1^4*a2^5*a3^2*b1*b3*b6 + a0^3*a1^4*a2^5*a3^2*b1*b4*b5 +
   a0^3*a1^4*a2^5*a3^2*b2*b3*b5 + a0^3*a1^4*a2^5*a3^2*b3^2*b4 +
   a0^3*a1^4*a2^5*b3^2*b5^2 + a0^3*a1^4*a2^4*a3^3*b0*b4*b5 +
   a0^3*a1^4*a2^4*a3^3*b1*b2*b6 + a0^3*a1^4*a2^4*a3^3*b1*b3*b5 +
   a0^3*a1^4*a2^4*a3^3*b1*b4^2 + a0^3*a1^4*a2^4*a3^3*b2^2*b5 +
   a0^3*a1^4*a2^4*a3^3*b2*b3*b4 + a0^3*a1^4*a2^4*a3^3*b3^3 +
   a0^3*a1^4*a2^4*a3*b0*b5^3 + a0^3*a1^4*a2^4*a3*b1*b4*b5^2 +
   a0^3*a1^4*a2^4*a3*b2*b3*b5^2 + a0^3*a1^4*a2^3*a3^2*b1*b3*b5^2 +
   a0^3*a1^4*a2^3*a3^2*b3^3*b5 + a0^3*a1^4*a2^2*a3^3*b1*b2*b5^2 +
   a0^3*a1^4*a2^2*a3^3*b2*b3^2*b5 + a0^3*a1^4*a2*a3^4*b1^2*b5^2 +
   a0^3*a1^4*a2*a3^4*b1*b3^2*b5 + a0^3*a1^4*a3^5*b0*b1*b5^2 +
   a0^3*a1^4*a3^5*b0*b3^2*b5 + a0^3*a1^4*a3^3*b1^2*b5^3 +
   a0^3*a1^3*a2^6*b3^3*b6 + a0^3*a1^3*a2^5*a3*b3^3*b5 +
   a0^3*a1^3*a2^4*a3^2*b3^3*b4 + a0^3*a1^3*a2^4*b3^3*b5^2 +
   a0^3*a1^3*a2^3*a3^3*b3^4 + a0^3*a1^3*a2^2*a3^4*b2*b3^3 +
   a0^3*a1^3*a2*a3^5*b1*b3^3 + a0^3*a1^3*a3^6*b0*b3^3 +
   a0^3*a1^3*a3^4*b1^2*b3*b5^2 + a0^3*a1^3*a3^4*b3^5 +
   a0^3*a1^2*a2^6*a3*b1^2*b5*b6 + a0^3*a1^2*a2^6*a3*b1*b3^2*b6 +
   a0^3*a1^2*a2^5*a3^2*b1^2*b5^2 + a0^3*a1^2*a2^5*a3^2*b1*b3^2*b5 +
   a0^3*a1^2*a2^4*a3^3*b1^2*b4*b5 + a0^3*a1^2*a2^4*a3^3*b1*b3^2*b4 +
   a0^3*a1^2*a2^4*a3*b1^2*b5^3 + a0^3*a1^2*a2^4*a3*b1*b3^2*b5^2 +
   a0^3*a1^2*a2^3*a3^4*b1^2*b3*b5 + a0^3*a1^2*a2^3*a3^4*b1*b3^3 +
   a0^3*a1^2*a2^2*a3^5*b1^2*b2*b5 + a0^3*a1^2*a2^2*a3^5*b1*b2*b3^2 +
   a0^3*a1^2*a2*a3^6*b1^3*b5 + a0^3*a1^2*a2*a3^6*b1^2*b3^2 +
   a0^3*a1^2*a3^7*b0*b1^2*b5 + a0^3*a1^2*a3^7*b0*b1*b3^2 +
   a0^3*a1^2*a3^5*b1^3*b5^2 + a0^3*a1^2*a3^5*b1^2*b3^2*b5 +
   a0^3*a1^2*a3^5*b1*b3^4 + a0^3*a1*a2^6*a3^2*b1^2*b3*b6 +
   a0^3*a1*a2^5*a3^3*b1^2*b3*b5 + a0^3*a1*a2^4*a3^4*b1^2*b3*b4 +
   a0^3*a1*a2^4*a3^2*b1^2*b3*b5^2 + a0^3*a1*a2^3*a3^5*b1^2*b3^2 +
   a0^3*a1*a2^2*a3^6*b1^2*b2*b3 + a0^3*a1*a2*a3^7*b1^3*b3 +
   a0^3*a1*a3^8*b0*b1^2*b3 + a0^3*a1*a3^6*b1^2*b3^3 +
   a0^3*a2^6*a3^3*b1^3*b6 + a0^3*a2^5*a3^4*b1^3*b5 + a0^3*a2^4*a3^5*b1^3*b4 +
   a0^3*a2^4*a3^3*b1^3*b5^2 + a0^3*a2^3*a3^6*b1^3*b3 +
   a0^3*a2^2*a3^7*b1^3*b2 + a0^3*a2*a3^8*b1^4 + a0^3*a3^9*b0*b1^3 +
   a0^3*a3^7*b1^4*b5 + a0^3*a3^7*b1^3*b3^2 + a0^2*a1^8*a2^4*b2*b6^2 +
   a0^2*a1^8*b2*b5^4 + a0^2*a1^7*a2^5*b1*b6^2 + a0^2*a1^7*a2^5*b2*b5*b6 +
   a0^2*a1^7*a2^4*a3*b1*b5*b6 + a0^2*a1^7*a2^4*a3*b2*b5^2 +
   a0^2*a1^7*a2^3*b2*b5^3 + a0^2*a1^7*a2^2*a3*b1*b5^3 +
   a0^2*a1^7*a2*a3^2*b0*b5^3 + a0^2*a1^7*a2*b1*b5^4 +
   a0^2*a1^6*a2^6*b0*b6^2 + a0^2*a1^6*a2^6*b2*b4*b6 +
   a0^2*a1^6*a2^5*a3*b0*b5*b6 + a0^2*a1^6*a2^5*a3*b2*b3*b6 +
   a0^2*a1^6*a2^5*a3*b2*b4*b5 + a0^2*a1^6*a2^4*a3^2*b0*b4*b6 +
   a0^2*a1^6*a2^4*a3^2*b0*b5^2 + a0^2*a1^6*a2^4*a3^2*b1*b3*b6 +
   a0^2*a1^6*a2^4*a3^2*b1*b4*b5 + a0^2*a1^6*a2^4*a3^2*b2*b4^2 +
   a0^2*a1^6*a2^4*b0*b5^2*b6 + a0^2*a1^6*a2^4*b2*b4*b5^2 +
   a0^2*a1^6*a2^3*a3*b2*b3*b5^2 + a0^2*a1^6*a2^2*a3^2*b1*b3*b5^2 +
   a0^2*a1^6*a2*a3^3*b0*b3*b5^2 + a0^2*a1^5*a2^7*b0*b5*b6 +
   a0^2*a1^5*a2^7*b1*b4*b6 + a0^2*a1^5*a2^7*b2*b3*b6 +
   a0^2*a1^5*a2^6*a3*b0*b5^2 + a0^2*a1^5*a2^6*a3*b1*b4*b5 +
   a0^2*a1^5*a2^6*a3*b2*b3*b5 + a0^2*a1^5*a2^5*a3^2*b0*b4*b5 +
   a0^2*a1^5*a2^5*a3^2*b1*b2*b6 + a0^2*a1^5*a2^5*a3^2*b1*b4^2 +
   a0^2*a1^5*a2^5*a3^2*b2^2*b5 + a0^2*a1^5*a2^5*a3^2*b2*b3*b4 +
   a0^2*a1^5*a2^5*b0*b5^3 + a0^2*a1^5*a2^5*b1*b4*b5^2 +
   a0^2*a1^5*a2^5*b2*b3*b5^2 + a0^2*a1^5*a2^4*a3^3*b0*b3*b5 +
   a0^2*a1^5*a2^4*a3^3*b1^2*b6 + a0^2*a1^5*a2^4*a3^3*b1*b2*b5 +
   a0^2*a1^5*a2^4*a3^3*b1*b3*b4 + a0^2*a1^5*a2^4*a3^3*b2*b3^2 +
   a0^2*a1^5*a2^3*a3^2*b1*b2*b5^2 + a0^2*a1^5*a2^3*a3^2*b2*b3^2*b5 +
   a0^2*a1^5*a2^2*a3^3*b1^2*b5^2 + a0^2*a1^5*a2^2*a3^3*b1*b3^2*b5 +
   a0^2*a1^5*a2*a3^4*b0*b1*b5^2 + a0^2*a1^5*a2*a3^4*b0*b3^2*b5 +
   a0^2*a1^5*a2*a3^2*b1^2*b5^3 + a0^2*a1^4*a2^8*b2^2*b6 +
   a0^2*a1^4*a2^7*a3*b0*b3*b6 + a0^2*a1^4*a2^7*a3*b1*b2*b6 +
   a0^2*a1^4*a2^7*a3*b2^2*b5 + a0^2*a1^4*a2^6*a3^2*b0*b2*b6 +
   a0^2*a1^4*a2^6*a3^2*b0*b3*b5 + a0^2*a1^4*a2^6*a3^2*b1^2*b6 +
   a0^2*a1^4*a2^6*a3^2*b1*b2*b5 + a0^2*a1^4*a2^6*a3^2*b2^2*b4 +
   a0^2*a1^4*a2^6*b1^2*b6^2 + a0^2*a1^4*a2^6*b2^2*b5^2 +
   a0^2*a1^4*a2^6*b2*b3^2*b6 + a0^2*a1^4*a2^5*a3^3*b0*b2*b5 +
   a0^2*a1^4*a2^5*a3^3*b0*b3*b4 + a0^2*a1^4*a2^5*a3^3*b1*b2*b4 +
   a0^2*a1^4*a2^5*a3^3*b2^2*b3 + a0^2*a1^4*a2^5*a3*b0*b3*b5^2 +
   a0^2*a1^4*a2^5*a3*b1^2*b5*b6 + a0^2*a1^4*a2^5*a3*b1*b2*b5^2 +
   a0^2*a1^4*a2^5*a3*b2*b3^2*b5 + a0^2*a1^4*a2^4*a3^4*b0^2*b6 +
   a0^2*a1^4*a2^4*a3^4*b0*b1*b5 + a0^2*a1^4*a2^4*a3^4*b0*b2*b4 +
   a0^2*a1^4*a2^4*a3^4*b0*b3^2 + a0^2*a1^4*a2^4*a3^4*b1^2*b4 +
   a0^2*a1^4*a2^4*a3^4*b1*b2*b3 + a0^2*a1^4*a2^4*a3^4*b2^3 +
   a0^2*a1^4*a2^4*a3^2*b0*b2*b5^2 + a0^2*a1^4*a2^4*a3^2*b1^2*b4*b6 +
   a0^2*a1^4*a2^4*a3^2*b1*b3^2*b5 + a0^2*a1^4*a2^4*a3^2*b2*b3^2*b4 +
   a0^2*a1^4*a2^4*b1^2*b5^2*b6 + a0^2*a1^4*a2^4*b2*b3^2*b5^2 +
   a0^2*a1^4*a2^3*a3^3*b2*b3^3 + a0^2*a1^4*a2^2*a3^4*b1*b3^3 +
   a0^2*a1^4*a2*a3^5*b0*b3^3 + a0^2*a1^4*a2*a3^3*b1^2*b3*b5^2 +
   a0^2*a1^4*a3^4*b2*b3^4 + a0^2*a1^3*a2^7*b1^2*b5*b6 +
   a0^2*a1^3*a2^7*b1*b3^2*b6 + a0^2*a1^3*a2^6*a3*b1^2*b5^2 +
   a0^2*a1^3*a2^6*a3*b1*b3^2*b5 + a0^2*a1^3*a2^5*a3^2*b1^2*b4*b5 +
   a0^2*a1^3*a2^5*a3^2*b1*b3^2*b4 + a0^2*a1^3*a2^5*b1^2*b5^3 +
   a0^2*a1^3*a2^5*b1*b3^2*b5^2 + a0^2*a1^3*a2^4*a3^3*b1^2*b3*b5 +
   a0^2*a1^3*a2^4*a3^3*b1*b3^3 + a0^2*a1^3*a2^3*a3^4*b1^2*b2*b5 +
   a0^2*a1^3*a2^3*a3^4*b1*b2*b3^2 + a0^2*a1^3*a2^2*a3^5*b1^3*b5 +
   a0^2*a1^3*a2^2*a3^5*b1^2*b3^2 + a0^2*a1^3*a2*a3^6*b0*b1^2*b5 +
   a0^2*a1^3*a2*a3^6*b0*b1*b3^2 + a0^2*a1^3*a2*a3^4*b1^3*b5^2 +
   a0^2*a1^3*a2*a3^4*b1^2*b3^2*b5 + a0^2*a1^3*a2*a3^4*b1*b3^4 +
   a0^2*a1^2*a2^7*a3*b1^2*b3*b6 + a0^2*a1^2*a2^6*a3^2*b1^2*b3*b5 +
   a0^2*a1^2*a2^5*a3^3*b1^2*b3*b4 + a0^2*a1^2*a2^5*a3*b1^2*b3*b5^2 +
   a0^2*a1^2*a2^4*a3^4*b1^2*b3^2 + a0^2*a1^2*a2^3*a3^5*b1^2*b2*b3 +
   a0^2*a1^2*a2^2*a3^6*b1^3*b3 + a0^2*a1^2*a2*a3^7*b0*b1^2*b3 +
   a0^2*a1^2*a2*a3^5*b1^2*b3^3 + a0^2*a1*a2^7*a3^2*b1^3*b6 +
   a0^2*a1*a2^6*a3^3*b1^3*b5 + a0^2*a1*a2^5*a3^4*b1^3*b4 +
   a0^2*a1*a2^5*a3^2*b1^3*b5^2 + a0^2*a1*a2^4*a3^5*b1^3*b3 +
   a0^2*a1*a2^3*a3^6*b1^3*b2 + a0^2*a1*a2^2*a3^7*b1^4 +
   a0^2*a1*a2*a3^8*b0*b1^3 + a0^2*a1*a2*a3^6*b1^4*b5 +
   a0^2*a1*a2*a3^6*b1^3*b3^2 + a0^2*a2^4*a3^4*b1^4*b6 +
   a0^2*a2*a3^7*b1^4*b3 + a0^2*a3^8*b1^4*b2 + a0*a1^9*a2^4*b1*b6^2 +
   a0*a1^9*b1*b5^4 + a0*a1^8*a2^5*b1*b5*b6 + a0*a1^8*a2^4*a3*b0*b5*b6 +
   a0*a1^8*a2^4*a3*b1*b5^2 + a0*a1^8*a2^3*b1*b5^3 +
   a0*a1^8*a2^2*a3*b0*b5^3 + a0*a1^7*a2^6*b0*b5*b6 +
   a0*a1^7*a2^6*b1*b4*b6 + a0*a1^7*a2^5*a3*b0*b5^2 +
   a0*a1^7*a2^5*a3*b1*b3*b6 + a0*a1^7*a2^5*a3*b1*b4*b5 +
   a0*a1^7*a2^4*a3^2*b0*b3*b6 + a0*a1^7*a2^4*a3^2*b0*b4*b5 +
   a0*a1^7*a2^4*a3^2*b1*b4^2 + a0*a1^7*a2^4*b0*b5^3 +
   a0*a1^7*a2^4*b1*b4*b5^2 + a0*a1^7*a2^3*a3*b1*b3*b5^2 +
   a0*a1^7*a2^2*a3^2*b0*b3*b5^2 + a0*a1^6*a2^7*b1*b3*b6 +
   a0*a1^6*a2^6*a3*b0*b3*b6 + a0*a1^6*a2^6*a3*b1*b3*b5 +
   a0*a1^6*a2^5*a3^2*b1^2*b6 + a0*a1^6*a2^5*a3^2*b1*b2*b5 +
   a0*a1^6*a2^5*a3^2*b1*b3*b4 + a0*a1^6*a2^5*b1*b3*b5^2 +
   a0*a1^6*a2^4*a3^3*b0*b1*b6 + a0*a1^6*a2^4*a3^3*b0*b2*b5 +
   a0*a1^6*a2^4*a3^3*b0*b3*b4 + a0*a1^6*a2^4*a3^3*b1*b3^2 +
   a0*a1^6*a2^4*a3*b0*b3*b5^2 + a0*a1^6*a2^4*a3*b1^2*b5*b6 +
   a0*a1^6*a2^3*a3^2*b1^2*b5^2 + a0*a1^6*a2^3*a3^2*b1*b3^2*b5 +
   a0*a1^6*a2^2*a3^3*b0*b1*b5^2 + a0*a1^6*a2^2*a3^3*b0*b3^2*b5 +
   a0*a1^6*a2^2*a3*b1^2*b5^3 + a0*a1^5*a2^8*b0*b3*b6 +
   a0*a1^5*a2^8*b1*b2*b6 + a0*a1^5*a2^7*a3*b0*b3*b5 +
   a0*a1^5*a2^7*a3*b1^2*b6 + a0*a1^5*a2^7*a3*b1*b2*b5 +
   a0*a1^5*a2^6*a3^2*b0*b1*b6 + a0*a1^5*a2^6*a3^2*b0*b3*b4 +
   a0*a1^5*a2^6*a3^2*b1*b2*b4 + a0*a1^5*a2^6*b0*b3*b5^2 +
   a0*a1^5*a2^6*b1^2*b5*b6 + a0*a1^5*a2^6*b1*b2*b5^2 +
   a0*a1^5*a2^6*b1*b3^2*b6 + a0*a1^5*a2^5*a3^3*b0*b1*b5 +
   a0*a1^5*a2^5*a3^3*b0*b3^2 + a0*a1^5*a2^5*a3^3*b1^2*b4 +
   a0*a1^5*a2^5*a3^3*b1*b2*b3 + a0*a1^5*a2^5*a3*b1*b3^2*b5 +
   a0*a1^5*a2^4*a3^4*b0^2*b5 + a0*a1^5*a2^4*a3^4*b0*b1*b4 +
   a0*a1^5*a2^4*a3^4*b0*b2*b3 + a0*a1^5*a2^4*a3^4*b1*b2^2 +
   a0*a1^5*a2^4*a3^2*b0*b1*b5^2 + a0*a1^5*a2^4*a3^2*b1^2*b3*b6 +
   a0*a1^5*a2^4*a3^2*b1^2*b4*b5 + a0*a1^5*a2^4*a3^2*b1*b3^2*b4 +
   a0*a1^5*a2^4*b1^2*b5^3 + a0*a1^5*a2^4*b1*b3^2*b5^2 +
   a0*a1^5*a2^3*a3^3*b1*b3^3 + a0*a1^5*a2^2*a3^4*b0*b3^3 +
   a0*a1^5*a2^2*a3^2*b1^2*b3*b5^2 + a0*a1^5*a3^4*b1*b3^4 +
   a0*a1^4*a2^9*b1^2*b6 + a0*a1^4*a2^8*a3*b0*b1*b6 +
   a0*a1^4*a2^8*a3*b1^2*b5 + a0*a1^4*a2^7*a3^2*b0*b1*b5 +
   a0*a1^4*a2^7*a3^2*b1^2*b4 + a0*a1^4*a2^7*b1^2*b5^2 +
   a0*a1^4*a2^6*a3^3*b0^2*b5 + a0*a1^4*a2^6*a3^3*b0*b1*b4 +
   a0*a1^4*a2^6*a3^3*b1^2*b3 + a0*a1^4*a2^6*a3*b0*b1*b5^2 +
   a0*a1^4*a2^6*a3*b1^2*b3*b6 + a0*a1^4*a2^5*a3^4*b0*b1*b3 +
   a0*a1^4*a2^5*a3^4*b1^2*b2 + a0*a1^4*a2^4*a3^5*b0^2*b3 +
   a0*a1^4*a2^4*a3^5*b0*b1*b2 + a0*a1^4*a2^4*a3^5*b1^3 +
   a0*a1^4*a2^4*a3^3*b1^3*b6 + a0*a1^4*a2^4*a3^3*b1^2*b2*b5 +
   a0*a1^4*a2^4*a3^3*b1^2*b3*b4 + a0*a1^4*a2^4*a3*b1^2*b3*b5^2 +
   a0*a1^4*a2^3*a3^4*b1^3*b5 + a0*a1^4*a2^3*a3^4*b1^2*b3^2 +
   a0*a1^4*a2^2*a3^5*b0*b1^2*b5 + a0*a1^4*a2^2*a3^5*b0*b1*b3^2 +
   a0*a1^4*a2^2*a3^3*b1^3*b5^2 + a0*a1^4*a2^2*a3^3*b1^2*b3^2*b5 +
   a0*a1^3*a2^8*b1^2*b3*b6 + a0*a1^3*a2^7*a3*b1^2*b3*b5 +
   a0*a1^3*a2^6*a3^2*b1^2*b3*b4 + a0*a1^3*a2^6*b1^2*b3*b5^2 +
   a0*a1^3*a2^5*a3^3*b1^2*b3^2 + a0*a1^3*a2^4*a3^4*b1^2*b2*b3 +
   a0*a1^3*a2^3*a3^5*b1^3*b3 + a0*a1^3*a2^2*a3^6*b0*b1^2*b3 +
   a0*a1^3*a2^2*a3^4*b1^2*b3^3 + a0*a1^2*a2^8*a3*b1^3*b6 +
   a0*a1^2*a2^7*a3^2*b1^3*b5 + a0*a1^2*a2^6*a3^3*b1^3*b4 +
   a0*a1^2*a2^6*a3*b1^3*b5^2 + a0*a1^2*a2^5*a3^4*b1^3*b3 +
   a0*a1^2*a2^4*a3^5*b1^3*b2 + a0*a1^2*a2^3*a3^6*b1^4 +
   a0*a1^2*a2^2*a3^7*b0*b1^3 + a0*a1^2*a2^2*a3^5*b1^4*b5 +
   a0*a1^2*a2^2*a3^5*b1^3*b3^2 + a0*a1*a2^4*a3^4*b1^4*b5 +
   a0*a1*a2^2*a3^6*b1^4*b3 + a0*a1*a3^8*b1^5 + a0*a2^6*a3^3*b1^4*b5 +
   a0*a2^4*a3^5*b1^4*b3 + a0*a2^2*a3^7*b1^5 + a1^10*a2^4*b0*b6^2 +
   a1^10*b0*b5^4 + a1^9*a2^5*b0*b5*b6 + a1^9*a2^4*a3*b0*b5^2 +
   a1^9*a2^3*b0*b5^3 + a1^8*a2^6*b0*b4*b6 + a1^8*a2^5*a3*b0*b3*b6 +
   a1^8*a2^5*a3*b0*b4*b5 + a1^8*a2^4*a3^2*b0*b4^2 + a1^8*a2^4*b0*b4*b5^2 +
   a1^8*a2^4*b1^2*b6^2 + a1^8*a2^3*a3*b0*b3*b5^2 + a1^8*b1^2*b5^4 +
   a1^7*a2^7*b0*b3*b6 + a1^7*a2^6*a3*b0*b3*b5 + a1^7*a2^5*a3^2*b0*b1*b6 +
   a1^7*a2^5*a3^2*b0*b2*b5 + a1^7*a2^5*a3^2*b0*b3*b4 + a1^7*a2^5*b0*b3*b5^2 +
   a1^7*a2^5*b1^2*b5*b6 + a1^7*a2^4*a3^3*b0*b3^2 + a1^7*a2^4*a3*b1^2*b5^2 +
   a1^7*a2^3*a3^2*b0*b1*b5^2 + a1^7*a2^3*a3^2*b0*b3^2*b5 +
   a1^7*a2^3*b1^2*b5^3 + a1^6*a2^8*b0*b2*b6 + a1^6*a2^7*a3*b0*b1*b6 +
   a1^6*a2^7*a3*b0*b2*b5 + a1^6*a2^6*a3^2*b0^2*b6 +
   a1^6*a2^6*a3^2*b0*b2*b4 + a1^6*a2^6*b0*b2*b5^2 + a1^6*a2^6*b0*b3^2*b6 +
   a1^6*a2^6*b1^2*b4*b6 + a1^6*a2^5*a3^3*b0^2*b5 + a1^6*a2^5*a3^3*b0*b1*b4 +
   a1^6*a2^5*a3^3*b0*b2*b3 + a1^6*a2^5*a3*b0*b1*b5^2 +
   a1^6*a2^5*a3*b0*b3^2*b5 + a1^6*a2^5*a3*b1^2*b3*b6 +
   a1^6*a2^5*a3*b1^2*b4*b5 + a1^6*a2^4*a3^4*b0*b2^2 +
   a1^6*a2^4*a3^2*b0^2*b5^2 + a1^6*a2^4*a3^2*b0*b3^2*b4 +
   a1^6*a2^4*a3^2*b1^2*b4^2 + a1^6*a2^4*b0*b3^2*b5^2 +
   a1^6*a2^4*b1^2*b4*b5^2 + a1^6*a2^3*a3^3*b0*b3^3 +
   a1^6*a2^3*a3*b1^2*b3*b5^2 + a1^6*a3^4*b0*b3^4 + a1^5*a2^9*b0*b1*b6 +
   a1^5*a2^8*a3*b0*b1*b5 + a1^5*a2^7*a3^2*b0^2*b5 + a1^5*a2^7*a3^2*b0*b1*b4 +
   a1^5*a2^7*b0*b1*b5^2 + a1^5*a2^7*b1^2*b3*b6 + a1^5*a2^6*a3^3*b0*b1*b3 +
   a1^5*a2^6*a3*b1^2*b3*b5 + a1^5*a2^5*a3^4*b0^2*b3 +
   a1^5*a2^5*a3^4*b0*b1*b2 + a1^5*a2^5*a3^2*b1^3*b6 +
   a1^5*a2^5*a3^2*b1^2*b2*b5 + a1^5*a2^5*a3^2*b1^2*b3*b4 +
   a1^5*a2^5*b1^2*b3*b5^2 + a1^5*a2^4*a3^5*b0*b1^2 +
   a1^5*a2^4*a3^3*b1^2*b3^2 + a1^5*a2^3*a3^4*b0*b1^2*b5 +
   a1^5*a2^3*a3^4*b0*b1*b3^2 + a1^5*a2^3*a3^2*b1^3*b5^2 +
   a1^5*a2^3*a3^2*b1^2*b3^2*b5 + a1^4*a2^10*b0^2*b6 + a1^4*a2^9*a3*b0^2*b5 +
   a1^4*a2^8*a3^2*b0^2*b4 + a1^4*a2^8*b0^2*b5^2 + a1^4*a2^8*b1^2*b2*b6 +
   a1^4*a2^7*a3^3*b0^2*b3 + a1^4*a2^7*a3*b1^3*b6 + a1^4*a2^7*a3*b1^2*b2*b5 +
   a1^4*a2^6*a3^4*b0^2*b2 + a1^4*a2^6*a3^2*b0*b1^2*b6 +
   a1^4*a2^6*a3^2*b1^2*b2*b4 + a1^4*a2^6*b1^2*b2*b5^2 +
   a1^4*a2^6*b1^2*b3^2*b6 + a1^4*a2^5*a3^5*b0^2*b1 +
   a1^4*a2^5*a3^3*b0*b1^2*b5 + a1^4*a2^5*a3^3*b1^3*b4 +
   a1^4*a2^5*a3^3*b1^2*b2*b3 + a1^4*a2^5*a3*b1^3*b5^2 +
   a1^4*a2^5*a3*b1^2*b3^2*b5 + a1^4*a2^4*a3^6*b0^3 +
   a1^4*a2^4*a3^4*b0^2*b3^2 + a1^4*a2^4*a3^4*b0*b1^2*b4 +
   a1^4*a2^4*a3^4*b1^2*b2^2 + a1^4*a2^4*a3^2*b0*b1^2*b5^2 +
   a1^4*a2^4*a3^2*b1^2*b3^2*b4 + a1^4*a2^4*b1^2*b3^2*b5^2 +
   a1^4*a2^3*a3^5*b0*b1^2*b3 + a1^4*a2^3*a3^3*b1^2*b3^3 +
   a1^4*a3^4*b1^2*b3^4 + a1^3*a2^9*b1^3*b6 + a1^3*a2^8*a3*b1^3*b5 +
   a1^3*a2^7*a3^2*b1^3*b4 + a1^3*a2^7*b1^3*b5^2 + a1^3*a2^6*a3^3*b1^3*b3 +
   a1^3*a2^5*a3^4*b1^3*b2 + a1^3*a2^4*a3^5*b1^4 + a1^3*a2^3*a3^6*b0*b1^3 +
   a1^3*a2^3*a3^4*b1^4*b5 + a1^3*a2^3*a3^4*b1^3*b3^2 +
   a1^2*a2^4*a3^4*b1^4*b4 + a1^2*a2^3*a3^5*b1^4*b3 + a1^2*a3^8*b0*b1^4 +
   a1*a2^7*a3^2*b1^4*b5 + a1*a2^5*a3^4*b1^4*b3 + a1*a2^3*a3^6*b1^5 +
   a2^10*b1^4*b6 + a2^9*a3*b1^4*b5 + a2^8*a3^2*b1^4*b4 + a2^8*b1^4*b5^2 +
   a2^7*a3^3*b1^4*b3 + a2^6*a3^4*b1^4*b2 + a2^5*a3^5*b1^5 +
   a2^4*a3^6*b0*b1^4 + a2^4*a3^4*b1^4*b3^2 + a3^8*b1^6
  ];
end function;

intrinsic ScaledIgusaInvariants(f::RngUPolElt, h::RngUPolElt) -> SeqEnum
    {Compute the Igusa J-invariants of the curve y^2 + h*y - f = 0,
    scaled by [16, 16^2, 16^3, 16^4, 16^5].  The polynomial h must have
    degree at most 3, the polynomial f must have degree at most 6, and 
    the characteristic of the base ring should not be 2.}

    require (Degree(h) le 3) and (Degree(f) le 6) :
    "The polynomials h and f must have degree at most 3 and 6, respectively.";

    require Characteristic(BaseRing(Parent(f))) ne 2 :
        "The base ring should not have characteristic 2.";
    return ScaledIgusaInvariants(h^2 + 4*f);
end intrinsic;


intrinsic ScaledIgusaInvariants(f::RngUPolElt) -> SeqEnum
  {Compute the Igusa J-invariants of a polynomial of degree at most 6,
  scaled by [16, 16^2, 16^3, 16^4, 16^5].  The coefficient ring
  must not have characteristic 2.}

  require Degree(f) le 6 : "Argument must have degree at most 6";
  require Characteristic(BaseRing(Parent(f))) ne 2 :
      "The base ring should not have characteristic 2.";
  b0,b1,b2,b3,b4,b5,b6 := Explode([ Coefficient(f,i) : i in [0..6] ]);
  return [
  -480*b0*b6 + 80*b1*b5 - 32*b2*b4 + 12*b3^2,
   5280*b0^2*b6^2 - 1760*b0*b1*b5*b6 + 2624*b0*b2*b4*b6 - 800*b0*b2*b5^2 -
   1344*b0*b3^2*b6 + 480*b0*b3*b4*b5 - 128*b0*b4^3 - 800*b1^2*b4*b6 +
   480*b1^2*b5^2 + 480*b1*b2*b3*b6 - 224*b1*b2*b4*b5 - 16*b1*b3^2*b5 +
   32*b1*b3*b4^2 - 128*b2^3*b6 + 32*b2^2*b3*b5 + 32*b2^2*b4^2 -
   32*b2*b3^2*b4 + 6*b3^4,
  20480*b0^3*b6^3 - 10240*b0^2*b1*b5*b6^2 - 57344*b0^2*b2*b4*b6^2 +
   25600*b0^2*b2*b5^2*b6 - 10176*b0^2*b3^2*b6^2 + 42240*b0^2*b3*b4*b5*b6 -
   16000*b0^2*b3*b5^3 - 16384*b0^2*b4^3*b6 + 6400*b0^2*b4^2*b5^2 +
   25600*b0*b1^2*b4*b6^2 - 8960*b0*b1^2*b5^2*b6 + 42240*b0*b1*b2*b3*b6^2 -
   26112*b0*b1*b2*b4*b5*b6 + 6400*b0*b1*b2*b5^3 - 17728*b0*b1*b3^2*b5*b6 +
   10496*b0*b1*b3*b4^2*b6 + 2560*b0*b1*b3*b4*b5^2 - 1536*b0*b1*b4^3*b5 -
   16384*b0*b2^3*b6^2 + 10496*b0*b2^2*b3*b5*b6 + 4096*b0*b2^2*b4^2*b6 -
   2560*b0*b2^2*b4*b5^2 - 6272*b0*b2*b3^2*b4*b6 + 320*b0*b2*b3^2*b5^2 +
   768*b0*b2*b3*b4^2*b5 + 1248*b0*b3^4*b6 - 192*b0*b3^3*b4*b5 -
   16000*b1^3*b3*b6^2 + 6400*b1^3*b4*b5*b6 - 1280*b1^3*b5^3 +
   6400*b1^2*b2^2*b6^2 + 2560*b1^2*b2*b3*b5*b6 - 2560*b1^2*b2*b4^2*b6 +
   256*b1^2*b2*b4*b5^2 + 320*b1^2*b3^2*b4*b6 + 704*b1^2*b3^2*b5^2 -
   896*b1^2*b3*b4^2*b5 + 256*b1^2*b4^4 - 1536*b1*b2^3*b5*b6 +
   768*b1*b2^2*b3*b4*b6 - 896*b1*b2^2*b3*b5^2 + 512*b1*b2^2*b4^2*b5 -
   192*b1*b2*b3^3*b6 + 448*b1*b2*b3^2*b4*b5 - 256*b1*b2*b3*b4^3 -
   112*b1*b3^4*b5 + 64*b1*b3^3*b4^2 + 256*b2^4*b5^2 - 256*b2^3*b3*b4*b5 +
   64*b2^2*b3^3*b5 + 64*b2^2*b3^2*b4^2 - 32*b2*b3^4*b4 + 4*b3^6,
  -9427200*b0^4*b6^4 + 6284800*b0^3*b1*b5*b6^3 - 209920*b0^3*b2*b4*b6^3 -
   960000*b0^3*b2*b5^2*b6^2 + 4830720*b0^3*b3^2*b6^3 -
   6336000*b0^3*b3*b4*b5*b6^2 + 1920000*b0^3*b3*b5^3*b6 +
   2304000*b0^3*b4^3*b6^2 - 768000*b0^3*b4^2*b5^2*b6 -
   960000*b0^2*b1^2*b4*b6^3 - 1171200*b0^2*b1^2*b5^2*b6^2 -
   6336000*b0^2*b1*b2*b3*b6^3 + 4968960*b0^2*b1*b2*b4*b5*b6^2 -
   960000*b0^2*b1*b2*b5^3*b6 + 752640*b0^2*b1*b3^2*b5*b6^2 -
   1344000*b0^2*b1*b3*b4^2*b6^2 + 960000*b0^2*b1*b3*b4*b5^2*b6 -
   320000*b0^2*b1*b3*b5^4 - 256000*b0^2*b1*b4^3*b5*b6 +
   128000*b0^2*b1*b4^2*b5^3 + 2304000*b0^2*b2^3*b6^3 -
   1344000*b0^2*b2^2*b3*b5*b6^2 - 1838592*b0^2*b2^2*b4^2*b6^2 +
   1152000*b0^2*b2^2*b4*b5^2*b6 - 160000*b0^2*b2^2*b5^4 +
   2509824*b0^2*b2*b3^2*b4*b6^2 - 499200*b0^2*b2*b3^2*b5^2*b6 -
   1059840*b0^2*b2*b3*b4^2*b5*b6 + 320000*b0^2*b2*b3*b4*b5^3 +
   299008*b0^2*b2*b4^4*b6 - 102400*b0^2*b2*b4^3*b5^2 -
   647712*b0^2*b3^4*b6^2 + 472320*b0^2*b3^3*b4*b5*b6 -
   48000*b0^2*b3^3*b5^3 - 135168*b0^2*b3^2*b4^3*b6 -
   38400*b0^2*b3^2*b4^2*b5^2 + 30720*b0^2*b3*b4^4*b5 - 
  4096*b0^2*b4^6 + 1920000*b0*b1^3*b3*b6^3 - 960000*b0*b1^3*b4*b5*b6^2 +
   396800*b0*b1^3*b5^3*b6 - 768000*b0*b1^2*b2^2*b6^3 +
   960000*b0*b1^2*b2*b3*b5*b6^2 + 1152000*b0*b1^2*b2*b4^2*b6^2 -
   1628160*b0*b1^2*b2*b4*b5^2*b6 + 320000*b0*b1^2*b2*b5^4 -
   499200*b0*b1^2*b3^2*b4*b6^2 - 157440*b0*b1^2*b3^2*b5^2*b6 +
   537600*b0*b1^2*b3*b4^2*b5*b6 - 64000*b0*b1^2*b3*b4*b5^3 -
   81920*b0*b1^2*b4^4*b6 - 256000*b0*b1*b2^3*b5*b6^2 -
   1059840*b0*b1*b2^2*b3*b4*b6^2 + 537600*b0*b1*b2^2*b3*b5^2*b6 +
   551424*b0*b1*b2^2*b4^2*b5*b6 - 192000*b0*b1*b2^2*b4*b5^3 +
   472320*b0*b1*b2*b3^3*b6^2 - 388608*b0*b1*b2*b3^2*b4*b5*b6 +
   19200*b0*b1*b2*b3^2*b5^3 - 64512*b0*b1*b2*b3*b4^3*b6 +
   61440*b0*b1*b2*b3*b4^2*b5^2 - 2048*b0*b1*b2*b4^4*b5 -
   20256*b0*b1*b3^4*b5*b6 + 45312*b0*b1*b3^3*b4^2*b6 +
   7680*b0*b1*b3^3*b4*b5^2 - 13312*b0*b1*b3^2*b4^3*b5 +
   2048*b0*b1*b3*b4^5 + 299008*b0*b2^4*b4*b6^2 - 81920*b0*b2^4*b5^2*b6 -
   135168*b0*b2^3*b3^2*b6^2 - 64512*b0*b2^3*b3*b4*b5*b6 +
   12800*b0*b2^3*b3*b5^3 - 82944*b0*b2^3*b4^3*b6 + 33280*b0*b2^3*b4^2*b5^2 +
   45312*b0*b2^2*b3^3*b5*b6 + 118272*b0*b2^2*b3^2*b4^2*b6 -
   30720*b0*b2^2*b3^2*b4*b5^2 - 11776*b0*b2^2*b3*b4^3*b5 +
   2048*b0*b2^2*b4^5 - 54336*b0*b2*b3^4*b4*b6 + 3360*b0*b2*b3^4*b5^2 +
   11520*b0*b2*b3^3*b4^2*b5 - 2048*b0*b2*b3^2*b4^4 + 7296*b0*b3^6*b6 -
   2016*b0*b3^5*b4*b5 + 384*b0*b3^4*b4^3 - 320000*b1^4*b3*b5*b6^2 -
   160000*b1^4*b4^2*b6^2 + 320000*b1^4*b4*b5^2*b6 - 83200*b1^4*b5^4 +
   128000*b1^3*b2^2*b5*b6^2 + 320000*b1^3*b2*b3*b4*b6^2 -
   64000*b1^3*b2*b3*b5^2*b6 - 192000*b1^3*b2*b4^2*b5*b6 +
   69120*b1^3*b2*b4*b5^3 - 48000*b1^3*b3^3*b6^2 + 19200*b1^3*b3^2*b4*b5*b6 +
   14080*b1^3*b3^2*b5^3 + 12800*b1^3*b3*b4^3*b6 - 25600*b1^3*b3*b4^2*b5^2 +
   5120*b1^3*b4^4*b5 - 102400*b1^2*b2^3*b4*b6^2 -
   38400*b1^2*b2^2*b3^2*b6^2 + 61440*b1^2*b2^2*b3*b4*b5*b6 -
   25600*b1^2*b2^2*b3*b5^3 + 33280*b1^2*b2^2*b4^3*b6 -
   12032*b1^2*b2^2*b4^2*b5^2 + 7680*b1^2*b2*b3^3*b5*b6 -
   30720*b1^2*b2*b3^2*b4^2*b6 + 9984*b1^2*b2*b3^2*b4*b5^2 +
   5632*b1^2*b2*b3*b4^3*b5 - 2048*b1^2*b2*b4^5 + 3360*b1^2*b3^4*b4*b6 -
   1632*b1^2*b3^4*b5^2 - 1152*b1^2*b3^3*b4^2*b5 + 512*b1^2*b3^2*b4^4 +
   30720*b1*b2^4*b3*b6^2 - 2048*b1*b2^4*b4*b5*b6 + 5120*b1*b2^4*b5^3 -
   13312*b1*b2^3*b3^2*b5*b6 - 11776*b1*b2^3*b3*b4^2*b6 +
   5632*b1*b2^3*b3*b4*b5^2 - 512*b1*b2^3*b4^3*b5 +
   11520*b1*b2^2*b3^3*b4*b6 - 1152*b1*b2^2*b3^3*b5^2 -
   4608*b1*b2^2*b3^2*b4^2*b5 + 1536*b1*b2^2*b3*b4^4 - 2016*b1*b2*b3^5*b6 +
   2016*b1*b2*b3^4*b4*b5 - 768*b1*b2*b3^3*b4^3 - 208*b1*b3^6*b5 +
   96*b1*b3^5*b4^2 - 4096*b2^6*b6^2 + 2048*b2^5*b3*b5*b6 +
   2048*b2^5*b4^2*b6 - 2048*b2^5*b4*b5^2 - 2048*b2^4*b3^2*b4*b6 +
   512*b2^4*b3^2*b5^2 + 1536*b2^4*b3*b4^2*b5 - 256*b2^4*b4^4 +
   384*b2^3*b3^4*b6 - 768*b2^3*b3^3*b4*b5 + 96*b2^2*b3^5*b5 +
   96*b2^2*b3^4*b4^2 - 32*b2*b3^6*b4 + 3*b3^8,
  -11943936*b0^5*b6^5 + 9953280*b0^4*b1*b5*b6^4 + 15925248*b0^4*b2*b4*b6^4 -
   8294400*b0^4*b2*b5^2*b6^3 + 8957952*b0^4*b3^2*b6^4 -
   19906560*b0^4*b3*b4*b5*b6^3 + 6912000*b0^4*b3*b5^3*b6^2 -
   3538944*b0^4*b4^3*b6^3 + 11059200*b0^4*b4^2*b5^2*b6^2 -
   5760000*b0^4*b4*b5^4*b6 + 800000*b0^4*b5^6 - 8294400*b0^3*b1^2*b4*b6^4 +
   138240*b0^3*b1^2*b5^2*b6^3 - 19906560*b0^3*b1*b2*b3*b6^4 +
   8183808*b0^3*b1*b2*b4*b5*b6^3 - 460800*b0^3*b1*b2*b5^3*b6^2 +
   3981312*b0^3*b1*b3^2*b5*b6^3 + 11943936*b0^3*b1*b3*b4^2*b6^3 -
   8017920*b0^3*b1*b3*b4*b5^2*b6^2 + 576000*b0^3*b1*b3*b5^4*b6 -
   5603328*b0^3*b1*b4^3*b5*b6^2 + 3993600*b0^3*b1*b4^2*b5^3*b6 -
   640000*b0^3*b1*b4*b5^5 - 3538944*b0^3*b2^3*b6^4 +
   11943936*b0^3*b2^2*b3*b5*b6^3 - 4423680*b0^3*b2^2*b4^2*b6^3 -
   1658880*b0^3*b2^2*b4*b5^2*b6^2 + 384000*b0^3*b2^2*b5^4*b6 +
   995328*b0^3*b2*b3^2*b4*b6^3 - 7050240*b0^3*b2*b3^2*b5^2*b6^2 -
   884736*b0^3*b2*b3*b4^2*b5*b6^2 + 5068800*b0^3*b2*b3*b4*b5^3*b6 -
   960000*b0^3*b2*b3*b5^5 + 2359296*b0^3*b2*b4^4*b6^2 -
   2703360*b0^3*b2*b4^3*b5^2*b6 + 512000*b0^3*b2*b4^2*b5^4 -
   2239488*b0^3*b3^4*b6^3 + 5474304*b0^3*b3^3*b4*b5*b6^2 -
   345600*b0^3*b3^3*b5^3*b6 - 2211840*b0^3*b3^2*b4^3*b6^2 -
   2488320*b0^3*b3^2*b4^2*b5^2*b6 + 576000*b0^3*b3^2*b4*b5^4 +
   1769472*b0^3*b3*b4^4*b5*b6 - 409600*b0^3*b3*b4^3*b5^3 -
   262144*b0^3*b4^6*b6 + 65536*b0^3*b4^5*b5^2 + 6912000*b0^2*b1^3*b3*b6^4 -
   460800*b0^2*b1^3*b4*b5*b6^3 + 104960*b0^2*b1^3*b5^3*b6^2 +
   11059200*b0^2*b1^2*b2^2*b6^4 - 8017920*b0^2*b1^2*b2*b3*b5*b6^3 -
   1658880*b0^2*b1^2*b2*b4^2*b6^3 + 2239488*b0^2*b1^2*b2*b4*b5^2*b6^2 -
   435200*b0^2*b1^2*b2*b5^4*b6 - 7050240*b0^2*b1^2*b3^2*b4*b6^3 +
   3946752*b0^2*b1^2*b3^2*b5^2*b6^2 + 4257792*b0^2*b1^2*b3*b4^2*b5*b6^2 -
   3156480*b0^2*b1^2*b3*b4*b5^3*b6 + 512000*b0^2*b1^2*b3*b5^5 -
   49152*b0^2*b1^2*b4^4*b6^2 + 63488*b0^2*b1^2*b4^3*b5^2*b6 -
   12800*b0^2*b1^2*b4^2*b5^4 - 5603328*b0^2*b1*b2^3*b5*b6^3 -
   884736*b0^2*b1*b2^2*b3*b4*b6^3 + 4257792*b0^2*b1*b2^2*b3*b5^2*b6^2 +
   3907584*b0^2*b1*b2^2*b4^2*b5*b6^2 - 3338240*b0^2*b1*b2^2*b4*b5^3*b6 +
   576000*b0^2*b1*b2^2*b5^5 + 5474304*b0^2*b1*b2*b3^3*b6^3 -
   5861376*b0^2*b1*b2*b3^2*b4*b5*b6^2 + 506880*b0^2*b1*b2*b3^2*b5^3*b6 -
   1474560*b0^2*b1*b2*b3*b4^3*b6^2 + 2598912*b0^2*b1*b2*b3*b4^2*b5^2*b6 -
   524800*b0^2*b1*b2*b3*b4*b5^4 - 163840*b0^2*b1*b2*b4^4*b5*b6 +
   40960*b0^2*b1*b2*b4^3*b5^3 - 1617408*b0^2*b1*b3^4*b5*b6^2 +
   1492992*b0^2*b1*b3^3*b4^2*b6^2 + 1009152*b0^2*b1*b3^3*b4*b5^2*b6 -
   230400*b0^2*b1*b3^3*b5^4 - 1142784*b0^2*b1*b3^2*b4^3*b5*b6 +
   261120*b0^2*b1*b3^2*b4^2*b5^3 + 196608*b0^2*b1*b3*b4^5*b6 -
   49152*b0^2*b1*b3*b4^4*b5^2 + 2359296*b0^2*b2^4*b4*b6^3 -
   49152*b0^2*b2^4*b5^2*b6^2 - 2211840*b0^2*b2^3*b3^2*b6^3 -
   1474560*b0^2*b2^3*b3*b4*b5*b6^2 - 30720*b0^2*b2^3*b3*b5^3*b6 -
   1114112*b0^2*b2^3*b4^3*b6^2 + 1232896*b0^2*b2^3*b4^2*b5^2*b6 -
   230400*b0^2*b2^3*b4*b5^4 + 1492992*b0^2*b2^2*b3^3*b5*b6^2 +
   2101248*b0^2*b2^2*b3^2*b4^2*b6^2 - 1161216*b0^2*b2^2*b3^2*b4*b5^2*b6 +
   211200*b0^2*b2^2*b3^2*b5^4 - 638976*b0^2*b2^2*b3*b4^3*b5*b6 +
   143360*b0^2*b2^2*b3*b4^2*b5^3 + 131072*b0^2*b2^2*b4^5*b6 -
   32768*b0^2*b2^2*b4^4*b5^2 - 1244160*b0^2*b2*b3^4*b4*b6^2 +
   41472*b0^2*b2*b3^4*b5^2*b6 + 718848*b0^2*b2*b3^3*b4^2*b5*b6 -
   161280*b0^2*b2*b3^3*b4*b5^3 - 147456*b0^2*b2*b3^2*b4^4*b6 +
   36864*b0^2*b2*b3^2*b4^3*b5^2 + 186624*b0^2*b3^6*b6^2 -
   124416*b0^2*b3^5*b4*b5*b6 + 27648*b0^2*b3^5*b5^3 +
   27648*b0^2*b3^4*b4^3*b6 - 6912*b0^2*b3^4*b4^2*b5^2 -
   5760000*b0*b1^4*b2*b6^4 + 576000*b0*b1^4*b3*b5*b6^3 +
   384000*b0*b1^4*b4^2*b6^3 - 435200*b0*b1^4*b4*b5^2*b6^2 +
   81920*b0*b1^4*b5^4*b6 + 3993600*b0*b1^3*b2^2*b5*b6^3 +
   5068800*b0*b1^3*b2*b3*b4*b6^3 - 3156480*b0*b1^3*b2*b3*b5^2*b6^2 -
   3338240*b0*b1^3*b2*b4^2*b5*b6^2 + 2500608*b0*b1^3*b2*b4*b5^3*b6 -
   409600*b0*b1^3*b2*b5^5 - 345600*b0*b1^3*b3^3*b6^3 +
   506880*b0*b1^3*b3^2*b4*b5*b6^2 - 53248*b0*b1^3*b3^2*b5^3*b6 -
   30720*b0*b1^3*b3*b4^3*b6^2 - 174592*b0*b1^3*b3*b4^2*b5^2*b6 +
   40960*b0*b1^3*b3*b4*b5^4 + 36864*b0*b1^3*b4^4*b5*b6 -
   9216*b0*b1^3*b4^3*b5^3 - 2703360*b0*b1^2*b2^3*b4*b6^3 +
   63488*b0*b1^2*b2^3*b5^2*b6^2 - 2488320*b0*b1^2*b2^2*b3^2*b6^3 +
   2598912*b0*b1^2*b2^2*b3*b4*b5*b6^2 - 174592*b0*b1^2*b2^2*b3*b5^3*b6 +
   1232896*b0*b1^2*b2^2*b4^3*b6^2 - 1389568*b0*b1^2*b2^2*b4^2*b5^2*b6 +
   261120*b0*b1^2*b2^2*b4*b5^4 + 1009152*b0*b1^2*b2*b3^3*b5*b6^2 -
   1161216*b0*b1^2*b2*b3^2*b4^2*b6^2 - 617472*b0*b1^2*b2*b3^2*b4*b5^2*b6 +
   143360*b0*b1^2*b2*b3^2*b5^4 + 837632*b0*b1^2*b2*b3*b4^3*b5*b6 -
   190976*b0*b1^2*b2*b3*b4^2*b5^3 - 147456*b0*b1^2*b2*b4^5*b6 +
   36864*b0*b1^2*b2*b4^4*b5^2 + 41472*b0*b1^2*b3^4*b4*b6^2 -
   27648*b0*b1^2*b3^3*b4^2*b5*b6 + 6144*b0*b1^2*b3^3*b4*b5^3 +
   6144*b0*b1^2*b3^2*b4^4*b6 - 1536*b0*b1^2*b3^2*b4^3*b5^2 +
   1769472*b0*b1*b2^4*b3*b6^3 - 163840*b0*b1*b2^4*b4*b5*b6^2 +
   36864*b0*b1*b2^4*b5^3*b6 - 1142784*b0*b1*b2^3*b3^2*b5*b6^2 -
   638976*b0*b1*b2^3*b3*b4^2*b6^2 + 837632*b0*b1*b2^3*b3*b4*b5^2*b6 -
   161280*b0*b1*b2^3*b3*b5^4 - 24576*b0*b1*b2^3*b4^3*b5*b6 +
   6144*b0*b1*b2^3*b4^2*b5^3 + 718848*b0*b1*b2^2*b3^3*b4*b6^2 -
   27648*b0*b1*b2^2*b3^3*b5^2*b6 - 405504*b0*b1*b2^2*b3^2*b4^2*b5*b6 +
   91136*b0*b1*b2^2*b3^2*b4*b5^3 + 81920*b0*b1*b2^2*b3*b4^4*b6 -
   20480*b0*b1*b2^2*b3*b4^3*b5^2 - 124416*b0*b1*b2*b3^5*b6^2 +
   82944*b0*b1*b2*b3^4*b4*b5*b6 - 18432*b0*b1*b2*b3^4*b5^3 -
   18432*b0*b1*b2*b3^3*b4^3*b6 + 4608*b0*b1*b2*b3^3*b4^2*b5^2 -
   262144*b0*b2^6*b6^3 + 196608*b0*b2^5*b3*b5*b6^2 +
   131072*b0*b2^5*b4^2*b6^2 - 147456*b0*b2^5*b4*b5^2*b6 +
   27648*b0*b2^5*b5^4 - 147456*b0*b2^4*b3^2*b4*b6^2 +
   6144*b0*b2^4*b3^2*b5^2*b6 + 81920*b0*b2^4*b3*b4^2*b5*b6 -
   18432*b0*b2^4*b3*b4*b5^3 - 16384*b0*b2^4*b4^4*b6 +
   4096*b0*b2^4*b4^3*b5^2 + 27648*b0*b2^3*b3^4*b6^2 -
   18432*b0*b2^3*b3^3*b4*b5*b6 + 4096*b0*b2^3*b3^3*b5^3 +
   4096*b0*b2^3*b3^2*b4^3*b6 - 1024*b0*b2^3*b3^2*b4^2*b5^2 +
   800000*b1^6*b6^4 - 640000*b1^5*b2*b5*b6^3 - 960000*b1^5*b3*b4*b6^3 +
   512000*b1^5*b3*b5^2*b6^2 + 576000*b1^5*b4^2*b5*b6^2 -
   409600*b1^5*b4*b5^3*b6 + 65536*b1^5*b5^5 + 512000*b1^4*b2^2*b4*b6^3 -
   12800*b1^4*b2^2*b5^2*b6^2 + 576000*b1^4*b2*b3^2*b6^3 -
   524800*b1^4*b2*b3*b4*b5*b6^2 + 40960*b1^4*b2*b3*b5^3*b6 -
   230400*b1^4*b2*b4^3*b6^2 + 261120*b1^4*b2*b4^2*b5^2*b6 -
   49152*b1^4*b2*b4*b5^4 - 230400*b1^4*b3^3*b5*b6^2 +
   211200*b1^4*b3^2*b4^2*b6^2 + 143360*b1^4*b3^2*b4*b5^2*b6 -
   32768*b1^4*b3^2*b5^4 - 161280*b1^4*b3*b4^3*b5*b6 +
   36864*b1^4*b3*b4^2*b5^3 + 27648*b1^4*b4^5*b6 -
   6912*b1^4*b4^4*b5^2 - 409600*b1^3*b2^3*b3*b6^3 +
   40960*b1^3*b2^3*b4*b5*b6^2 - 9216*b1^3*b2^3*b5^3*b6 +
   261120*b1^3*b2^2*b3^2*b5*b6^2 + 143360*b1^3*b2^2*b3*b4^2*b6^2 -
   190976*b1^3*b2^2*b3*b4*b5^2*b6 + 36864*b1^3*b2^2*b3*b5^4 +
   6144*b1^3*b2^2*b4^3*b5*b6 - 1536*b1^3*b2^2*b4^2*b5^3 -
   161280*b1^3*b2*b3^3*b4*b6^2 + 6144*b1^3*b2*b3^3*b5^2*b6 +
   91136*b1^3*b2*b3^2*b4^2*b5*b6 - 20480*b1^3*b2*b3^2*b4*b5^3 -
   18432*b1^3*b2*b3*b4^4*b6 + 4608*b1^3*b2*b3*b4^3*b5^2 +
   27648*b1^3*b3^5*b6^2 - 18432*b1^3*b3^4*b4*b5*b6 + 4096*b1^3*b3^4*b5^3 +
   4096*b1^3*b3^3*b4^3*b6 - 1024*b1^3*b3^3*b4^2*b5^2 +
   65536*b1^2*b2^5*b6^3 - 49152*b1^2*b2^4*b3*b5*b6^2 -
   32768*b1^2*b2^4*b4^2*b6^2 + 36864*b1^2*b2^4*b4*b5^2*b6 -
   6912*b1^2*b2^4*b5^4 + 36864*b1^2*b2^3*b3^2*b4*b6^2 -
   1536*b1^2*b2^3*b3^2*b5^2*b6 - 20480*b1^2*b2^3*b3*b4^2*b5*b6 +
   4608*b1^2*b2^3*b3*b4*b5^3 + 4096*b1^2*b2^3*b4^4*b6 -
   1024*b1^2*b2^3*b4^3*b5^2 - 6912*b1^2*b2^2*b3^4*b6^2 +
   4608*b1^2*b2^2*b3^3*b4*b5*b6 - 1024*b1^2*b2^2*b3^3*b5^3 -
   1024*b1^2*b2^2*b3^2*b4^3*b6 + 256*b1^2*b2^2*b3^2*b4^2*b5^2
  ];
end intrinsic;

intrinsic IgusaInvariants(f::RngUPolElt, h::RngUPolElt) -> SeqEnum 
    {Compute the Igusa J-invariants of the curve y^2 + h*y - f = 0.
    The polynomial h must have degree at most 3, and the polynomial f
    must have degree at most 6.}

    require (Degree(h) le 3) and (Degree(f) le 6):
    "The polynomials h and f must have degree at most 3 and 6, respectively.";
  
    K := BaseRing(Parent(f));
    if Characteristic(K) eq 2 then
	return IgusaInvariantsCharacteristicTwo(f,h);
    else
	ScaledJs := ScaledIgusaInvariants(f,h);
	return [ExactQuotient(ScaledJs[i],16^i) : i in [1..5]];
    end if;
end intrinsic;

intrinsic IgusaInvariants(f::RngUPolElt: Quick  := false) -> SeqEnum
    {Compute the Igusa J-invariants of a polynomial of degree at most 6.
    The integer 2 must be a unit of the coefficient ring, and if Quick,
    the base field must not be of characteristic 2, 3, or 5.}
    require Degree(f) le 6: "Degree of polynomial must be at most 6.";
    R := BaseRing(Parent(f));
    require IsUnit(R!2):
        "The integer 2 must be a unit of the coefficient ring.";
    if Quick then
	return QuickIgusaInvariants(f);
    end if;
    return IgusaInvariants((R!1/4)*f, Parent(f)!0);
end intrinsic;

intrinsic IgusaInvariants(C::CrvHyp : Quick := false) -> SeqEnum 
    {Compute the Igusa J-invariants of a genus 2 curve over a field.
    If Quick, the base field must not be of characteristic 2, 3, or 5.}
    
    require Genus(C) eq 2: "Curve must be of genus 2.";
    K := BaseField(C);
    R := PolynomialRing(K); x := R.1;
    f, h := HyperellipticPolynomials(C);
    require (Degree(h) le 3) and (Degree(f) le 6): 
    "The curve must be of form y^2 + h*y = f, where
    h has degree at most 3 and f has degree at most 6.";

    if Quick then
	return QuickIgusaInvariantsCurve(C);
    end if;
    return IgusaInvariants(f,h);
end intrinsic;

intrinsic JInvariants(f::RngUPolElt, h::RngUPolElt) -> SeqEnum 
    {Compute the Igusa J-invariants of the curve y^2 + h*y - f = 0.
    The polynomial h must have degree at most 3, and the polynomial f
    must have degree at most 6.}
    return IgusaInvariants(f,h);
end intrinsic;

intrinsic JInvariants(f::RngUPolElt: Quick := false) -> SeqEnum
    {Compute the Igusa J-invariants of a polynomial of degree at most 6.
    The integer 2 must be a unit of the coefficient ring, and if Quick,
    the base field must not be of characteristic 2, 3, or 5.}
    return IgusaInvariants(f);
end intrinsic;

intrinsic JInvariants(C::CrvHyp : Quick := false) -> SeqEnum 
    {Compute the Igusa J-invariants of a genus 2 curve over a field.
    If Quick, the base field must not be of characteristic 2, 3, or 5.}
    return IgusaInvariants(C);
end intrinsic;

/*--------------------------------------------------------------------*/
// Now for the IgusaClebsch invariants...


intrinsic IgusaClebschInvariants(f::RngUPolElt : Quick := false) -> SeqEnum
    {Compute the Igusa-Clebsch invariants A', B', C', D' of a polynomial
    of degree at most 6 (see p. 319 of Mestre).  The integer 2 must be a
    unit of the coefficient ring, and if Quick, the base field must not
    be of characteristic 2, 3, or 5.}

    if Quick then
	return QuickIgusaClebschInvariants(f);
    end if;
     
    Js := IgusaInvariants(f);
    I2 := 8*Js[1];
    I4 := 4*Js[1]^2 - 96*Js[2];
    I6 := 8*Js[1]^3 - 160*Js[1]*Js[2] - 576*Js[3];
    I10:= 4096*Js[5];
    return [I2, I4, I6, I10];
end intrinsic;

intrinsic IgusaClebschInvariants(f::RngUPolElt, h::RngUPolElt) -> SeqEnum 
    {Compute the Igusa-Clebsch invariants of the curve y^2 + h*y - f = 0.
    The polynomial h must have degree at most 3, and the polynomial f must
    have degree at most 6. These will be all be zero in characteristic 2.}
    require Degree(h) le 3 and Degree(f) le 6 :
        "Argument 1 can have degree at most 3 and " * 
        "argument 2 cat have degree at most 6.";
    Js := IgusaInvariants(f,h);
    I2 := 8*Js[1];
    I4 := 4*Js[1]^2 - 96*Js[2];
    I6 := 8*Js[1]^3 - 160*Js[1]*Js[2] - 576*Js[3];
    I10:= 4096*Js[5];
    return [I2, I4, I6, I10];
end intrinsic;

intrinsic IgusaClebschInvariants(C::CrvHyp: Quick := false ) -> SeqEnum 
    {Compute the Igusa J-invariants of a genus 2 curve over a field.
    These will be all be zero in characteristic 2, and if Quick,
    the base field must not be of characteristic 2, 3, or 5.}
     
    if Quick then
	return QuickIgusaClebschInvariantsCurve(C);
    end if;
     
    Js := IgusaInvariants(C);
    I2 := 8*Js[1];
    I4 := 4*Js[1]^2 - 96*Js[2];
    I6 := 8*Js[1]^3 - 160*Js[1]*Js[2] - 576*Js[3];
    I10:= 4096*Js[5];
    return [I2, I4, I6, I10];
end intrinsic;

intrinsic AbsoluteInvariants(C::CrvHyp) -> SeqEnum
    {Compute the 10 absolute invariants as on p. 325 by Mestre:
    J_2^5/J_10, J_2^3*J4/J_10, J_2^2*J_6/J_10, J_2*J_8/J_10, J_4*J_6/J_10,
    J_4*J_8^2/J_10^2, J_6^2*J_8/J_10^2, J_6^5/J_10^3, J_6*J_8^3/J_10^3,
    J_8^5/J_10^4};

    require IsUnit(BaseRing(C)!2):
        "The integer 2 must be a unit of the coefficient ring.";
    require Genus(C) eq 2: "Curve must be of genus 2.";
    JS := JInvariants(HyperellipticPolynomials(SimplifiedModel(C)));
    J2, J4, J6, J8, J10 := Explode(JS);
    AI := [ BaseField(C) |
        J2^5/J10, J2^3*J4/J10, J2^2*J6/J10, J2*J8/J10, J4*J6/J10,
	J4*J8^2/J10^2, J6^2*J8/J10^2,
	J6^5/J10^3, J6*J8^3/J10^3,
        J8^5/J10^4 ];
    return AI;
end intrinsic;

intrinsic ClebschToIgusaClebsch(Inv::[FldElt]) -> SeqEnum
    {Convert Clebsch invariants to Igusa-Clebsch invariants.}
    require #Inv eq 4 :
        "Argument must be a sequence of four Clebsch invariants.";
    A, B, C, D := Explode(Inv);    
    AP := -120*A;
    BP := -720*A^2+6750*B;
    CP := 8640*A^3-108000*A*B+202500*C;
    DP := -62208*A^5+972000*A^3*B+1620000*A^2*C-3037500*A*B^2
        -6075000*B*C-4556250*D;
    return [AP,BP,CP,DP];
end intrinsic;
 
intrinsic IgusaClebschToClebsch(Inv::[FldElt]) -> SeqEnum
    {Convert Igusa-Clebsch invariants to Clebsch invariants.}
    require #Inv eq 4 :
        "Argument must be a sequence of four Igusa-Clebsch invariants.";
    AP, BP, CP, DP := Explode(Inv); 
    A :=-AP/120 ;
    B :=(BP+720*A^2)/6750 ;
    C :=(CP-8640*A^3+108000*A*B)/202500 ;
    D :=(DP+62208*A^5-972000*A^3*B-1620000*A^2*C
        +3037500*A*B^2+6075000*B*C)/(-4556250) ;
    return [A,B,C,D];
end intrinsic;
 
