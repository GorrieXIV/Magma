freeze;

/* This is an implementation of the L_3-U_3-quotient algorithm. 
 * Given a finitely presented group G on two generators, it computes all
 * quotients of G that are isomorphic to L_3(q), U_3(q), PGL(3,q), or PGU(3,q),
 * where the prime power q is not part of the input, but all possible q are
 * computed by the algorithm.
 * 
 * For references, see my PhD thesis (www.math.auckland.ac.nz/~jambor).
 *
 * (C) Sebastian Jambor 2011-2014
 */
declare verbose L3Quotients, 3;

declare type L3Quotient;
declare attributes L3Quotient: Group, Ideal;

/* The polynomial ring is graded. x1, xm1 (this stands for x_{minus 1}), x2, xm2 correspond 
 * to the traces of the two generators and their inverses; they should have degree 1.
 * x12 corresponds to the trace of a*b etc; they should have degree 2.
 * xcom corresponds to the trace of a*b*a^{-1}*b^{-1}; it should have degree 4.
 *
 * However, we want to calculate over the polynomial ring with coefficients in Z[zeta].
 * The easiest solution is to add zeta as a variable and always add the relation zeta^2 + zeta + 1
 * to all ideals. Since zeta is not really a variable, it should have a low degree, hence
 * it gets the lowest degree 1. The other degrees are simply multiplied by 2, to
 * make them bigger than zeta, but still retain their difference to each other.
 *
 * According to Allan, the variables of the highest degree should be in front.
 * Indeed, putting xcom in front made a big difference. But for some reasons,
 * changing the order of the variables of degree 2 and 4 seems to be slower.
 * (Also, according to Allan, PolynomialRing(R, [1,2,3]) is more efficient than
 * PolynomialRing(R, "grevlexw", [1,2,3]).)
 * 
 * If you change the order of the variables in R, make sure to change the 
 * homomorphisms below as well!
 */
R<xcom, x1, xm1, x2, xm2, x12, xm12, xm21, xm2m1, zeta> := PolynomialRing(Integers(), [8,2,2,2,2,4,4,4,4,1]);

/* Sometimes, we have to eliminate zeta from the variables (for example, to compute
 * the degree of the residue class field).
 */
RR := PolynomialRing(Integers(), [8,2,2,2,2,4,4,4,4]);

import "ideals/a6ideals.m": a6presentations;
import "ideals/a7ideals.m": a7presentations;
import "ideals/h36ideals.m": h36presentations;
import "ideals/l27ideals.m": l27presentations;
import "ideals/m10ideals.m": m10presentations;
import "ideals/pgu32ideals.m": pgu32presentations;
import "ideals/psu32ideals.m": psu32presentations;


/* a prime ideal of R corresponds to an absolutely irreducible representation
 * if and only if it does not contain rho.
 */
rho := ideal< R | 
    x1*xm1*x2*xm2-xm1*xm2*x12-x1*xm2*xm12-xm1*x2*xm21-x1*x2*xm2m1+x1*xm1+x2*xm2+xm12*xm21+x12*xm2m1-2*xcom-3,
    x2^2*x1^2-x1*xm1^2*xm2-xm1*x2*xm2^2-x1*xm1*x2*xm12-x1*x2*xm2*xm21+x2^2*xm1+x1^2*xm2-4*x2*x12*x1+xm2^2*xm12+2*xm1*x12*xm12+x1*xm12^2+xm1^2*xm21+2*xm2*x12*xm21+x2*xm21^2+x1*xm1*xm2m1+x2*xm2*xm2m1+xm12*xm21*xm2m1+xm1*xm2*xcom+3*xm1*xm2+3*x12^2-3*xm12*x2-3*x1*xm21-xm2m1*xcom-6*xm2m1,
    xm1^2*x2^2-x1^2*xm1*xm2-x1*x2*xm2^2-x1*xm1*x2*x12-xm1*x2*xm2*xm2m1+x1*x2^2+xm1^2*xm2+xm2^2*x12+xm1*x12^2-4*xm1*x2*xm12+2*x1*x12*xm12+x1*xm1*xm21+x2*xm2*xm21+x1^2*xm2m1+2*xm2*xm12*xm2m1+x12*xm21*xm2m1+x2*xm2m1^2+x1*xm2*xcom+3*xm2*x1-3*x2*x12+3*xm12^2-3*xm1*xm2m1-xm21*xcom-6*xm21,
    x12*xm12*xm2m1+xm1*x2*xcom-xm12*xcom-x1*x2*xm2*x12+xm2*x12^2+2*x2*x12*xm21-x1*xm1*xm2*xm2m1+2*xm1*xm21*xm2m1+x1*xm2m1^2-x1*xm1^2*x2-xm1*x2^2*xm2+x1^2*xm2^2+xm1^2*x12+x1*xm1*xm12+x2*xm2*xm12-4*x1*xm2*xm21+3*xm21^2+x2^2*xm2m1+x2*x1^2+xm1*xm2^2-3*x12*x1-3*xm2m1*xm2+3*x2*xm1-6*xm12,
    x12*xm12*xm21+x1*x2*xcom-x12*xcom-xm1*x2*xm2*xm12+xm2*xm12^2-x1*xm1*xm2*xm21+xm1*xm21^2+2*x2*xm12*xm2m1+2*x1*xm21*xm2m1-x1^2*xm1*x2-x1*x2^2*xm2+xm1^2*xm2^2+x1*xm1*x12+x2*xm2*x12+x1^2*xm12+x2^2*xm21-4*xm1*xm2*xm2m1+3*xm2m1^2+xm1^2*x2+x1*xm2^2-3*xm1*xm12-3*xm2*xm21+3*x1*x2-6*x12,
    -x2^2*xm12-xm2^2*xm2m1-x12*xm12^2+xm1*x2^3-xm21*xm2m1^2+xm1*xm2^3+xm1*x2*x12*xm12+xm1*xm2*xm21*xm2m1+xm1*x2*xm2*xcom+x2*xm2*x12*xm21-3*x1^2+x2^2*xm2*xm2m1+x2*xm2^2*xm12-xm1^2*xm2*x12+xm1*xm12*xm21+xm1*x12*xm2m1+xm1*x2*xm2-xm1*x2^2*xm2^2-xm2*xm12*xcom-xm1^2*x2*xm21-x2*xm2m1*xcom-2*x1*xm2*x12+3*x1^2*xm2*x2-2*x1*xm12*xm2m1-2*xm21*x1*x2-2*x1*xm2^2*xm21-2*x1*x2^2*x12+2*x2*x12^2+2*xm2*xm21^2-3*xm2m1*x2-3*xm2*xm12+3*xm21*x12-3*xm1*xcom+2*x1*xm1^2,
    -xm2^2*xm21-x2^2*x12+x1*xm2^3+x1*x2^3-x12^2*xm12-xm21^2*xm2m1+x1*xm2*xm21*xm2m1+x1*x2*xm2*xcom+x1*x2*x12*xm12+x2*xm2*xm12*xm2m1-3*xm1^2+x2^2*xm2*xm21+x1*xm2*x2-x2*xm21*xcom+x1*xm12*xm21-x1^2*xm2*xm12+x1*x12*xm2m1-x1^2*x2*xm2m1-x1*x2^2*xm2^2+x2*xm2^2*x12-xm2*x12*xcom-2*xm1*x2*xm2m1-2*xm1*xm2*xm12-2*xm1*x12*xm21-2*xm1*x2^2*xm12+3*xm1^2*x2*xm2-2*xm1*xm2^2*xm2m1+2*x1^2*xm1-3*x2*xm21-3*xm2*x12+3*xm12*xm2m1-3*x1*xcom+2*xm2*xm2m1^2+2*x2*xm12^2,
    x1^3*xm2-xm1^2*xm2m1-x1^2*xm21-x12*xm21^2+xm1^3*xm2-xm12*xm2m1^2+x1*xm2*x12*xm21+x1*xm1*xm2*xcom+x1*xm1*x12*xm12+xm1*xm2*xm12*xm2m1-3*x2^2-x1*xm2m1*xcom+x1*xm1^2*xm21+x1^2*xm1*xm2m1+xm1*xm2*x1-xm1*xm21*xcom-x1^2*xm1^2*xm2+xm2*xm12*xm21-xm1*xm2^2*x12-x1*xm2^2*xm12+xm2*x12*xm2m1-2*x2*xm21*xm2m1-2*x12*xm1*x2+3*x1*x2^2*xm1-2*x2*x1*xm12-2*x1^2*x2*x12-2*xm1^2*x2*xm12+2*xm1*xm12^2+2*x1*x12^2+2*x2*xm2^2-3*xm21*xm1-3*xm2*xcom+3*x12*xm12-3*x1*xm2m1,
    x1^3*x2-xm1^2*xm12+xm1^3*x2-x12*x1^2-x12^2*xm21-xm12^2*xm2m1+xm1*x2*xm12*xm2m1+x1*x2*x12*xm21+x1*xm1*x2*xcom+x1*xm1*xm21*xm2m1-3*xm2^2-x1*xm12*xcom+x2*xm12*xm21+x2*x12*xm2m1-x1^2*xm1^2*x2+x1*xm1^2*x12+x1^2*xm1*xm12+x1*x2*xm1-xm1*x12*xcom-xm1*x2^2*xm21-x1*x2^2*xm2m1-2*x1*xm2*xm2m1-2*x1^2*xm2*xm21-2*xm1^2*xm2*xm2m1-2*xm2*x12*xm12+3*x1*xm1*xm2^2-2*xm1*xm2*xm21+2*xm1*xm2m1^2+2*x1*xm21^2+2*x2^2*xm2-3*x12*xm1-3*x1*xm12-3*x2*xcom+3*xm2m1*xm21,
    -18+9*x1*xm1+6*x2*xm2+6*x12*xm2m1+6*xm12*xm21+x1*xm1*xm2*xm21*xm2m1+x1^2*xm1^2-3*xcom-2*x1^3-2*xm1^3-xm2^3-xm21^3-xm2m1^3-3*x1*xm2*xm12-3*xm1*xm2*x12-3*xm1*x2*xm21-3*x1*x2*xm2m1-xm1^2*xm2*xm12-x1^2*xm2*x12-x1*xm21*xm2m1^2-x1^2*xm12*xm2m1-xm1*xm21^2*xm2m1-xm1^2*xm2^2*xm2m1-x1^2*x2*xm21-xm1*xm2^2*xm21-xm1^2*x12*xm21-xm1^2*x2*xm2m1-x1*xm2^2*xm2m1+xm1^3*x2*xm2+x1*xm1*xm2^3-x1^2*xm2^2*xm21+x1^3*x2*xm2+2*xm1*xm2*xm2m1^2+3*x1*x12*xm21+3*xm1*xm12*xm2m1+3*xm2*xm21*xm2m1+2*x1*xm2*xm21^2-xcom*x1*xm1,
    -18+6*x1*xm1+9*x2*xm2+6*x12*xm2m1+6*xm12*xm21+xm1*x2*xm2*xm12*xm2m1+x2^2*xm2^2-3*xcom-2*x2^3-xm1^3-2*xm2^3-xm12^3-xm2m1^3-3*x1*xm2*xm12-3*xm1*xm2*x12-3*xm1*x2*xm21-3*x1*x2*xm2m1-x1*x2^2*xm12-xm1^2*xm2*xm12-xm2^2*x12*xm12-xm1*x2^2*x12-xm2*xm12^2*xm2m1-x2^2*xm21*xm2m1-x2*xm12*xm2m1^2-xm1^2*xm2^2*xm2m1-xm1*xm2^2*xm21-xm1^2*x2*xm2m1-x1*xm2^2*xm2m1+xm1^3*x2*xm2+x1*xm1*xm2^3-xm1^2*x2^2*xm12+x1*xm1*x2^3+3*x2*x12*xm12+2*xm1*xm2*xm2m1^2+3*xm1*xm12*xm2m1+3*xm2*xm21*xm2m1+2*xm1*x2*xm12^2-xm2*xcom*x2,
    -18+6*x1*xm1+9*x2*xm2+6*x12*xm2m1+6*xm12*xm21+x1*x2*xm2*x12*xm21+x2^2*xm2^2-3*xcom-2*x2^3-x1^3-x12^3-2*xm2^3-xm21^3-3*x1*xm2*xm12-3*xm1*xm2*x12-3*xm1*x2*xm21-3*x1*x2*xm2m1-x1*x2^2*xm12-xm2^2*x12*xm12-xm1*x2^2*x12-x1^2*xm2*x12-x2^2*xm21*xm2m1-x1^2*x2*xm21-xm1*xm2^2*xm21-xm2*x12^2*xm21-x2*x12*xm21^2-x1*xm2^2*xm2m1+x1*xm1*xm2^3-x1^2*x2^2*x12-x1^2*xm2^2*xm21+x1^3*x2*xm2+x1*xm1*x2^3+2*x1*x2*x12^2+3*x2*x12*xm12+3*x1*x12*xm21+3*xm2*xm21*xm2m1+2*x1*xm2*xm21^2-xm2*xcom*x2,
    -18+9*x1*xm1+6*x2*xm2+6*x12*xm2m1+6*xm12*xm21+x1*xm1*x2*x12*xm12+x1^2*xm1^2-3*xcom-x2^3-2*x1^3-2*xm1^3-x12^3-xm12^3-3*x1*xm2*xm12-3*xm1*xm2*x12-3*xm1*x2*xm21-3*x1*x2*xm2m1-x1*x2^2*xm12-xm1^2*xm2*xm12-xm1*x12^2*xm12-xm1*x2^2*x12-x1^2*xm2*x12-x1^2*xm12*xm2m1-x1*x12*xm12^2-x1^2*x2*xm21-xm1^2*x12*xm21-xm1^2*x2*xm2m1+xm1^3*x2*xm2-x1^2*x2^2*x12-xm1^2*x2^2*xm12+x1^3*x2*xm2+x1*xm1*x2^3+2*x1*x2*x12^2+3*x2*x12*xm12+3*x1*x12*xm21+3*xm1*xm12*xm2m1+2*xm1*x2*xm12^2-xcom*x1*xm1,
    30-13*x1*xm1-13*x2*xm2-13*x12*xm2m1-7*xm12*xm21+x2*xm2*x12*xm2m1-x1*x2^2*xm2*xm2m1-x1^2*xm1*x2*xm2m1+x1*xm1*x12*xm2m1+8*xcom+xcom^2+2*x2^3+2*x1^3+xm1^3+x12^3+xm2^3+2*xm2m1^3-xm2m1*xcom*x12+4*x1*xm2*xm12+4*xm1*xm2*x12+4*xm1*x2*xm21+7*x1*x2*xm2m1+x1*x2^2*xm12+xm1*x2^2*x12+x1^2*xm2*x12+x1*xm21*xm2m1^2+x1^2*xm12*xm2m1+x2^2*xm21*xm2m1+x2*xm12*xm2m1^2+x1^2*x2*xm21+xm1^2*x2*xm2m1+x1*xm2^2*xm2m1+x1^2*x2^2*x12-x1^3*x2*xm2-x1*xm1*x2^3-2*x1*x2*x12^2-3*x2*x12*xm12-2*xm1*xm2*xm2m1^2-3*x1*x12*xm21-3*xm1*xm12*xm2m1-3*xm2*xm21*xm2m1-xcom*x1*xm1-xm2*xcom*x2+xm2m1*xcom*x1*x2,
    30-13*x1*xm1-13*x2*xm2-7*x12*xm2m1-13*xm12*xm21-x1*xm1^2*x2*xm21-xm1*x2^2*xm2*xm21+x2*xm2*xm12*xm21+x1*xm1*xm12*xm21+8*xcom+xcom^2+2*x2^3+x1^3+2*xm1^3+xm2^3+xm12^3+2*xm21^3-xm21*xcom*xm12+4*x1*xm2*xm12+4*xm1*xm2*x12+7*xm1*x2*xm21+4*x1*x2*xm2m1+x1*x2^2*xm12+xm1^2*xm2*xm12+xm1*x2^2*x12+x2^2*xm21*xm2m1+xm1*xm21^2*xm2m1+x1^2*x2*xm21+xm1*xm2^2*xm21+xm1^2*x12*xm21+x2*x12*xm21^2+xm1^2*x2*xm2m1-xm1^3*x2*xm2+xm1^2*x2^2*xm12-x1*xm1*x2^3-3*x2*x12*xm12-3*x1*x12*xm21-3*xm1*xm12*xm2m1-3*xm2*xm21*xm2m1-2*xm1*x2*xm12^2-2*x1*xm2*xm21^2-xcom*x1*xm1-xm2*xcom*x2+xm21*xcom*x2*xm1,
    30-13*x1*xm1-13*x2*xm2-7*x12*xm2m1-13*xm12*xm21+x2*xm2*xm12*xm21-x1*x2*xm2^2*xm12-x1^2*xm1*xm2*xm12+x1*xm1*xm12*xm21+8*xcom+xcom^2+x2^3+2*x1^3+xm1^3+2*xm2^3+2*xm12^3+xm21^3-xm21*xcom*xm12+7*x1*xm2*xm12+4*xm1*xm2*x12+4*xm1*x2*xm21+4*x1*x2*xm2m1+x1*x2^2*xm12+xm1^2*xm2*xm12+xm2^2*x12*xm12+x1^2*xm2*x12+x1^2*xm12*xm2m1+xm2*xm12^2*xm2m1+x1*x12*xm12^2+x1^2*x2*xm21+xm1*xm2^2*xm21+x1*xm2^2*xm2m1-x1*xm1*xm2^3+x1^2*xm2^2*xm21-x1^3*x2*xm2-3*x2*x12*xm12-3*x1*x12*xm21-3*xm1*xm12*xm2m1-3*xm2*xm21*xm2m1-2*xm1*x2*xm12^2-2*x1*xm2*xm21^2-xcom*x1*xm1-xm2*xcom*x2+xm2*xm12*xcom*x1,
    30-13*x1*xm1-13*x2*xm2-13*x12*xm2m1-7*xm12*xm21+x2*xm2*x12*xm2m1-xm1*x2*xm2^2*x12-x1*xm1^2*xm2*x12+x1*xm1*x12*xm2m1+8*xcom+xcom^2+x2^3+x1^3+2*xm1^3+2*x12^3+2*xm2^3+xm2m1^3-xm2m1*xcom*x12+4*x1*xm2*xm12+7*xm1*xm2*x12+4*xm1*x2*xm21+4*x1*x2*xm2m1+xm1^2*xm2*xm12+xm2^2*x12*xm12+xm1*x12^2*xm12+xm1*x2^2*x12+x1^2*xm2*x12+xm1^2*xm2^2*xm2m1+xm1*xm2^2*xm21+xm1^2*x12*xm21+xm2*x12^2*xm21+xm1^2*x2*xm2m1+x1*xm2^2*xm2m1-xm1^3*x2*xm2-x1*xm1*xm2^3-2*x1*x2*x12^2-3*x2*x12*xm12-2*xm1*xm2*xm2m1^2-3*x1*x12*xm21-3*xm1*xm12*xm2m1-3*xm2*xm21*xm2m1-xcom*x1*xm1-xm2*xcom*x2+xm2*x12*xcom*xm1,
    3*x1^3*xm2+xm1^2*xm2m1+x1^2*xm21-5*x12*xm21^2+3*xm1^3*xm2-5*xm12*xm2m1^2-x1^2*xm12^2-x1^3*x2^2-x1*xm1*x2*xm21*xm2m1-xm1^2*x12^2-xm1^3*x2^2+2*x2^3*xm2-x2^2*xcom+xm2*xcom^2+xm21^2*xm2m1^2+x1*xm2*x12*xm21-x1*xm1*x12*xm12+xm1*xm2*xm12*xm2m1+5*xm1*x2*xm2*xm21+x1^2*xm1*x2*xm12+5*x1*x2*xm2*xm2m1+x1*xm1^2*x2*x12+27*xm2-12*x2^2-x2*x12^2*xm21-x1*x2^3*xm2m1-x2*xm12^2*xm2m1-xm1*x2^3*xm21+xm2^4+xm1*x2^2*xm12*xm2m1+x1*x2^2*x12*xm21+x2*xm21*xm2m1*xcom-2*x1*xm2m1*xcom+x1*xm1^2*xm21+x1^2*xm1*xm2m1-13*xm1*xm2*x1-2*xm1*xm21*xcom-x1^2*xm1^2*xm2-4*xm2*xm12*xm21-4*xm2*x12*xm2m1-4*x2*xm21*xm2m1-4*x12*xm1*x2+9*x1*x2^2*xm1-4*x2*x1*xm12-3*x1^2*x2*x12-3*xm1^2*x2*xm12-2*x2*xm2*x12*xm12-2*xm2^2*xm21*xm2m1+x12*xm12*xcom+x2^2*xm12*xm21+x2^2*x12*xm2m1-x2*xm2^2*xcom+4*xm1*xm12^2+4*x1*x12^2-5*x2*xm2^2-6*xm21*xm1+12*x12*xm12-6*x1*xm2m1,
    x2^2*xm12+xm2^2*xm2m1-5*x12*xm12^2+3*xm1*x2^3-5*xm21*xm2m1^2+3*xm1*xm2^3-x2^2*xm21^2-x1^2*x2^3-x1*x2*xm2*xm12*xm2m1-xm2^2*x12^2-x1^2*xm2^3+2*x1^3*xm1-x1^2*xcom+xm1*xcom^2+xm12^2*xm2m1^2+xm1*x2*x12*xm12+xm1*xm2*xm21*xm2m1-x2*xm2*x12*xm21+5*x1*xm1*xm2*xm12+x1*x2^2*xm2*xm21+x1*x2*xm2^2*x12+5*x1*xm1*x2*xm2m1+27*xm1-12*x1^2-x1*x12^2*xm12-x1*xm21^2*xm2m1-x1^3*x2*xm2m1-x1^3*xm2*xm12+x1*xm12*xm2m1*xcom+x1^2*x2*x12*xm12+x1^2*xm2*xm21*xm2m1+x2^2*xm2*xm2m1+x2*xm2^2*xm12-4*xm1*xm12*xm21-4*xm1*x12*xm2m1-13*xm1*x2*xm2-xm1*x2^2*xm2^2-2*xm2*xm12*xcom-2*x2*xm2m1*xcom-4*x1*xm2*x12+9*x1^2*xm2*x2-4*x1*xm12*xm2m1-4*xm21*x1*x2-3*x1*xm2^2*xm21-3*x1*x2^2*x12-2*x1*xm1*x12*xm21-2*xm1^2*xm12*xm2m1-x1*xm1^2*xcom+x12*xm21*xcom+x1^2*xm12*xm21+x1^2*x12*xm2m1+xm1^4+4*x2*x12^2+4*xm2*xm21^2-6*xm2m1*x2-6*xm2*xm12+12*xm21*x12-5*x1*xm1^2,
    xm2^2*xm21+x2^2*x12+3*x1*xm2^3+3*x1*x2^3-5*x12^2*xm12-5*xm21^2*xm2m1-xm1*x2*xm2*x12*xm21-x2^2*xm2m1^2-xm1^2*x2^3-xm1^2*xm2^3-xm2^2*xm12^2-xm1^2*xcom+2*x1*xm1^3+x1*xcom^2+x12^2*xm21^2+x1*xm2*xm21*xm2m1+x1*x2*x12*xm12-x2*xm2*xm12*xm2m1+xm1*x2^2*xm2*xm2m1+5*x1*xm1*xm2*x12+27*x1-12*xm1^2-xm1*xm21*xm2m1^2-xm1^3*x2*xm21-xm1*x12*xm12^2-xm1^3*xm2*x12+xm1*x12*xm21*xcom+x2^2*xm2*xm21-13*x1*xm2*x2-2*x2*xm21*xcom-4*x1*xm12*xm21-4*x1*x12*xm2m1-x1*x2^2*xm2^2+x2*xm2^2*x12-2*xm2*x12*xcom+5*x1*xm1*x2*xm21+xm1*x2*xm2^2*xm12-4*xm1*x2*xm2m1-4*xm1*xm2*xm12-4*xm1*x12*xm21-3*xm1*x2^2*xm12+9*xm1^2*x2*xm2-3*xm1*xm2^2*xm2m1-2*x1*xm1*xm12*xm2m1-2*x1^2*x12*xm21+xm1^2*x2*x12*xm12+xm1^2*xm2*xm21*xm2m1-x1^2*xm1*xcom+xm12*xm2m1*xcom+xm1^2*xm12*xm21+xm1^2*x12*xm2m1+x1^4-5*x1^2*xm1-6*x2*xm21-6*xm2*x12+12*xm12*xm2m1+4*xm2*xm2m1^2+4*x2*xm12^2,
    3*x1^3*x2+xm1^2*xm12+3*xm1^3*x2+x12*x1^2-5*x12^2*xm21-5*xm12^2*xm2m1+x1*xm2^2*x12*xm21+xm1*xm2^2*xm12*xm2m1-x1^2*xm2m1^2-x1^3*xm2^2-xm1^3*xm2^2-xm1^2*xm21^2+2*x2*xm2^3-xm2^2*xcom+x2*xcom^2+x12^2*xm12^2+xm1*x2*xm12*xm2m1+x1*x2*x12*xm21-x1*xm1*xm21*xm2m1+27*x2-12*xm2^2-xm2*x12*xm21^2-xm2*xm12*xm2m1^2-x1*xm2^3*xm12-xm1*xm2^3*x12+x2^4-2*x1*xm12*xcom-4*x2*xm12*xm21-4*x2*x12*xm2m1-x1^2*xm1^2*x2+x1*xm1^2*x12+x1^2*xm1*xm12-13*x1*x2*xm1-2*xm1*x12*xcom+x1^2*xm1*xm2*xm2m1+5*xm1*x2*xm2*x12+x1*xm1^2*xm2*xm21+5*x1*x2*xm2*xm12-4*x1*xm2*xm2m1-3*x1^2*xm2*xm21-3*xm1^2*xm2*xm2m1-4*xm2*x12*xm12+9*x1*xm1*xm2^2-4*xm1*xm2*xm21-2*x2*xm2*xm21*xm2m1-2*x2^2*x12*xm12-x1*xm1*xm2*x12*xm12-x2^2*xm2*xcom+xm21*xm2m1*xcom+xm2^2*xm12*xm21+xm2^2*x12*xm2m1+xm2*x12*xm12*xcom+4*xm1*xm2m1^2+4*x1*xm21^2-5*x2^2*xm2-6*x12*xm1-6*x1*xm12+12*xm2m1*xm21
>;


/* an absolutely irreducible representation F_2 \to SL(3,K) is uniquely determined
 * by nine traces. However, the nine traces are not algebraically independent,
 * they have to satisfy the relation commutatorrel.
 */
commutatorrel := xcom^2 - (-3+x1*xm1+x12*xm2m1-xm1*xm2*x12+x2*xm2+xm12*xm21+x1*xm1*x2*xm2-x1*xm2*xm12-xm1*x2*xm21-x1*x2*xm2m1)*xcom + 9-6*x1*xm1-6*x2*xm2+x2^3+x1^3+xm1^3+x12^3+xm2^3+xm12^3+xm21^3+xm2m1^3-6*x12*xm2m1-2*x1*x2*x12^2+x1*x2^2*xm12+xm1^2*xm2*xm12+xm2^2*x12*xm12+xm1*x12^2*xm12+x12*xm12*xm21*xm2m1+xm1*x2^2*x12+x1^2*xm2*x12-x1*xm1^2*x2*xm21-xm1*x2^2*xm2*xm21+x1*xm21*xm2m1^2+3*xm1*xm2*x12+3*x1*xm2*xm12-3*x2*x12*xm12-6*xm12*xm21+x1^2*xm12*xm2m1+xm2*xm12^2*xm2m1+x2^2*xm21*xm2m1+xm1*xm21^2*xm2m1-2*xm1*xm2*xm2m1^2+x2*xm12*xm2m1^2+3*xm1*x2*xm21-3*x1*x12*xm21+3*x1*x2*xm2m1-3*xm1*xm12*xm2m1-3*xm2*xm21*xm2m1+x2*xm2*xm12*xm21+x2*xm2*x12*xm2m1-xm1*x2*xm2^2*x12-x1*x2*xm2*x12*xm21+x1*xm1*x2*xm2+xm1^2*xm2^2*xm2m1-2*xm1*x2*xm12^2+x1*x12*xm12^2+x1^2*x2*xm21+xm1*xm2^2*xm21+xm1^2*x12*xm21+xm2*x12^2*xm21-x1*x2^2*xm2*xm2m1-2*x1*xm2*xm21^2+x2*x12*xm21^2+xm1^2*x2*xm2m1+x1*xm2^2*xm2m1-x1*xm1*xm2*xm21*xm2m1-xm1*x2*xm2*xm12*xm2m1-x1*x2*xm2^2*xm12+x1*xm1*x2^2*xm2^2-xm1^3*x2*xm2-x1*xm1*xm2^3+x1^2*x2^2*x12+xm1^2*x2^2*xm12+x1^2*xm2^2*xm21+x1^2*xm1^2*x2*xm2-x1^3*x2*xm2-x1^2*xm1*x2*xm2m1-x1*xm1*x2^3-x1*xm1^2*xm2*x12-x1^2*xm1*xm2*xm12-x1*xm1*x2*x12*xm12+x1*xm1*xm12*xm21+x1*xm1*x12*xm2m1;

/* 
 */
xcominv := (-3+x1*xm1+x12*xm2m1-xm1*xm2*x12+x2*xm2+xm12*xm21+x1*xm1*x2*xm2-x1*xm2*xm12-xm1*x2*xm21-x1*x2*xm2m1) - xcom;



F<a,b> := FreeGroup(2);


/* a representation F \to SL(3,K) is absolutely irreducible if and only if the images of the
 * 14 words in generatingSystem generate K^{3 \times 3} as vector space
 */
generatingSystem := [ F!1, a, a^(-1), b, b^(-1), a*b, b*a, a^(-1)*b, b*a^(-1), a*b^(-1), b^(-1)*a, a^(-1)*b^(-1), b^(-1)*a^(-1), a*b*a^(-1)*b^(-1) ];

/* a representation F \to SL(3,K) is absolutely irreducible if and only if the images of 
 * one of the tuples in possibleBases is a vector space basis of K^{3 \times 3}.
 */
possibleBases := [
    [F!1, a, b, b^(-1), a*b, b*a, a*b^(-1), b^(-1)*a, a*b*a^(-1)*b^(-1)],
    [F!1, a, a^(-1), b, a*b, b*a, a^(-1)*b, b*a^(-1), a*b*a^(-1)*b^(-1)],

    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, b^-1 * a, a^-1 * b^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, a * b^-1, a^-1 * b^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, a * b^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, a * b^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b^-1, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, a * b^-1, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a^-1 * b^-1, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), a * b, a * b^-1, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a^-1 * b^-1, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, b^-1 * a, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, a * b^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, a * b^-1, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, a^-1 * b^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b^-1, a^-1 * b^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, a^-1 * b^-1, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, a * b^-1, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, a^-1 * b^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b^-1, a^-1 * b^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, a * b^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b^-1, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, a * b^-1, a^-1 * b^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, b^-1 * a, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, a * b^-1, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, a * b^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, a^-1 * b^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, a * b^-1, a^-1 * b^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, a^-1 * b^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, a * b^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, a * b^-1, a^-1 * b^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, a^-1 * b^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b^-1, a^-1 * b^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), a * b, a^-1 * b^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, a * b^-1, a^-1 * b^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, a^-1 * b^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b * a^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a^-1 * b^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, a^-1 * b^-1, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), a * b, a * b^-1, a^-1 * b^-1, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b * a^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, a * b^-1, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, a * b^-1, a^-1 * b^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, a^-1 * b^-1, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), a * b^-1, a^-1 * b^-1, b * a^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, b^-1 * a, a * b^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, a^-1 * b^-1, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b^-1, a^-1 * b^-1, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, a^-1 * b^-1, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b^-1, a^-1 * b^-1, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, a^-1 * b^-1, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, a^-1 * b^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), a * b, a * b^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, b^-1 * a, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b, a * b^-1, a^-1 * b^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, a * b^-1, a^-1 * b^-1, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, b^-1 * a, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, b^-1 * a, a * b^-1, a^-1 * b ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a^-1, a * b, a * b^-1, b * a^-1 ],
    [F!1, a, a^(-1), b, b^(-1), a * b, a^-1 * b^-1, b * a^-1, b * a ],
    [F!1, a, a^(-1), b, b^(-1), b^-1 * a, b * a^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a^-1 * b^-1, b * a^-1, a^-1 * b, b * a ],
    [F!1, a, a^(-1), b, b^(-1), a * b^-1, b * a^-1, a^-1 * b, b * a ]
];


/* test, whether the ideal I is above any of the ideals of L
 */
IsSuperset := function(I, L) 
    for J in L do
        if J subset I then
            return true;
        end if;
    end for;

    return false;
end function;

/* Input: Prime ideal P in Z[x_1, \dotsc, x_m].
 * Ouput: Generator of P \cap \Z.
 */
characteristic := function(P)
    ints := [f : f in Basis(P) | f in Integers()];

    if #ints eq 0 then
        return 0;
    else
        return Integers()!ints[1];
    end if;
end function;


/* Input: Prime ideal P in Z[x_1, \dotsc, x_m].
 * Output: Krull dimension of P \otimes K,
 *         where K = GF(p) if P contains a prime p, and K = \Q otherwise.
 */
dimensionOverField := function(P)
    p := characteristic(P);

    if p eq 0 then
        Q := ChangeRing(P, Rationals());
    else
        Q := ChangeRing(P, GF(p));
    end if;

    return Dimension(Q);
end function;


/* Input: Zero dimensional prime ideal P in Z[x_1, \dotsc,  x_m].
 * Output: Vector space dimension of the residue class algebra K[x_1, \dotsc, x_m]/P \otimes K,
 *         where K = GF(p) if P contains a prime p, and K = \Q otherwise.
 */
quotientDimensionOverField := function(P)
    p := characteristic(P);

    if p eq 0 then
        Q := ChangeRing(P, Rationals());
    else
        Q := ChangeRing(P, GF(p));
    end if;

    return QuotientDimension(Q);
end function;


L3SignAction := function(P, sigma)
    alpha := hom< R -> R | xcom, sigma[1]*x1, sigma[1]^2*xm1, sigma[2]*x2, sigma[2]^2*xm2, sigma[1]*sigma[2]*x12, sigma[1]^2*sigma[2]*xm12, sigma[1]*sigma[2]^2*xm21, sigma[1]^2*sigma[2]^2*xm2m1, zeta >;

    return ideal< R | [alpha(f) : f in Basis(P)]>;
end function;

L3InverseTransposeAction := function(P)
    alpha := hom< R -> R | xcominv, xm1, x1, xm2, x2, xm2m1, xm21, xm12, x12, zeta >;

    return ideal< R | [alpha(f) : f in Basis(P)]>;
end function;

L3ZetaAction := function(P)
    alpha := hom< R -> R | xcom, x1, xm1, x2, xm2, x12, xm12, xm21, xm2m1, - zeta - 1 >;

    return ideal< R | [alpha(f) : f in Basis(P)]>;
end function;

L3GetCharacteristic := function(P)
    Groebner(P);
    
    integers := [f : f in Basis(P) | f in Integers()];

    if #integers eq 0 then
        return 0;
    else
        return Integers()!integers[1];
    end if;
end function;

L3GetDimension := function(P)
    char := L3GetCharacteristic(P);

    if char eq 0 then
        return Dimension(ChangeRing(P, Rationals()));
    else
        return Dimension(ChangeRing(P, GF(char)));
    end if;
end function;

L3EliminateZeta := function(P)
    Q := EliminationIdeal(P, { R.i : i in [1..9] } );

    alpha := hom<R -> RR | RR.1, RR.2, RR.3, RR.4, RR.5, RR.6, RR.7, RR.8, RR.9, 0 >;

    return ideal< RR | [alpha(f) : f in Basis(Q)]>;
end function;


/* return the residue class dimension of the ideal, where zeta
 * is removed.
 *
 * If the ideal is not maximal, return -1.
 */
L3ResidueClassFieldDimension := function(P)
    p := L3GetCharacteristic(P);

    if p eq 0 then
        return -1;
    end if;

    if L3GetDimension(P) gt 0 then
        return -1;
    end if;

    Q := ChangeRing(L3EliminateZeta(P), GF(p));

    return Dimension(Generic(Q)/Q);
end function;



/* Check, whether the word is of the form X*Y*X*Z (possibly after rotation).
 *
 * Returns (true, X, Y, Z) or (false, _, _, _).
 */
HasDouble := function(word)
    n := #word;
    k := Floor(n/2);

    while k gt 0 do
        for i in [1..n] do
            cand := word[[1..k]];
            for j in [k+1..n-k+1] do
                if word[[j..j+k-1]] eq cand then
                    return true, cand, word[[k+1..j-1]], word[[j+k..n]];
                end if;
            end for;

            word := word[[2..n]] cat [word[1]];
        end for;

        k -:= 1;
    end while;

    return false, _, _, _;
end function;



/* Find the biggest e such that word = X^e*Y.
 * Returns (X, e, Y).
 */
FindHighestPower := function(word)
    n := #word;

    base := [];
    exp := 1;
    remainder := word;
    max := 0;

    doubleword := word cat word;

    for k in [1..Floor(n/2)] do
        for i in [1..n] do
            e := 1;
            while k*e lt n do
                ispower := true;
                for j in [0..k-1] do
                    if doubleword[i+j] ne doubleword[i+k*e+j] then
                        ispower := false;
                        break;
                    end if;
                end for;

                if ispower then
                    e +:= 1;
                else
                    break;
                end if;
            end while;

            total := k*e;

            if e gt 1 and total gt max then
                max := total;

                exp := e;
                base := doubleword[[i..i+k-1]];
                remainder := doubleword[[i+total..i+n-1]];

                if max gt n/4 then
                    // this is good enough
                    return base, exp, remainder;
                end if;
            end if;

        end for;
    end for;

    return base, exp, remainder;
end function;




/* Tr(x^n*y) = c_n(x)*Tr(x*y) + c_{n-1}(x)*Tr(x^(-1)*y) + d_n(x)*Tr(y),
 * where c_n(x) and d_n(x) are polynomials in the trace polynomial of x.
 *
 * This function calculates c_n(x).
 */
PowerWordHelper1 := function(powersx, powersxinv, n : I := ideal< R | > )
    if n lt 1 then
        return R!0;
    end if;

    return &+[
                &+[R | (-1)^(i+j)*Binomial(i,j)*Binomial(n-i-j-1,i)*powersxinv[i-j+1]*powersx[n-2*i-j] 
                    : i in [j..Floor((n-j-1)/2)]
                  ] 
              : j in [0..Floor((n-1)/2)]
        ];
end function;


/* Tr(x^n*y) = c_n(x)*Tr(x*y) + c_{n-1}(x)*Tr(x^(-1)*y) + d_n(x)*Tr(y),
 * where c_n(x) and d_n(x) are polynomials in the trace polynomial of x.
 *
 * This function calculates d_n(x).
 */
PowerWordHelper2 := function(powersx, powersxinv, n : I := ideal< R | > )
    if n lt 2 then
        return R!0;
    end if;

    return &+[
                &+[R | (-1)^(i+j+1)*Binomial(i+1,j)*Binomial(n-i-j-2,i)*powersxinv[i-j+2]*powersx[n-2*i-j-1] 
                    : i in [Max(0, j-1)..Floor((n-j-2)/2)]
                  ] 
              : j in [0..Floor((n-1)/2)]
        ];
end function;


/* Compute the trace polynomial of a word, given as a list.
 * Reduce the polynomial modulo I.
 */
L3TracePolynomialList := function(word, F : I := ideal< R | >)
    F<a, b> := F;

    while #word gt 0 and word[1] + word[#word] eq 0 do
        word := word[[2..#word - 1]];
    end while;

    if #word eq 0 then
        return R!3;
    end if;

    if #word eq 1 then
        if word[1] eq 1 then    
            return x1;
        elif word[1] eq -1 then
            return xm1;
        elif word[1] eq 2 then  
            return x2;
        else
            return xm2;
        end if;
    end if;

    if #word eq 2 then
        if word[1] + word[2] eq 3 then
            // a*b
            return x12;
        elif word[1] + word[2] eq 1 then 
            return xm12;
        elif word[1] + word[2] eq -1 then
            return xm21;
        elif word[1] + word[2] eq -3 then
            return xm2m1;
        end if;
    end if;

    if #word eq 4 and word[1] + word[2] + word[3] + word[4] eq 0 then
        // word is a commutator
        if word[1]*word[2] gt 0 then
            if Abs(word[2]) gt Abs(word[1]) then
                return xcom;
            else
                return x1*xm1+x2*xm2+x12*xm2m1+xm12*xm21-x1*x2*xm2m1-x1*xm2*xm12-xm1*x2*xm21-xm1*xm2*x12+x1*xm1*x2*xm2-3-xcom;
            end if;
        else
            if Abs(word[1]) gt Abs(word[2]) then
                return xcom;
            else
                return x1*xm1+x2*xm2+x12*xm2m1+xm12*xm21-x1*x2*xm2m1-x1*xm2*xm12-xm1*x2*xm21-xm1*xm2*x12+x1*xm1*x2*xm2-3-xcom;
            end if;
        end if;
    end if;

    // ensure that the word does not start and end with the same letter.
    // this simplifies the search for the highest exponent.
    // To avoid infinite loops, check first if the word is not a power
    // of a single letter.
    if (1 in word or -1 in word) and (2 in word or -2 in word) then
        while word[1] eq word[#word] do
            word := [word[#word]] cat word[[1..#word-1]];
        end while;
    end if;


    // Use the formula 
    //      Tr(x^n*y) = c_n(x)*Tr(x*y) - c_{n-1}(x)*Tr(x^-1*y) + d_n(x)*Tr(y), 
    // This is much more efficient if the word contains a letter to a high power.

    base, power, remainder := FindHighestPower(word);

    if power gt 1 then
        x := $$(base, F : I := I);
        xinv := $$(Eltseq((F!base)^(-1)), F : I := I);

        // Careful: powersx[1] = 1 = x^0, powersx[2] = x = x^1, etc
        powersx := [R!1];
        powersxinv := [R!1];
        for i in [1..power-1] do
            Append(~powersx, NormalForm(powersx[i]*x, I));
            Append(~powersxinv, NormalForm(powersxinv[i]*xinv, I));
        end for;

        return NormalForm(PowerWordHelper1(powersx, powersxinv, power : I := I), I)*NormalForm($$(base cat remainder, F : I := I), I) 
                + NormalForm(PowerWordHelper1(powersx, powersxinv, power-1 : I := I), I)*NormalForm($$(Eltseq((F!base)^(-1)*(F!remainder)), F : I := I), I)
                + NormalForm(PowerWordHelper2(powersx, powersxinv, power : I := I), I)*NormalForm($$(Eltseq(F!remainder), F : I := I), I);
    end if;

    hasDouble, X, Y, Z := HasDouble(word);

    if hasDouble then
        X := F!X;
        Y := F!Y;
        Z := F!Z;

        tpxinv := L3TracePolynomial(X^(-1) : I := I);
        tpy := L3TracePolynomial(Y : I := I);
        tpz := L3TracePolynomial(Z : I := I);

        return NormalForm(L3TracePolynomial(X^(-1)*Y : I := I)*tpz
            + L3TracePolynomial(X^(-1)*Z : I := I)*tpy
            + tpxinv*L3TracePolynomial(Y*Z : I := I)
            + L3TracePolynomial(X*Y : I := I)*L3TracePolynomial(X*Z : I := I)
            - tpxinv*tpy*tpz
            - L3TracePolynomial(X^(-1)*Y*Z : I := I)
            - L3TracePolynomial(X^(-1)*Z*Y : I := I), I);
    end if;


    error "illegal word", word;
end function;


intrinsic L3TracePolynomial(word::GrpFPElt : I := ideal< R | >) -> RngMPolElt
{ Compute the L3TracePolynomial of G}
    return L3TracePolynomialList(Eltseq(word), Parent(word) : I := I);
end intrinsic;


/* Let $\Delta: F_2 \to \SL(3,K)$ be absolutely irreducible and $B = \{1, a, b, \dotsc, [a,b]}$. 
 * Then $\Delta(w) = I_3$ if and only if $\tr(\Delta(w)\Delta(\beta)) = \tr(\Delta(\beta))$ for 
 * all $\beta \in B$ (since $\{\delta(\beta) \mid \beta \in B\}$ is a generating set of K^{3 \times 3}$).
 * Equivalently, $\tr(\Delta(w_1)\Delta(\beta)) = \tr(\Delta(w_2^{-1})\Delta(\beta))$, where $w = w_1w_2$,
 * or, converting to trace polynomials, $\tau(w_1\beta)(t) = \tau(w_2^{-1}\beta)(t)$,
 * where $\tau(w)$ denotes the trace polynomial of $w$ and $t$ denotes the trace tuple of $\Delta$.
 * (The word $w$ is split into $w_1w_2$ to minimize the degree of the polynomial; recall that the
 * degree of the polynomial is the length of the word.)
 *
 * During the course of the algorithm, not only $\Delta(w) = I_3$ is tested, but also $\Delta(w) = \zeta^i I_3$
 * for $i \in \{0,1,2\}$. The computation of trace polynomials is expensive (the algorithm is exponential).
 * Therefore, the algorithm uses this method to compute the pairs of polynomials
 * $(\tau(w_1\beta), \tau(w_2^{-1}\beta))$ once, so that they can be reused for different sign systems.
 */
L3ConditionsForWord := function(rel : I := ideal< R | >)
    result := [];

    F<a,b> := Parent(rel);

    seq := Eltseq(rel);
    k := Floor(#seq/2);
    left := F!seq[[1..k]];
    right := (F!seq[[k+1..#seq]])^(-1);

    for beta in [F!1, a, a^(-1), b, b^(-1), a*b, b*a, a^(-1)*b, b*a^(-1), a*b^(-1), b^(-1)*a, a^(-1)*b^(-1), b^(-1)*a^(-1), a*b*a^(-1)*b^(-1)] do
        Append(~result, <L3TracePolynomial(left*beta : I := I), L3TracePolynomial(right*beta : I := I)>);
    end for;

    return result;
end function;


/* Compute the trace presentation ideal for the group G = < a,b | w_1, \dotsc, w_k >,
 * using precomputed data. The parameter conditions is a list of lists of pairs,
 * where each list of pairs is computed using L3ConditionsForWord(w_i).
 */
L3TracePresentationIdealPrecomputed := function(conditions, signSystem)
    assert #conditions eq #signSystem;

    result := [commutatorrel, zeta^2 + zeta + 1];

    for i in [1..#conditions] do
        cond := conditions[i];

        for c in cond do
            Append(~result, c[1] - signSystem[i]*c[2]);
        end for;
    end for;

    return ideal< R | result >;
end function;


/* Compute the trace presentation ideal for the given relations and sign system.
 * This method should not be used when trace presentation ideals are computed for
 * different sign system. In that case, use L3TracePresentationIdealPrecomputed
 * instead.
 */
L3TracePresentationIdeal := function(rels, signSystem : I := ideal< R | >)
    assert #rels eq #signSystem;

    conditions := [L3ConditionsForWord(r : I := I) : r in rels];
    return L3TracePresentationIdealPrecomputed(conditions, signSystem);
end function;



GramMatrixDeterminant := function(basis, I)
    mat := Matrix(R, 9, 9, [[NormalForm(L3TracePolynomial(b*c), I) : c in basis] : b in basis]);

    return NormalForm(Determinant(mat), I);
end function;



/* Given an ideal corresponding to an absolutely irreducible trace tuple t
 * and hence an absolutely irreducible representation $\Delta\colon F_2 \to \SL(3,K)$,
 * find a tuple of nine words $(w_1, \dotsc, w_9)$ such that $(\Delta(w_1), \dotsc, \Delta(w_9))$
 * is a basis of $K^{3 \times 3}$.
 *
 * Note that $(\Delta(w_1), \dotsc, \Delta(w_9))$ is a basis if and only if
 * the matrix $(\tr(\Delta(w_i)\Delta(w_j)))_{i,j}$ has full rank, hence
 * non-zero determinant.
 */
L3FindBasis := function(I)
    for bas in possibleBases do
        if GramMatrixDeterminant(bas, I) ne 0 then
            return bas;
        end if;
    end for;

    error "not absolutely irreducible";
end function;


L3IsAbsolutelyIrreducible := function(I)
    return not rho subset I;
end function;


L3IsOrthogonal := function(I)
    F<a, b> := FreeGroup(2);

    if not (L3TracePolynomial((a,b)) - L3TracePolynomial((b,a)) in I) then
        // Necessary condition: commutator and the inverse have the same trace
        return false;
    end if;

    if (x1 - xm1 in I) and (x2 - xm2 in I) and (x12 - xm2m1 in I) and (xm12 - xm21 in I) then
        return true;
    end if;

    // It might happen that the representation takes values in SL(3, q) \times C_3,
    // so multiply generators with third roots of unity to check for that
    if (zeta*x1 - zeta^2*xm1 in I) and (x2 - xm2 in I) and (zeta*x12 - zeta^2*xm2m1 in I) and (zeta^2*xm12 - zeta*xm21 in I) then
        // a -> zeta*a, b -> b
        return true;
    end if;

    if (zeta^2*x1 - zeta*xm1 in I) and (x2 - xm2 in I) and (zeta^2*x12 - zeta*xm2m1 in I) and (zeta*xm12 - zeta^2*xm21 in I) then
        // a -> zeta^2*a, b -> b
        return true;
    end if;

    if (x1 - xm1 in I) and (zeta*x2 - zeta^2*xm2 in I) and (zeta*x12 - zeta^2*xm2m1 in I) and (zeta*xm12 - zeta^2*xm21 in I) then
        // a -> a, b -> zeta*b
        return true;
    end if;

    if (zeta*x1 - zeta^2*xm1 in I) and (zeta*x2 - zeta^2*xm2 in I) and (zeta^2*x12 - zeta*xm2m1 in I) and (xm12 - xm21 in I) then
        // a -> zeta*a, b -> zeta*b
        return true;
    end if;

    if (zeta^2*x1 - zeta*xm1 in I) and (zeta*x2 - zeta^2*xm2 in I) and (x12 - xm2m1 in I) and (zeta^2*xm12 - zeta*xm21 in I) then
        // a -> zeta^2*a, b -> zeta*b
        return true;
    end if;

    if (x1 - xm1 in I) and (zeta^2*x2 - zeta*xm2 in I) and (zeta^2*x12 - zeta*xm2m1 in I) and (zeta^2*xm12 - zeta*xm21 in I) then
        // a -> a, b -> zeta^2*b
        return true;
    end if;

    if (zeta*x1 - zeta^2*xm1 in I) and (zeta^2*x2 - zeta*xm2 in I) and (x12 - xm2m1 in I) and (zeta*xm12 - zeta^2*xm21 in I) then
        // a -> zeta*a, b -> zeta^2*b
        return true;
    end if;

    if (zeta^2*x1 - zeta*xm1 in I) and (zeta^2*x2 - zeta*xm2 in I) and (zeta*x12 - zeta^2*xm2m1 in I) and (xm12 - xm21 in I) then
        // a -> zeta^2*a, b -> zeta^2*b
        return true;
    end if;

    return false;
end function;


imprimitiveIdeals := [
    // four possibilities for an imprimitive group with factor group C_3
    ideal< R | x1, xm1, x12, xm12, xm21, xm2m1 >,
    ideal< R | x2, xm2, x12, xm12, xm21, xm2m1 >,
    ideal< R | x1, xm1, x2, xm2, x12, xm2m1 >,
    ideal< R | x1, xm1, x2, xm2, xm12, xm21 >,
    // three possibilities for an imprimitive group with factor group S_3
    ideal< R | x1*xm1 - 1, x2*xm2 - 1, x12, xm12, xm21, xm2m1, xcom >,
    ideal< R | x1*xm1 - 1, x2, xm2, x12*xm2m1 - 1, x1*x12 + xm12, xm1*xm2m1 + xm21, xcom >,
    ideal< R | x1, xm1, x2*xm2 - 1, x12*xm2m1 - 1, xm2*xm2m1 + xm12, x2*x12 + xm21, xcom >
];


L3IsImprimitive := function(I)
    for imp in imprimitiveIdeals do
        if imp subset I then
            return true;
        end if;
    end for;

    return false;
end function;


L3ImprimitiveCondition := function(I)
    result := [];

    for imp in imprimitiveIdeals do 
        ma := [P : P in MinimalAssociatedPrimes(I + imp) | L3IsAbsolutelyIrreducible(P)];
        for p in ma do
            Append(~result, p);
        end for;
    end for;

    return MinimalIdeals(result);
end function;

L3IrreducibilityCondition := function(I)
    return MinimalAssociatedPrimes(I + rho);
end function;


orthogonalIdeals := [
    // nine ideals, one for each sign system
    ideal< R | x1 - xm1, x2 - xm2, x12 - xm2m1, xm12 - xm21, xcom - xcominv >,
    ideal< R | zeta*x1 - zeta^2*xm1, x2 - xm2, zeta*x12 - zeta^2*xm2m1, zeta^2*xm12 - zeta*xm21, xcom - xcominv >,
    ideal< R | zeta^2*x1 - zeta*xm1, x2 - xm2, zeta^2*x12 - zeta*xm2m1, zeta*xm12 - zeta^2*xm21, xcom - xcominv >,
    ideal< R | x1 - xm1, zeta*x2 - zeta^2*xm2, zeta*x12 - zeta^2*xm2m1, zeta*xm12 - zeta^2*xm21, xcom - xcominv >,
    ideal< R | x1 - xm1, zeta^2*x2 - zeta*xm2, zeta^2*x12 - zeta*xm2m1, zeta^2*xm12 - zeta*xm21, xcom - xcominv >,
    ideal< R | zeta*x1 - zeta^2*xm1, zeta*x2 - zeta^2*xm2, zeta^2*x12 - zeta*xm2m1, xm12 - xm21, xcom - xcominv >,
    ideal< R | zeta*x1 - zeta^2*xm1, zeta^2*x2 - zeta*xm2, x12 - xm2m1, zeta*xm12 - zeta^2*xm21, xcom - xcominv >,
    ideal< R | zeta^2*x1 - zeta*xm1, zeta*x2 - zeta^2*xm2, x12 - xm2m1, zeta^2*xm12 - zeta*xm21, xcom - xcominv >,
    ideal< R | zeta^2*x1 - zeta*xm1, zeta^2*x2 - zeta*xm2, zeta*x12 - zeta^2*xm2m1, xm12 - xm21, xcom - xcominv >
];


L3OrthogonalCondition := function(I)
    result := [];

    for orth in orthogonalIdeals do 
        ma := [P : P in MinimalAssociatedPrimes(I + orth) | L3IsAbsolutelyIrreducible(P)];
        for p in ma do
            Append(~result, p);
        end for;
    end for;

    return MinimalIdeals(result);
end function;


L3ContainsConjugate := function(list, P, Sigma)
    for sigma in Sigma do
        Psigma := L3SignAction(P, sigma);
        for Q in list do
            if Q subset Psigma then
                return true;
            end if;
        end for;

        Psigmait := L3InverseTransposeAction(Psigma);
        for Q in list do
            if Q subset Psigmait then
                return true;
            end if;
        end for;

        Psigmazeta := L3ZetaAction(Psigma);
        for Q in list do
            if Q subset Psigmazeta then
                return true;
            end if;
        end for;

        Psigmaitzeta := L3ZetaAction(Psigmait);
        for Q in list do
            if Q subset Psigmaitzeta then
                return true;
            end if;
        end for;
    end for;

    return false;
end function;




L3SatisfiesRelation := function(I, rel)
    F<a,b> := Parent(rel);

    // check, whether [rel,a] and [rel,b] are in the center of the group algebra
    for x in [a,b] do
        for y in [ F!1, a, a^(-1), b, b^(-1), a*b, b*a, a^(-1)*b, b*a^(-1), a*b^(-1), b^(-1)*a, a^(-1)*b^(-1), b^(-1)*a^(-1), a*b*a^(-1)*b^(-1) ] do
            if not L3TracePolynomial(rel*x*y : I := I) - L3TracePolynomial(x*rel*y : I := I) in I then
                return false;
            end if;
        end for;
    end for;

    return true;
end function;


/* check whether the representation defined by I satisfies the relations of fpgroup.
 * permgroup should be a permutation group which has fpgroup as a presentation.
 *
 * if pres is given, then first check whether pres has permgroup as a quotient.
 * if this is not the case, return false; otherwise, check whether the presentation
 * in fpgroup is satisfied.
 */
L3SatisfiesPresentation := function(I, fpgroup : pres := FreeGroup(2), permgroup := PermutationGroup< 1 | (1), (1) >, presideal := ideal< R | > )
    if not L3IsAbsolutelyIrreducible(I) then
        error "representation is not absolutely irreducible.";
    end if;

    if not IsSatisfied(Relations(pres), [permgroup.1, permgroup.2]) then
        return false;
    end if;

    // if there is a precomputed ideal, use this instead of  constructing the trace polynomials anew
    // TODO: should this be done before or after testing whether the group is an image?
    if presideal ne ideal< R | > then
        return L3ContainsConjugate([presideal], I, [[R!1, R!1], [R!1, R!zeta], [R!1, zeta^2], [zeta, R!1], [zeta, zeta], [zeta, zeta^2], [zeta^2, R!1], [zeta^2, zeta], [zeta^2, zeta^2]]);
    end if;

    rels := Relations(fpgroup);

    for i in [1..#rels] do
        rel := LHS(rels[i])*RHS(rels[i])^(-1);

        if not L3SatisfiesRelation(I, rel) then
            return false;
        end if;
    end for;

    return true;
end function;


L3GroupPresentationIdeal := function(grp)
    rels := Relations(grp);

    F<a,b> := grp;

    gens := [];

    // check, whether [rel,a] and [rel,b] are in the center of the group algebra
    for x in [a,b] do
        for r in rels do
            rel := LHS(r)*RHS(r)^(-1);
            for y in [ F!1, a, a^(-1), b, b^(-1), a*b, b*a, a^(-1)*b, b*a^(-1), a*b^(-1), b^(-1)*a, a^(-1)*b^(-1), b^(-1)*a^(-1), a*b*a^(-1)*b^(-1) ] do
                Append(~gens, L3TracePolynomial(rel*x*y) - L3TracePolynomial(x*rel*y));
            end for;
        end for;
    end for;

    return ideal< R | gens >;
end function;



L3PresentationCondition := function(I, presentations : pres := FreeGroup(2))
    result := [];

    // presentations is a list of triples (G, H, P), where G is the permutation group, H its presentation, and P the ideal
    for pp in presentations do
        G := pp[1];
        P := pp[3];

        if IsSatisfied(Relations(pres), [G.1, G.2]) then
            for sigma in [[R!1, R!1], [R!1, R!zeta], [R!1, zeta^2], [zeta, R!1], [zeta, zeta], [zeta, zeta^2], [zeta^2, R!1], [zeta^2, zeta], [zeta^2, zeta^2]] do
                Psigma := L3SignAction(P, sigma);
                for PP in [Psigma, L3InverseTransposeAction(Psigma), L3ZetaAction(Psigma), L3InverseTransposeAction(L3ZetaAction(Psigma))] do
                    ma := [Q : Q in MinimalAssociatedPrimes(I + PP) | L3IsAbsolutelyIrreducible(Q)];
                    for p in ma do
                        Append(~result, p);
                    end for;
                end for;
            end for;
        end if;
    end for;

    return MinimalIdeals(result);
end function;



L3IsA6 := function(I : pres := FreeGroup(2))
    dim := L3GetDimension(I);
    if dim gt 0 then
        return false;
    end if;

    for X in a6presentations do
        permgroup := X[1];
        fpgroup := X[2];
        if L3SatisfiesPresentation(I, fpgroup : pres := pres, permgroup := permgroup, presideal := X[3]) then
            return true;
        end if;
    end for;

    return false;
end function;

L3IsL27 := function(I : pres := FreeGroup(2))
    dim := L3GetDimension(I);
    if dim gt 0 then
        return false;
    end if;

    for X in l27presentations do
        permgroup := X[1];
        fpgroup := X[2];
        if L3SatisfiesPresentation(I, fpgroup : pres := pres, permgroup := permgroup, presideal := X[3]) then
            return true;
        end if;
    end for;

    return false;
end function;

L3IsPGU32 := function(I : pres := FreeGroup(2))
    dim := L3GetDimension(I);
    if dim gt 0 then
        return false;
    end if;

    for X in pgu32presentations do
        permgroup := X[1];
        fpgroup := X[2];
        if L3SatisfiesPresentation(I, fpgroup : pres := pres, permgroup := permgroup, presideal := X[3]) then
            return true;
        end if;
    end for;

    return false;
end function;

L3IsPSU32 := function(I : pres := FreeGroup(2))
    dim := L3GetDimension(I);
    if dim gt 0 then
        return false;
    end if;

    for X in psu32presentations do
        permgroup := X[1];
        fpgroup := X[2];
        if L3SatisfiesPresentation(I, fpgroup : pres := pres, permgroup := permgroup, presideal := X[3]) then
            return true;
        end if;
    end for;

    return false;
end function;

L3IsH36 := function(I : pres := FreeGroup(2))
    dim := L3GetDimension(I);
    if dim gt 0 then
        return false;
    end if;

    for X in h36presentations do
        permgroup := X[1];
        fpgroup := X[2];
        if L3SatisfiesPresentation(I, fpgroup : pres := pres, permgroup := permgroup, presideal := X[3]) then
            return true;
        end if;
    end for;

    return false;
end function;

L3IsA7 := function(P : pres := FreeGroup(2))
    // A7 only occurs as a subgroup of L_3(5^2), so do this cheap check first.
    p := L3GetCharacteristic(P);

    if p ne 5 then
        return false;
    end if;

    dim := L3ResidueClassFieldDimension(P);

    if dim ne 2 then
        return false;
    end if;
    
    for X in a7presentations do
        permgroup := X[1];
        fpgroup := X[2];
        if L3SatisfiesPresentation(P, fpgroup : pres := pres, permgroup := permgroup, presideal := X[3]) then
            return true;
        end if;
    end for;

    return false;
end function;

L3IsM10 := function(P : pres := FreeGroup(2))
    // M10 only occurs as a subgroup of L_3(5^2), so do this cheap check first.
    p := L3GetCharacteristic(P);

    if p ne 5 then
        return false;
    end if;

    dim := L3ResidueClassFieldDimension(P);
    
    if dim ne 2 then
        return false;
    end if;
    
    for X in m10presentations do
        permgroup := X[1];
        fpgroup := X[2];
        if L3SatisfiesPresentation(P, fpgroup : pres := pres, permgroup := permgroup, presideal := X[3]) then
            return true;
        end if;
    end for;

    return false;
end function;


L3A6Condition := function(I : pres := FreeGroup(2))
    return L3PresentationCondition(I, a6presentations : pres := pres);
end function;

L3L27Condition := function(I : pres := FreeGroup(2))
    return L3PresentationCondition(I, l27presentations : pres := pres);
end function;

L3PGU32Condition := function(I : pres := FreeGroup(2))
    return L3PresentationCondition(I, pgu32presentations : pres := pres);
end function;

L3PSU32Condition := function(I : pres := FreeGroup(2))
    return L3PresentationCondition(I, psu32presentations : pres := pres);
end function;

L3H36Condition := function(I : pres := FreeGroup(2))
    return L3PresentationCondition(I, h36presentations : pres := pres);
end function;

L3A7Condition := function(I : pres := FreeGroup(2))
    return L3PresentationCondition(I, a7presentations : pres := pres);
end function;

L3M10Condition := function(I : pres := FreeGroup(2))
    return L3PresentationCondition(I, m10presentations : pres := pres);
end function;



L3ExceptionalCondition := function(I : pres := FreeGroup(2))
    return &cat[
        L3A6Condition(I : pres := pres),
        L3L27Condition(I : pres := pres),
        L3PGU32Condition(I : pres := pres),
        L3PSU32Condition(I : pres := pres),
        L3H36Condition(I : pres := pres),
        L3A7Condition(I : pres := pres),
        L3M10Condition(I : pres := pres)
    ];
end function;



// return the orbit under the full acting group
L3Orbit := function(P)
    vprintf L3Quotients, 2: "sigmaact ...";
    t := Cputime();
    sigmaact := &meet [L3SignAction(P, sigma) : sigma in [[R!1, R!1], [R!1, zeta], [R!1, zeta^2], [zeta, R!1], [zeta, zeta], [zeta, zeta^2], [zeta^2, R!1], [zeta^2, zeta], [zeta^2, zeta^2]]];
    t := Cputime(t);
    vprintf L3Quotients, 2: "%o\n", t;

    vprintf L3Quotients, 2: "sigmainvact ... ";
    t := Cputime();
    sigmainvact := L3InverseTransposeAction(sigmaact);
    t := Cputime(t);
    vprintf L3Quotients, 2: "%o\n", t;

    vprintf L3Quotients, 2: "sigmazetaact ...\n";
    t := Cputime();
    sigmazetaact := L3ZetaAction(sigmaact);
    t := Cputime(t);
    vprintf L3Quotients, 2: "%o\n", t;

    vprintf L3Quotients, 2: "sigmainvzetaact ...\n";
    t := Cputime();
    sigmainvzetaact := L3ZetaAction(sigmainvact);
    t := Cputime(t);
    vprintf L3Quotients, 2: "%o\n", t;

    return sigmaact meet sigmainvact meet sigmazetaact meet sigmainvzetaact;
end function;



L3IsPGL := function(I)
    if 3 in I then
        // in characteristic 3, PGL = PSL
        return false;
    end if;

    for sigma in [[R!1, zeta], [R!1, zeta^2], [zeta, R!1], [zeta, zeta], [zeta, zeta^2], [zeta^2, R!1], [zeta^2, zeta], [zeta^2, zeta^2]] do
        if L3SignAction(I, sigma) eq I then
            return true;
        end if;
    end for;

    return false;
end function;

L3IsUnitary := function(I)
    for sigma in [[1,1], [R!1, zeta], [R!1, zeta^2], [zeta, R!1], [zeta, zeta], [zeta, zeta^2], [zeta^2, R!1], [zeta^2, zeta], [zeta^2, zeta^2]] do
        J := L3SignAction(I, sigma);
        if L3InverseTransposeAction(J) eq J or L3ZetaAction(L3InverseTransposeAction(J)) eq J then
            return true;
        end if;
    end for;

    return false;
end function;



L3SignMatrix := function(rels)
    F<a,b> := Parent(rels[1]);

    return Matrix(GF(3), 2, #rels, [[Weight(r, x) : r in rels] : x in [a,b]]);
end function;


allCombinations := function(template, set)
    if #set eq 0 then
        return [template];
    end if;

    result := [];

    s := Min(set);

    if #set eq 1 then
        for t in [zeta, zeta^2] do
            template[s] := t;
            Append(~result, template);
        end for;

        return result;
    end if;

    tmp := $$(template, set diff {s});
    for x in tmp do
        for t in [R!1, zeta, zeta^2] do
            foo := x;
            foo[s] := t;
            Append(~result, foo);
        end for;
    end for;

    return result;
end function;

CompareSignSystems := function(s1, s2)
    n := Dimension(Parent(s1));
    i := 1;
    while i le n and s1[i] eq s2[i] do  
        i +:= 1;
    end while;

    if i gt n then
        return 0;
    end if;

    return Integers()!s1[i] - Integers()!s2[i];
end function;

L3SignSystems := function(relations)
    /* Identify sign systems with vectors over GF(3).
     * The set of all sign systems is the full vector space.
     * The group acts by addition with certain vectors. 
     *
     * Two sign systems are in the same orbit if their difference is a group element.
     * Choose orbit representatives. Furthermore, we can assume that the vectors are
     * normalized (since zeta^2 + zeta + 1 is added to the ideal, we handle zeta and zeta^2
     * simultaneously).
     */
    n := #relations;

    if n eq 0 then
        return [[]];
    end if;

    K := GF(3);
    V := VectorSpace(K, n);

    P := Parent(relations[1]);

    grp := [];
    for a in [0..2] do
        for b in [0..2] do 
            Append(~grp, V![a*ExponentSum(r, P.1) + b*ExponentSum(r, P.2) : r in relations]);
        end for;
    end for;

    result := [];

    for v in V do
        isnew := true;
        for g in grp do
            if Normalise(v - g) in result then
                isnew := false;
                break;
            end if;
        end for;

        if isnew then
            Append(~result, Normalise(v));
        end if;
    end for;

    Sort(~result, CompareSignSystems);

    return [[zeta^(Integers()!r[i]) : i in [1..n]] : r in result];
end function;


L3Ideals := function(I : pres := FreeGroup(2), checkExceptional := true, Sigma := [[1,1], [zeta,1], [zeta^2,1], [1,zeta], [zeta,zeta], [zeta^2,zeta], [1,zeta^2], [zeta,zeta^2], [zeta^2,zeta^2]])
    IndentPush();
    MA := MinimalAssociatedPrimes(I);

    vprintf L3Quotients, 2: "%o minimal primes\n", #MA;

    primes := [P : P in MA | L3IsAbsolutelyIrreducible(P)];
    vprintf L3Quotients, 2: "%o primes are absolutely irreducible\n", #primes;
    primes := [P : P in primes | not L3IsImprimitive(P)];
    vprintf L3Quotients, 2: "%o primes are not imprimitive\n", #primes;
    primes := [P : P in primes | not L3IsOrthogonal(P)];
    vprintf L3Quotients, 2: "%o primes are not orthogonal\n", #primes;

    // the exceptional tests can be very expensive, so first choose orbit representatives
    result := [];
    for P in primes do
        if not L3ContainsConjugate(result, P, Sigma) then
            Append(~result, P);
        end if;
    end for;
    vprintf L3Quotients, 2: "%o orbit representatives\n", #result;


    if checkExceptional then
        result := [P : P in result | not L3IsA6(P : pres := pres)];
        vprintf L3Quotients, 2: "%o primes are not A_6\n", #result;
        result := [P : P in result | not L3IsL27(P : pres := pres)];
        vprintf L3Quotients, 2: "%o primes are not L_2(7)\n", #result;
        result := [P : P in result | not L3IsPGU32(P : pres := pres)];
        vprintf L3Quotients, 2: "%o primes are not PGU(3,2)\n", #result;
        result := [P : P in result | not L3IsPSU32(P : pres := pres)];
        vprintf L3Quotients, 2: "%o primes are not PSU(3,2)\n", #result;
        result := [P : P in result | not L3IsH36(P : pres := pres)];
        vprintf L3Quotients, 2: "%o primes are not H_{36}\n", #result;
        result := [P : P in result | not L3IsA7(P : pres := pres)];
        vprintf L3Quotients, 2: "%o primes are not A_7\n", #result;
        result := [P : P in result | not L3IsM10(P : pres := pres)];
        vprintf L3Quotients, 2: "%o primes are not M_{10}\n", #result;
    end if;

    IndentPop();

    return result;
end function;


L3SignKernel := function(relations)
    m := L3SignMatrix(relations);

    result := [x : x in Kernel(m)];

    return [[zeta^(Integers()!x) : x in Eltseq(k)] : k in result];
end function;


tmpIdeal := function(G : short := 10)
    result := [];
    resultchar3 := [];

    rels := [LHS(r)*RHS(r)^(-1) : r in Relations(G)];

    signSystems1, signSystems2 := L3SignSystems(rels, []);

    result := [];

    for s in signSystems1 do
        Append(~result, L3TracePresentationIdeal(rels, s));
    end for;

    return result;
end function;

signSystemString := function(s)
    result := "[ ";

    if #s gt 0 then
        result cat:= Sprint(s[1]);
    end if;

    for i in [2..#s] do
        result cat:= ", ";
        result cat:= Sprint(s[i]);
    end for;

    result cat:= " ]";

    return result;
end function;


intrinsic L3Quotients(G::GrpFP : 
        short := 10, 
        exactOrders := [], 
        useRandomTechniques := true, 
        exclude := [],
        factorizationBound := 10^60,
        trialDivisonBound := 10^4,
        groebnerBasisBound := 20
        ) -> SeqEnum[L3Quotients]
{ Compute the L3Quotients of G}
    result := [];
    resultchar3 := [];

    rels := [LHS(r)*RHS(r)^(-1) : r in Relations(G)];

    ker := L3SignKernel(rels);
    
    shortrels := [r : r in rels | #r le short];
    longrels := [r : r in rels | #r gt short];
    r1 := #shortrels;
    r2 := #longrels;
    r := r1 + r2;

    signSystems := L3SignSystems(shortrels cat longrels);

    vprintf L3Quotients: "%o short and %o long relations; %o sign systems in total\n", r1, r2, #signSystems;

    /* We want to handle the short first. To do this, accumulate the sign systems
     * in tuples <s, [t_1, ..., t_k]> such that the different s cat t_i will give
     * all sign systems.
     *
     * We can loop in the way below since the sign systems are sorted lexicographically.
     */
    signSystemsAcc := [ < signSystems[1][1..r1], [signSystems[1][r1 + 1..r]] > ];

    for i in [2..#signSystems] do
        if signSystems[i][1..r1] eq signSystemsAcc[#signSystemsAcc][1] then
            Append(~signSystemsAcc[#signSystemsAcc][2], signSystems[i][r1+1..r]);
        else
            Append(~signSystemsAcc, < signSystems[i][1..r1], [signSystems[i][r1+1..r]] >);
        end if;
    end for;

    counter1 := 1;
    shortconditions := [L3ConditionsForWord(r) : r in shortrels];
    for tup in signSystemsAcc do
        vprintf L3Quotients: "Sign system %o of %o: %o\n", counter1, #signSystemsAcc, signSystemString(tup[1]);
        t := Cputime();
        tmp1 := L3Ideals(L3TracePresentationIdealPrecomputed(shortconditions, tup[1]) : pres := G, Sigma := ker);
        t := Cputime(t);
        vprintf L3Quotients: "Time: %o; ideals: %o\n", t, #tmp1;
        IndentPush();
        if #tmp1 gt 0 then
            counter2 := 1;
            for P in tmp1 do
                vprintf L3Quotients: "ideal %o ...\n", counter2;
                IndentPush();
                longconditions := [L3ConditionsForWord(r : I := P) : r in longrels];
                counter3 := 1;
                for s in tup[2] do
                    vprintf L3Quotients: "Sign system %o of %o: %o\n", counter3, #tup[2], signSystemString(s);
                    t := Cputime();
                    if #longrels gt 0 then
                        tmp2 := L3Ideals(P + L3TracePresentationIdealPrecomputed(longconditions, s) : pres := G, Sigma := ker);
                    else
                        tmp2 := [P];
                    end if;
                    t := Cputime(t);
                    vprintf L3Quotients: "Time: %o; ideals: %o\n", t, #tmp2;
                    for Q in tmp2 do
                        if 3 in Q then
                            /* Treat the primes containing 3 differently, since these are the only 
                             * ideals which can contain prime ideals of other sign systems.
                             */

                            q := New(L3Quotient);
                            q`Group := G;
                            q`Ideal := Q;

                            Append(~resultchar3, q);
                        else
                            // don't add ideals which can be created from known ideals by a change of signs.
                            if not L3ContainsConjugate([q`Ideal : q in result], Q, ker) then
                                q := New(L3Quotient);
                                q`Group := G;
                                q`Ideal := Q;
                                
                                Append(~result, q);
                            end if;
                        end if;
                    end for;
                    counter3 +:= 1;
                end for;
                IndentPop();
                counter2 +:= 1;
            end for;
        end if;
        IndentPop();
        counter1 +:= 1;
    end for;

    resultchar3final := [];

    for x in resultchar3 do
        if not IsSuperset(x`Ideal, [q`Ideal : q in result]) then
            Append(~result, x);
        end if;
    end for;

    return result;
end intrinsic;


L3SmallestConjugate := function(P)
    if dimensionOverField(P) gt 0 then
        return P;
    end if;

    dim := quotientDimensionOverField(L3EliminateZeta(P));

    for sigma in [[1, zeta], [1, zeta^2], [zeta, 1], [zeta, zeta], [zeta, zeta^2], [zeta^2, 1], [zeta^2, zeta], [zeta^2, zeta^2]] do
        Q := L3SignAction(P, sigma);
        dimQ := quotientDimensionOverField(L3EliminateZeta(Q));

        if dimQ lt dim then
            // if the residue class dimension is smaller than a previous one,
            // it is already minimal
            return Q;
        end if;
    end for;

    return P;
end function;



l3Type := function(P : checkAll := false)
    if checkAll then
        if not L3IsAbsolutelyIrreducible(P) then
            return "reducible";
        elif L3IsA6(P) then
            return "Alt(6)";
        elif L3IsL27(P) then
            return "L_2(7)";
        elif L3IsPGU32(P) then
            return "PGU(3,2)";
        elif L3IsPSU32(P) then
            return "PSU(3,2)";
        elif L3IsH36(P) then
            return "(C_3 x C_3) \rtimes C_4";
        end if;
    end if;


    p := characteristic(P);
    d := dimensionOverField(P);

    if d gt 0 then
        if p eq 0 then
            if d eq 1 then
                return Sprintf("L_3(infty^infty)");
            else
                return Sprintf("L_3(infty^(infty^%o))", d);
            end if;
        else
            if d eq 1 then
                return Sprintf("L_3(%o^infty)", p);
            else
                return Sprintf("L_3(%o^(infty^%o))", p, d);
            end if;
        end if;
    else
        Q := L3EliminateZeta(L3SmallestConjugate(P));
        k := quotientDimensionOverField(Q);

        if p eq 0 then
            return Sprintf("L_3(infty^%o)", k);
        else
            if L3IsPGL(P) then
                k /:= 3;
                if L3IsUnitary(P) then
                    k /:= 2;
                    if k eq 1 then
                        return Sprintf("PGU(3, %o)", p);
                    else
                        return Sprintf("PGU(3, %o^%o)", p, k);
                    end if;
                else
                    if k eq 1 then
                        return Sprintf("PGL(3, %o)", p);
                    else
                        return Sprintf("PGL(3, %o^%o)", p, k);
                    end if;
                end if;
            else
                if L3IsUnitary(P) then
                    k /:= 2;
                    if k eq 1 then
                        return Sprintf("U_3(%o)", p);
                    else
                        return Sprintf("U_3(%o^%o)", p, k);
                    end if;
                else
                    if k eq 1 then
                        return Sprintf("L_3(%o)", p);
                    else
                        return Sprintf("L_3(%o^%o)", p, k);
                    end if;
                end if;
            end if;
        end if;
    end if;
end function;

intrinsic Print(q::L3Quotient)
{ Print L3Quotients }
    P := q`Ideal;

    printf "%o", l3Type(P);
end intrinsic;


L3TraceTuple := function(M1, M2)
    return [Trace(x) : x in [M1, M1^-1, M2, M2^-1, M1*M2, M1^-1*M2, M2^-1*M1, M2^-1*M1^-1, M1*M2*M1^-1*M2^-1, M2*M1*M2^-1*M1^-1]];
end function;


intrinsic GetMatrices(q::L3Quotient) -> GrpMat[FldFin]
{ Compute matrix images for the L3 quotient }
    if not IsFinite(q) then
        error "L3 quotient is not finite";
    end if;

    P := q`Ideal;

    p := characteristic(P);
    d := dimensionOverField(P);

    Q := ChangeRing(L3EliminateZeta(L3SmallestConjugate(P)), GF(p));
    S := Parent(Basis(Q)[1]);

    k := QuotientDimension(Q);

    if k eq 1 then
        K := GF(p);
        tr := [K!NormalForm(z, Q) : z in [S.i : i in [1..9]]];
    else
        K := GF(p^k);
        QQ := ChangeRing(Q, K);

        Q := RadicalDecomposition(QQ)[1];
        
        S := Parent(Basis(QQ)[1]);

        tr := [K!NormalForm(z, Q) : z in [S.i : i in [1..9]]];
    end if;


    bas := L3FindBasis(P);

    // reduction homomorphism from Z(zeta)[x_1, ..., x_{[1,2]}] to F_q[x_1, ... x_{[1,2]}]
    alpha := hom< R -> S | S.1, S.2, S.3, S.4, S.5, S.6, S.7, S.8, S.9, 0 >;

    mat := Matrix(K, 9, 9, [[K!NormalForm(alpha(L3TracePolynomial(bas[j]*bas[k])), Q) : k in [1..9]] : j in [1..9]]);
    A := Matrix(K, 9, 9, [[K!NormalForm(alpha(L3TracePolynomial(a*bas[j]*bas[k])), Q) : k in [1..9]] : j in [1..9]])*mat^-1;
    B := Matrix(K, 9, 9, [[K!NormalForm(alpha(L3TracePolynomial(b*bas[j]*bas[k])), Q) : k in [1..9]] : j in [1..9]])*mat^-1;

    m := RModule([A, B]);

    v, w, _ := Meataxe(m);

    if Dimension(v) eq 3 then
        return MatrixGroup(v);
    else
        return MatrixGroup(w);
    end if;
end intrinsic;

intrinsic AddRingRelations(q::L3Quotient, rels::SeqEnum[RngMPolElt]) -> SeqEnum[L3Quotients]
{ compute L_3-quotients with the additional ideal relations }
    I := q`Ideal + ideal< Generic(q`Ideal) | rels >;

    result := [];
    for P in L3Ideals(I : pres := q`Group) do
        r := New(L3Quotient);
        r`Group := q`Group;
        r`Ideal := P;
        Append(~result, r);
    end for;

    return result;
end intrinsic;

intrinsic SpecifyCharacteristic(q::L3Quotient, p::RngIntElt) -> SeqEnum[L3quotients]
{ }
    return AddRingRelations(q, [Generic(q`Ideal)!p]);
end intrinsic;


allSignSystems := function(m)
    result := [];

    for s in CartesianPower([1,zeta,zeta^2],m) do
        ss := [s[i] : i in [1..m]];

        // we can always normalize the sign system, so the first entry which is not 1
        // can be normalized to zeta (instead of zeta^2)
        i := 1;
        while i lt #ss and ss[i] eq 1 do
            i +:= 1;
        end while;
        if i le #ss and ss[i] eq zeta^2 then
            continue;
        end if;

        Append(~result, ss);
    end for;

    return result;
end function;


intrinsic AddGroupRelations(q::L3Quotient, rels::SeqEnum[GrpFPElt]) -> SeqEnum[L3Quotients]
{ compute L_3-quotients with the additional group relations }
    P := q`Ideal;
    G := q`Group;
    H := quo< G | [G!Eltseq(r) : r in rels] >;
    conditions := [L3ConditionsForWord(r : I := P) : r in rels];

    result := [];
    resultchar3 := [];

    for s in allSignSystems(#rels) do
        tmp := L3Ideals(P + L3TracePresentationIdealPrecomputed(conditions, s) : pres := G);

        for Q in tmp do
            r := New(L3Quotient);
            r`Group := H;
            r`Ideal := Q;

            if 3 in Q then
                Append(~resultchar3, r);
            elif not L3ContainsConjugate([q`Ideal : q in result], Q, [[R!1, R!1], [R!1, R!zeta], [R!1, zeta^2], [zeta, R!1], [zeta, zeta], [zeta, zeta^2], [zeta^2, R!1], [zeta^2, zeta], [zeta^2, zeta^2]]) then
                Append(~result, r);
            end if;
        end for;
    end for;

    for x in resultchar3 do
        if not IsSuperset(x`Ideal, [q`Ideal : q in result]) then
            Append(~result, x);
        end if;
    end for;

    return result;
end intrinsic;


intrinsic IsFinite(q::L3Quotient) -> BoolElt
{ Decide whether an L3 quotient is finite }
    P := q`Ideal;

    p := characteristic(P);

    return characteristic(P) ne 0 and dimensionOverField(P) eq 0;
end intrinsic;
