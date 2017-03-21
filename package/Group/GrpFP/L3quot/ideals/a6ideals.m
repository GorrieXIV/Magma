freeze;

import "../l3.m": R, x1, xm1, x2, xm2, x12, xm12, xm21, xm2m1, xcom, zeta;

a6presentations := [
<
    PermutationGroup< 6 | (4, 5, 6), (1, 2, 3, 4)(5, 6) >,
    Group< a,b | [ a^3, b^4, (a^-1, b^-1)^2, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, (b^-1 * a^-1)^5 ] >,
    ideal< R| [xcom + zeta,xm21^2 - xm21 - 1,xm21*xm2m1 - zeta - 1,xm2m1^2 - xm21 + xm2m1 - zeta + 1,xm21*zeta + xm21 - xm2m1 - zeta - 1,xm2m1*zeta + xm21 - 1,x12 - xm21 + xm2m1 + 1,xm12 - xm21,x1,xm1,x2 + zeta + 1,xm2 - zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (4, 5, 6), (1, 2, 3, 4, 5) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^-1)^4, (a^-1, b^-1)^2 ] >,
    ideal< R | [xcom + zeta,xm2^2 - xm2 - 1,x12 + zeta + 1,xm12 + xm2*zeta - zeta,xm21 - xm2*zeta - xm2 + zeta + 1,xm2m1 - zeta,x1,xm1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (4, 5, 6), (1, 2, 3, 4, 6) >,
    Group< a,b | [ a^3, b^5, (a^-1, b^-1)^2, (a * b^-1)^4 ] >,
    ideal< R | [xcom + zeta,x2^2 - xm2 + zeta + 1,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 - zeta,x12 - x2 - xm2 - 1,xm12 + zeta + 1,xm21 - zeta,xm2m1 - x2 - xm2 - 1,x2*zeta - xm2,xm2*zeta + x2 + xm2,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (4, 5, 6), (1, 2, 4)(3, 5, 6) >,
    Group< a,b | [ a^3, b^3, (a^-1 * b^-1)^4, (b^-1 * a)^5, a^-1 * b * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b * a^-1 *b^-1 * a^-1 * b * a * b ] >,
    ideal< R | [xcom + xm12 - zeta,xm12^2 - xm21 + zeta + 1,xm12*xm21 + xm12 + xm21 - 1,xm21^2 - xm12 - zeta,xm12*zeta - xm21,xm21*zeta + xm12 + xm21,x12 - 1,xm2m1 - 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (4, 5, 6), (1, 2, 4, 3, 5) >,
    Group< a,b | [ a^3, b^5, (b^-1 * a^-1)^3, (a * b^-1)^4, (a * b^2 * a^-1 * b^-2)^2 ] >,
    ideal< R | [xcom + x2 - zeta,x2^2 - xm2 + zeta + 1,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 - zeta,x12,xm12 - 1,xm21 - 1,xm2m1,x2*zeta - xm2,xm2*zeta + x2 + xm2,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (4, 5, 6), (1, 2, 4, 6)(3, 5) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a)^3, (b^-1 * a^-1)^5, a^-1 * b^-2 * a * b * a^-1 * b^-1 * a^-1 * b^2 * a * b * a^-1 *b^-1 ] >,
    ideal< R | [xcom + x12 - zeta,x12^2 - xm2m1 + zeta + 1,x12*xm2m1 + x12 + xm2m1 - 1,xm2m1^2 - x12 - zeta,x12*zeta - xm2m1,xm2m1*zeta + x12 + xm2m1,xm12,xm21,x1,xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (4, 5, 6), (1, 2, 4)(3, 6, 5) >,
    Group< a,b | [ a^3, b^3, (a * b^-1)^4, (b^-1 * a^-1)^5, a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 *a^-1 * b^-1 * a * b * a * b ] >,
    ideal< R | [xcom + xm2m1*zeta - zeta,xm2m1^2 - xm2m1 - 1,x12 - xm2m1,xm12 - zeta,xm21 + zeta + 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (4, 5, 6), (1, 2, 4, 3, 6) >,
    Group< a,b | [ a^3, b^5, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a * b^2 * a^-1 * b^-2)^2 ] >,
    ideal< R | [xcom + xm2*zeta - zeta,xm2^2 - xm2 - 1,x12 - zeta,xm12,xm21,xm2m1 + zeta + 1,x1,xm1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (4, 5, 6), (1, 2, 4, 5)(3, 6) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a^-1)^3, (b^-1 * a)^5, a^-1 * b^-2 * a^-1 * b * a^-1 * b^-1 * a * b^2 * a^-1 * b^2 * a * b] >,
    ideal< R | [xcom + xm21*zeta - zeta,xm21^2 - xm21 - 1,x12,xm12 - xm21,xm2m1,x1,xm1,x2 - zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (3, 4)(5, 6), (1, 2, 3, 4, 5) >,
    Group< a,b | [ a^2, b^5, (a * b^-1)^5, (b * a * b)^4 ] >,
    ideal< R | [xcom - xm2,xm2^2 - xm2 - 1,x12 + xm2*zeta + xm2,xm12 - xm2,xm21 - xm2,xm2m1 - xm2*zeta,x1 + zeta,xm1 - zeta - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (3, 4)(5, 6), (1, 3)(2, 4, 5, 6) >,
    Group< a,b | [ a^2, b^4, (a * b^-1)^5, b^-2 * a * b^-2 * a * b^2 * a * b^2 * a * b^2 * a ] >,
    ideal< R | [xcom - 1,xm21^2 + xm21 + xm2m1 - zeta,xm21*xm2m1 - xm21 + zeta + 1,xm2m1^2 - xm2m1 - 1,xm21*zeta - xm2m1,xm2m1*zeta + xm21 + xm2m1,x12 - xm2m1,xm12 + xm21 + xm2m1,x1 + zeta,xm1 - zeta - 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (3, 4)(5, 6), (1, 3, 2, 4, 5) >,
    Group< a,b | [ a^2, b^5, (b^-1 * a)^4, (b^-2 * a)^5 ] >,
    ideal< R | [xcom - 1,xm2^2 - xm2 - 1,x12 + zeta + 1,xm12 - 1,xm21 - 1,xm2m1 - zeta,x1 + zeta,xm1 - zeta - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2)(5, 6) >,
    Group< a,b | [ a^5, b^2, (b * a^-1)^5, (a * b * a)^4 ] >,
    ideal< R | [xcom - xm1,xm1^2 - xm1 - 1,x12 - xm1*zeta,xm12 - xm1,xm21 - xm1,xm2m1 + xm1*zeta + xm1,x1 - xm1,x2 - zeta - 1,xm2 + zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2)(4, 6) >,
    Group< a,b | [ a^5, b^2, (a^-1 * b)^4, (a^-2 * b)^5 ] >,
    ideal< R | [xcom - 1,xm1^2 - xm1 - 1,x12 - zeta,xm12 + zeta + 1,xm21 - zeta,xm2m1 + zeta + 1,x1 - xm1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2)(3, 4, 5, 6) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a^-1, b^-1)^2 ] >,
    ideal< R | [xcom + zeta,xm1^2 - xm1 - 1,x12 - 1,xm12,xm21,xm2m1 - 1,x1 - xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2)(3, 4, 6, 5) >,
    Group< a,b | [ a^5, b^4, b^-2 * a^-1 * b^2 * a^-1, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a^-1 ] >,ideal< R | [xcom - 1,xm1^2 - xm1 - 1,x12 + xm1 - 1,xm12 + xm1 - 1,xm21 + xm1 - 1,xm2m1 + xm1 - 1,x1 - xm1,x2 - zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2)(3, 5, 4, 6) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a * b^-2 * a^-1 * b^-1 * a^2 *b^2 * a^-1 * b^-1 * a ] >,
    ideal< R | [xcom - xm1*zeta - xm1 + zeta + 1,xm1^2 - xm1 - 1,x12 - xm1,xm12,xm21,xm2m1 - xm1,x1 - xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2)(3, 6, 5, 4) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a^-1)^3, (a^-1, b^-1)^2 ] >,
    ideal< R | [xcom - zeta - 1,xm1^2 - xm1 - 1,x12,xm12 - 1,xm21 - 1,xm2m1,x1 - xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2)(3, 6, 4, 5) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a^-1)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a^-1 * b^-2 * a * b^-1 * a^2* b^2 * a^-1 * b * a^-1 ] >,
    ideal< R | [xcom + xm1*zeta - zeta,xm1^2 - xm1 - 1,x12,xm12 + xm1*zeta + xm1,xm21 - xm1*zeta,xm2m1,x1 - xm1,x2 + zeta + 1,xm2 - zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 3) >,
    Group< a,b | [ a^5, b^3, (a^-1 * b^-1)^4, (a^-1, b^-1)^2 ] >,
    ideal< R | [xcom + zeta,xm1^2 - xm1 - 1,x12 - zeta,xm12 + xm1*zeta - zeta,xm21 - xm1*zeta - xm1 + zeta + 1,xm2m1 + zeta + 1,x1 - xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 3)(4, 5, 6) >,
    Group< a,b | [ a^5, b^3, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a * b * a^-2 * b^-1 * a)^2 ] >,
    ideal< R | [xcom - xm1*zeta - xm1 + zeta + 1,xm1^2 - xm1 - 1,x12 - 1,xm12,xm21,xm2m1 - 1,x1 - xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 3, 4, 5) >,
    Group< a,b | [ a^5, b^5, (b^-1 * a^-1)^3, (b^-1 * a)^3, (a^-1, b^-1)^2 ] >,
    ideal< R | [xcom - zeta - 1,xm2^2 - xm2 - 1,x12,xm12,xm21,xm2m1,x1 + xm2 - 1,xm1 + xm2 - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 3, 4, 6) >,
    Group< a,b | [ a^5, b^5, (a * b^-1)^2, (a^-1 * b^-1)^4 ] >,
    ideal< R | [xcom + x2 + xm2,x2^2 - xm2 + zeta + 1,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 - zeta,x12 - zeta,xm12 - zeta - 1,xm21 + zeta,xm2m1 + zeta + 1,x2*zeta - xm2,xm2*zeta + x2 + xm2,x1 + x2 + xm2,xm1 + x2 + xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 3, 5, 4) >,
    Group< a,b | [ a^5, b^5, (a * b^2 * a)^2, a^-1 * b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [xcom - 1,x2^2 - xm2 - zeta,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 + zeta + 1,x12 - x2 - xm2 - 1,xm12 - x2,xm21 - xm2,xm2m1 - x2 - xm2 - 1,x2*zeta + x2 + xm2,xm2*zeta - x2,x1 + x2 + xm2,xm1 + x2 + xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 3, 5)(4, 6) >,
    Group< a,b | [ a^5, b^4, (a * b^-1 * a)^2, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^-1 * b *a^-1 * b^-1 * a * b^-1 * a * b^-1 * a ] >,
    ideal< R | [xcom - xm1,xm1^2 - xm1 - 1,x12 - zeta,xm12 - xm1,xm21 - xm1,xm2m1 + zeta + 1,x1 - xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (2, 3)(5, 6) >,
    Group< a,b | [ a^4, b^2, (b * a^-1)^5, a^-2 * b * a^-2 * b * a^2 * b * a^2 * b * a^2 * b ] >,
    ideal< R | [xcom - 1,xm21^2 - xm2m1 - zeta,xm21*xm2m1 + xm21 + xm2m1 - 1,xm2m1^2 - xm21 + zeta + 1,xm21*zeta + xm21 + xm2m1,xm2m1*zeta - xm21,x12 - xm21,xm12 - xm2m1,x1 - 1,xm1 - 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (2, 3, 4) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a^-1)^3, (b^-1 * a)^5, a * b^-1 * a^-2 * b * a^-1 * b^-1 * a * b^-1 * a^2 * b * a^-1 *b^-1 ] >,
    ideal< R | [xcom - xm21*zeta - xm21 + zeta + 1,xm21^2 - xm21 - 1,x12,xm12 - xm21,xm2m1,x1 - 1,xm1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (2, 3, 4, 5, 6) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a^-1, b^-1)^2 ] >,
    ideal< R | [xcom - zeta - 1,xm2^2 - xm2 - 1,x12 - 1,xm12,xm21,xm2m1 - 1,x1 - 1,xm1 - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (2, 3, 4, 6, 5) >,
    Group< a,b | [ a^4, b^5, a^-1 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a^-1] >,
    ideal< R | [xcom - 1,xm2^2 - xm2 - 1,x12 + xm2*zeta - zeta,xm12 - xm2*zeta - xm2 + zeta + 1,xm21 + xm2*zeta - zeta,xm2m1 - xm2*zeta - xm2 + zeta + 1,x1 - 1,xm1 - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (2, 3, 5, 6, 4) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1)^3, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a^-1 * b^2 * a^-2 * b^-1 * a * b^-2* a^2 * b ] >,
    ideal< R | [xcom - xm2*zeta - xm2 + zeta + 1,xm2^2 - xm2 - 1,x12,xm12 - xm2,xm21 - xm2,xm2m1,x1 - 1,xm1 - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (2, 3, 5, 4, 6) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a)^3, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a^-1 * b^2 * a^-2 * b^-1 * a^-1 * b^2 *a^2 * b^-1 ] >,
    ideal< R | [xcom - xm2*zeta - xm2 + zeta + 1,xm2^2 - xm2 - 1,x12 - xm2,xm12,xm21,xm2m1 - xm2,x1 - 1,xm1 - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (2, 3, 6, 5, 4) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1)^3, (a^-1, b^-1)^2 ] >,
    ideal< R | [xcom - zeta - 1,x2^2 - xm2 + zeta + 1,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 - zeta,x12,xm12 - zeta,xm21 + zeta + 1,xm2m1,x2*zeta - xm2,xm2*zeta + x2 + xm2,x1 - 1,xm1 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (2, 3, 6) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a)^3, (b^-1 * a^-1)^5, a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a * b * a^2 * b^-1 * a^2* b ] >,
    ideal< R | [xcom + xm2m1 + zeta + 1,x12^2 - xm2m1 + zeta + 1,x12*xm2m1 + x12 + xm2m1 - 1,xm2m1^2 - x12 - zeta,x12*zeta - xm2m1,xm2m1*zeta + x12 + xm2m1,xm12,xm21,x1 - 1,xm1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (1, 2, 3) >,
    Group< a,b | [ a^4, b^3, (a^-1, b^-1)^2, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 * a^-1)^5 ] >,ideal< R | [xcom + zeta,xm12^2 + xm2m1 + 2*zeta + 2,xm12*xm2m1 + 1,xm2m1^2 + xm12 - 2*zeta,xm12*zeta + xm2m1 + zeta + 1,xm2m1*zeta - xm12 + xm2m1 + zeta,x12 + xm12 - zeta,xm21 + xm2m1 + zeta + 1,x1 - 1,xm1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (1, 2, 3, 4, 6) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^2, (b^-1 * a^-1)^5 ] >,
    ideal< R | [xcom - 1,x2^2 - xm2 + zeta + 1,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 - zeta,x12 - x2 - xm2 - 1,xm12 + 1,xm21 + 1,xm2m1 - x2 - xm2 - 1,x2*zeta - xm2,xm2*zeta + x2 + xm2,x1 - 1,xm1 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (1, 2, 3, 5, 4) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^2, (b^-1 * a)^5 ] >,
    ideal< R | [xcom - 1,x2^2 - xm2 - zeta,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 + zeta + 1,x12 + 1,xm12 - x2 - xm2 - 1,xm21 - x2 - xm2 - 1,xm2m1 + 1,x2*zeta + x2 + xm2,xm2*zeta - x2,x1 - 1,xm1 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (1, 2, 3, 5)(4, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1,(a^-1, b^-1)^2 ] >,
    ideal< R | [xcom + zeta,xm2m1^2 - xm2m1 - 1,x12 - xm2m1,xm12 + xm2m1 - 1,xm21 + xm2m1 - 1,x1 - 1,xm1 - 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (1, 3)(2, 4, 6, 5) >,
    Group< a,b | [ a^4, b^4, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^-1, (a * b^-1)^4, a^-1 * b^-1 * a^-2 *b^-1 * a^-1 * b^-1 * a^2 * b^-1, b^-1 * a^-2 * b^-2 * a^-2 * b^-1 * a * b * a, a * b * a^-1 * b^-2 * a^2 * b^2 * a^-1 * b ] >,
    ideal< R | [xcom - xm2m1,xm2m1^2 - xm2m1 - 1,x12 - xm2m1,xm12 + zeta + 1,xm21 - zeta,x1 - 1,xm1 - 1,x2 + zeta + 1,xm2 - zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (1, 3, 2, 4, 5) >,
    Group< a,b | [ a^4, b^5, (a * b^-2)^2, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a * b^-1 *a^-1 * b^-1 * a * b^-1 * a^-1 * b * a^-1 ] >,
    ideal< R | [xcom - xm2,xm2^2 - xm2 - 1,x12 + zeta + 1,xm12 - xm2,xm21 - xm2,xm2m1 - zeta,x1 - 1,xm1 - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (1, 3, 5, 6)(2, 4) >,
    Group< a,b | [ a^4, b^4, (a^-1 * b^-1)^4, a * b^-2 * a * b^-1 * a * b^2 * a * b^-1, a * b^-1 * a^-2 * b^-1 * a *b^-1 * a^2 * b^-1, b^-1 * a^-2 * b^-2 * a^-2 * b^-1 * a^-1 * b * a^-1, a * b^-1 * a^-1 * b^-2 * a^2 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [xcom + xm12 + xm21,xm12^2 - xm21 + zeta + 1,xm12*xm21 + xm12 + xm21 - 1,xm21^2 - xm12 - zeta,xm12*zeta - xm21,xm21*zeta + xm12 + xm21,x12 + zeta + 1,xm2m1 - zeta,x1 - 1,xm1 - 1,x2 + zeta + 1,xm2 - zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (1, 2)(3, 4, 5, 6), (1, 3, 6, 2, 4) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-2)^2, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-1 *b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a^-1 ] >,
    ideal< R | [xcom - xm2,xm2^2 - xm2 - 1,x12 - xm2,xm12 - zeta,xm21 + zeta + 1,xm2m1 - xm2,x1 - 1,xm1 - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 3, 6)(4, 5) >,
    Group< a,b | [ a^5, b^4, (a * b^-1)^2, (b^-1 * a^-1)^5 ] >,
    ideal< R | [xcom - 1,xm1^2 - xm1 - 1,x12 - xm1*zeta - xm1 + zeta + 1,xm12 + 1,xm21 + 1,xm2m1 + xm1*zeta - zeta,x1 - xm1,x2 - zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 4, 3)(5, 6) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^2, (b^-1 * a)^5 ] >,
    ideal< R | [xcom - 1,xm1^2 - xm1 - 1,x12 + 1,xm12 + xm1*zeta - zeta,xm21 - xm1*zeta - xm1 + zeta + 1,xm2m1 + 1,x1 - xm1,x2 + zeta + 1,xm2 - zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 4) >,
    Group< a,b | [ a^5, b^3, (b^-1 * a^-1)^3, (a * b^-1)^4, (a * b * a^-2 * b^-1 * a)^2 ] >,
    ideal< R | [xcom - xm1*zeta - xm1 + zeta + 1,xm1^2 - xm1 - 1,x12,xm12 - 1,xm21 - 1,xm2m1,x1 - xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 5, 4)(3, 6) >,
    Group< a,b | [ a^5, b^4, (a * b * a)^2, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^-1 * b^-1 *a^-1 * b^-1 * a * b * a * b^-1 * a^-1 ] >,
    ideal< R | [xcom - xm1,xm1^2 - xm1 - 1,x12 + xm1*zeta + xm1,xm12 - zeta,xm21 + zeta + 1,xm2m1 - xm1*zeta,x1 - xm1,x2 + zeta + 1,xm2 - zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 5)(3, 6, 4) >,
    Group< a,b | [ a^5, b^3, (a^-1, b^-1)^2, (a * b^-1)^4 ] >,
    ideal< R | [xcom + zeta,xm1^2 - xm1 - 1,x12 + xm1*zeta - zeta,xm12 - zeta,xm21 + zeta + 1,xm2m1 - xm1*zeta - xm1 + zeta + 1,x1 - xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 3, 6, 4) >,
    Group< a,b | [ a^5, b^5, (a * b * a)^2, a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 ] >,
    ideal< R | [xcom - 1,x2^2 - xm2 - zeta,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 + zeta + 1,x12 - zeta,xm12 - xm2,xm21 - x2,xm2m1 + zeta + 1,x2*zeta + x2 + xm2,xm2*zeta - x2,x1 - x2 - xm2 - 1,xm1 - x2 - xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 3, 6, 5) >,
    Group< a,b | [ a^5, b^5, (a * b^-2 * a)^2, (a * b^-1 * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [xcom - 1,xm2^2 - xm2 - 1,x12 - xm2,xm12 - xm2*zeta - xm2 + zeta + 1,xm21 + xm2*zeta - zeta,xm2m1 - xm2,x1 - xm2,xm1 - xm2,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 4, 5, 3) >,
    Group< a,b | [ a^5, b^5, (a^-1 * b^-2)^2, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b ] >,
    ideal< R | [xcom - 1,x2^2 - xm2 - zeta,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 + zeta + 1,x12 - zeta,xm12 - x2 - xm2 - 1,xm21 - x2 - xm2 - 1,xm2m1 + zeta + 1,x2*zeta + x2 + xm2,xm2*zeta - x2,x1 - x2 - xm2 - 1,xm1 - x2 - xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 5, 4, 3) >,
    Group< a,b | [ a^5, b^5, (a^-1 * b^-1)^2, (a * b^-1)^4 ] >,
    ideal< R | [xcom - xm2,xm2^2 - xm2 - 1,x12 - zeta - 1,xm12 - 1,xm21 - 1,xm2m1 + zeta,x1 - xm2,xm1 - xm2,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 4, 6, 5) >,
    Group< a,b | [ a^5, b^5, (a * b^-1 * a)^2, a^-1 * b * a^-1 * b^-1 * a * b^-1 * a * b^-1 ] >,
    ideal< R | [xcom - 1,x2^2 - xm2 - zeta,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 + zeta + 1,x12 + x2 + xm2,xm12 - 1,xm21 - 1,xm2m1 + x2 + xm2,x2*zeta + x2 + xm2,xm2*zeta - x2,x1 - x2 - xm2 - 1,xm1 - x2 - xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 4, 3, 6) >,
    Group< a,b | [ a^5, b^5, (a * b^-2)^2, (a * b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [xcom - 1,xm2^2 - xm2 - 1,x12 - xm2*zeta - xm2 + zeta + 1,xm12 - zeta,xm21 + zeta + 1,xm2m1 + xm2*zeta - zeta,x1 + xm2 - 1,xm1 + xm2 - 1,x2 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 6 | (2, 3, 4, 5, 6), (1, 2, 4, 6, 3) >,
    Group< a,b | [ a^5, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, (a^-2 * b^-1)^3, (a^-2 * b)^3, a^-1 * b^-1 * a * b^-1 * a^-2 *b^2 * a^2 * b^-1 ] >,
    ideal< R | [xcom + xm2 - zeta,x2^2 - xm2 - zeta,x2*xm2 + x2 + xm2 - 1,xm2^2 - x2 + zeta + 1,x12 + zeta + 1,xm12 + zeta + 1,xm21 - zeta,xm2m1 - zeta,x2*zeta + x2 + xm2,xm2*zeta - x2,x1 + x2 + xm2,xm1 + x2 + xm2,zeta^2 + zeta + 1] >
>
];

