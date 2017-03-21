freeze;

import "../l3.m": R, x1, xm1, x2, xm2, x12, xm12, xm21, xm2m1, xcom, zeta;

m10presentations := [
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 3)(4, 5, 7)(6, 10, 8) >,
    Group< a,b | [ a^4, b^3, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 *a^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a * b * a^2 * b * a * b^-1, a * b * a^-2 * b^-1 * a^-1 * b^-1 * a * b^-1 * a^2 * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 4,x12 + zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 1,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 3, 4)(5, 8, 7, 9) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^3, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^-2 * b * a^2 *b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + 4,x12,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 3, 5, 6, 8, 10, 7)(4, 9) >,
    Group< a,b | [ a^4, b^8, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a^-1 * b^-3)^2, b^-1 * a^-1 * b * a* b * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 4,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 3, 6, 5, 4, 7, 10)(8, 9) >,
    Group< a,b | [ a^4, b^8, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 *a^-1)^5, b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 * b^3 * a, b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a * b^-1 * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12 + 2,xm21 + 2,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 3, 7, 6)(4, 8, 5, 9, 10) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, b^-1* a^-1 * b * a^-1 * b^-1 * a * b^-2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 3, 8)(4, 10, 9, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^-1 * b^2 * a * b^-1, a^-1 * b^-2 * a^-2 * b^-1 *a^-1 * b^2 * a^2 * b, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 3, 9)(5, 10, 6, 7) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^4, a * b^-2 * a *b^-1 * a * b^2 * a * b^-1, b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^2 * a^2 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + 4,x12 + 4,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 3, 10, 5)(4, 6, 9, 7, 8) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^4, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, a^-1 *b^-2 * a^-1 * b^-1 * a * b * a * b^-2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 4,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 5, 8, 3)(4, 9, 6, 7, 10) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^4, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, (a * b^2* a^-1 * b^-1)^2, b * a * b * a^-1 * b^-1 * a^-1 * b^2 * a * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + zeta + 2,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 5, 10)(4, 8, 6, 9) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a)^3, (a^-1 * b^-1)^4, a * b^-1 * a^-2 * b^-1 * a^-2 * b * a^2 *b^2 * a * b ] >,
    ideal< R | [5,xcom + 4,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 5, 9, 3, 4, 7, 8)(6, 10) >,
    Group< a,b | [ a^4, b^8, (b^-1 * a^-1)^3, (a * b^-1)^4, (a * b^-3)^2, b^-1 * a * b * a^-1 * b* a^-2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 4,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 4,xm1 + 4,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 5, 7, 9)(3, 6, 8, 4, 10) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, (a *b^2 * a^-1 * b^-1)^2, a * b^-2 * a * b^-1 * a^-1 * b * a^-1 * b^-2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 1,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 5)(3, 7, 4)(8, 10, 9) >,
    Group< a,b | [ a^4, b^3, (a^-1 * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 *a^-1, a^-1 * b^-1 * a^-1 * b * a * b * a^2 * b^-1 * a^2 * b * a^-1 * b ] >,
    ideal< R | [5,xcom + 4,x12 + 4*zeta,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 5, 6)(3, 8, 9, 7) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 *b^2 * a^-1 * b^-1, (a * b^-1)^4, b * a^-2 * b^-1 * a^-1 * b^-1 * a * b^2 * a^-1 * b * a ] >,
    ideal< R | [5,xcom + 4,x12 + 3*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 1,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 5, 3, 9, 10, 8, 7)(4, 6) >,
    Group< a,b | [ a^4, b^8, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 *a^-1)^5, b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b^2, b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^-2 * a^-1 * b^-1, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 2, 5, 4)(3, 10, 7, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a * b^-2 * a^-1 * b^2 * a^2 * b^-1, a * b^-2 * a^-2 * b^-1 * a *b^2 * a^2 * b, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3)(2, 4)(5, 7)(8, 9) >,
    Group< a,b | [ a^4, b^2, a^-2 * b * a^-2 * b * a^2 * b * a^2 * b * a^2 * b, (a^-1 * b * a * b)^3,(a^-1 * b)^8, b * a^-1 * b * a^-1 * b * a * b * a^-2 * b * a * b * a^2 * b * a * b * a^2 * b * a ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 1,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + zeta + 2,x1 + 4,xm1 + 4,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 2, 4, 8, 6, 10, 7)(5, 9) >,
    Group< a,b | [ a^4, b^8, (a * b^-1)^2, b^-1 * a * b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b * a* b^-1, (b^-1 * a^-1)^5, b^-2 * a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 1,xm21 + 1,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 5, 10, 6, 9, 2, 4)(7, 8) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b^-1)^2, b^-1 * a^-1 * b * a * b^-1 * a^2 * b^-1 * a * b *a^-1 * b^-1, (b^-1 * a)^5, b^-2 * a * b^-2 * a * b^-1 * a * b^2 * a^-1 * b^-2 * a ] >,
    ideal< R | [5,xcom,x12 + zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4*zeta + 4,x1 + 4,xm1 + 4,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 6, 8, 5)(2, 4, 9, 7, 10) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-1 * a^-1 * b^-1 * a^-2 * b * a^2 *b^-1 * a, (a * b^2 * a^-1 * b^-1)^2, a^-1 * b^2 * a^-2 * b^-1 * a^-1 * b^-2 * a^2 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 7, 9, 6)(2, 4, 10, 5, 8) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-1 * a * b^-1 * a^-2 * b * a^2 *b^-1 * a^-1, (a^-1 * b^2 * a * b^-1)^2, a * b^2 * a^-2 * b^-1 * a * b^-2 * a^2 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 8, 10, 9)(2, 4, 5, 6, 7) >,
    Group< a,b | [ a^4, b^5, a^-1 * b^-1 * a^2 * b^-1 * a^-1, a^-1 * b * a^-1 * b^-1 * a^-1 *b^-1 * a * b^-1 * a * b * a * b, b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^2 * a * b^2 * a * b ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 4,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 2*zeta + 1,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 9, 10)(2, 4, 7, 6) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^2 * a^2 * b, a^-1 * b^-2 * a^-2 * b^-1 * a * b^2 *a^2 * b^-1, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 10, 8)(2, 4, 6, 5) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b^-1, a^-1 * b^-2 * a^-2 * b * a *b^2 * a^2 * b, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3)(2, 5, 4, 10, 9, 7, 8, 6) >,
    Group< a,b | [ a^4, b^8, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^-2 * a * b, b *a^-2 * b^-2 * a^2 * b^-1 * a^2 * b * a, b^-2 * a^-2 * b^2 * a^-1 * b^4 * a ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 2, 5)(4, 6, 7, 9) >,
    Group< a,b | [ a^4, b^4, a^-1 * b^-2 * a^2 * b^2 * a^-1, (a^-1 * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1* b^2 * a * b^2 * a^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b^-1 * a^-1, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 2,xm21 + 2,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 4, 9, 2, 5, 7, 6)(8, 10) >,
    Group< a,b | [ a^4, b^8, b * a^-2 * b^2 * a^2 * b, b^-2 * a^-2 * b * a^2 * b^-1, (a *b^-1)^4, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 6, 10)(2, 5, 8, 7) >,
    Group< a,b | [ a^4, b^4, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-1)^4, b^-1 * a^-1 * b^-1 * a^-2 * b *a^2 * b^-1 * a^-1, b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^2 * a^2 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + zeta + 4,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 7, 10, 6, 4, 8, 9)(2, 5) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b^-1)^4, b^2 * a * b^-1 * a^-1 * b * a^2 * b * a^-1, a^-1 *b * a^-2 * b^-1 * a^2 * b^-2 * a^2 * b, b^2 * a^-2 * b^-2 * a^-1 * b^4 * a ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 8, 4)(2, 5, 9, 10) >,
    Group< a,b | [ a^4, b^4, b^-1 * a * b^-2 * a^-1 * b^2 * a^2 * b^-1, a * b^-2 * a^-2 * b^-1 * a *b^2 * a^2 * b, b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 1,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + zeta + 2,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 9, 6, 8)(2, 5, 10, 7, 4) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b^-1)^2, b^-1 * a * b^-1 * a^-2* b * a^2 * b^-1 * a, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 10, 4, 7)(2, 5, 6, 9, 8) >,
    Group< a,b | [ a^4, b^5, a * b * a^-1 * b^-1 * a^-1 * b^-2 * a * b^-1, a * b^-1 * a^-1 * b^-1* a^2 * b^2 * a^2 * b^-1, a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 1,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3)(2, 7, 4, 6, 9, 5, 8, 10) >,
    Group< a,b | [ a^4, b^8, (b^-1 * a)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 *a^-1, (b^-1 * a^-1)^5, a * b^2 * a^-2 * b^-1 * a * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 2, 7, 8)(4, 9, 10, 5, 6) >,
    Group< a,b | [ a^4, b^5, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a * b^-1)^4, b * a^-1 * b^-1* a^-1 * b^-1 * a * b^-2 * a * b ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 2,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 4)(2, 7, 5)(6, 10, 9) >,
    Group< a,b | [ a^4, b^3, (a * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2* b^-1, a^-1 * b * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^2 * b^-1 * a^-1 * b^-1, a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^-1 * b * a * b^-1 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 1,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 5, 9)(2, 7, 6, 8) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^3, a * b^-2 * a^-2 * b^-1 * a * b^2 * a^2 * b^-1, a^-1 * b^-2* a^-2 * b^-2 * a^2 * b^2 * a^2 * b^2 * a^-1, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 2*zeta,x12,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 6, 2, 7)(4, 5, 10, 8, 9) >,
    Group< a,b | [ a^4, b^5, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^4, (a * b^-2 *a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 8, 6)(2, 7, 10, 4) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a)^3, a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b^-1, a^-1 *b^-2 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^2 * a^-1, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 9, 8, 4, 10, 6, 5)(2, 7) >,
    Group< a,b | [ a^4, b^8, (b^-1 * a^-1)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1* a^-1, (b^-1 * a)^5, a^-1 * b^2 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12,xm12 + 2,xm21 + 2,xm2m1,x1 + 4,xm1 + 4,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 10)(2, 7, 9)(4, 8, 5) >,
    Group< a,b | [ a^4, b^3, (a^-1 * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 *a^2 * b^-1, a * b^-1 * a^-1 * b * a * b * a^2 * b^-1 * a^2 * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 2, 8, 4, 5, 7, 10)(6, 9) >,
    Group< a,b | [ a^4, b^8, (a^-1, b^-1)^2, (a * b^-3)^2, b * a^-1 * b^-1 * a^-2 * b * a^2 *b^-1 * a^-1, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 1,x12 + 3*zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 5, 4, 6)(2, 8, 9, 10, 7) >,
    Group< a,b | [ a^4, b^5, (a^-1, b^-1)^2, b * a^-1 * b^-1 * a^-2 * b * a^2 * b^-1 * a^-1,(a^-1 * b^-2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 1,x12 + 4*zeta + 3,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + zeta + 4,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3)(2, 9)(5, 6)(7, 10) >,
    Group< a,b | [ a^4, b^2, a^-1 * b * a^-2 * b * a^2 * b * a^2 * b * a^-1, (a^-1 * b)^8, a^-1 * b *a^-2 * b * a^-1 * b * a^-2 * b * a * b * a^2 * b * a^-1 * b * a^2 * b, b * a^-2 * b * a^-1 * b * a^-1 * b * a^-2 * b * a * b * a * b * a^2 * b * a^-1 * b * a ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 2,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta + 1,x1 + 4,xm1 + 4,x2 + zeta,xm2 + 4*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 2, 9)(4, 10, 8, 7) >,
    Group< a,b | [ a^4, b^4, a^-1 * b^-1 * a^2 * b^-1 * a^-1, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a * b^2* a^-1, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^-2 * a * b * a * b^2 * a^-1 * b^-1, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a * b * a * b^-1 ] >,ideal< R | [5,xcom + 2,x12 + 4*zeta + 3,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + zeta + 4,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 4, 2, 9, 10, 6, 7)(5, 8) >,
    Group< a,b | [ a^4, b^8, (a * b^-1)^2, (a^-1 * b^-1)^4, (b^-2 * a^-1 * b^-1)^3, b * a * b^2 *a * b * a^2 * b * a * b^2 * a * b ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta,xm12 + zeta,xm21 + 4*zeta + 4,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 5)(2, 9, 6)(4, 8, 10) >,
    Group< a,b | [ a^4, b^3, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a^-1 * b * a^-2 * b^-1 * a^-1 *b^-1 * a * b * a^2 * b^-1 * a * b^-1, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b * a^-1 * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta + 1,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + zeta + 2,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 6)(2, 9, 5)(4, 7, 8) >,
    Group< a,b | [ a^4, b^3, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a * b * a^-2 * b^-1 * a^-1 * b^-1* a * b * a^2 * b^-1 * a^-1 * b^-1, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 4,xm12 + 2*zeta + 1,xm21 + 3*zeta + 4,xm2m1 + 2*zeta + 1,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 7, 6, 10, 2, 9, 8)(4, 5) >,
    Group< a,b | [ a^4, b^8, (b^-1 * a^-1)^3, (b^-1 * a)^3, b^-1 * a^-2 * b * a^-1 * b^-1 * a * b* a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12,xm21,xm2m1,x1 + 4,xm1 + 4,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 8, 2, 9, 7, 5, 10)(4, 6) >,
    Group< a,b | [ a^4, b^8, (b^-1 * a^-1)^3, (b^-1 * a)^3, b^-1 * a^-2 * b * a * b^-1 * a^-1 * b* a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12,xm21,xm2m1,x1 + 4,xm1 + 4,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 10, 5, 7, 2, 9, 4)(6, 8) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b^-1)^2, (a * b^-1)^4, (b^-2 * a * b^-1)^3, b * a^-1 * b^2 *a^-1 * b * a^2 * b * a^-1 * b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + 2,x12 + zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta + 4,x1 + 4,xm1 + 4,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3)(2, 10, 8, 5, 9, 6, 4, 7) >,
    Group< a,b | [ a^4, b^8, (b^-1 * a^-1)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1* a^-1, (b^-1 * a)^5, a * b^-2 * a^-2 * b^-1 * a * b^-2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12,xm12 + 2,xm21 + 2,xm2m1,x1 + 4,xm1 + 4,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 2, 10, 4)(5, 8, 9, 7, 6) >,
    Group< a,b | [ a^4, b^5, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a * b^-1)^4, b^-1 * a * b^-1* a^-1 * b^-1 * a^-1 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 2,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 4, 5)(2, 10, 7, 8) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a)^3, a * b^-2 * a^-2 * b * a * b^2 * a^2 * b, a^-1 * b^-2 * a^-2* b^-2 * a^2 * b^2 * a^2 * b^2 * a^-1, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 3,xm12,xm21,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 3, 7)(2, 10, 9)(4, 6, 8) >,
    Group< a,b | [ a^4, b^3, (a^-1 * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 *a^2 * b^-1, a * b^-1 * a^-1 * b * a * b * a^2 * b^-1 * a^-1 * b * a^2 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 2, 3)(4, 9, 7, 6) >,
    Group< a,b | [ a^4, b^4, a^-1 * b^-2 * a^2 * b^2 * a^-1, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 *b^2 * a * b^2 * a^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b^-1 * a^-1, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 7, 8, 9, 4, 10, 6)(2, 3) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b^-1)^4, a^-1 * b * a^-2 * b * a^-1 * b^-1 * a * b^2, b *a^-2 * b^-2 * a^2 * b^-1 * a^2 * b * a^-1, b^-2 * a^-2 * b^2 * a * b^4 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5)(2, 3, 4, 8, 6, 7, 10, 9) >,
    Group< a,b | [ a^4, b^8, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b * a * b^-2, a * b* a^-2 * b^-1 * a^2 * b^-2 * a^2 * b, b^2 * a^-2 * b^-2 * a * b^4 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 10, 4)(2, 3, 6, 8) >,
    Group< a,b | [ a^4, b^4, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b^-1)^2, b^-1 * a * b^-1 * a^-2 * b *a^2 * b^-1 * a, b^-1 * a * b * a * b^-1 * a * b^2 * a^2 * b^2 * a ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 4, 6, 2, 3, 7, 9)(8, 10) >,
    Group< a,b | [ a^4, b^8, b * a^-2 * b^2 * a^2 * b, b^-2 * a^-2 * b * a^2 * b^-1, (a^-1 *b^-1)^4, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom,x12 + zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 6, 9, 10)(2, 3, 8, 7, 4) >,
    Group< a,b | [ a^4, b^5, b^-2 * a^-1 * b^-1 * a^-1 * b * a * b^-1 * a, a * b^-2 * a^-2 * b^-1* a * b^2 * a^2 * b ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 4,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + 2*zeta + 1,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 8, 4, 7)(2, 3, 9, 6, 10) >,
    Group< a,b | [ a^4, b^5, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-1)^4, b^-1 * a^-1 * b^-1 * a^-2* b * a^2 * b^-1 * a^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 1,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 9, 8)(2, 3, 10, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^-1 * b^2 * a * b^-1, a^-1 * b^-2 * a^-2 * b^-1 *a^-1 * b^2 * a^2 * b, b^-1 * a^-2 * b^-1 * a * b^-1 * a^-1 * b * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 4,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 4*zeta + 3,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 9, 10, 3)(2, 4, 6, 7, 8) >,
    Group< a,b | [ a^4, b^5, (a^-1, b^-1)^2, b * a * b^-1 * a^-2 * b * a^2 * b^-1 * a, (a * b^-2* a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 1,x12 + zeta + 2,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + 4*zeta + 1,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 2, 4, 10, 9, 8, 7)(3, 6) >,
    Group< a,b | [ a^4, b^8, (a^-1, b^-1)^2, (a^-1 * b^-3)^2, b * a * b^-1 * a^-2 * b * a^2 *b^-1 * a, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 1,x12 + 3*zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 6, 10, 4, 8, 9, 3)(2, 7) >,
    Group< a,b | [ a^4, b^8, (b^-1 * a)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 *a^-1, (b^-1 * a^-1)^5, a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b^-2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 4)(2, 7, 3)(6, 9, 8) >,
    Group< a,b | [ a^4, b^3, (a * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2* b^-1, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a^2 * b^-1 * a^2 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 3,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 10, 9)(2, 7, 8, 4) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^3, a^-1 * b^-2 * a^-2 * b * a^-1 * b^2 * a^2 * b, a^-1 *b^-2 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^2 * a^-1, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 4, 9, 7)(5, 8, 6, 10), (1, 5, 9, 2, 7)(3, 8, 10, 6, 4) >,
    Group< a,b | [ a^4, b^5, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^4, a^-1 * b^-2* a^-1 * b^-1 * a * b^-1 * a * b^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 2, 3, 4)(5, 8, 7, 9) >,
    Group< a,b | [ a^4, b^4, (a^-1 * b^-1)^4, (a^-1 * b * a^-1 * b^-1)^2, a^-1 * b * a^-1 * b^-2 * a *b^2 * a^-1 * b, b^-1 * a^-2 * b^-2 * a^-2 * b^-1 * a * b^-1 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom,x12 + zeta + 1,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + 4*zeta,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 2, 3, 5, 6, 8, 10, 7)(4, 9) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b * a^-1 * b^-1)^2, (a * b^-1)^4, a^-1 * b^-4 * a^-1 * b *a^2 * b, b * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b^2, b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + zeta + 4,x1 + 4*zeta,xm1 + zeta + 1,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 2, 3, 6, 5, 4, 7, 10)(8, 9) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b^-1)^4, (a^-1 * b * a^-1 * b^-1)^2, a^-1 * b^-4 * a^-1 *b^-1 * a^2 * b^-1, b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^-2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + zeta + 1,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4*zeta,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 2, 3, 8)(4, 10, 9, 6) >,
    Group< a,b | [ a^4, b^4, (a^-1 * b * a^-1 * b^-1)^2, (a * b^-1)^4, a^-1 * b^-1 * a^-1 * b^-2 * a *b^2 * a^-1 * b^-1, b^-1 * a^-2 * b^-2 * a^-2 * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta + 1,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 2, 4, 8, 6, 10, 7)(5, 9) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-1 * a^-1 * b^-1 * a^-2 * b * a^2 *b^-1 * a, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, b^-1 * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b^3 * a, b * a * b * a^-1 * b^-1 * a^-1 * b * a * b^-1 * a^-1 * b ] >,
    ideal< R |[5,xcom + 2*zeta,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 5, 10, 6, 9, 2, 4)(7, 8) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-1 * a * b^-1 * a^-2 * b * a^2 *b^-1 * a^-1, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, b^-1 * a^-2 * b^-1 * a^-2 * b^-1 * a * b^3 * a^-1, b^-1 * a * b * a^-1 * b^-1 * a^-1 * b * a * b^2 * a^-1 ] >,
    ideal< R |[5,xcom + 2*zeta,x12 + zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta,x1 + 4*zeta,xm1 + zeta + 1,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 9, 10)(2, 4, 7, 6) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^2 * a^2 * b, a^-1 * b^-2 * a^-2 * b^-1 * a * b^2 *a^2 * b^-1, b^-1 * a * b * a^-1 * b^-1 * a * b * a * b^2 * a ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 4,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + 2*zeta + 1,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 10, 8)(2, 4, 6, 5) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b^-1, a^-1 * b^-2 * a^-2 * b * a *b^2 * a^2 * b, b^-1 * a * b * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 1,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + zeta + 2,x1 + 4*zeta,xm1 + zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3)(2, 5, 4, 10, 9, 7, 8, 6) >,
    Group< a,b | [ a^4, b^8, (a * b^-2)^2, (a * b^-1 * a^-1 * b^-1)^2, b^-1 * a^-1 * b^-1 * a^-2* b * a^2 * b^-1 * a^-1, (b^-1 * a^-1 * b^-1)^3 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 4,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 2, 5)(4, 6, 7, 9) >,
    Group< a,b | [ a^4, b^4, b^-2 * a^-1 * b^2 * a^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b^-1* a^-1, b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^-2 * b * a * b * a^2 * b^-1 * a^-1, a * b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a^-1 * b * a * b^-1 ] >,ideal< R | [5,xcom + 2,x12 + 4*zeta + 3,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + zeta + 4,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 4, 9, 2, 5, 7, 6)(8, 10) >,
    Group< a,b | [ a^4, b^8, b * a^-2 * b^2 * a^2 * b, b^-2 * a^-2 * b * a^2 * b^-1, a^-1 * b^-1* a^-2 * b^-1 * a * b^4, (b^-1 * a^-1 * b^-1)^3, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b * a * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta + 3,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + zeta + 4,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 7, 10, 6, 4, 8, 9)(2, 5) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b^-2)^2, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b, b^-1* a * b^-1 * a^-2 * b * a^2 * b^-1 * a, (b * a^-1 * b)^3 ] >,
    ideal< R | [5,xcom + 2,x12 + 4,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + 4,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3)(2, 7, 4, 6, 9, 5, 8, 10) >,
    Group< a,b | [ a^4, b^8, (a * b^-2)^2, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, b^-1 * a^-2 *b * a * b^-1 * a * b * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 4,x12 + 4*zeta,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + zeta + 1,x1 + 4*zeta,xm1 + zeta + 1,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 5, 9)(2, 7, 6, 8) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a * b^-1)^4, a^-1 * b^-1 *a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b^-1, b^-1 * a^-2 * b * a^-1 * b^-1 * a^-1 * b^2 * a * b * a ] >,
    ideal< R | [5,xcom + 4,x12 + 4*zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + zeta + 2,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 8, 6)(2, 7, 10, 4) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1)^4, a * b^-1 *a^-2 * b^-1 * a * b^-1 * a^2 * b^-1, b * a^-1 * b * a * b * a^2 * b^2 * a^2 * b^-1 * a ] >,
    ideal< R | [5,xcom + 4,x12 + zeta + 1,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + 4*zeta,x1 + 4*zeta,xm1 + zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 9, 8, 4, 10, 6, 5)(2, 7) >,
    Group< a,b | [ a^4, b^8, (a^-1 * b^-2)^2, (a * b^-1)^4, (b * a^-1 * b)^3, b^-1 * a^-2 * b *a^-1 * b^-1 * a^-1 * b * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 4,x12 + zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 3,x1 + 4*zeta,xm1 + zeta + 1,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 4, 2, 9, 10, 6, 7)(5, 8) >,
    Group< a,b | [ a^4, b^8, b^-1 * a^-2 * b * a^-1 * b * a^2 * b^-1, a^-1 * b^2 * a^-1 * b^-1 *a * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 1,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + zeta + 2,x1 + 4*zeta,xm1 + zeta + 1,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 5, 9, 6)(4, 10, 7, 8), (1, 3, 7, 6, 10, 2, 9, 8)(4, 5) >,
    Group< a,b | [ a^4, b^8, b * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b, a^-1 * b^2 * a^-1 * b^-1 *a * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 4,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 2*zeta + 1,x1 + 4*zeta,xm1 + zeta + 1,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 9)(4, 7)(5, 6)(8, 10), (1, 2, 3, 4)(5, 8, 7, 9) >,
    Group< a,b | [ a^2, b^4, b^-2 * a * b^-2 * a * b^2 * a * b^2 * a * b^2 * a, (b^-1 * a * b * a)^3,(b^-1 * a)^8, a * b^-1 * a * b^-1 * a * b * a * b^-2 * a * b * a * b^2 * a * b * a * b^2 * a * b ] >,
    ideal< R | [5,xcom,x12 + zeta + 2,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4*zeta + 1,x1 + 1,xm1 + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 9)(4, 7)(5, 6)(8, 10), (1, 2, 3, 5, 6, 8, 10, 7)(4, 9) >,
    Group< a,b | [ a^2, b^8, (b^-1 * a)^4, (b^-1 * a * b * a)^3, (b^-2 * a)^5, b^-1 * a * b^-3 *a * b^-3 * a * b^-2 * a * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + 1,xm1 + 1,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 9)(4, 7)(5, 6)(8, 10), (1, 3, 2, 4, 8, 6, 10, 7)(5, 9) >,
    Group< a,b | [ a^2, b^8, (b^-2 * a)^3, a * b^2 * a * b^-2 * a * b * a * b^4 * a * b^-1, (b^-1* a)^8 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 2,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4*zeta + 1,x1 + 1,xm1 + 1,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 9)(4, 7)(5, 6)(8, 10), (1, 3)(2, 5, 4, 10, 9, 7, 8, 6) >,
    Group< a,b | [ a^2, b^8, (b * a * b)^4, b^-3 * a * b^4 * a * b^4 * a * b^-1, b * a * b^-1 * a* b * a * b^-2 * a * b * a * b^-1 * a * b * a, a * b * a * b^-2 * a * b^3 * a * b^-2 * a * b * a * b ] >,
    ideal< R | [5,xcom + 4,x12 + 4*zeta + 3,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + zeta + 4,x1 + 1,xm1 + 1,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 9)(4, 7)(5, 6)(8, 10), (1, 3)(2, 7, 4, 6, 9, 5, 8, 10) >,
    Group< a,b | [ a^2, b^8, (b^-1 * a)^4, (b * a * b)^4, b^-3 * a * b^4 * a * b^4 * a * b^-1, a* b^-3 * a * b * a * b^4 * a * b * a * b^-1 * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1 + 1,xm1 + 1,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 9)(4, 7)(5, 6)(8, 10), (1, 3, 5, 9)(2, 7, 6, 8) >,
    Group< a,b | [ a^2, b^4, b^-1 * a * b^-2 * a * b^2 * a * b^2 * a * b^-1, (b^-1 * a)^8, b^-1 * a *b^-2 * a * b^-1 * a * b^-2 * a * b * a * b^2 * a * b^-1 * a * b^2 * a, a * b^-2 * a * b^-1 * a * b^-1 * a * b^-2 * a * b * a * b * a * b^2 * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 4,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + 2*zeta + 1,x1 + 1,xm1 + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (3, 9)(4, 7)(5, 6)(8, 10), (1, 3, 4, 2, 9, 10, 6, 7)(5, 8) >,
    Group< a,b | [ a^2, b^8, (b * a * b^-1 * a)^2, b^-1 * a * b^2 * a * b^-2 * a * b^2 * a * b^-1* a, (b^-2 * a)^5 ] >,
    ideal< R | [5,xcom + 1,x12 + 4*zeta + 3,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + zeta + 4,x1 + 1,xm1 + 1,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2)(3, 4, 5, 10, 9, 7, 6, 8) >,
    Group< a,b | [ a^3, b^8, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-4 * a^-1 * b^4 * a^-1, a^-1 *b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a * b^2, b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a * b^-2 ] >,
    ideal< R | [5,xcom + 4,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1,xm1,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2)(3, 7, 5, 8, 9, 4, 6, 10) >,
    Group< a,b | [ a^3, b^8, (a * b^-1 * a^-1 * b^-1)^2, b^-4 * a^-1 * b^4 * a^-1, a^-1 * b^-2* a^-1 * b^-2 * a^-1 * b^2 * a * b^2, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b^-1 * a^-1 * b^-2 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 2,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4*zeta + 1,x1,xm1,x2 + 2*zeta + 1,xm2 + 3*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 3, 4)(5, 8, 7, 9) >,
    Group< a,b | [ a^3, b^4, (a * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2* a^-1 * b^-1, a * b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^2 * a^-1 * b^-1 * a^-1 * b^-1, a^-1 * b^-2 * a * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 2,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 3, 5, 6, 8, 10, 7)(4, 9) >,
    Group< a,b | [ a^3, b^8, (a * b^-1)^4, (b * a^-1 * b)^3, a^-1 * b^-1 * a^-1 * b^-2 * a^-1* b^4 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 3,x1,xm1,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 4, 8, 10, 6, 5, 3)(7, 9) >,
    Group< a,b | [ a^3, b^8, (a * b^-2)^2, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^4 * a * b,a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a * b * a * b ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 1,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 3*zeta + 4,x1,xm1,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 4, 6)(5, 7, 10, 9) >,
    Group< a,b | [ a^3, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a * b^-2 * a^-1 * b^-1 *a^-1 * b^-1 * a * b^2 * a^-1 * b * a^-1 * b, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 4,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 2*zeta + 1,x1,xm1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 4, 10, 8, 9, 3, 5)(6, 7) >,
    Group< a,b | [ a^3, b^8, (a^-1 * b^-1)^4, (a * b^-1)^4, a * b^2 * a^-1 * b^-1 * a^-1 * b^4* a * b^-1, b^-1 * a * b^-4 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1, (a * b^-3 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1,xm1,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 4, 9)(3, 7, 8, 6) >,
    Group< a,b | [ a^3, b^4, (a^-1 * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1,a^-1 * b^-2 * a * b^-1 * a^-1 * b^-1 * a * b^2 * a^-1 * b * a * b, a * b^-2 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + 4,x12 + 4,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 5, 10)(4, 8, 6, 9) >,
    Group< a,b | [ a^3, b^4, (a^-1 * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 *b^2 * a^-1 * b^-1, a * b^-2 * a * b * a^-1 * b^-1 * a * b^-1 * a^-1 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 1,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 5, 9, 3, 4, 7, 8)(6, 10) >,
    Group< a,b | [ a^3, b^8, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a^-1 * b * a^-1 * b^2 *a^-1 * b^4 * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4,x1,xm1,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 5, 3, 9, 10, 8, 7)(4, 6) >,
    Group< a,b | [ a^3, b^8, (a * b^-1)^4, (b * a^-1 * b)^3, b^-1 * a^-1 * b^-1 * a^-1 * b^-1* a^-1 * b^4 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 4,x1,xm1,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 5, 4)(3, 10, 7, 6) >,
    Group< a,b | [ a^3, b^4, (a * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 *b^2 * a^-1 * b^-1, a * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^2 * a * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta + 3,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 7, 3)(4, 10, 5, 9) >,
    Group< a,b | [ a^3, b^4, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-1* b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^-1 * a^-1 * b^-1, a * b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^2 * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 4,x12 + zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 1,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 7, 10, 8, 5, 6, 9)(3, 4) >,
    Group< a,b | [ a^3, b^8, (a^-1 * b^-2)^2, a^-1 * b^2 * a^-1 * b * a^-1 * b^4 * a * b^-1,a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a^-1 * b * a * b ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 4,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta + 3,x1,xm1,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 7, 5)(3, 6, 4, 8) >,
    Group< a,b | [ a^3, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a * b^-2 * a^-1 * b^-1 *a^-1 * b^-1 * a * b^2 * a^-1 * b^-1 * a^-1 * b^-1, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b * a * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 4,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4*zeta + 3,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 7, 8, 10, 3, 9, 6)(4, 5) >,
    Group< a,b | [ a^3, b^8, (a^-1 * b^-1)^4, (a * b^-1)^4, b * a^-1 * b * a^-1 * b^-1 * a^-1* b^4 * a * b, b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b^4 * a * b^-1, b * a^-1 * b^2 * a^-1 * b^-1 * a * b^2 * a * b^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta,x1,xm1,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 9, 10)(3, 5, 7, 8) >,
    Group< a,b | [ a^3, b^4, (a^-1 * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 *b^2 * a^-1 * b^-1, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^2 * a * b ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + zeta + 1,x1,xm1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (2, 3, 9)(4, 10, 5)(6, 8, 7), (1, 2, 9, 6, 5, 10, 8, 4)(3, 7) >,
    Group< a,b | [ a^3, b^8, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, b * a^-1 * b * a^-1 * b* a^-1 * b^4 * a^-1 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 4,x1,xm1,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 3)(4, 6)(5, 8)(7, 10) >,
    Group< a,b | [ a^8, b^2, (a * b * a)^4, a^-3 * b * a^4 * b * a^4 * b * a^-1, a * b * a^-1 * b* a * b * a^-2 * b * a * b * a^-1 * b * a * b, b * a * b * a^-2 * b * a^3 * b * a^-2 * b * a * b * a ] >,
    ideal< R | [5,xcom + 4,x12 + zeta + 4,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 3, 4, 5)(6, 9, 8, 10) >,
    Group< a,b | [ a^8, b^4, (a * b * a)^2, (a * b^-1)^4, (a^-2 * b)^3, b * a^-1 * b^-2 * a^3 *b^2 * a^-1 * b * a ] >,
    ideal< R | [5,xcom + 4,x12 + 4*zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 3, 5, 10)(4, 8, 9, 7) >,
    Group< a,b | [ a^8, b^4, (a * b^-1)^4, b * a * b^-2 * a^-2 * b^2 * a^-1 * b^2 * a, a^-1 *b^-2 * a^-1 * b^-1 * a^-2 * b * a * b^-1, a^-1 * b * a^-2 * b^-1 * a^4 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2,xm12 + 4,xm21 + 4,xm2m1 + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 3, 6, 7)(4, 9, 10, 8) >,
    Group< a,b | [ a^8, b^4, (a^-1 * b^-1)^4, b * a * b^-1 * a^-2 * b * a^-1 * b^2 * a^-1, a *b^-2 * a^-1 * b^-2 * a^-2 * b^2 * a * b^-1, a * b^-2 * a^-2 * b^-1 * a^4 * b * a ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + 2,xm21 + 2,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 3, 7, 8)(5, 6, 10, 9) >,
    Group< a,b | [ a^8, b^4, (b^-1 * a)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a* b * a^-1 * b^-2 * a^3 * b^-1 * a * b * a, a * b * a * b^-2 * a^2 * b * a * b^2 * a, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 3, 8, 6)(4, 7, 5, 9) >,
    Group< a,b | [ a^8, b^4, (a * b^-1 * a)^2, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, b^-1 * a^-1 *b^-2 * a^3 * b^2 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + 4,x12 + 4,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 3, 9)(4, 10, 5)(6, 8, 7) >,
    Group< a,b | [ a^8, b^3, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b^-1 * a^4 * b^-1 * a^-3,a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b^-1 * a^-1, b^-1 * a^-1 * b * a^-1 * b^-1 * a^3 * b^-1 * a * b^-1 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + 4,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 3, 10, 4)(5, 7, 9, 6) >,
    Group< a,b | [ a^8, b^4, (b^-1 * a^-1)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 *a^-1, a * b^-1 * a * b * a^3 * b^2 * a^-1 * b^-1 * a, a * b^-2 * a * b^-1 * a^2 * b^2 * a * b^-1 * a, b * a^-4 * b^-1 * a^-2 * b^2 * a^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 4, 10, 3)(5, 6, 9, 7) >,
    Group< a,b | [ a^8, b^4, (b^-1 * a)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a* b * a * b^-1 * a^3 * b^2 * a^-1 * b * a, a * b^-2 * a * b * a^2 * b^2 * a * b * a, a^-1 * b * a^-2 * b^-1 * a^4 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 3,xm12,xm21,xm2m1 + 2*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 4, 9, 8)(5, 10, 7, 6) >,
    Group< a,b | [ a^8, b^4, (a * b^-1 * a)^2, a^-1 * b * a^-1 * b^-1 * a * b^-1 * a * b^-1, a^-1* b^-1 * a^-1 * b^-2 * a * b^2 * a^-1 * b^-1, (a^-2 * b^-1)^3 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 4)(3, 5)(6, 8)(9, 10) >,
    Group< a,b | [ a^8, b^2, (a^-1 * b)^4, (a * b * a)^4, a^-3 * b * a^4 * b * a^4 * b * a^-1, b* a^-3 * b * a * b * a^4 * b * a * b * a^-1 * b * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 4, 3, 6)(5, 7, 8, 10) >,
    Group< a,b | [ a^8, b^4, (a^-1 * b^-1)^4, b^-1 * a * b^-2 * a^-2 * b^2 * a^-1 * b^2 * a, a *b^-2 * a * b^-1 * a^-1 * b * a^2 * b^-1, b * a^-4 * b^-1 * a^-2 * b^2 * a^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 4, 5, 9)(3, 7, 10, 8) >,
    Group< a,b | [ a^8, b^4, (a * b^-1)^4, b^-1 * a * b * a^-2 * b^-1 * a^-1 * b^2 * a^-1, a *b^-2 * a^-1 * b^-2 * a^-2 * b^2 * a * b, b * a^-4 * b^-1 * a^2 * b^2 * a^-2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2,xm12 + 4,xm21 + 4,xm2m1 + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 4, 6, 10)(3, 8, 7, 9) >,
    Group< a,b | [ a^8, b^4, (a * b * a)^2, a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1, a^-1 *b * a^-1 * b^-2 * a * b^2 * a^-1 * b, (a^-2 * b)^3 ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 4, 8, 5)(3, 9, 6, 7) >,
    Group< a,b | [ a^8, b^4, (b^-1 * a^-1)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1,a * b^-1 * a^-1 * b^-2 * a^3 * b * a * b^-1 * a, a * b^-1 * a * b^-2 * a^2 * b^-1 * a * b^2 * a, a * b^-2 * a^-2 * b^-1 * a^4 * b * a ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (2, 4, 7)(3, 10, 6)(5, 8, 9) >,
    Group< a,b | [ a^8, b^3, (a^-1 * b * a^-1 * b^-1)^2, a^-1 * b^-1 * a^4 * b^-1 * a^-3, a^-1* b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b^-1 * a^-1, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^3 * b * a * b^-1 * a^-1 * b * a ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta + 1,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + zeta + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 3)(4, 5, 7)(6, 10, 8) >,
    Group< a,b | [ a^8, b^3, (a^-1 * b^-1)^4, (a * b^-1)^4, a * b * a^-1 * b * a^-2 * b^-1 *a^4 * b, b * a^-4 * b^-1 * a^-1 * b^-1 * a^2 * b * a^-1, (a * b * a * b^-1 * a^2)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 3, 4)(5, 8, 7, 9) >,
    Group< a,b | [ a^8, b^4, (a^-1 * b^-1)^2, (a * b^-1)^4, (a^3 * b^-1)^3, a * b^-1 * a^2 * b^-1* a^2 * b^2 * a^-1 * b * a * b^-1 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 3, 5, 6, 8, 10, 7)(4, 9) >,
    Group< a,b | [ a^8, b^8, (b^-1 * a^-1)^3, (a * b^-1 * a^2)^2, (a^-1 * b * a^-1 *b^-1)^2, b^-1 * a^-1 * b * a^-2 * b^4 * a ] >,
    ideal< R | [5,xcom + 2,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 3, 6, 5, 4, 7, 10)(8, 9) >,
    Group< a,b | [ a^8, b^8, (b^-1 * a)^3, (a * b * a^2)^2, (a^-1 * b^-1)^4, (a^-1 * b *a^-1 * b^-1)^2, b * a^-1 * b^-1 * a^-2 * b^4 * a ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 3, 7, 6)(4, 8, 5, 9, 10) >,
    Group< a,b | [ a^8, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, a * b^2 * a^-2 * b^-1 * a *b^2, (a^-2 * b)^3 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 3, 8)(4, 10, 9, 6) >,
    Group< a,b | [ a^8, b^4, (a * b^-1)^2, (a^-1 * b^-1)^4, (a^3 * b)^3, a * b * a^2 * b * a^2 *b^2 * a^-1 * b^-1 * a * b * a ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 1,xm12 + zeta,xm21 + 4*zeta + 4,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 3, 9)(5, 10, 6, 7) >,
    Group< a,b | [ a^8, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b * a^-1 * b^-2 * a * b^2 *a^-1 * b^-1, a^-1 * b^-2 * a * b * a^2 * b^2 * a^-1 * b * a^-1, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b * a^-3 * b^-1 * a * b^2 * a * b^2 * a, a^-1 * b * a * b^-1 * a^-2 *b^2 * a * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 3, 10, 5)(4, 6, 9, 7, 8) >,
    Group< a,b | [ a^8, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, (a^-2 * b^-1)^3, b^-1 * a * b *a^-2 * b^-2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 4, 8, 10, 6, 5, 3)(7, 9) >,
    Group< a,b | [ a^8, b^8, (a * b^-1)^2, (a^-1 * b^-1)^4, (a^3 * b)^3, (a * b^3 * a^2)^2,b * a^-3 * b^-1 * a^3 * b^4 * a^2 ] >,
    ideal< R | [5,xcom + 4,x12 + 4*zeta,xm12 + 4*zeta + 4,xm21 + zeta,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 4, 6)(5, 7, 10, 9) >,
    Group< a,b | [ a^8, b^4, (b^-1 * a^-1)^3, (a * b^-1 * a^2)^2, (a * b^-1)^4, b * a^-2 * b^-2 *a^2 * b^2 * a * b^-1 * a ] >,
    ideal< R | [5,xcom + 4,x12,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 4, 10, 8, 9, 3, 5)(6, 7) >,
    Group< a,b | [ a^8, b^8, (a^-1 * b^-1)^2, (a * b^-1)^4, (a^3 * b^-1)^3, (a * b^-3 *a^2)^2, b^-1 * a^-3 * b * a^3 * b^4 * a^2 ] >,
    ideal< R | [5,xcom + 4,x12 + zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 4, 5, 8)(3, 6, 9, 10, 7) >,
    Group< a,b | [ a^8, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, b * a * b^-1 * a^-2 * b^2 * a *b, (a^-2 * b)^3 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 4, 9)(3, 7, 8, 6) >,
    Group< a,b | [ a^8, b^4, (b^-1 * a)^3, (a * b * a^2)^2, (a^-1 * b^-1)^4, b^-1 * a^-2 * b^-2 *a^2 * b^2 * a * b * a ] >,
    ideal< R | [5,xcom + 4,x12 + 4,xm12,xm21,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 4, 7)(3, 8, 5, 10) >,
    Group< a,b | [ a^8, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b^-1 * a^-1 * b^-2 * a * b^2 *a^-1 * b, a^-1 * b^-2 * a * b^-1 * a^2 * b^2 * a^-1 * b^-1 * a^-1, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b^-1 * a^-3 * b * a * b^2 * a * b^2 * a, a * b * a^-1 * b^-1 * a^-2 *b * a * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 4)(3, 9, 8)(5, 6, 10) >,
    Group< a,b | [ a^8, b^3, (a^-1 * b^-1)^4, (a * b^-1)^4, a * b^-1 * a^-1 * b^-1 * a^-2 * b* a^4 * b^-1, b * a^-4 * b^-1 * a^-2 * b * a^-1 * b * a, b^-1 * a^2 * b^-1 * a^3 * b * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 2, 4, 3, 10)(5, 9, 6, 8, 7) >,
    Group< a,b | [ a^8, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, (a^-2 * b^-1)^3, a * b^-2 *a^-2 * b * a * b^-2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3)(2, 4)(5, 7)(8, 9) >,
    Group< a,b | [ a^8, b^2, (a * b * a^-1 * b)^2, a^-1 * b * a^2 * b * a^-2 * b * a^2 * b * a^-1* b, (a^-2 * b)^5 ] >,
    ideal< R | [5,xcom + 1,x12 + 4*zeta + 1,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + zeta + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 2, 4, 8, 6, 10, 7)(5, 9) >,
    Group< a,b | [ a^8, b^8, (b^-1 * a^-1)^3, b^-2 * a^3 * b^-1 * a * b^-1, b * a^-1 * b^-2* a^2 * b * a^-1 * b * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12 + 2,xm21 + 2,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 5, 10, 6, 9, 2, 4)(7, 8) >,
    Group< a,b | [ a^8, b^8, (b^-1 * a)^3, a * b * a^3 * b^3, a^-1 * b^-1 * a^-1 * b^-1 *a^2 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 6, 8, 5)(2, 4, 9, 7, 10) >,
    Group< a,b | [ a^8, b^5, (a * b * a)^2, (a^-1, b^-1)^2, (a * b^-1)^4, a^-1 * b * a^-1 *b^-2 * a^4 * b^-2 ] >,
    ideal< R | [5,xcom + 1,x12 + zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 7, 9, 6)(2, 4, 10, 5, 8) >,
    Group< a,b | [ a^8, b^5, (a * b^-1 * a)^2, (a^-1 * b^-1)^4, (a^-1, b^-1)^2, a * b * a *b^-2 * a^4 * b^-2 ] >,
    ideal< R | [5,xcom + 1,x12 + 4,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 8, 10, 9)(2, 4, 5, 6, 7) >,
    Group< a,b | [ a^8, b^5, (a^-1 * b^-1)^4, (a^-1, b^-1)^2, (a * b^-1)^4, a^-1 * b^-1 *a^4 * b^-1 * a^-3, a * b^-2 * a^-1 * b^-1 * a^2 * b * a^-1 * b^2 * a ] >,
    ideal< R | [5,xcom + 1,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 9, 10)(2, 4, 7, 6) >,
    Group< a,b | [ a^8, b^4, (b^-1 * a^-1)^3, (b^-1 * a)^3, b * a^-1 * b^-2 * a^3 * b^2 * a^-1 *b^-1 * a ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12,xm21,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 10, 8)(2, 4, 6, 5) >,
    Group< a,b | [ a^8, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b * a^-1 * b *a^3 * b^-1 * a^-1 * b^-1 * a^-1, b^-1 * a * b^-2 * a^3 * b^2 * a * b * a, a^-1 * b^-2 * a^-1 * b^-1 * a^2 * b^2 * a * b^-1 * a^-1, b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1 * b^-1 * a,(b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3)(2, 5, 4, 10, 9, 7, 8, 6) >,
    Group< a,b | [ a^8, b^8, (a * b^-2 * a)^2, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-1 * a^-1 *b * a^3 * b * a^-1 * b^-1 * a, b * a * b * a^3 * b * a * b^2 ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 2, 5)(4, 6, 7, 9) >,
    Group< a,b | [ a^8, b^4, a * b^-2 * a^2 * b^2 * a, a^-2 * b^-2 * a * b^2 * a^-1, (a^-1 *b^-1)^4, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom,x12 + zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 4, 9, 2, 5, 7, 6)(8, 10) >,
    Group< a,b | [ a^8, b^8, (a * b^-1)^4, b * a^-1 * b^-1 * a^3 * b^-1 * a^-1 * b * a, b *a^-2 * b^-1 * a^2 * b^-2 * a^-1 * b, b * a^2 * b^-1 * a^2 * b^2 * a * b ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 6, 10)(2, 5, 8, 7) >,
    Group< a,b | [ a^8, b^4, a * b^-2 * a^-2 * b^2 * a * b, a * b * a^-1 * b^-1 * a^2 * b^-1 *a^-1 * b * a ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 4,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 2*zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 7, 10, 6, 4, 8, 9)(2, 5) >,
    Group< a,b | [ a^8, b^8, (a * b^2 * a)^2, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-3)^2,b^-1 * a * b^-1 * a^3 * b^2 * a^-1 * b^-1, b^-1 * a * b * a^3 * b * a * b^-1 * a ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 8, 4)(2, 5, 9, 10) >,
    Group< a,b | [ a^8, b^4, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b^-1)^2, a^-1 * b^-2 * a^-1 *b^-1 * a^4 * b^-1, b * a^-1 * b^-2 * a^3 * b^2 * a^-1 * b * a^-1, a * b * a * b^-1 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + zeta + 1,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 9, 6, 8)(2, 5, 10, 7, 4) >,
    Group< a,b | [ a^8, b^5, (a * b^2 * a)^2, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-1)^4, a *b^-1 * a^4 * b^-1 * a * b^-2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 10, 4, 7)(2, 5, 6, 9, 8) >,
    Group< a,b | [ a^8, b^5, (a * b^-2 * a)^2, a * b^-1 * a^4 * b^-1 * a * b^2 ] >,
    ideal<R | [5,xcom,x12 + zeta + 2,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 4*zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3)(2, 6, 8, 7, 9, 10, 4, 5) >,
    Group< a,b | [ a^8, b^8, (a * b^2 * a)^2, (a^-1 * b^-1)^4, (a * b^-1)^4, b * a^-1 *b^-1 * a^3 * b^-1 * a^-1 * b * a, b^-1 * a * b^-1 * a^3 * b^-1 * a * b^-2 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 3*zeta + 4,xm2 + 2*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 2, 6)(5, 10, 9, 8) >,
    Group< a,b | [ a^8, b^4, a * b^-2 * a^2 * b^2 * a, a^-2 * b^-2 * a * b^2 * a^-1, (a *b^-1)^4, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 4, 8)(2, 6, 9, 7) >,
    Group< a,b | [ a^8, b^4, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-1)^4, a * b^-2 * a * b^-1 * a^4 *b^-1, b^-1 * a^-1 * b^-2 * a^3 * b^2 * a^-1 * b^-1 * a^-1, a * b^-1 * a * b * a^2 * b^2 * a^2 * b ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 5, 7)(2, 6, 4, 10) >,
    Group< a,b | [ a^8, b^4, a * b^-2 * a^-2 * b^2 * a * b^-1, a * b * a^-1 * b^-1 * a^2 * b^-1 *a^-1 * b * a ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 1,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + 3*zeta + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 7, 8, 10)(2, 6, 5, 9, 4) >,
    Group< a,b | [ a^8, b^5, (a * b^2 * a)^2, a^-1 * b^-1 * a^4 * b^-1 * a^-1 * b^2 ] >,ideal< R | [5,xcom,x12 + 2*zeta + 1,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 3*zeta + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 8, 9, 2, 6, 10, 5)(4, 7) >,
    Group< a,b | [ a^8, b^8, (a^-1 * b^-1)^4, b^-1 * a^-1 * b * a^3 * b * a^-1 * b^-1 * a,b^-1 * a^-2 * b^-1 * a^2 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 9, 5, 4)(2, 6, 7, 10, 8) >,
    Group< a,b | [ a^8, b^5, (a * b^-2 * a)^2, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b^-1)^2,a^-1 * b^-1 * a^4 * b^-1 * a^-1 * b^-2 ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + 2*zeta + 1,xm21 + 3*zeta + 4,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 10, 7, 5, 8, 4, 9)(2, 6) >,
    Group< a,b | [ a^8, b^8, (a * b^-2 * a)^2, (a * b^-1 * a^-1 * b^-1)^2, (a^-1 * b^-3)^2,b * a * b^-1 * a^3 * b^-1 * a * b * a, a^-1 * b^-2 * a^3 * b * a * b^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3)(2, 7, 4, 6, 9, 5, 8, 10) >,
    Group< a,b | [ a^8, b^8, (a * b * a^2)^2, (a * b^-2 * a)^2, (a^-1 * b * a^-1 * b^-1)^2,b^-1 * a^-1 * b^-1 * a^3 * b^-1 * a^-1 * b^-2, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-3 * a ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 2, 7, 8)(4, 9, 10, 5, 6) >,
    Group< a,b | [ a^8, b^5, b * a^-1 * b * a^2 * b^2 * a^-1, (a^-1 * b^-1)^4, (a^-2 * b)^3] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 4)(2, 7, 5)(6, 10, 9) >,
    Group< a,b | [ a^8, b^3, (a * b^-1)^4, (a^-2 * b)^3, a^-1 * b^-1 * a^-1 * b^-1 * a^-2 *b^-1 * a^4 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 5, 9)(2, 7, 6, 8) >,
    Group< a,b | [ a^8, b^4, (a * b^-1)^2, a^-1 * b * a * b^-2 * a^2 * b^2 * a * b * a^-1, (b^-1 *a^-1)^5, a^-2 * b^-1 * a^-1 * b^-1 * a^3 * b^-1 * a^-1 * b^-1 * a^-2 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta,xm12 + 4*zeta + 4,xm21 + zeta,xm2m1 + 3*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 6, 2, 7)(4, 5, 10, 8, 9) >,
    Group< a,b | [ a^8, b^5, a^-1 * b^-2 * a^2 * b^-1 * a^-1 * b^-1, (a * b^-1)^4, (a^-2 *b^-1)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + zeta + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 8, 6)(2, 7, 10, 4) >,
    Group< a,b | [ a^8, b^4, (a^-1 * b^-1)^2, a^-1 * b^-1 * a * b^-2 * a^2 * b^2 * a * b^-1 *a^-1, (b^-1 * a)^5, a^-2 * b * a^-1 * b * a^3 * b * a^-1 * b * a^-2 * b ] >,
    ideal< R | [5,xcom,x12 + 1,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 9, 8, 4, 10, 6, 5)(2, 7) >,
    Group< a,b | [ a^8, b^8, (a * b^-1 * a^2)^2, (a * b^2 * a)^2, (a^-1 * b * a^-1 *b^-1)^2, b * a^-1 * b * a^3 * b * a^-1 * b^2, b^-3 * a^-1 * b^-1 * a * b^-1 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 10)(2, 7, 9)(4, 8, 5) >,
    Group< a,b | [ a^8, b^3, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, a^-2 * b * a^-1 * b * a^-1 * b* a^4 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3)(2, 9)(5, 6)(7, 10) >,
    Group< a,b | [ a^8, b^2, (a^-2 * b)^3, b * a^2 * b * a^-2 * b * a * b * a^4 * b * a^-1, (a^-1* b)^8 ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta + 3,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + zeta + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta,xm2 + 4*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 2, 9)(4, 10, 8, 7) >,
    Group< a,b | [ a^8, b^4, a * b^-2 * a^2 * b^2 * a, a^-2 * b^-2 * a * b^2 * a^-1, a^-1 * b^-2* a^-1 * b^-1 * a * b^2 * a * b^-1, a^-2 * b^-1 * a^-2 * b * a^2 * b, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a * b * a^-1 * b^-1 ] >,
    ideal< R |[5,xcom + 2,x12 + zeta + 2,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 4, 2, 9, 10, 6, 7)(5, 8) >,
    Group< a,b | [ a^8, b^8, (a^-1 * b^-1)^2, (b^-1 * a)^3, (a * b^-3 * a^2)^2, b * a^-3 *b * a^4 * b * a^-3 * b ] >,
    ideal< R | [5,xcom + 2,x12 + zeta,xm12,xm21,xm2m1 + 4*zeta + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 5)(2, 9, 6)(4, 8, 10) >,
    Group< a,b | [ a^8, b^3, (a * b * a)^2, a * b^-1 * a^2 * b^-1 * a^-3 * b^-1 * a^2 * b^-1,a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 4,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 4*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 6)(2, 9, 5)(4, 7, 8) >,
    Group< a,b | [ a^8, b^3, (a * b^-1 * a)^2, a * b^-1 * a^-2 * b^-1 * a^-3 * b * a^2 * b,a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 1,xm12 + 2*zeta + 1,xm21 + 3*zeta + 4,xm2m1 + 3*zeta + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 7, 6, 10, 2, 9, 8)(4, 5) >,
    Group< a,b | [ a^8, b^8, (b^-1 * a^-1)^3, (a * b * a^2)^2, (a * b^-3)^2, a * b^-1 * a^4* b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + 2,x12,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 8, 2, 9, 7, 5, 10)(4, 6) >,
    Group< a,b | [ a^8, b^8, (a * b^-1)^2, (b^-1 * a^-1)^3, (a * b^3 * a^2)^2, b^-1 * a^-3* b^-1 * a^4 * b^-1 * a^-3 * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12,xm12 + zeta,xm21 + 4*zeta + 4,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 3, 10, 5, 7, 2, 9, 4)(6, 8) >,
    Group< a,b | [ a^8, b^8, (b^-1 * a)^3, (a * b^-1 * a^2)^2, (a^-1 * b^-3)^2, a^-1 * b^-1* a^4 * b^2 * a * b ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta,xm12,xm21,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 10, 2, 3)(5, 6, 7, 9, 8) >,
    Group< a,b | [ a^8, b^5, a^-1 * b^2 * a^2 * b * a^-1 * b, (a^-1 * b^-1)^4, (a^-2 * b)^3] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 7, 6, 9, 5, 10, 8)(2, 3) >,
    Group< a,b | [ a^8, b^8, (a * b^-1)^2, b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b, (b^-1 *a^-1)^5, b * a^-2 * b^-1 * a^3 * b^-1 * a^-2 * b^2 ] >,
    ideal< R | [5,xcom + 1,x12 + 2*zeta,xm12 + 1,xm21 + 1,xm2m1 + 3*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 6, 10)(2, 3, 5, 9) >,
    Group< a,b | [ a^8, b^4, (a * b * a^2)^2, (a^-1, b^-1)^2, a * b * a^-1 * b^-2 * a * b^2 *a^-1 * b, a * b^-2 * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b^2 * a, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 1,x12 + 2*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 3,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 2, 3, 6)(5, 8, 10, 9, 7) >,
    Group< a,b | [ a^8, b^5, b^-1 * a^-1 * b^-1 * a^2 * b^-2 * a^-1, (a * b^-1)^4, (a^-2 *b^-1)^3 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + zeta + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 5)(2, 3, 7)(6, 8, 9) >,
    Group< a,b | [ a^8, b^3, (a * b^-1)^4, (a^-2 * b)^3, a^-2 * b^-1 * a^-1 * b^-1 * a^-1 *b^-1 * a^4 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 9)(2, 3, 8)(5, 7, 10) >,
    Group< a,b | [ a^8, b^3, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, a^-1 * b * a^-1 * b * a^-2 * b* a^4 * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 1,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4)(2, 3, 9, 10, 7, 8, 6, 5) >,
    Group< a,b | [ a^8, b^8, (a^-1 * b^-1)^2, b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1,(b^-1 * a)^5, b^-1 * a^-2 * b * a^3 * b * a^-2 * b^-2 ] >,
    ideal< R | [5,xcom + 1,x12 + 4*zeta + 4,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 3*zeta + 4,xm2 + 2*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 8, 7)(2, 3, 10, 6) >,
    Group< a,b | [ a^8, b^4, (a * b^-1 * a^2)^2, (a^-1, b^-1)^2, a * b^-1 * a^-1 * b^-2 * a * b^2* a^-1 * b^-1, a * b^-2 * a^-1 * b * a^2 * b * a^-1 * b^2 * a, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 1,x12 + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 7, 3)(2, 6, 5, 8) >,
    Group< a,b | [ a^8, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^-1 *b^-1 * a^3 * b * a^-1 * b * a^-1, b * a * b^-2 * a^3 * b^2 * a * b^-1 * a, a * b^-1 * a^-1 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a^-1 * b^-2 * a^-1 * b * a^2 * b^2 * a * b * a^-1,(b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12 + 2,xm21 + 2,xm2m1 + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 8, 9, 10)(2, 6, 7, 5, 3) >,
    Group< a,b | [ a^8, b^5, (a * b * a)^2, a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1, a* b^-1 * a * b^-2 * a^4 * b^-2 ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 4,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4)(2, 6)(5, 10)(7, 9) >,
    Group< a,b | [ a^8, b^2, (a^-1 * b)^4, (a^-1 * b * a * b)^3, (a^-2 * b)^5, a^-1 * b * a^-3 *b * a^-3 * b * a^-2 * b * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom,x12 + zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta,xm2 + 4*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 2, 6, 9, 8, 3, 5)(7, 10) >,
    Group< a,b | [ a^8, b^8, (b^-1 * a)^3, b^2 * a^3 * b * a * b, b^-1 * a^-1 * b^2 * a^2 *b^2 * a^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 9, 3, 7)(2, 6, 10, 8, 5) >,
    Group< a,b | [ a^8, b^5, (a * b^-1 * a^-1 * b^-1)^2, (a^-1 * b * a^-1 * b^-1)^2, a^-1 *b^-1 * a^4 * b^-1 * a^-3, b * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b^-2 * a * b * a ] >,
    ideal< R | [5,xcom,x12 + zeta + 2,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + 4*zeta + 1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 10, 3, 8, 7, 2, 6)(5, 9) >,
    Group< a,b | [ a^8, b^8, (b^-1 * a^-1)^3, a * b^-1 * a^3 * b^-3, a^2 * b^-2 * a^2 *b^-2 * a^-1 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 3, 9)(2, 6, 8, 10) >,
    Group< a,b | [ a^8, b^4, (b^-1 * a^-1)^3, (b^-1 * a)^3, b^-1 * a^-1 * b^-2 * a^3 * b^2 * a^-1* b * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12,xm21,xm2m1,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2)(3, 4, 5, 10, 9, 7, 6, 8), (1, 4, 5, 7, 8)(2, 6, 3, 10, 9) >,
    Group< a,b | [ a^8, b^5, (a * b^-1 * a)^2, a^-1 * b * a^-1 * b^-1 * a * b^-1 * a *b^-1, a^-1 * b^-1 * a^-1 * b^-2 * a^4 * b^-2 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 2,x1 + zeta + 4,xm1 + 4*zeta + 3,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (3, 4, 9, 7)(5, 8, 6, 10) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, b * a^2 * b^-1 * a^2 * b^-1 * a * b * a^-1, b^-1 *a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 1,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (3, 7, 9, 4)(5, 10, 6, 8) >,
    Group< a,b | [ a^5, b^4, (a * b^-1)^4, a * b^-1 * a^-1 * b^-1 * a^2 * b * a^2 * b, b^-1 * a^2* b^-2 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 4,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (3, 8, 9, 10)(4, 5, 7, 6) >,
    Group< a,b | [ a^5, b^4, (a * b^-1)^4, (a * b * a^-1 * b^-1 * a)^2, b * a^2 * b * a^2 * b^-1* a^-1 * b^-1 * a, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 1,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (3, 10, 9, 8)(4, 6, 7, 5) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, b^-1 * a^2 * b^-1 * a^2 * b * a^-1 * b * a, b^-1 *a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4,xm12 + 2*zeta + 1,xm21 + 3*zeta + 4,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 3, 7, 8)(5, 6, 10, 9) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b^-1 * a^-1 * b^-2 * a * b^2 *a^-1 * b, a^-1 * b^-2 * a * b^-1 * a^2 * b^2 * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 3, 10, 4)(5, 7, 9, 6) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b * a^-1 * b^-1)^2, (a * b^-1)^4, a^-1 * b^-1 * a^-1 * b^-2* a * b^2 * a^-1 * b^-1, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 4, 10, 3)(5, 6, 9, 7) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, (a^-1 * b * a^-1 * b^-1)^2, a^-1 * b * a^-1 * b^-2* a * b^2 * a^-1 * b, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 4, 3, 6)(5, 7, 8, 10) >,
    Group< a,b | [ a^5, b^4, b * a^-1 * b * a^-2 * b^-1 * a^-1 * b^-1 * a, a^-1 * b^-2 * a^-1 * b* a^2 * b^2 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta + 1,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + 3*zeta + 4,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 5, 9, 7)(4, 6, 8, 10) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a * b^-1)^4, b *a^-2 * b^-1 * a^2 * b^-1 * a * b * a ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 1,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 5, 8, 4)(3, 7, 6, 9) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b * a^-1 * b^-2 * a * b^2 *a^-1 * b^-1, (a * b * a^-1 * b^-1 * a)^2, a^-1 * b^-2 * a * b * a^2 * b^2 * a^-1 * b * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 5, 7, 10)(3, 9, 8, 6) >,
    Group< a,b | [ a^5, b^4, (a^-1, b^-1)^2, a * b * a^-1 * b^-2 * a * b^2 * a^-1 * b, a * b^-2 *a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b^2 * a ] >,
    ideal< R | [5,xcom + 1,x12 + 4*zeta + 3,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + zeta + 4,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 6, 9, 10)(4, 7, 8, 5) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a * b^-1)^4, a^-1 *b^-1 * a^-1 * b^-1 * a^2 * b * a^-2 * b ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + zeta + 4,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 6, 3, 4)(5, 10, 8, 7) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^-1 * b^-1 * a^-2 * b * a^-1 * b * a, a^-1 * b^-2 * a^-1 *b^-1 * a^2 * b^2 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta + 3,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + zeta + 4,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 7, 9, 5)(4, 10, 8, 6) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1)^4, b^-1* a^-2 * b^-1 * a^2 * b * a^-1 * b * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 7, 8, 9)(3, 4, 6, 5) >,
    Group< a,b | [ a^5, b^4, (a^-1, b^-1)^2, a * b^-1 * a^-1 * b^-2 * a * b^2 * a^-1 * b^-1, a *b^-2 * a^-1 * b * a^2 * b * a^-1 * b^2 * a ] >,
    ideal< R | [5,xcom + 1,x12 + 2*zeta + 1,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + 3*zeta + 4,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 8, 6, 9)(3, 10, 7, 4) >,
    Group< a,b | [ a^5, b^4, b^-2 * a^-1 * b^2 * a^-1, a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a *b * a^-1 * b * a^-1 * b, a^-2 * b^-1 * a^-2 * b^-1 * a^-2 * b * a * b * a * b * a * b ] >,
    ideal< R | [5,xcom,x12 + zeta + 4,xm12 + zeta + 4,xm21 + 4*zeta + 3,xm2m1 + 4*zeta + 3,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (2, 9, 4, 10)(3, 6, 5, 8) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1)^4, (a *b * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2)(3, 4, 5, 10, 9, 7, 6, 8) >,
    Group< a,b | [ a^5, b^8, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 * a *b^2, (b * a^-1 * b)^3 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2)(3, 7, 5, 8, 9, 4, 6, 10) >,
    Group< a,b | [ a^5, b^8, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-2 * b^-1 * a^-2 * b^2 * a *b^-1, (b * a^-1 * b)^3 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 2*zeta + 1,xm2 + 3*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2)(3, 8, 6, 7, 9, 10, 5, 4) >,
    Group< a,b | [ a^5, b^8, (a^-1 * b^-1)^4, (a * b^-1)^4, a * b^-2 * a^-2 * b * a^-2 * b,(b^-1 * a^-1 * b^-1)^3 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2)(3, 10, 6, 4, 9, 8, 5, 7) >,
    Group< a,b | [ a^5, b^8, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-2 * b * a^-2 * b^-2 * a * b,(b^-1 * a^-1 * b^-1)^3 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2, 3, 5, 6, 8, 10, 7)(4, 9) >,
    Group< a,b | [ a^5, b^8, b * a * b * a^2 * b^-2 * a, (a * b^-1)^4, (b^-1 * a^-1 *b^-1)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 4,x1 + 2,xm1 + 2,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2, 3, 6, 5, 4, 7, 10)(8, 9) >,
    Group< a,b | [ a^5, b^8, a * b^-2 * a^2 * b * a * b, (a * b^-1)^4, (b^-1 * a^-1 *b^-1)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 1,x1 + 2,xm1 + 2,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2, 4, 8, 10, 6, 5, 3)(7, 9) >,
    Group< a,b | [ a^5, b^8, (a^-1 * b^-2)^2, (a^-1, b^-1)^2, (a * b^-1)^4, a * b * a^-1 *b * a^2 * b^4 * a ] >,
    ideal< R | [5,xcom + 1,x12 + zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2, 5, 9, 3, 4, 7, 8)(6, 10) >,
    Group< a,b | [ a^5, b^8, (a * b^-2)^2, (a * b^-1 * a^-1 * b^-1)^2, a * b * a * b * a^2* b^4 * a ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 4,x1 + 2,xm1 + 2,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2, 5, 3, 9, 10, 8, 7)(4, 6) >,
    Group< a,b | [ a^5, b^8, (a * b^2 * a)^2, (a^-1 * b * a^-1 * b^-1)^2, (a * b^-1)^4, b *a^-2 * b * a^-1 * b^4 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 4,x1 + 2,xm1 + 2,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 2, 9, 5, 6, 7, 4, 8)(3, 10) >,
    Group< a,b | [ a^5, b^8, (a^-1 * b^-1)^4, (a^-1, b^-1)^2, (a * b^-1)^4, b^-4 * a^-1 *b^4 * a^-1, a^2 * b^-1 * a^-1 * b^-1 * a^2 * b^2 * a^-1 * b^2 ] >,
    ideal< R | [5,xcom + 1,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 2*zeta + 1,xm2 + 3*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 3, 5, 6, 10, 8, 4, 2)(7, 9) >,
    Group< a,b | [ a^5, b^8, (a * b^-2)^2, (a^-1 * b^-1)^4, (a^-1, b^-1)^2, a * b^-1 * a^-1* b^-1 * a^2 * b^4 * a ] >,
    ideal< R | [5,xcom + 1,x12 + 4*zeta,xm12 + 4*zeta + 1,xm21 + zeta + 2,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 3, 5, 10, 6, 9, 2, 4)(7, 8) >,
    Group< a,b | [ a^5, b^8, (a * b^-2 * a)^2, b * a^2 * b * a^-1 * b^4 * a^-1 ] >,
    ideal<R | [5,xcom,x12 + zeta + 4,xm12 + 2*zeta + 1,xm21 + 3*zeta + 4,xm2m1 + 4*zeta + 3,x1 + 2,xm1 + 2,x2 + zeta + 4,xm2 + 4*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 3)(2, 5, 4, 10, 9, 7, 8, 6) >,
    Group< a,b | [ a^5, b^8, a * b^2 * a^2 * b^-1 * a * b^-1, (a^-1 * b^-1)^4, (b * a^-1 *b)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 4*zeta + 3,xm2 + zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 3, 8, 9, 2, 6, 10, 5)(4, 7) >,
    Group< a,b | [ a^5, b^8, (a * b^-1 * a^-1 * b^-1)^2, (a^-1 * b * a^-1 * b^-1)^2, b^-4 *a^-1 * b^4 * a^-1, b * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 4,xm12 + 3*zeta + 4,xm21 + 2*zeta + 1,xm2m1 + 2*zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 3, 10, 7, 5, 8, 4, 9)(2, 6) >,
    Group< a,b | [ a^5, b^8, b^-1 * a * b^-1 * a^2 * b^2 * a, (a^-1 * b^-1)^4, (b * a^-1 *b)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + 4*zeta + 3,xm21 + zeta + 4,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 4)(2, 5, 6, 8, 7, 10, 9, 3) >,
    Group< a,b | [ a^5, b^8, (a^-1 * b^-2)^2, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b,a * b^-1 * a * b^-1 * a^2 * b^4 * a ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 4*zeta + 1,xm2 + zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 4, 7, 9, 6, 3, 8, 10)(2, 5) >,
    Group< a,b | [ a^5, b^8, (a * b^2 * a)^2, b^-1 * a^2 * b^-1 * a^-1 * b^4 * a^-1 ] >,ideal< R | [5,xcom,x12 + 4*zeta + 1,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + zeta + 2,x1 + 2,xm1 + 2,x2 + zeta + 2,xm2 + 4*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 10 | (1, 2, 3, 7, 6)(4, 8, 5, 9, 10), (1, 4, 6, 7, 2, 10, 5, 8)(3, 9) >,
    Group< a,b | [ a^5, b^8, (a * b^-2 * a)^2, (a^-1 * b^-1)^4, (a^-1 * b * a^-1 * b^-1)^2,b^-1 * a^-2 * b^-1 * a^-1 * b^4 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + zeta + 2,xm21 + 4*zeta + 1,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 3*zeta + 4,xm2 + 2*zeta + 1,zeta^2 + zeta + 1] >
>
];

