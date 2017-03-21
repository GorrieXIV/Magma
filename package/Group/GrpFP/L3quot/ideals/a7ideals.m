freeze;

import "../l3.m": R, x1, xm1, x2, xm2, x12, xm12, xm21, xm2m1, xcom, zeta;

a7presentations := [
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 3, 4, 5) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b * a^-1 * b^-1)^2, (a^-1 * b^-1 * a * b^-1)^3, (a^-1 * b^2 * a^-1 * b^-2)^2 ] >,
    ideal< R |[5,xcom,x12 + 2*zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 3*zeta + 1,x1,xm1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 3, 4, 5, 6, 7) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b * a^-1 * b^-1)^2, (b^-1 * a^-1 * b^-1)^3, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 3,x1,xm1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 3, 4, 5, 7, 6) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b * a^-1 * b^-1)^2, (b * a^-1 * b)^3, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta + 3,x1,xm1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 3, 5)(4, 6) >,
    Group< a,b | [ a^3, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-1 * b^-2 * a * b * a^-1 * b^-1 * a^-1 *b^2 * a * b^-1 * a * b, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + zeta + 3,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 3, 5, 4, 6, 7) >,
    Group< a,b | [ a^3, b^7, (a * b^-1)^4, (a * b^-2)^4, (b^-1 * a^-1)^7, a^-1 * b^-2 * a * b^-1 * a^-1 * b^-1 * a * b * a *b * a^-1 * b^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 4,x1,xm1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 3, 5, 7, 4, 6) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-1)^4, (a^-1 * b^-2)^4, a^-1 * b^-1 * a * b^-2 * a^-1 * b^-1 * a * b^2 * a^-1 * b^3,b^-3 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^2 * a ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4,x1,xm1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 3, 5)(4, 7) >,
    Group< a,b | [ a^3, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-2 * a^-1 * b * a^-1 * b^-1 * a * b^2 *a^-1 * b^-1 * a * b, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 4*zeta + 2,x1,xm1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 3, 5, 4, 7, 6) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-1)^4, (a^-1 * b^-2)^4, b^2 * a^-1 * b^-2 * a^-1 * b^-1 * a * b^-1 * a * b * a^-1 * b* a ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta,x1,xm1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 3, 5, 6, 4, 7) >,
    Group< a,b | [ a^3, b^7, (a * b^-1)^4, (a * b^-2)^4, (b^-1 * a^-1)^7, b * a * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-2 *a * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 1,x1,xm1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 5)(3, 4, 6) >,
    Group< a,b | [ a^3, b^3, (b^-1 * a^-1)^7, (b^-1 * a)^7, a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a *b * a * b^-1 * a * b^-1, a^-1 * b * a * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b * a * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4*zeta + 2,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 5, 3, 4, 6, 7) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a)^3, a^-1 * b^2 * a^-1 * b^-2 * a * b^2 * a * b^-2, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 2,xm12,xm21,xm2m1 + 2*zeta + 4,x1,xm1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 5, 7, 3, 4, 6) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1)^3, a^-1 * b^2 * a^-1 * b^-2 * a * b^2 * a * b^-2, b^-1 * a * b^-1 * a^-1 * b *a^-1 * b^-1 * a * b^-3 * a^-1 * b^-2 ] >,
    ideal< R | [5,xcom + 2,x12,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1,x1,xm1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 5)(3, 6)(4, 7) >,
    Group< a,b | [ a^3, b^6, a^-1 * b * a^-1 * b^-1 * a * b * a * b^-1, (a * b^-2 * a^-1 * b^-2)^2, (a^-1 * b^2 * a^-1 *b^-2)^2, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + zeta + 3,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 5, 3, 6, 4, 7) >,
    Group< a,b | [ a^3, b^7, a^-1 * b * a^-1 * b^-1 * a * b * a * b^-1, (a * b^-1)^6, (a^-1 * b^2 * a^-1 * b^-2)^2 ] >,ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + zeta + 3,x1,xm1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (5, 6, 7), (1, 2, 5, 4, 7, 3, 6) >,
    Group< a,b | [ a^3, b^7, a^-1 * b * a^-1 * b^-1 * a * b * a * b^-1, (a^-1 * b^-1)^6, (a^-1 * b^2 * a^-1 * b^-2)^2 ] >,ideal< R | [5,xcom,x12 + 3*zeta,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta + 2,x1,xm1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 3, 4)(5, 6) >,
    Group< a,b | [ a^2, b^4, b^-1 * a * b^-2 * a * b^-2 * a * b^2 * a * b^2 * a * b^2 * a * b^-1, (a * b^-1)^7, b^-1 * a *b^-2 * a * b^-1 * a * b^-2 * a * b^-1 * a * b^2 * a * b^-1 * a * b^2 * a, a * b^-2 * a * b * a * b^-1 * a * b^-2 * a * b * a * b^-1 * a * b^2 * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 4,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta + 2,x1 + 1,xm1 + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 3, 4, 5, 6, 7) >,
    Group< a,b | [ a^2, b^7, (a * b^-1)^5, (b * a * b^-2 * a * b)^2, (a * b^3 * a * b^-1)^3 ] >,
    ideal< R | [5,xcom + 2,x12 + 2,xm12 + 2,xm21 + 2,xm2m1 + 2,x1 + 1,xm1 + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 3, 4, 6, 7, 5) >,
    Group< a,b | [ a^2, b^7, (b^-1 * a)^4, (b * a * b^2)^4, (b^-1 * a * b^2 * a * b^-1)^3, b^-1 * a * b^-2 * a * b * a *b^-1 * a * b^-2 * a * b^2 * a * b * a * b^-1 * a * b * a ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1 + 1,xm1 + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 3, 4, 6) >,
    Group< a,b | [ a^2, b^5, (a * b^-1)^7, (b * a * b * a * b^-1 * a * b^-1 * a)^2, (b^-1 * a * b^2 * a * b^-1)^3, b * a * b^2* a * b^-2 * a * b^-2 * a * b^2 * a * b * a * b^2 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta + 1,x1 + 1,xm1 + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 3, 4, 6, 5, 7) >,
    Group< a,b | [ a^2, b^7, (b^-1 * a * b * a)^3, (b * a * b^-1 * a * b^-1 * a * b)^2, (a * b^-1)^7, (b^-2 * a)^5 ] >,ideal< R | [5,xcom,x12 + zeta + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 1,xm1 + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 4, 6, 3, 5, 7) >,
    Group< a,b | [ a^2, b^7, (b * a * b^-1 * a)^2, (a * b^-1)^7, (b * a * b)^6 ] >,
    ideal< R | [5,xcom + 1,x12 + 2*zeta + 4,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta + 2,x1 + 1,xm1 + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 4)(3, 6)(5, 7) >,
    Group< a,b | [ a^2, b^6, (b * a * b)^4, (b^-1 * a * b * a)^3, (a * b^-1)^7, a * b^2 * a * b^-3 * a * b^-1 * a * b^-1* a * b^3 * a * b * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 4,x1 + 1,xm1 + 1,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 4, 3, 6) >,
    Group< a,b | [ a^2, b^5, (b^-1 * a * b * a)^3, (a * b^-1)^7, b^-1 * a * b^2 * a * b^-1 * a * b^2 * a * b^-1 * a * b * a * b* a ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta + 1,x1 + 1,xm1 + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 4, 5, 3, 6, 7) >,
    Group< a,b | [ a^2, b^7, (a * b^-1)^5, (b^-1 * a * b * a)^3, (a * b^-2 * a * b)^3 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta,x1 + 1,xm1 + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 2, 4, 7, 3, 6, 5) >,
    Group< a,b | [ a^2, b^7, (b * a * b)^4, (b^-1 * a)^6, (b^-1 * a * b * a)^3, a * b^-2 * a * b * a * b * a * b^-3 * a *b * a * b * a * b^-1 * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3*zeta,x1 + 1,xm1 + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 4)(2, 5, 3, 6) >,
    Group< a,b | [ a^2, b^4, b^-1 * a * b^-2 * a * b^2 * a * b^2 * a * b^-1, (a * b^-1)^7, (b * a * b^-1 * a)^6, b^-1 * a *b^-2 * a * b^-1 * a * b^-2 * a * b^-1 * a * b^-2 * a * b * a * b^2 * a * b * a * b^2 * a * b^-1 * a * b^2 * a, a * b * a * b^-1 * a * b * a * b * a * b^-1 * a * b^-1 * a * b * a *b^-1 * a * b * a * b * a * b^2 * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 1,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta + 3,x1 + 1,xm1 + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 4)(2, 5, 7)(3, 6) >,
    Group< a,b | [ a^2, b^6, b^-1 * a * b^-3 * a * b^3 * a * b^-2, (a * b^-1)^7, (b^-2 * a)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 1,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta + 3,x1 + 1,xm1 + 1,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 4, 2, 5, 3, 6, 7) >,
    Group< a,b | [ a^2, b^7, (b^-1 * a)^4, (b * a * b)^4, b * a * b^-1 * a * b * a * b^-2 * a * b^-3 * a * b * a * b^-1 *a * b^2 * a * b^-2 * a ] >,
    ideal< R | [5,xcom + 3,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + 1,xm1 + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 4, 2, 5, 7, 3, 6) >,
    Group< a,b | [ a^2, b^7, (b^-1 * a)^6, (b^-2 * a)^5, (a * b^-2 * a * b^-1)^3 ] >,
    ideal< R | [5,xcom + 3,x12 + 3,xm12 + 3,xm21 + 3,xm2m1 + 3,x1 + 1,xm1 + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (4, 5)(6, 7), (1, 4, 3, 6, 2, 5, 7) >,
    Group< a,b | [ a^2, b^7, (a * b^-1)^7, (a * b^-2 * a * b)^3, b^-2 * a * b^-2 * a * b^-3 * a * b * a * b^-1 * a * b *a * b^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 4*zeta + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + zeta + 3,x1 + 1,xm1 + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3) >,
    Group< a,b | [ a^5, b^3, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-1 * a^-2 * b^-1 * a)^2, (a^-1 * b^-1 * a^-1 * b)^3 ] >,
    ideal< R| [5,xcom,x12 + 2*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(5, 6, 7) >,
    Group< a,b | [ a^5, b^3, (a * b * a * b^-1 * a)^2, (b^-1 * a)^5, (a * b * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(5, 7, 6) >,
    Group< a,b | [ a^5, b^3, (a * b^-1 * a * b * a)^2, (b^-1 * a^-1)^5, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(4, 5)(6, 7) >,
    Group< a,b | [ a^5, b^6, (a^-1 * b * a^-1 * b^-1)^2, (b^-1 * a^-1)^5, a^-1 * b^-2 * a^-1 * b^-1 * a * b^-2 * a *b^-1 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 2,xm21 + 2,xm2m1 + 2,x1 + 2,xm1 + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(4, 5, 6) >,
    Group< a,b | [ a^5, b^3, (a * b^-1 * a * b * a)^2, (b^-1 * a)^5, (a * b * a)^4 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(4, 5, 7) >,
    Group< a,b | [ a^5, b^3, (a * b^-1)^4, (a * b * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(4, 6, 5) >,
    Group< a,b | [ a^5, b^3, (a * b * a * b^-1 * a)^2, (b^-1 * a^-1)^5, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(4, 6, 7) >,
    Group< a,b | [ a^5, b^3, (a * b^-1)^4, (a * b^-1 * a^-1 * b * a)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(4, 6)(5, 7) >,
    Group< a,b | [ a^5, b^6, (a^-1, b^-1)^2, (a^-1 * b^-2 * a^-1 * b^-1)^2, (a * b^-2 * a * b^-1)^2, (a * b * a^2 *b^-1 * a)^2, a^-1 * b^2 * a * b^-1 * a^2 * b^2 * a^-2 * b^-1, b^-2 * a^-2 * b^-1 * a^-2 * b^-2 * a * b^2 * a ] >,
    ideal< R | [5,xcom + 1,x12 + 3*zeta + 1,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(4, 7, 5) >,
    Group< a,b | [ a^5, b^3, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b * a)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 1,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(4, 7, 6) >,
    Group< a,b | [ a^5, b^3, (a^-1 * b^-1)^4, (a * b * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3)(4, 7)(5, 6) >,
    Group< a,b | [ a^5, b^6, b^-3 * a^-1 * b^3 * a^-1, (a^-1 * b^-1)^4, (a * b^-1 * a)^4, (a, b)^3, b^-2 * a * b^-1 *a^-1 * b^-1 * a^-2 * b^-1 * a * b^-1 * a^-2 * b * a ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4)(6, 7) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a^-1)^3, a^-1 * b * a^-1 * b^-1 * a^2 * b^2 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4)(5, 6) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a^-1)^3, a^-1 * b^-1 * a * b * a^3 * b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 2,xm21 + 2,xm2m1,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4)(5, 7) >,
    Group< a,b | [ a^5, b^4, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^-1, (a * b^-1)^4, (a * b^-1 * a)^4, (a * b* a)^4, a * b^-2 * a^2 * b^-2 * a^2 * b^2 * a * b^-1 * a^-1 * b^-1, a^-1 * b^-2 * a^2 * b^-1 * a^-2 * b^2 * a^-1 * b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4, 5) >,
    Group< a,b | [ a^5, b^5, (a^-1, b^-1)^2, (b^-1 * a)^5, (a * b * a^2 * b^-1 * a)^2, a * b^2 * a * b^-1 * a^2 * b^2 * a^2* b^-1 ] >,
    ideal< R | [5,xcom + 1,x12 + 3*zeta + 1,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4, 5, 6, 7) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a)^3, (a * b^-2 * a)^2, (a * b * a * b * a)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12,xm21,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4, 5, 7, 6) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, (a^-2 * b)^3, (a * b * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 1,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4, 6, 7, 5) >,
    Group< a,b | [ a^5, b^7, (a^-2 * b^-1)^3, b^-1 * a * b * a^-2 * b^2 * a^-1 * b^-1, (a * b * a^-1 * b^-1 * a)^2 ]>,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4, 6) >,
    Group< a,b | [ a^5, b^5, (a * b^-1)^4, (a^-2 * b)^3, (a * b^-1 * a^-1 * b * a)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4, 6, 5, 7) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a * b * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4, 7, 6, 5) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, (a^-2 * b^-1)^3, (a * b^-1 * a * b * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4, 7) >,
    Group< a,b | [ a^5, b^5, (b^-1 * a)^3, b * a^-1 * b^2 * a^2 * b^-1 * a * b * a, (a * b * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 1,xm12,xm21,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 4, 7, 5, 6) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b * a^-1 * b^-1)^2, (b * a^-1 * b)^3, (a * b^-3 * a)^2 ] >,
    ideal< R | [5,xcom,x12 + zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5, 4) >,
    Group< a,b | [ a^5, b^5, (b^-1 * a^-1)^3, (a * b * a * b^-1 * a)^2, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5, 6, 7, 4) >,
    Group< a,b | [ a^5, b^7, (a^-1, b^-1)^2, (a^-1 * b^-3)^2, (a * b * a^2 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 1,x12 + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5, 7, 6, 4) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a^-1)^3, (a * b^-1 * a^-1 * b * a)^2, a^-1 * b * a^-1 * b^-1 * a^-2 * b^-1 * a *b^-1 * a * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5)(6, 7) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a * b^-2 * a^-2 * b^-1 * a^2 * b * a * b^2 * a^-1 * b^-1 ] >,ideal< R | [5,xcom,x12 + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5, 6) >,
    Group< a,b | [ a^5, b^5, (a * b^-1)^4, (a^-2 * b)^3, (a * b * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5, 7) >,
    Group< a,b | [ a^5, b^5, (a^-1 * b * a^-1 * b^-1)^2, (b^-1 * a^-1 * b^-1)^3, (a * b * a^-2 * b^-1 * a)^2, a^-1 * b^2 *a^-1 * b^-1 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + zeta + 3,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5)(4, 6) >,
    Group< a,b | [ a^5, b^4, (a^-2 * b^-1)^3, (a * b^-1 * a * b * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta + 2,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5, 4, 6, 7) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a)^3, (a^-1 * b^-1)^4, a^-2 * b^-2 * a^2 * b * a * b^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12,xm21,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5, 7, 4, 6) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-2)^2, (a^-2 * b)^3, (a * b * a^-1 * b * a)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5)(4, 7) >,
    Group< a,b | [ a^5, b^4, (a^-2 * b^-1)^3, a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b * a * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5, 4, 7, 6) >,
    Group< a,b | [ a^5, b^7, b * a * b^-1 * a^-2 * b^-2 * a^-1 * b, (a^-2 * b)^3, (a * b^-1 * a^-1 * b * a)^2 ] >,ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 5, 6, 4, 7) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a)^3, (a * b * a^-1 * b^-1 * a)^2, a^-1 * b^-1 * a^-1 * b * a^-2 * b * a * b * a* b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 4,xm12,xm21,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6, 7, 5, 4) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a^-1)^3, (a * b^-1)^4, b^-2 * a * b^-1 * a^2 * b^2 * a^-2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6, 4) >,
    Group< a,b | [ a^5, b^5, (a^-1 * b * a^-1 * b^-1)^2, (b * a^-1 * b)^3, (a * b * a^-2 * b^-1 * a)^2, b * a^2 * b^-2 * a^2* b * a^-1 * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6, 5, 7, 4) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a^-1)^3, (a * b * a^-1 * b^-1 * a)^2, a * b^-1 * a * b^-1 * a^-2 * b^-1 * a^-1 *b * a^-1 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6, 5) >,
    Group< a,b | [ a^5, b^5, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, (a * b * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6, 7) >,
    Group< a,b | [ a^5, b^5, (b^-1 * a)^3, (a * b * a * b^-1 * a)^2, (a * b * a)^4 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 2,xm12,xm21,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6)(5, 7) >,
    Group< a,b | [ a^5, b^4, (a^-2 * b)^3, a^-1 * b^-1 * a * b^-1 * a^2 * b^2 * a^-1 * b * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 1,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6, 7, 4, 5) >,
    Group< a,b | [ a^5, b^7, (a^-2 * b^-1)^3, a^-1 * b^2 * a^-2 * b * a * b^-2, (a * b^-1 * a^-1 * b * a)^2 ] >,ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 4,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6)(4, 5) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a * b^-2 * a^2 * b^-1 * a^2 * b^2 * a^2 * b^-1 * a, b^-1 * a* b * a^-1 * b^-1 * a^2 * b^2 * a^-2 * b^2 * a ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6, 4, 5, 7) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a)^3, (a * b^-1 * a^-1 * b * a)^2, a * b * a * b * a^-2 * b * a^-1 * b^-1 * a^-1* b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 3,xm12,xm21,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6, 4, 7, 5) >,
    Group< a,b | [ a^5, b^7, (a * b^-2)^2, (a^-2 * b^-1)^3, (a * b^-1 * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6, 5, 4, 7) >,
    Group< a,b | [ a^5, b^7, (a^-1, b^-1)^2, (a * b^-3)^2, (a * b * a^2 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 1,x12 + 2*zeta,xm12 + 3,xm21 + 3,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 6)(4, 7) >,
    Group< a,b | [ a^5, b^4, (a^-2 * b)^3, (a * b * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7, 6, 5, 4) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a^-1)^3, (a * b^2 * a)^2, (a * b^-1 * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom,x12,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7, 4) >,
    Group< a,b | [ a^5, b^5, (b^-1 * a^-1)^3, a * b^-1 * a * b * a^2 * b^-2 * a^-1 * b^-1, (a * b^-1 * a)^4 ] >,
    ideal< R |[5,xcom + 2*zeta,x12,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1,x1 + 2,xm1 + 2,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7, 5, 6, 4) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a^-1)^3, (a * b^-1)^4, (a * b * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7, 5) >,
    Group< a,b | [ a^5, b^5, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, (a * b^-1 * a^-1 * b * a)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7, 6) >,
    Group< a,b | [ a^5, b^5, (a^-1, b^-1)^2, (b^-1 * a^-1)^5, (a * b * a^2 * b^-1 * a)^2, a * b^-2 * a^-1 * b^-1 * a^2 *b^-1 * a^-1 * b^-2 * a ] >,
    ideal< R | [5,xcom + 1,x12 + 2*zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7)(5, 6) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a)^3, a^-1 * b^-1 * a^-1 * b * a^2 * b^2 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7, 6, 4, 5) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, (a^-2 * b^-1)^3, (a * b * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7)(4, 5) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a)^3, (a * b * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 3,xm12,xm21,xm2m1 + 2*zeta,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7, 4, 5, 6) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, (a^-2 * b)^3, (a * b^-1 * a * b * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7, 4, 6, 5) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b * a^-1 * b^-1)^2, (b^-1 * a^-1 * b^-1)^3, (a * b^3 * a)^2 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7, 5, 4, 6) >,
    Group< a,b | [ a^5, b^7, a^-1 * b^-2 * a^-2 * b^-1 * a * b^2, (a^-2 * b)^3, (a * b * a^-1 * b^-1 * a)^2 ] >,ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 2, 3, 7)(4, 6) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, a * b^-2 * a * b^-1 * a * b^2 * a * b^-1, (a * b^-1 * a)^4, (a * b * a)^4,a * b^-2 * a^2 * b^-2 * a^2 * b^2 * a * b * a^-1 * b, a * b * a^-2 * b^-1 * a^-2 * b^2 * a^-1 * b^2 * a * b^-1 * a ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4) >,
    Group< a,b | [ a^5, b^2, (b * a^-1)^7, (a * b * a * b * a^-1 * b * a^-1 * b)^2, (a^-1 * b * a^2 * b * a^-1)^3, a * b * a^2* b * a^-2 * b * a^-2 * b * a^2 * b * a * b * a^2 * b ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2 + zeta,xm2 + 4*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4)(5, 6, 7) >,
    Group< a,b | [ a^5, b^6, (a * b^-2 * a)^2, (a^-2 * b^-1)^3, a * b * a * b * a^-1 * b^3 * a^-1 * b ] >,
    ideal< R |[5,xcom,x12 + zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4)(5, 7, 6) >,
    Group< a,b | [ a^5, b^6, (a * b^2 * a)^2, (a^-2 * b)^3, a * b^-1 * a * b^-1 * a^-1 * b^3 * a^-1 * b^-1 ] >,
    ideal<R | [5,xcom,x12 + 2*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4, 5)(6, 7) >,
    Group< a,b | [ a^5, b^6, (a^-1 * b^-1)^4, (b^-1 * a)^5, a * b * a * b^-3 * a^-1 * b^3 * a * b^-2, a^-1 * b^-1 *a^2 * b^-1 * a^2 * b^-2 * a^2 * b, (a * b^2 * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4, 5, 6) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (b^-1 * a)^5, a * b^-1 * a^-1 * b * a^-2 * b* a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 1,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4, 5, 7) >,
    Group< a,b | [ a^5, b^4, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-1 * b^-1 * a^-1 * b^-2* a^-2 * b * a * b^-1 * a * b, b * a * b^-2 * a^-1 * b * a^2 * b * a^-1 * b^2 * a^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 3*zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4, 6, 5) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, (a^-2 * b)^3, a * b^-2 * a^-1 * b * a^2 * b^2 * a^-1 * b * a ] >,
    ideal< R| [5,xcom + 4*zeta + 2,x12 + zeta + 1,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4, 6, 7) >,
    Group< a,b | [ a^5, b^4, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-1 * a * b * a^-2 *b^2 * a^-1 * b^-1 * a^-1 * b, b^-1 * a * b * a * b^-1 * a^2 * b * a * b^2 * a^-2, a^2 * b^-2 * a^-1 * b * a^2 * b * a^-1 * b^2 * a * b ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 2*zeta + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4, 6)(5, 7) >,
    Group< a,b | [ a^5, b^6, (b * a^-1 * b)^3, b^2 * a * b^-1 * a^2 * b * a * b * a, b^-1 * a^-1 * b * a^-1 * b^-1 * a* b * a^-1 * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4, 7, 5) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1, a * b^-2 * a^-2 * b^-1 * a^-1 * b^2 * a^-1 * b^2* a * b, (a^-1 * b^-1)^6, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b^-2 * a * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4, 7, 6) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a^-1)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-1 * a * b^-2 *a^2 * b^-1 * a * b^2 * a ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 4, 7)(5, 6) >,
    Group< a,b | [ a^5, b^6, (b^-1 * a^-1)^3, (a * b^-1)^4, (a^-2 * b^-1)^3, b^-1 * a^-1 * b * a^-2 * b^-1 * a^2 * b^2* a^-1 * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1,x1 + 2,xm1 + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4)(6, 7) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-2* a^-2 * b^-1 * a^2 * b^2 * a^-2 * b^-1 * a, a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a^-1 * b, a * b^-2 * a^2 * b^-1 * a^-2 * b * a^-1 * b^2 * a^-2 * b ] >,ideal< R | [5,xcom + 2*zeta + 4,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4)(5, 6) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-1* a^-2 * b^-2 * a^2 * b^-1 * a^-2 * b^2 * a, a * b * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a^-1 * b^-1, a^-2 * b^-2 * a^-1 * b^-1 * a^-2 * b * a^2 * b^2 * a * b^-1 ] >,ideal< R | [5,xcom + 2*zeta + 4,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4)(5, 7) >,
    Group< a,b | [ a^5, b^4, (a^-2 * b^-1)^3, (a^-2 * b)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 *a^-1 * b^-1 * a * b^-1 * a^-2 * b^2 * a * b * a * b^2 * a ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4, 5) >,
    Group< a,b | [ a^5, b^5, (a * b^-1)^4, (b * a^-1 * b)^3, b * a * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b^-1 * a ] >,ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4, 5, 6, 7) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^2, a^-1 * b^3 * a^-1 * b^-1 * a^-1 * b^2 * a * b^-2, b * a^-2 * b^-1 * a^-1 *b^-1 * a^2 * b^2 * a * b^2 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 4,xm12 + zeta,xm21 + 4*zeta + 4,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4, 5, 7, 6) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a^-1)^3, (a * b^-1)^4, (a * b^-1 * a)^4, b^-1 * a * b^3 * a^2 * b^-1 * a * b * a* b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4, 6, 7, 5) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, (a^-2 * b)^3, (b^-1 * a^-1 * b^-1)^3, (a^-1 * b^-2 * a * b^-1)^2 ] >,ideal< R | [5,xcom + 2*zeta + 2,x12 + zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4, 6) >,
    Group< a,b | [ a^5, b^5, a^-1 * b^-1 * a * b^-1 * a^-2 * b * a * b^-1 * a^-1 * b^-1, b * a^-1 * b^-1 * a^-1 * b^-1 *a^-1 * b * a * b^-2 * a^-1, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta + 1,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4, 6, 5, 7) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a^-1)^3, (b * a^-1 * b)^3, (a * b^3 * a)^2 ] >,
    ideal< R | [5,xcom,x12,xm12 + 3,xm21 + 3,xm2m1,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4, 7, 6, 5) >,
    Group< a,b | [ a^5, b^7, a * b * a^-1 * b^-1 * a^-1 * b * a^-1 * b^-2, (b * a^-1 * b)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4, 7) >,
    Group< a,b | [ a^5, b^5, (a * b^-1 * a^-1 * b^-1)^2, (a^-2 * b^-1)^3, b^-2 * a^2 * b^-1 * a^2 * b^-2 * a * b^-1 * a ] >,ideal< R | [5,xcom,x12 + 3*zeta + 1,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 4, 7, 5, 6) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, b^2 * a * b * a^-2 * b * a * b^-1 * a * b, b^-1 * a * b^-1 * a^-1 * b^-1 *a^-1 * b^2 * a * b^-2 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5, 2, 4) >,
    Group< a,b | [ a^5, b^5, (a * b^-1 * a^-1 * b^-1)^2, (a^-2 * b)^3, a * b * a^-1 * b^-2 * a^2 * b^-2 * a^-1 * b * a ] >,ideal< R | [5,xcom,x12 + 3,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5, 6, 7, 2, 4) >,
    Group< a,b | [ a^5, b^7, b^2 * a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a, (b^-1 * a^-1 * b^-1)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5, 7, 6, 2, 4) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, a * b * a * b^-1 * a^-2 * b^-1 * a * b^-3, b^2 * a * b^-2 * a^-1 * b *a^-1 * b * a * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + zeta + 1,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5)(2, 4)(6, 7) >,
    Group< a,b | [ a^5, b^6, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a^-2 * b)^3, a^-1 * b^-2 * a^-2 * b^-1 * a^2 * b * a *b^3 * a * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4*zeta,xm12,xm21,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5, 6)(2, 4) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-2 * a * b * a^2 *b^2 * a * b * a ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 3*zeta + 2,xm12,xm21,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5, 7)(2, 4) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b^-1 * a * b^-2 * a^-1 * b^-2 * a^-1 * b * a^-2* b^2 * a, a * b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^2 * a * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta + 2,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5)(2, 4, 6) >,
    Group< a,b | [ a^5, b^3, (a * b * a^-1 * b * a)^2, b * a * b * a * b^-1 * a^2 * b * a^2 * b^-1 * a, (a * b^-1 * a^-1* b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5, 2, 4, 6, 7) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, b * a^-1 * b^-1 * a^-2 * b^3 * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5, 7, 2, 4, 6) >,
    Group< a,b | [ a^5, b^7, (a * b^-1 * a)^2, (b^-1 * a^-1 * b^-1)^3, a * b^-2 * a^-1 * b^-1 * a^-1 * b^-2 * a * b^-2] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 1,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5)(2, 4, 7) >,
    Group< a,b | [ a^5, b^3, (a * b^-1 * a)^4, (a * b * a)^4, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b * a * b^-1 * a^-1 *b^-1 * a * b * a^-1 * b * a * b^-1, b * a * b * a^-1 * b * a^-2 * b^-1 * a^-1 * b^-1 * a * b^-1 * a ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 3*zeta + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5, 2, 4, 7, 6) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, a^-1 * b * a * b * a^-2 * b^3 * a^-1 * b, (a * b^-1 * a)^4 ] >,
    ideal< R| [5,xcom + 2*zeta + 4,x12 + zeta + 1,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 5, 6, 2, 4, 7) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, a^-1 * b^-3 * a^-2 * b^-1 * a * b^-1 * a^-1 * b^-1, (a * b^-1 * a)^4, (a *b^-2 * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 3*zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 7, 5, 2, 4) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a)^3, (b^-1 * a^-1 * b^-1)^3, (a * b^-1 * a^-1 * b^-1 * a)^2, (a * b^-3 * a)^2 ]>,
    ideal< R | [5,xcom,x12 + 2*zeta + 2,xm12,xm21,xm2m1 + 3*zeta,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 2, 4) >,
    Group< a,b | [ a^5, b^5, a^-1 * b * a * b^-1 * a^-2 * b * a * b * a^-1 * b, b * a^-1 * b * a^-1 * b^-1 * a^-1 * b^2 * a* b^-1 * a^-1, (a * b * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 5, 7, 2, 4) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, (b * a^-1 * b)^3, (a * b^-2 * a^-1 * b^-1)^2 ] >,ideal< R | [5,xcom + 2*zeta + 2,x12 + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 5)(2, 4) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-1 * b * a^-1 * b^-2* a^-2 * b^-1 * a * b * a * b^-1, b^-1 * a * b^-2 * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b^2 * a^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4*zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 7)(2, 4) >,
    Group< a,b | [ a^5, b^4, (a * b^-1)^4, (a^-2 * b^-1)^3, a * b^-1 * a^-1 * b^-2 * a^2 * b^-1 * a^-1 * b^2 * a ] >,ideal< R | [5,xcom + 4*zeta + 2,x12 + zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6)(2, 4)(5, 7) >,
    Group< a,b | [ a^5, b^6, (b^-1 * a^-1 * b^-1)^3, a * b^-1 * a * b^-1 * a^2 * b * a * b^-2, b * a^-1 * b^-1 * a^-1* b^-1 * a * b * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 3,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 7, 2, 4, 5) >,
    Group< a,b | [ a^5, b^7, b^2 * a^-1 * b^-1 * a^2 * b * a^-2 * b, (b^-1 * a)^5, b * a * b^-1 * a * b^-1 * a^-1 * b* a^-1 * b^-2 * a^-1, b^-1 * a * b * a * b^-1 * a^2 * b^-2 * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6)(2, 4, 5) >,
    Group< a,b | [ a^5, b^3, (b^-1 * a)^3, (a * b * a)^4, (a^-1 * b^-1)^6, a^-1 * b * a * b * a^-2 * b^-1 * a^2 * b^-1 *a^-1 * b^-1 * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta,xm12,xm21,xm2m1 + 2*zeta + 2,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 2, 4, 5, 7) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, a^-1 * b^-1 * a * b^-1 * a^-2 * b^-3 * a^-1 * b^-1, (a * b^-1 * a)^4, (a *b^2 * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 2*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 2, 4, 7, 5) >,
    Group< a,b | [ a^5, b^7, (a * b * a)^2, (b * a^-1 * b)^3, b^-3 * a * b^-1 * a^-1 * b^2 * a^-1 * b^-1 * a ] >,ideal< R | [5,xcom + 2,x12 + zeta + 3,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 5, 2, 4, 7) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, b^-3 * a^-2 * b * a^-1 * b^-1 * a, (b^-1 * a^-1 * b^-1)^3 ] >,
    ideal< R| [5,xcom + 4*zeta,x12 + 4,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6)(2, 4, 7) >,
    Group< a,b | [ a^5, b^3, (a * b^-1 * a^-1 * b^-1 * a)^2, a * b * a^2 * b^-1 * a^2 * b * a * b^-1 * a * b^-1, a^-1 *b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a * b ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 4,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3*zeta + 2,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 6, 5, 2, 4) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^2, a * b^3 * a * b^-1 * a * b^2 * a^-1 * b^-2, b^-1 * a * b^-1 * a^2 * b^-1* a^2 * b^-1 * a * b^-2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4*zeta + 4,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 2, 4) >,
    Group< a,b | [ a^5, b^5, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, (a * b^2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 5, 6, 2, 4) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a * b^-2 * a^-1 * b^-1 * a)^2, b^-1 * a * b * a^-1 * b^-1* a^2 * b^-1 * a^-1 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 4,xm12,xm21,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 5)(2, 4) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b * a * b^-1 *a^-2 * b^2 * a^-1 * b * a^-1 * b^-1, a * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a * b^2 * a^-1 * b, a^2 * b^-2 * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 6)(2, 4) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (b^-1 * a^-1)^5, a * b * a * b^-1 * a^-2 *b^-1 * a^-1 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7)(2, 4)(5, 6) >,
    Group< a,b | [ a^5, b^6, (a * b^-1)^4, (b^-1 * a^-1)^5, b^2 * a * b^-3 * a^-1 * b^3 * a * b^-1 * a, b^2 * a^2 *b^-1 * a^2 * b^3 * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 6, 2, 4, 5) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a)^3, (a * b^2 * a)^2, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7)(2, 4, 5) >,
    Group< a,b | [ a^5, b^3, (a^-1 * b^-1)^4, (a * b^-1)^4, (a * b^-1 * a * b * a^-1 * b * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 2, 4, 5, 6) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a^-1)^3, (a * b^-2 * a)^2, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 2, 4, 6, 5) >,
    Group< a,b | [ a^5, b^7, b^-1 * a^-2 * b^-1 * a^2 * b * a^-1 * b^-2, (b^-1 * a^-1)^5, b^-1 * a * b * a^-1 * b^-1 *a^-1 * b^-1 * a * b * a * b^-1, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 5, 2, 4, 6) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, a^-1 * b^3 * a^-2 * b * a * b * a^-1 * b, (a * b^-1 * a)^4 ] >,
    ideal< R| [5,xcom + 2*zeta + 4,x12 + 4,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7)(2, 4, 6) >,
    Group< a,b | [ a^5, b^3, (b^-1 * a^-1)^3, (a * b^-1 * a)^4, (a * b^-1)^6, a^-1 * b^-1 * a * b^-1 * a^-2 * b^-1 * a^2* b * a^-1 * b * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5, 4)(6, 7) >,
    Group< a,b | [ a^5, b^6, (a * b^-1)^4, (b^-1 * a^-1)^5, a * b^-1 * a * b^-3 * a^-1 * b^3 * a * b^2, a^2 * b^-1 *a^-1 * b^-1 * a^2 * b^3 * a * b^-2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2,x1 + 2,xm1 + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5, 6, 4) >,
    Group< a,b | [ a^5, b^4, (a * b^-1)^4, (a^-2 * b^-1)^3, a * b^-2 * a^-1 * b^-1 * a^2 * b^2 * a^-1 * b^-1 * a ] >,ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5, 7, 4) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1, a * b^-2 * a^-2 * b^-1 * a^-1 * b^2 * a * b^2 *a * b, a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^2 * a * b * a^-1 * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3*zeta + 1,xm12 + 3,xm21 + 3,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5) >,
    Group< a,b | [ a^5, b^2, (a^-1 * b * a * b)^3, (b * a^-1)^7, a^-1 * b * a^2 * b * a^-1 * b * a^2 * b * a^-1 * b * a * b * a* b ] >,
    ideal< R | [5,xcom,x12 + zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5, 6, 7) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (b^-1 * a)^5, a * b^-1 * a * b * a^-2 * b *a^-1 * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5, 7, 6) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, a * b^-1 * a * b^-2 * a^-2 * b^-1 * a^-1 * b * a^-1 * b, b^-1 * a^-1 * b^-2* a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1, b * a^-1 * b^-2 * a^-1 * b^-1 * a^2 * b * a^-1 * b^2 * a^-2 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5)(4, 6, 7) >,
    Group< a,b | [ a^5, b^6, (b^-1 * a)^3, (a^-1 * b^-2)^2, a * b^-1 * a^-2 * b^-1 * a^-3 * b * a^-1 * b^-1 * a^-1 * b* a ] >,
    ideal< R | [5,xcom + 3,x12 + 4*zeta + 2,xm12,xm21,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5, 4, 6) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, a^-1 * b * a^-1 * b^-1 * a^-2 * b^2 * a * b^-1 * a * b, a^-1 * b * a^2 * b* a^2 * b * a * b^2 * a^-1 * b, a^-2 * b^-2 * a^-1 * b * a^2 * b^-1 * a^-1 * b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + zeta + 1,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5, 7)(4, 6) >,
    Group< a,b | [ a^5, b^6, (b * a^-1 * b)^3, a * b * a * b * a^2 * b^-1 * a * b^2, b^-1 * a^-1 * b * a^-1 * b^-1 *a^-1 * b * a^-1 * b * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5)(4, 7, 6) >,
    Group< a,b | [ a^5, b^6, (b^-1 * a^-1)^3, (a * b^-2)^2, a^-1 * b^-1 * a^2 * b^-1 * a^-2 * b * a * b^-1 * a * b *a^-1 ] >,
    ideal< R | [5,xcom + 3,x12,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1,x1 + 2,xm1 + 2,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5, 4, 7) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a^-1)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-2 * a * b^-1 *a^2 * b^2 * a * b^-1 * a ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3)(2, 5, 6)(4, 7) >,
    Group< a,b | [ a^5, b^6, (b^-1 * a)^3, (a^-2 * b^-1)^3, a * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a * b, (a * b^-1 *a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3,xm12,xm21,xm2m1 + 3,x1 + 2,xm1 + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5, 4) >,
    Group< a,b | [ a^5, b^5, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b * a * b^-1 *a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5, 6, 7, 4) >,
    Group< a,b | [ a^5, b^7, a^-1 * b * a^-1 * b^-1 * a^-1 * b^2 * a * b^-1, (b^-1 * a^-1 * b^-1)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3,xm12 + 2,xm21 + 2,xm2m1 + 3,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5, 7, 6, 4) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, (b * a^-1 * b)^3, (a^-1 * b^-2 * a * b^-1)^2 ] >,ideal< R | [5,xcom + 2*zeta + 2,x12 + 4*zeta,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5)(6, 7) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a^-1)^3, (b^-1 * a)^3, a * b^-2 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^2 * a, a^-1 * b *a * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^-1 * b * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12,xm12,xm21,xm2m1,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5, 6) >,
    Group< a,b | [ a^5, b^5, (b^-1 * a)^3, (a * b^-1 * a^-2 * b^-1 * a)^2, b^-2 * a^2 * b^-1 * a^2 * b^-2 * a^-1 * b^-1 *a^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 2*zeta + 3,xm12,xm21,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5, 7) >,
    Group< a,b | [ a^5, b^5, a^-1 * b^-1 * a * b * a^-2 * b^-1 * a * b^-1 * a^-1 * b^-1, b * a^-1 * b^-1 * a^-1 * b^-1 *a^-1 * b * a^-1 * b^-2 * a, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4*zeta + 2,xm12 + 3,xm21 + 3,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5)(4, 6) >,
    Group< a,b | [ a^5, b^4, a^-1 * b^-2 * a * b^-1 * a^-1 * b^2 * a * b^-1, a^-1 * b^-1 * a^-1 * b^-2 * a^-2 * b^2 *a^-1 * b^-1 * a * b, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + zeta + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5, 4, 6, 7) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a^-1)^3, (a * b^-1)^4, (a * b^-1 * a)^4, b^-1 * a * b * a * b^-1 * a^2 * b^3 * a* b^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5, 7, 4, 6) >,
    Group< a,b | [ a^5, b^7, (a * b^-1 * a)^2, (a^-1 * b^-3 * a^-1 * b^-1)^2, (a, b)^3, (a^-1 * b^2 * a^-1 * b^-2)^2 ]>,
    ideal< R | [5,xcom,x12 + 3*zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5)(4, 7) >,
    Group< a,b | [ a^5, b^4, a * b^-2 * a^-1 * b^-1 * a * b^2 * a^-1 * b^-1, a * b^-1 * a^-1 * b^-2 * a^-2 * b^2 * a^-1 *b^-1 * a^-1 * b, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4*zeta + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5, 4, 7, 6) >,
    Group< a,b | [ a^5, b^7, (a * b^-3)^2, (a^-2 * b^-1)^3, (a * b^-1 * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3,x12 + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 2, 5, 6, 4, 7) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, a * b^-1 * a * b * a^-2 * b * a * b^3, a * b^2 * a^-1 * b^-1 * a^-1 * b^-1* a * b^-3 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4)(2, 5)(6, 7) >,
    Group< a,b | [ a^5, b^6, (a^-1 * b^-1)^4, (b^-1 * a)^5, b^-2 * a * b^-3 * a^-1 * b^3 * a * b * a, b^-2 * a^2 *b^-1 * a^2 * b^-1 * a^-1 * b * a^2, a * b^-2 * a * b^-1 * a^2 * b * a * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4)(2, 5, 6) >,
    Group< a,b | [ a^5, b^3, (a * b * a * b * a)^2, (b^-1 * a)^5, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b* a * b^-1, b^-1 * a * b * a * b^-1 * a^-2 * b * a^-2 * b * a^-2 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta + 2,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4)(2, 5, 7) >,
    Group< a,b | [ a^5, b^3, (a * b^-1)^4, (a^-2 * b)^3, (a^-1 * b^-1)^6, a^-1 * b^-1 * a^-1 * b^-1 * a * b * a^2 * b * a* b * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3,xm12 + 4,xm21 + 4,xm2m1 + 3,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4, 2, 5) >,
    Group< a,b | [ a^5, b^5, (a * b^-1)^4, (b * a^-1 * b)^3, b * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a ] >,ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4, 2, 5, 6, 7) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^2, b^-1 * a * b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b * a * b^-1, a * b^2 *a^-1 * b^-1 * a^-2 * b^-2 * a^-2 * b^-2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 1,xm21 + 1,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4, 2, 5, 7, 6) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-2 * a * b^-1 * a^-2 * b^-1 * a * b^2 * a^-1, b^2 * a *b^-1 * a^-2 * b * a^-1 * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4, 6, 7, 2, 5) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-3)^2, (a^-2 * b)^3, (a * b * a * b * a)^2 ] >,
    ideal< R | [5,xcom + 3,x12 + zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4, 6)(2, 5) >,
    Group< a,b | [ a^5, b^4, (b^-1 * a)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b * a * b^-2 * a^2 *b * a * b^2 * a ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 2*zeta + 3,xm12,xm21,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4, 6, 2, 5, 7) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, b^3 * a^-2 * b^-1 * a^-1 * b * a, (b * a^-1 * b)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4, 7, 6, 2, 5) >,
    Group< a,b | [ a^5, b^7, (b^-1 * a)^3, (a^-1 * b^-1)^4, a^-1 * b^2 * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b * a *b^-1, (a * b^-1 * a^-1 * b^-2 * a)^2 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4, 7)(2, 5) >,
    Group< a,b | [ a^5, b^4, (a * b^-1)^4, a * b * a * b^-2 * a^-2 * b * a^-1 * b^-1 * a^-1 * b^-1, b^-1 * a^-1 * b^-2 *a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1, b^-1 * a^-1 * b^-2 * a * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-1 * b^-2 * a^-1 * b * a^2 * b^-1 * a^-1 * b^2 * a^-2] >,
    ideal< R | [5,xcom + zeta + 3,x12 + zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta + 2,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 4, 7, 2, 5, 6) >,
    Group< a,b | [ a^5, b^7, b * a^-2 * b^-1 * a^2 * b^-3 * a, (b^-1 * a)^5, a * b^2 * a * b^-1 * a^-1 * b * a^-1 * b* a * b^-1, a^-1 * b^-1 * a^-1 * b^-2 * a^2 * b^-1 * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 1,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 4)(2, 5) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b^-1 * a * b^-2 * a^-1 * b^-2 * a^-1 * b * a^-1* b^2 * a^2, (a^-1 * b^-1)^6, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b^2 * a^-1 * b * a^-1 * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 7, 2, 5, 4) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, b^2 * a^-1 * b^-1 * a^-2 * b * a * b^-2 * a^-1, b^-2 * a *b * a^-2 * b * a * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 2, 5, 7, 4) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-2)^2, (a^-2 * b^-1)^3, (a * b^-2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3,x12 + 2*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 7, 4, 2, 5) >,
    Group< a,b | [ a^5, b^7, (a * b^-1)^4, (a^-2 * b)^3, (b^-1 * a^-1 * b^-1)^3, (a * b^-2 * a^-1 * b^-1)^2 ] >,ideal< R | [5,xcom + 2*zeta + 2,x12 + 3*zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6)(2, 5, 4) >,
    Group< a,b | [ a^5, b^3, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, (a * b^-1)^6, a^-1 * b * a^-1 * b^-1 * a * b^-1 * a^2 *b^-1 * a * b * a^-1 * b * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4,xm12 + 3,xm21 + 3,xm2m1 + 4,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 4, 2, 5, 7) >,
    Group< a,b | [ a^5, b^7, (a * b^-2)^2, (a^-2 * b)^3, (a^-1 * b^-2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 1,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 2, 5) >,
    Group< a,b | [ a^5, b^5, a^-1 * b * a * b * a^-2 * b^-1 * a * b * a^-1 * b, a * b^2 * a^-1 * b^-1 * a^-1 * b * a^-1 * b* a^-1 * b^-1, a * b^-1 * a^-1 * b^-2 * a^2 * b * a * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 7)(2, 5) >,
    Group< a,b | [ a^5, b^4, (a * b^-1)^4, a^-1 * b^-1 * a^-1 * b * a^-2 * b^2 * a * b * a * b^-1, a^-1 * b^-1 * a^2 *b^-1 * a^2 * b^-1 * a * b^2 * a^-1 * b^-1, a^-2 * b^-2 * a^-1 * b^-1 * a^2 * b * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6)(2, 5, 7) >,
    Group< a,b | [ a^5, b^3, (a * b^-1 * a)^4, (a * b * a)^4, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b * a * b^-1 * a^-1 *b^-1 * a * b * a^-1 * b^-1 * a * b, b^-1 * a * b^-1 * a^-1 * b^-1 * a^-2 * b * a^-1 * b * a * b * a ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 1,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 4, 7, 2, 5) >,
    Group< a,b | [ a^5, b^7, (a * b * a)^2, (a, b)^3, (a * b^-3 * a * b^-1)^2, (a^-1 * b^2 * a^-1 * b^-2)^2 ] >,ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + zeta + 3,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6)(2, 5)(4, 7) >,
    Group< a,b | [ a^5, b^6, (b^-1 * a^-1 * b^-1)^3, b^-2 * a * b * a^2 * b^-1 * a * b^-1 * a, b * a * b^-1 * a^-1 *b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 3,x1 + 2,xm1 + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 6, 2, 5, 4, 7) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, b^-1 * a^-1 * b * a^-2 * b^-3 * a, (b^-1 * a^-1 * b^-1)^3 ] >,
    ideal< R| [5,xcom + 4*zeta,x12 + 4*zeta,xm12 + 3,xm21 + 3,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 4)(2, 5) >,
    Group< a,b | [ a^5, b^4, (a^-1 * b^-1)^4, (a^-2 * b)^3, a * b * a^-1 * b^-2 * a^2 * b * a^-1 * b^2 * a ] >,
    ideal< R| [5,xcom + zeta + 3,x12 + 4*zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 6, 2, 5, 4) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^2, b * a * b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1 * a * b, a * b^-2 * a^-1* b * a^-2 * b^2 * a^-2 * b^2 ] >,
    ideal< R | [5,xcom,x12 + 1,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 1,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 2, 5, 6, 4) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-2 * a * b * a^-2 * b^-1 * a^-1 * b^2 * a^-1, b^2 * a *b * a^-2 * b * a * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 6, 4, 2, 5) >,
    Group< a,b | [ a^5, b^7, a^-1 * b * a^-1 * b^-1 * a^-1 * b * a * b^-2, (b * a^-1 * b)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12 + 3,xm21 + 3,xm2m1 + 2,x1 + 2,xm1 + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7)(2, 5, 4) >,
    Group< a,b | [ a^5, b^3, (a * b^-1 * a * b^-1 * a)^2, (b^-1 * a^-1)^5, a^-1 * b * a^-1 * b * a^-1 * b^-1 * a * b^-1 *a * b^-1 * a * b^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^-2 * b * a * b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 4, 2, 5, 6) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, b^2 * a * b^-1 * a^-2 * b^-1 * a * b^-2 * a^-1, b^-2 *a^-1 * b * a^-2 * b^-1 * a * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 2, 5) >,
    Group< a,b | [ a^5, b^5, (b^-1 * a^-1)^3, (a * b^-1 * a^-2 * b^-1 * a)^2, b^-1 * a * b * a^-1 * b^-1 * a^2 * b * a^-1 *b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3,x12,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1,x1 + 2,xm1 + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 6)(2, 5) >,
    Group< a,b | [ a^5, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (b^-1 * a^-1)^5, a * b * a^-1 * b^-1 * a^-2 *b^-1 * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2,x1 + 2,xm1 + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7)(2, 5, 6) >,
    Group< a,b | [ a^5, b^3, (a^-1 * b^-1)^4, (a * b^-1)^4, (a * b * a * b^-1 * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta,x1 + 2,xm1 + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 4, 6, 2, 5) >,
    Group< a,b | [ a^5, b^7, (a^-1 * b^-1)^4, b^-2 * a * b^-1 * a^-2 * b^-1 * a * b * a * b^-1, b * a * b^-1 * a *b^-1 * a^-1 * b^-3 * a^-1 * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4*zeta,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + zeta + 1,x1 + 2,xm1 + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7)(2, 5)(4, 6) >,
    Group< a,b | [ a^5, b^6, (b^-1 * a^-1)^3, (a^-2 * b)^3, a^-1 * b^-2 * a * b^-1 * a * b^2 * a^-1 * b, (a * b * a)^4] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12,xm12 + 3,xm21 + 3,xm2m1,x1 + 2,xm1 + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (3, 4, 5, 6, 7), (1, 3, 7, 2, 5, 4, 6) >,
    Group< a,b | [ a^5, b^7, a * b^3 * a^2 * b * a^-2 * b^-1, (b^-1 * a^-1)^5, b * a * b^-1 * a^-1 * b^-1 * a^-1 * b *a * b^-2 * a, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2,x1 + 2,xm1 + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4) >,
    Group< a,b | [ a^4, b^2, a^-1 * b * a^-2 * b * a^-2 * b * a^2 * b * a^2 * b * a^2 * b * a^-1, (b * a^-1)^7, a^-1 * b *a^-2 * b * a^-1 * b * a^-2 * b * a^-1 * b * a^2 * b * a^-1 * b * a^2 * b, b * a^-2 * b * a * b * a^-1 * b * a^-2 * b * a * b * a^-1 * b * a^2 * b * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + zeta,xm2 + 4*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4)(5, 6, 7) >,
    Group< a,b | [ a^4, b^6, (a^-1 * b^-2)^2, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 *a)^5, (a, b)^3, b * a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a^2 * b^-1 * a ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4)(5, 7, 6) >,
    Group< a,b | [ a^4, b^6, (a * b^-2)^2, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 *a^-1)^5, (a, b)^3, b^-1 * a * b * a * b^-1 * a^-1 * b^-1 * a * b * a^2 * b^-1 * a^-1 * b * a ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4, 5)(6, 7) >,
    Group< a,b | [ a^4, b^6, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, a^-1 * b^2 * a^-1 * b^-1 * a * b^3 * a * b^-1,(b^-1 * a)^5, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b * a * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 4*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4, 5, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 *a^2 * b^-1, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, (b^-1 * a)^5, a * b^-2 * a^-1 * b * a^-1 * b^-1 * a * b * a^2 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4, 5, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b^-1, (a * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2* a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1, a^-1 * b^-2 * a * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 2*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4, 6, 5) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^2 * a^2 * b, (a^-1 * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 *a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1 * a^-1 * b)^3, a^-1 * b * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a^-1 * b^2 * a * b ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + zeta + 1,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4, 6, 7) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^2 * a^2 * b, (a * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1* b^2 * a^-1 * b^2 * a^-1 * b^-1, a * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^2 * a^-1 * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 3*zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 3,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4, 6)(5, 7) >,
    Group< a,b | [ a^4, b^6, a^-1 * b^-1 * a^2 * b^-1 * a^-1, a^-1 * b^-2 * a^-1 * b^-2 * a * b^2 * a * b^-2, b^-1* a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a * b * a, a^-1 * b * a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a * b^-1 * a^-1 * b^2 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4, 7, 5) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b^-1, (a^-1 * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 *b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-2 * a^-1 * b * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 4,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4, 7, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, a * b^-1 * a^-2 * b^-1 * a * b^-1 * a^2 *b^-1, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, (b^-1 * a^-1)^5, a * b^-2 * a^-2 * b^-1 * a^-1 * b^-1 * a * b * a * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2)(3, 4, 7)(5, 6) >,
    Group< a,b | [ a^4, b^6, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, (b^-1 * a^-1)^5, a^-1 * b^-3 * a^-1 * b^-1 * a *b^2 * a * b^-1, a^-1 * b * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b^-2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4)(6, 7) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^5, (b^-1 * a)^5, b^-1 * a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b^2 * a * b^2 *a, b^-1 * a^-2 * b^-1 * a^-2 * b * a * b^2 * a^2 * b * a, a * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^2 * a^2 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4)(5, 6) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^5, (b^-1 * a)^5, b^-1 * a * b^-2 * a^-2 * b^-1 * a * b^2 * a^-1 * b^2 *a^-1, b^-1 * a^-2 * b^-1 * a^-2 * b * a^-1 * b^2 * a^2 * b * a^-1, a^-1 * b^-2 * a^-2 * b^-2 * a^-1 * b^-1 * a^-1 * b * a * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4)(5, 7) >,
    Group< a,b | [ a^4, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b * a^-1 * b^-2 * a * b^2 * a^-1 * b^-1, a^-2 *b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, b * a^-2 * b^-2 * a^-1 * b * a^-2 * b * a^-1 * b^-1 * a^2 * b^2 * a ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4, 5) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1)^3, (b^-1 * a)^5, a * b^-2 * a * b^-1 * a^-1 * b^2 * a^2 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 2,xm21 + 2,xm2m1,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4, 5, 6, 7) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^3, (a^-1 * b^-1)^4, b * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b * a^2 * b^-1 *a^-1 * b ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12,xm21,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4, 5, 7, 6) >,
    Group< a,b | [ a^4, b^7, (b * a^-1 * b)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 *a^-1)^5, (b^-1 * a)^5, a * b^-2 * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b^2 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4, 6, 7, 5) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^3, (b^-1 * a)^5, b * a * b^-1 * a^-2 * b^2 * a * b^-1 * a^2 * b, a *b^-2 * a^-2 * b^-1 * a^-1 * b * a^-1 * b * a^2 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 2,xm21 + 2,xm2m1,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4, 6) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1,(a^-1 * b^-1 * a * b^-1)^3, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a * b, b * a * b^-2 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4, 6, 5, 7) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^3, (b^-1 * a^-1)^5, b * a^-1 * b^-1 * a^-2 * b^2 * a^-1 * b^-1 * a^2 * b,b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^2 * b^2 * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4, 7, 6, 5) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^3, (a * b^-1)^4, b^-1 * a^-1 * b * a^-2 * b^-1 * a^-1 * b * a^2 * b *a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4, 7) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a)^3, (b^-1 * a^-1)^5, a^-1 * b^-2 * a^-1 * b^-1 * a * b^2 * a^2 * b ] >,
    ideal< R |[5,xcom + 4*zeta,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 3, 4, 7, 5, 6) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1 * b^-1)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1,(b^-1 * a^-1)^5, (b^-1 * a)^5, a^-1 * b^-2 * a^-2 * b^-1 * a * b^-1 * a^2 * b^2 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3)(6, 7) >,
    Group< a,b | [ a^4, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-1 * a * b^-1 * a^-2 * b * a^2 * b^-1 * a^-1, b^-1 *a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1 * a^-1 * b)^3, b * a^-2 * b * a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b^-1 * a^-1 ] >,
    ideal<R | [5,xcom + 3*zeta + 2,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3)(5, 6) >,
    Group< a,b | [ a^4, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-1 * a^-1 * b^-1 * a^-2 * b * a^2 * b^-1 * a, b^-1 *a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1 * a^-1 * b)^3, b * a^-2 * b * a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b * a^2 * b^-2 * a^-1 ] >,
    ideal< R| [5,xcom + 3*zeta + 2,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3)(5, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1, a^-2 * b^-1 *a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^6, a^-1 * b^-2 * a^-1 * b * a^-1 * b^-1 * a * b^-1 * a^2 * b^-1 * a^2 * b^-2, a * b^-2 * a * b * a^-1 * b^-1 * a *b^2 * a * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5, 3) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b^-1, a^-1 * b^-1 * a^-1 *b^-1 * a^-1 * b^-1 * a * b * a * b * a * b^-1, (a, b)^3, b^-2 * a^-1 * b * a^-1 * b^-1 * a^-1 * b * a * b^-1 * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 3,xm12 + 4,xm21 + 4,xm2m1 + 3,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5, 6, 7, 3) >,
    Group< a,b | [ a^4, b^7, (a * b^-1)^2, (a^-1 * b^-1)^6, (a^-1 * b^-2)^4, a^-1 * b^-2 * a * b * a * b * a^-2 * b* a * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 2,xm12 + 4*zeta + 4,xm21 + zeta,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5, 7, 6, 3) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-1 * a * b^-1 * a^-2 * b * a^2 * b^-1 * a^-1, a^-1 *b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^2 * a^-1 * b^-2 * a^-1 * b^2 * a^2 * b * a ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6, 7, 5, 3) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-2)^2, (a * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 *a^2 * b^-1, b * a * b^-1 * a * b * a^-1 * b^-1 * a^2 * b * a * b^-1 * a^2 * b^-1 * a ] >,
    ideal< R | [5,xcom,x12 + 3*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta + 2,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6, 3) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1 * b^-1)^3, (b * a^-1 * b)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 *b^-1 * a^-1, b^-1 * a^-1 * b * a^-1 * b^-2 * a^-2 * b * a * b * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6, 5, 7, 3) >,
    Group< a,b | [ a^4, b^7, (a * b^-2)^2, (a^-1 * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 *a^2 * b^-1, b^-1 * a * b * a * b^-1 * a * b * a^-2 * b * a * b^-1 * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + 3,xm21 + 3,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7, 6, 5, 3) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^2, (a * b^-1)^6, (a * b^-2)^4, b^-2 * a^-1 * b * a^-1 * b * a * b^-1 *a^-2 * b^-1 * a * b^-1 * a * b * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta + 4,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + zeta,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7, 3) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, a * b^-1 * a^-2 * b^-1 * a * b^-1 * a^2 * b^-1, (a^-1 * b^-1 * a * b^-1)^3,(a, b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^-1 * a^2 * b ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7, 5, 6, 3) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-1 * a^-1 * b^-1 * a^-2 * b * a^2 * b^-1 * a, a^-1 *b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a * b^-2 * a^-2 * b^-1 * a^-1 * b^-2 * a * b^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4) >,
    Group< a,b | [ a^4, b^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a^-1 * b * a^-2 * b^-1 * a^-1 * b^-1 *a * b * a^2 * b^-1 * a * b, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta + 4,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4)(5, 6, 7) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a)^5, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a^-1 * b* a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b * a^2 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4)(5, 7, 6) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a^-1)^5, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a *b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 * b * a^2 * b * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 3,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5)(6, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, (a^-1 * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 *a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 * a)^5, b^-1 * a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^2 * a * b * a, a^-1 * b^-2 * a^-1 * b^-2 * a * b^-1 * a^-1 * b^2 * a^-1 * b * a * b ] >,ideal< R | [5,xcom + 3*zeta + 2,x12 + zeta + 1,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5, 6) >,
    Group< a,b | [ a^4, b^5, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (b^-1 * a)^5, b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 *b^2 * a^-1 * b * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5, 7) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^4, b * a * b * a * b^-1 * a^-1 * b^-1 * a^2 * b^2 * a^-1, a^-2 * b * a^-2 * b *a^2 * b * a^2 * b * a^2 * b, a^-1 * b * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^2, b^2 * a * b^-1 * a^-2 * b^-1 * a^-1 * b^-2 * a^2 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6, 5) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, a * b^2 * a^-2 * b^-1 * a * b^2 * a^2 * b^-1 ] >,
    ideal<R | [5,xcom + zeta + 3,x12 + zeta + 1,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6, 7) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a^-1 * b^2 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b^-1 ]>,
    ideal< R | [5,xcom + zeta + 3,x12 + 4*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6)(5, 7) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b^2 * a *b^2 * a * b, a^-1 * b * a^-2 * b^-1 * a^-1 * b^-1 * a * b^-1 * a^2 * b^-2 * a^-1 * b, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 2,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7, 5) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, b * a * b^-1 * a * b^-1 * a^-1 * b^-2 * a^2 * b * a^-1, a^-2 * b^-1 * a^-2* b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a * b * a^-2 * b^-1 * a * b^-1 * a * b^2 * a * b^2, b^2 * a^-1 * b^-1 * a^-2 * b^-1 * a * b^-2 * a^2 * b^-1 * a ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + zeta + 1,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7, 6) >,
    Group< a,b | [ a^4, b^5, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (b^-1 * a^-1)^5, b * a^-1 * b^-1 * a * b^-1 * a^-1 *b^-1 * a * b^2 * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7)(5, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 *a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 * a^-1)^5, b^-1 * a * b^-1 * a^-2 * b^-1 * a * b^2 * a^-1 * b * a^-1, a * b^-2 * a^-1 * b^-2 * a^-1 * b^-1 * a * b^-1 * a^-1 * b^2 * a^-1 * b] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 3*zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4)(3, 5)(6, 7) >,
    Group< a,b | [ a^4, b^6, (b^-1 * a)^3, (a^-1 * b^-1)^4, a * b * a^-2 * b * a^-1 * b^-1 * a * b^2 * a * b^-2 ]>,
    ideal< R | [5,xcom + zeta + 1,x12 + 4,xm12,xm21,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4)(3, 5, 7) >,
    Group< a,b | [ a^4, b^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a * b * a^-2 * b^-1 * a^-1 *b^-1 * a * b * a^2 * b^-1 * a^-1 * b^-1, (a * b^-1)^6, (b^-1 * a^-1)^7, b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b^-1 * a^-1 * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 3,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3, 5) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1 * b^-1)^3, (a^-1 * b^-2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3, 5, 6, 7) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^5, (a^-1 * b^2 * a * b^-1)^2, a * b^-2 * a^-2 * b^-1 * a * b^-2 * a^2 *b^-1, b * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^2 * b * a * b ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6)(3, 5) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^6, a * b^-2 * a * b^-1 * a^-1 * b^-1* a * b^-1 * a * b^2 * a^-1 * b, b * a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^2 * a^-1 * b^2 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6, 3, 5, 7) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-2 * a * b^-1 * a^-1 * b^2 * a^2 * b^-1, a * b^-2 * a^-2 * b^-1 * a * b^-2 *a^2 * b^-1, a * b^-1 * a^-2 * b^-2 * a^-1 * b^-1 * a^2 * b^3 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 2,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7, 6, 3, 5) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1 * b^-1)^3, (b^-1 * a^-1)^5, (a^-1 * b^-2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7, 3, 5, 6) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^3, (a * b^-1)^4, a * b^2 * a^-2 * b^-1 * a * b^2 * a^2 * b^-1, a^-1 *b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-3 * a * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4)(3, 6, 5) >,
    Group< a,b | [ a^4, b^3, (a^-1 * b^-1)^4, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b *a^-1 * b * a * b^-1, b * a^-2 * b^-1 * a^-1 * b * a^-2 * b^-1 * a^-1 * b * a^2 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4*zeta,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4)(3, 6, 7) >,
    Group< a,b | [ a^4, b^3, (a * b^-1)^4, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b *a^-1 * b * a * b^-1, b * a^-2 * b^-1 * a^-1 * b * a^-2 * b^-1 * a^-1 * b * a^2 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4)(3, 6)(5, 7) >,
    Group< a,b | [ a^4, b^6, a^-1 * b * a^-2 * b^-1 * a^-1 * b * a^2 * b^-1, b^-2 * a^-2 * b^-2 * a * b^-1 * a * b* a^-1, b^-1 * a^-2 * b^-3 * a^-2 * b^3 * a^2 * b^-2, b^-2 * a * b^-1 * a^-1 * b^-1 * a^-1 * b^3 * a^-1 * b^2 * a ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3, 6, 7, 5) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-2* b^-2 * a^2 * b^-2 * a^2 * b^-1, b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4*zeta + 2,xm12,xm21,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3, 6) >,
    Group< a,b | [ a^4, b^5, a^-1 * b * a^-2 * b^-1 * a^-1 * b * a^2 * b^-1, b^-1 * a^-2 * b^-1 * a * b^-1 * a^-1 * b * a* b^-1 * a^2 * b^-1, (a^-1 * b^-2)^4 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3, 6, 5, 7) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 *a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, a^-1 * b^2 * a * b^-1 * a^-1 * b * a^-1 * b * a^2 * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5)(3, 6) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a)^3, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b * a^-2 * b * a * b^-1 * a^-1* b * a * b^2 * a, a^-1 * b^-1 * a^-1 * b * a^-2 * b^-1 * a^-1 * b * a^2 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta + 4,xm12,xm21,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5, 3, 6, 7) >,
    Group< a,b | [ a^4, b^7, a^-1 * b * a^-2 * b^-1 * a^-1 * b * a^2 * b^-1, (b^-1 * a)^5, b * a^-1 * b^-1 * a^-2 *b^2 * a^-1 * b^-1 * a^2 * b, b^-1 * a * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5, 7, 3, 6) >,
    Group< a,b | [ a^4, b^7, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a * b^-1)^4, b^-1 * a * b * a^-1 * b^-1 * a^-1* b^-2 * a * b^-1, a^-1 * b * a^-2 * b^-2 * a^-1 * b^-1 * a * b^-3 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7, 3, 6, 5) >,
    Group< a,b | [ a^4, b^7, a^-1 * b * a^-2 * b^-1 * a^-1 * b * a^2 * b^-1, (b^-1 * a^-1)^5, b * a * b^-1 * a^-2 *b^2 * a * b^-1 * a^2 * b, b * a * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 3,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7, 5, 3, 6) >,
    Group< a,b | [ a^4, b^7, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^4, b * a^-1 * b * a^-1 * b^-1 * a* b^2 * a * b, a^-1 * b^2 * a^-2 * b^-1 * a^-1 * b^3 * a * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 7)(3, 6) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^3, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b * a^-2 * b * a^-1 * b^-1* a * b * a^-1 * b^2 * a^-1, a * b * a^-2 * b^-1 * a * b * a^2 * b^2 * a^-1 * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4)(3, 7, 5) >,
    Group< a,b | [ a^4, b^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (a^-1 * b^-1)^6, a^-1 * b *a^-2 * b^-1 * a * b^-1 * a^-1 * b * a^2 * b^-1 * a * b^-1, b * a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4)(3, 7)(5, 6) >,
    Group< a,b | [ a^4, b^6, (b^-1 * a^-1)^3, (a * b^-1)^4, a^-1 * b * a^-2 * b * a * b^-1 * a^-1 * b^2 * a^-1 *b^-2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1,x1 + 4,xm1 + 4,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3, 7, 6, 5) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^5, (a * b^2 * a^-1 * b^-1)^2, a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b^-2 *a^2 * b^-1, b^-1 * a * b^-1 * a^-2 * b^-1 * a^-1 * b * a^-1 * b * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 3, 7) >,
    Group< a,b | [ a^4, b^5, (b * a^-1 * b)^3, (a * b^-2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5, 3, 7, 6) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^3, (a^-1 * b^-1)^4, a^-1 * b^2 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b^-1,a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^3 * a * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta,xm12,xm21,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 5, 6, 3, 7) >,
    Group< a,b | [ a^4, b^7, (b * a^-1 * b)^3, (a * b^-2 * a^-1 * b^-1)^2, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6, 3, 7, 5) >,
    Group< a,b | [ a^4, b^7, a * b^-2 * a^-1 * b^-1 * a * b^2 * a^2 * b^-1, a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b^-2* a^2 * b^-1, b^-1 * a^-2 * b^3 * a^-1 * b^-1 * a^2 * b^-2 * a ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 2, 4, 6)(3, 7) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a * b *a^-1 * b^-1 * a^-1 * b, a^-1 * b * a^-2 * b^-1 * a^-1 * b^-1 * a * b^-1 * a^2 * b^-2 * a^-1 * b^-1, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 2)(6, 7) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^5, (b^-1 * a)^5, b^-1 * a^-2 * b^-2 * a * b^-1 * a^-1 * b^2 * a^-1 * b^2 *a, b * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b * a^2 * b^2 * a^-1, a * b^-1 * a * b * a^-1 * b^-1 * a^-1 * b^2 * a^2 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 2)(5, 6) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^5, b^-1 * a^-2 * b^-2 * a^-1 * b^-1 * a * b^2 * a * b^2 * a^-1, b * a^-2 *b^-1 * a^-2 * b^-1 * a * b * a^2 * b^2 * a, a * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b^2 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 2)(5, 7) >,
    Group< a,b | [ a^4, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b^-1 * a^-1 * b^-2 * a * b^2 * a^-1 * b, a^-2 *b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, b^-1 * a^-2 * b^-2 * a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b * a^2 * b^2 * a ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 3, 2) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1)^3, (a * b^2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 2,xm21 + 2,xm2m1,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 6, 7, 3, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^3, (a^-1 * b^-1)^4, b * a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^2 * b^-1 *a^2 * b ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta,xm12,xm21,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 7, 6, 3, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1 * b^-1)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1,(b^-1 * a^-1)^5, (b^-1 * a)^5, a^-1 * b^2 * a^-2 * b^-1 * a * b^-1 * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 7, 5, 3, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^3, (b^-1 * a)^5, a * b^2 * a^-2 * b^-1 * a * b^2 * a^2 * b^-1, b^-3 * a* b^-1 * a^-1 * b^2 * a^-1 * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 3, 2) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1,(a^-1 * b^-1 * a * b^-1)^3, a * b * a * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b * a * b^-1, b^-1 * a^-2 * b^2 * a^-2 * b^-1 * a^-1 * b^2 * a^-1 * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 5, 7, 3, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^3, (b^-1 * a^-1)^5, a^-1 * b^2 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b^-1, b *a^-2 * b * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 6, 5, 3, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^3, (a * b^-1)^4, b^-1 * a^-2 * b * a^-2 * b * a^-1 * b^-1 * a^2 * b *a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 3, 2) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a)^3, (b^-1 * a^-1)^5, (a^-1 * b^2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 3,xm12,xm21,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 5, 6, 3, 2) >,
    Group< a,b | [ a^4, b^7, (b * a^-1 * b)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 *a^-1)^5, (b^-1 * a)^5, a * b^2 * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 3*zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2) >,
    Group< a,b | [ a^4, b^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 *a * b^-1 * a^2 * b * a * b, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2)(5, 6, 7) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a)^5, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a * b^-1* a * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b * a^2 * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta + 3,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2)(5, 7, 6) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a^-1)^5, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a * b* a^-1 * b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 3,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 2)(6, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, (a^-1 * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 *a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-1 * b * a * b * a^2 * b * a * b^2 * a^-1, (b^-1 * a)^5, a * b^-2 * a * b^-1 * a^-1 * b^-1 * a * b^2 * a * b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 4*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 6, 2) >,
    Group< a,b | [ a^4, b^5, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (b^-1 * a)^5, b * a^-1 * b^-1 * a * b^-1 * a^-1 *b^-1 * a * b * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 7, 2) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a^-1 * b^-1 * a^-2 * b^2 * a^-1 * b^-1 * a^2 * b^2 ]>,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 5, 2) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, b * a^-2 * b^-1 * a * b^-1 * a^-1 * b * a^-1 * b * a * b, a^-2 * b^-1 *a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, b * a * b^2 * a * b^-1 * a * b^-1 * a^2 * b * a * b, b * a^-2 * b * a^-1 * b^-2 * a * b * a^2 * b * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 7, 2) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^4, b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a^2 * b^-1, a^-2 * b * a^-2* b * a^2 * b * a^2 * b * a^2 * b, b * a^-1 * b^2 * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b * a^-1 * b, b * a^-2 * b * a * b^-2 * a^-1 * b * a^2 * b * a * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 2)(5, 7) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a * b^-2 * a^-2 * b^-1 * a^-1 * b^-1 * a * b^-1 *a^2 * b * a * b, a * b^-2 * a * b * a^-1 * b^-1 * a * b^2 * a * b * a^-1 * b^-1, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 5, 2) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, a * b^-1 * a^-2 * b^2 * a * b^-1 * a^2 * b^2 ] >,
    ideal<R | [5,xcom + zeta + 3,x12 + zeta + 1,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 6, 2) >,
    Group< a,b | [ a^4, b^5, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (b^-1 * a^-1)^5, b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1* b * a * b^2 * a ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 2)(5, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 *a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 * a^-1)^5, b * a^-2 * b * a^-1 * b^-1 * a^-1 * b * a^-1 * b^2 * a^-1, a * b * a^-2 * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a * b^2 * a^2 * b^-1 ]>,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 2*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2)(3, 5)(6, 7) >,
    Group< a,b | [ a^4, b^6, (b^-1 * a^-1)^3, (a * b^-1)^4, b^-1 * a^-1 * b^2 * a^-1 * b^-1 * a * b * a^2 * b *a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 4,xm1 + 4,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2)(3, 5, 6) >,
    Group< a,b | [ a^4, b^3, (a * b^-1)^4, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b *a^-1 * b^-1 * a * b, b^-1 * a^-2 * b * a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2)(3, 5, 7) >,
    Group< a,b | [ a^4, b^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (a * b^-1)^6, a^-1 * b^-1 *a^-2 * b * a * b^-1 * a^-1 * b^-1 * a^2 * b * a * b^-1, (b^-1 * a^-1)^7, b * a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 3,xm12 + 3,xm21 + 3,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 5, 2) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1 * b^-1)^3, (a * b^-2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 2,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 5, 6, 7, 2) >,
    Group< a,b | [ a^4, b^7, (b * a^-1 * b)^3, (b^-1 * a)^5, (a^-1 * b^-2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta + 2,xm12 + 2,xm21 + 2,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 5, 7, 6, 2) >,
    Group< a,b | [ a^4, b^7, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^4, a^-1 * b^-2 * a * b^-1 * a * b* a^-1 * b^-2, b * a * b^3 * a^-1 * b^-1 * a^2 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 7, 3, 5, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-2* b^-2 * a^2 * b^-2 * a^2 * b^-1, b^-1 * a * b * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta + 4,xm12,xm21,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 2)(3, 5) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^6, a * b^-2 * a^-2 * b^-1 * a^-1 *b^-1 * a * b^-1 * a^2 * b * a * b^-1, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b * a^-1 * b, b * a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a^-1 *b^-1 * a ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 3, 5, 7, 2) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-1 * a * b^-2 * a^-1 * b^-1 * a^2 * b^2, a * b^-1 * a^-2 * b^-2 * a * b^-1 *a^2 * b^-2, b^3 * a^-2 * b^-1 * a^-1 * b^-2 * a^2 * b^-1 * a ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 6, 3, 5, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^5, (a^-1 * b^2 * a * b^-1)^2, a^-1 * b^-1 * a^-2 * b^-2 * a^-1 * b^-1 *a^2 * b^-2, b^-1 * a^-2 * b * a^-1 * b * a^-1 * b^-1 * a^2 * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 2)(3, 5) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^3, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b^-1 * a^-2 * b^-1 * a * b* a^-1 * b^-1 * a * b^2 * a, a * b^-2 * a^-2 * b^-1 * a * b^-1 * a^2 * b * a * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 3, 5, 6, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^3, (a^-1 * b^-1)^4, b * a^-1 * b^-1 * a^-2 * b^2 * a^-1 * b^-1 * a^2 * b,a^-1 * b^-3 * a^-1 * b^-1 * a * b * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4,xm12,xm21,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2)(3, 6)(5, 7) >,
    Group< a,b | [ a^4, b^6, a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^2 * b, b * a^-1 * b * a^-1 * b^-1 * a * b^2 *a^2 * b, b^-1 * a^-2 * b^-3 * a^-2 * b^3 * a^2 * b^-2, b * a^-1 * b^-3 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-2 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 3*zeta + 1,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta + 3,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 6, 2) >,
    Group< a,b | [ a^4, b^5, a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^2 * b, b^-1 * a^-2 * b^-1 * a * b * a^-1 * b^-1 * a* b^-1 * a^2 * b^-1, (a^-1 * b^-2)^4 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta + 4,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 3, 6, 7, 2) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^2 * b, (b^-1 * a)^5, a^-1 * b^2 * a^-2 * b^-1* a^-1 * b^2 * a^2 * b^-1, b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 3, 6, 5, 2) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^2 * b, (b^-1 * a^-1)^5, a * b^2 * a^-2 * b^-1* a * b^2 * a^2 * b^-1, a^-1 * b^-2 * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2)(3, 7, 5) >,
    Group< a,b | [ a^4, b^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (a^-1 * b^-1)^6, a * b^-1 *a^-2 * b * a^-1 * b^-1 * a * b^-1 * a^2 * b * a^-1 * b^-1, b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b * a^-1 * b * a ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2)(3, 7, 6) >,
    Group< a,b | [ a^4, b^3, (a^-1 * b^-1)^4, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b *a^-1 * b^-1 * a * b, b^-1 * a^-2 * b * a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2)(3, 7)(5, 6) >,
    Group< a,b | [ a^4, b^6, (b^-1 * a)^3, (a^-1 * b^-1)^4, b^-1 * a * b^2 * a * b^-1 * a^-1 * b * a^2 * b * a *b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7, 6, 5, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1 * b^-1)^3, (b^-1 * a^-1)^5, (a * b^-2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7, 2) >,
    Group< a,b | [ a^4, b^5, (b * a^-1 * b)^3, (a^-1 * b^-2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 3,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7, 5, 6, 2) >,
    Group< a,b | [ a^4, b^7, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a * b^-1)^4, a * b^-2 * a^-1 * b^-1 * a^-1 * b* a * b^-2, b^-3 * a * b^-1 * a^-1 * b^-2 * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 2)(3, 7) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a)^3, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b^-1 * a^-2 * b^-1 * a^-1 * b* a * b^-1 * a^-1 * b^2 * a^-1, a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b * a^-1 * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3*zeta + 1,xm12,xm21,xm2m1 + 2*zeta + 3,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 3, 7, 6, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^3, (a * b^-1)^4, b * a * b^-1 * a^-2 * b^2 * a * b^-1 * a^2 * b, a^-1 *b^3 * a^-1 * b^-1 * a * b * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 6, 3, 7, 2) >,
    Group< a,b | [ a^4, b^7, (a * b^2 * a^-1 * b^-1)^2, (b^-1 * a)^5, a * b^-1 * a^-2 * b^-2 * a * b^-1 * a^2 *b^-2, b * a^-2 * b * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b^2 * a ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 3, 7, 5, 2) >,
    Group< a,b | [ a^4, b^7, a * b^-1 * a^-1 * b^-2 * a * b^-1 * a^2 * b^2, a^-1 * b^-1 * a^-2 * b^-2 * a^-1 * b^-1* a^2 * b^-2, a * b^-2 * a^-2 * b^-1 * a^-1 * b^3 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 3,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 5, 3, 7, 2) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 *a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, b^-1 * a^-1 * b * a * b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 2)(3, 7) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, a * b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 *a^-1 * b^2 * a^-1 * b, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(3, 5, 6, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2* a^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 * a)^5, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^-1 * a^-1 * b^-1, a * b^-2 * a^-2* b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b * a^2 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(3, 5, 7, 6) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^3, a * b^-2 * a^-2 * b^-1 * a * b^2 * a^2 * b^-1, b^-1 * a^-1 * b^-2 * a^-1* b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta,x12,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 5, 6) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a^-1 * b^-1 * a^-2* b^-2 * a^-1 * b^-1 * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 3*zeta + 2,xm12,xm21,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 5, 7) >,
    Group< a,b | [ a^4, b^5, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, a * b^2 * a^-2 * b^-1 * a^-1 * b^-1 * a^2 *b^-1 * a^2 * b, a * b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 3, 5) >,
    Group< a,b | [ a^4, b^5, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, b * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b^-2 *a^2 * b * a, (a^-1 * b^-1)^6, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-1 * a * b * a^-1 * b^-1 * a * b^-1 * a * b^-1 * a^2 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 7)(3, 5) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^-1 * b^2 * a * b^-1, (a * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 * a^2* b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 2*zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 3, 5) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-2 *b^-1 * a * b^-1 * a^-1 * b * a * b * a^-1 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, a * b^-1 * a^-2 * b * a^-1 * b^-1 * a * b^-1 * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 6)(3, 5) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, a * b^-2 * a * b^-1 * a * b^2 * a * b^-1,a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 * a^-1)^5, a * b * a^-2 * b^-1 * a^-1 * b^-1 * a * b * a * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(3, 6, 7, 5) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a)^3, a * b^-2 * a^-2 * b * a * b^2 * a^2 * b, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 *a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 2*zeta + 4,xm12,xm21,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(3, 6) >,
    Group< a,b | [ a^4, b^2, a^-1 * b * a^-2 * b * a^2 * b * a^2 * b * a^-1, (b * a^-1)^7, (a * b * a^-1 * b)^6, a^-1 * b *a^-2 * b * a^-1 * b * a^-2 * b * a^-1 * b * a^-2 * b * a * b * a^2 * b * a * b * a^2 * b * a^-1 * b * a^2 * b, b * a * b * a^-1 * b * a * b * a * b * a^-1 * b * a^-1 * b * a * b *a^-1 * b * a * b * a * b * a^2 * b * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 4*zeta + 4,xm2 + zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(3, 6, 5, 7) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^3, a^-1 * b^-2 * a^-2 * b * a^-1 * b^2 * a^2 * b, b^-1 * a^-1 * b^-2 * a^-1* b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 6, 5) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a * b^-1 * a^-2* b^-2 * a^-1 * b * a * b * a^-1 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, a * b * a^-1 * b * a^-1 * b^-1 * a^-1 * b * a^-1 * b * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 6, 7) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b * a^-1 * b^-1 *a * b^-1 * a^-1 * b^2 * a^2 * b * a, a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a^2 * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 2*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 6)(5, 7) >,
    Group< a,b | [ a^4, b^4, a^-1 * b^-1 * a^2 * b^-1 * a^-1, b^-2 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a * b^2* a * b^2 * a^-1, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a * b * a, b^-1 * a * b * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a * b^2 * a *b * a * b^2 * a * b^-1, b^-1 * a * b * a * b^-2 * a^-1 * b * a^-1 * b^-2 * a^-1 * b^-1 * a * b^2 * a * b * a * b^2 * a * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 2*zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5)(3, 6, 7) >,
    Group< a,b | [ a^4, b^3, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (b^-1 * a)^5, (a^-1 * b^-1)^6, a^-1 * b^-1 * a^-1* b * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a * b * a * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 3, 6) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a^-1 * b^-2 * a^-2* b^-1 * a^-1 * b^-2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 4*zeta + 2,xm12,xm21,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 7)(3, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a * b^-2 * a^-1 * b^2 * a^2 * b^-1, (a * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 * a^2* b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, a * b * a * b^-1 * a^-1 * b^-1 * a^-1 * b * a^2 * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 3*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 5)(3, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^-1 * b^2 * a * b^-1, (a^-1 * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 *a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-1 * a * b * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4*zeta,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7)(3, 6, 5) >,
    Group< a,b | [ a^4, b^3, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (b^-1 * a^-1)^5, (a * b^-1)^6, a^-1 * b * a^-1 *b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-1 * a * b * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3*zeta + 3,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 3, 6) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a * b^-2 * a^-2* b^-1 * a * b^-2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(3, 7, 6, 5) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2* a^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 * a^-1)^5, a * b^-1 * a * b * a * b * a^2 * b^-1 * a * b^2 * a^2 * b ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(3, 7, 5, 6) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a)^3, a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b^-1, b^-1 * a^-1 * b^-2 *a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 2*zeta + 3,xm12,xm21,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7, 5) >,
    Group< a,b | [ a^4, b^5, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, a * b^2 * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b* a^2 * b, (a^-1 * b^-1)^6, (a^-1 * b^-1 * a^-1 * b)^3, a^-1 * b * a^-1 * b * a^-1 * b^-1 * a * b * a * b^-1 * a^2 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7, 6) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a * b^-1 * a^-2* b^-2 * a * b^-1 * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 3*zeta,x12,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 3, 7) >,
    Group< a,b | [ a^4, b^5, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b * a^-1 * b^-1 *a * b^-1 * a^-1 * b * a * b * a^2 * b, (a^-1 * b^-1 * a * b^-1)^3, a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4*zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 3,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 6)(3, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^2 *a^-1 * b^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, (b^-1 * a)^5, (a, b)^3, a * b^-1 * a^-1 * b * a * b^-2 * a^2 * b * a^-1 * b * a^2 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 5)(3, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a * b^-2 * a^-1 * b^2 * a^2 * b^-1, (a^-1 * b^-1)^4, a^-2 * b^-1 * a^-2 * b^-1 *a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-1 * a^2 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4*zeta,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 3, 7) >,
    Group< a,b | [ a^4, b^5, b^-1 * a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, b * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 *a^2 * b^2 * a, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta + 3,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3*zeta + 1,x1 + 4,xm1 + 4,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 3, 5)(6, 7) >,
    Group< a,b | [ a^4, b^6, (b^-1 * a^-1)^5, (b^-1 * a)^5, b^-1 * a^-2 * b * a^-1 * b^2 * a * b * a^2 * b^-1, b^-2* a * b^-3 * a^-1 * b^3 * a^2 * b^-1, b^-1 * a * b^-3 * a^-2 * b^-1 * a^2 * b^3 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 3, 5, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, (a^-1 * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 *b^2 * a^-1 * b^2 * a^-1, (b^-1 * a)^5, b^-1 * a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^2 * a^-1 * b^-1 * a, a^-1 * b^-1 * a^-2 * b^-2 * a^-1 * b^-1 * a * b^2 * a^2 * b * a^2 * b ] >,ideal< R | [5,xcom + 3*zeta + 2,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 3, 5) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, (a^-1 * b^-1 * a * b^-1)^3, b * a^-2 * b^-2 * a^-1 * b^-1 * a* b^-1 * a^2 * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom,x12 + zeta + 1,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 3, 5, 7, 6) >,
    Group< a,b | [ a^4, b^7, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-2* b^-2 * a^2 * b^-2 * a^2 * b^-1, (b^-1 * a^-1)^5, b * a^-1 * b^-1 * a^-1 * b^2 * a * b^-1 * a^2 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 3*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 7, 2, 3, 5) >,
    Group< a,b | [ a^4, b^7, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^4, (a * b^-2 * a^-1 * b^-1)^2,(b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 4*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 2, 3, 5, 7) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, (a^-1 * b^-3)^2, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1* a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, a * b^-1 * a^-2 * b * a^-1 * b^-1 * a^-1 * b * a^2 * b * a^2 * b^-2 ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7)(2, 3, 5) >,
    Group< a,b | [ a^4, b^3, (a * b^-1)^4, (b^-1 * a^-1)^5, a^-1 * b^-1 * a * b * a^-1 * b * a^-2 * b^-1 * a^2 * b^-1* a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 2, 3, 5, 6) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^5, b^-1 * a * b * a^-1 * b^-1 * a^-1 * b * a^2 * b^-2, (b^-1 * a)^5,b^-1 * a^-2 * b * a * b^-1 * a * b * a^-1 * b^-2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 3, 6, 5) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 *b^2 * a^-1 * b^2 * a^-1, (b^-1 * a^-1)^5, b^-1 * a * b * a^-1 * b * a^-2 * b^-1 * a * b^2 * a, a^-1 * b * a^-2 * b * a * b^-1 * a * b * a^2 * b * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 2*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 3, 6, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, (a^-1 * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 *b^2 * a^-1 * b^2 * a^-1, b^-1 * a^-1 * b * a * b * a^2 * b^-1 * a^-1 * b^2 * a^-1, (b^-1 * a)^5, a * b * a^-2 * b * a^-1 * b^-1 * a^-1 * b * a^2 * b * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 3, 6)(5, 7) >,
    Group< a,b | [ a^4, b^6, (b^-1 * a^-1)^3, (b^-1 * a)^3, b^-1 * a^-2 * b^-3 * a^-2 * b^3 * a^2 * b^-2, a^-2 *b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a * b^2 * a^-1 * b^-2)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12,xm12,xm21,xm2m1,x1 + 4,xm1 + 4,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 3, 6, 7, 5) >,
    Group< a,b | [ a^4, b^7, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1)^4, (b^-1 * a)^5, (a^-1 * b^-2 * a* b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 4,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 3, 6) >,
    Group< a,b | [ a^4, b^5, (b^-1 * a^-1)^3, (b^-1 * a)^3, b * a^-2 * b^2 * a^-2 * b^2 * a^2 * b^2 * a^2 * b, a^-1 *b^-2 * a^-1 * b^2 * a^-1 * b^-1 * a * b^2 * a * b^-2 * a * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12,xm12,xm21,xm2m1,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 3, 6, 5, 7) >,
    Group< a,b | [ a^4, b^7, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a * b^-1)^4, (b^-1 * a^-1)^5, (a * b^-2 * a^-1* b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5)(2, 3, 6) >,
    Group< a,b | [ a^4, b^3, (a^-1 * b^-1)^4, (b^-1 * a)^5, a * b * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a^2 * b^-1* a^2 * b ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 4*zeta,xm12 + 2,xm21 + 2,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 2, 3, 6, 7) >,
    Group< a,b | [ a^4, b^7, (a * b^-1)^2, (a^-1 * b^-1)^4, (a^-1 * b^-2)^6, a * b * a^-1 * b^-1 * a * b * a^-1 *b^-1 * a * b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b * a * b^-1 * a^-1 * b * a * b^-2, b^2 * a^-1 * b^-1 * a * b * a^-1 * b^-2 * a * b * a * b^-1 * a^-1 * b * a * b^-1 * a^-1 * b^2 *a * b ] >,
    ideal< R | [5,xcom + 3,x12 + zeta + 1,xm12 + 4*zeta + 4,xm21 + zeta,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 7, 2, 3, 6) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 *a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, (b^-1 * a)^5, a^-1 * b^2 * a * b^-1 * a * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + zeta + 1,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 2, 3, 6, 5) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^2, (a * b^-1)^4, (a * b^-2)^6, a^-1 * b * a * b^-1 * a^-1 * b * a * b^-1* a^-1 * b * a * b^-1 * a^2 * b^-1 * a * b * a^-1 * b^-1 * a * b * a^-1 * b^-2, b^2 * a * b^-2 * a^-1 * b * a * b^-1 * a^-1 * b * a * b^-1 * a * b^-2 * a * b * a^-1 * b^-1 * a * b] >,
    ideal< R | [5,xcom + 3,x12 + 4*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 5, 2, 3, 6) >,
    Group< a,b | [ a^4, b^7, (a * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-2* b^-2 * a^2 * b^-2 * a^2 * b^-1, (b^-1 * a^-1)^5, a * b^2 * a^-1 * b^-1 * a^-1 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7)(2, 3, 6) >,
    Group< a,b | [ a^4, b^3, (a * b^-1)^4, (b^-1 * a^-1)^5, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a^2 * b^-1* a^2 * b ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 2*zeta,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 3,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 3, 7, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-2 * b^-2 * a^2 * b^2 * a^2 * b^-1, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 *b^2 * a^-1 * b^2 * a^-1, (b^-1 * a^-1)^5, b^-1 * a * b^-1 * a^-2 * b^-1 * a * b^2 * a * b^-1 * a^-1, a * b * a^-2 * b^-2 * a^-1 * b^-1 * a * b^2 * a^2 * b^-1 * a^2 * b ] >,
    ideal<R | [5,xcom + 3*zeta + 2,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 3, 7)(5, 6) >,
    Group< a,b | [ a^4, b^6, (b^-1 * a^-1)^5, (b^-1 * a)^5, b^-1 * a^-2 * b * a * b^2 * a^-1 * b * a^2 * b^-1, b^-2* a^-1 * b^-3 * a * b^3 * a^2 * b^-1, b^-1 * a^-1 * b^-3 * a^-2 * b^-1 * a^2 * b^3 * a ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2,xm12 + 2,xm21 + 2,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 3, 7) >,
    Group< a,b | [ a^4, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, (a^-1 * b^-1 * a * b^-1)^3, (a * b * a * b^-1 * a^-1 *b^-1)^2, a * b^-1 * a^-1 * b * a * b * a^2 * b^-2 * a^2 * b^2 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 3, 7, 5, 6) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 *a^-2 * b^-2 * a^2 * b^-2 * a^2 * b^-1, (b^-1 * a)^5, a * b^-2 * a^-1 * b * a^-1 * b^-2 * a^2 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 4*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5)(2, 3, 7) >,
    Group< a,b | [ a^4, b^3, (a^-1 * b^-1)^4, (b^-1 * a)^5, a * b^-1 * a^-1 * b * a * b * a^2 * b^-1 * a^2 * b^-1 *a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + 4,xm1 + 4,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 2, 3, 7, 6) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^5, b^-1 * a^-2 * b * a^-1 * b^-1 * a^-1 * b * a * b^-2, (b^-1 * a)^5,b^-1 * a^-1 * b * a * b^-1 * a * b * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2,xm12 + 2,xm21 + 2,xm2m1 + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 2, 3, 7, 5) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, (a * b^-3)^2, a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 *a^2 * b^-1 * a^2 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, a * b * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 5, 2, 3, 7) >,
    Group< a,b | [ a^4, b^7, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, (a * b^-1)^4, (b^-1 * a^-1)^5, (a^-1 * b^-2 * a* b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 3*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 5)(3, 6, 7) >,
    Group< a,b | [ a^4, b^6, (a * b^-1)^4, (b * a^-1 * b)^3, a^-1 * b^2 * a^-2 * b^-1 * a^-1 * b^2 * a^2 * b^-1, a* b^-3 * a^-2 * b * a * b * a * b^2, b^-1 * a * b * a^-1 * b^-1 * a^-1 * b^3 * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 5, 3, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a * b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a *b^2 * a^-1 * b^-1 * a * b^-1, a * b^-1 * a * b * a^-1 * b^-1 * a^-1 * b * a^2 * b * a^2 * b, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 5, 7)(3, 6) >,
    Group< a,b | [ a^4, b^6, b * a^-2 * b^2 * a^2 * b, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b * a^-1, a^-1 *b^2 * a^-1 * b^-1 * a * b^-2 * a * b^-1, (a^-1 * b^-1)^6, b^-2 * a^-1 * b * a^-2 * b^-1 * a * b^-2 * a^-1 * b^-1 * a^-1, b^-1 * a * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b* a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 4,xm1 + 4,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 5)(3, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1)^6, a * b * a^-2 * b^-1 *a^-1 * b^-1 * a * b * a^2 * b^-1 * a^-1 * b^-1, a * b^-1 * a * b * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a^2 * b^-1, b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1* a^-1 * b * a ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 2,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 5, 3, 6, 7) >,
    Group< a,b | [ a^4, b^7, (a * b^-1)^4, (b * a^-1 * b)^3, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a *b^-1 * a^-1 * b, (a^-1 * b * a * b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 5, 7, 3, 6) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a * b * a^-1 * b^-1* a^-1 * b^3 * a, (a * b^2 * a^-1 * b^-1)^2, b * a^-2 * b^-1 * a * b^-1 * a^-1 * b^-2 * a * b^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 6, 7, 2, 5) >,
    Group< a,b | [ a^4, b^7, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-1)^4, (a^-1 * b^-3)^2, (a^-1 * b^-1)^6, b^-2 *a^-2 * b * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 6)(2, 5) >,
    Group< a,b | [ a^4, b^4, a^-1 * b^-2 * a^2 * b^2 * a^-1, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^2 * a *b^-1 * a^-1 * b^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1, (a * b^-1)^6, b^-2 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a * b^2 * a * b^2 *a^-1, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b * a * b * a, b^-1 * a^-1 * b * a^-2 * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b * a^-1 * b * a ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 3,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 6, 2, 5, 7) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a * b * a^-1 * b^-1* a^-1 * b^-1 * a * b^-2 * a^-1, b^-1 * a * b * a * b^-1 * a^-1 * b^-1 * a^2 * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 4,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 3, 6, 2, 5) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-1* a * b^-1 * a * b, (a * b * a^-1 * b * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7)(2, 5)(3, 6) >,
    Group< a,b | [ a^4, b^6, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b^-1)^2, b^-1 * a^-2 * b^-3 * a^-2 * b^3 * a^2 *b^-2, a * b^-3 * a * b^-1 * a^-2 * b^-1 * a^2 * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 4,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 7, 2, 5, 3, 6) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a^-1 * b^-2 * a^-2 * b^-1 * a * b^-2 * a * b] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 5)(3, 7, 6) >,
    Group< a,b | [ a^4, b^6, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a * b^-3 * a^-2 * b^-1 * a * b^-1 * a * b^-2,b * a^-2 * b * a * b^-1 * a^-1 * b * a^2 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 1,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 5, 3, 7) >,
    Group< a,b | [ a^4, b^4, b^-2 * a^-1 * b^2 * a^-1, a^-1 * b^-1 * a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b *a^2 * b^-1 * a^-1, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a^-1 * b^-1 * a^-1, a^-1 * b * a * b^-1 * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b *a^2 * b * a * b * a^2 * b * a^-1, b^-1 * a^-2 * b * a * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^-2 * b * a^-1 * b * a^2 * b * a * b * a^2 * b^-1 * a ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 5, 6)(3, 7) >,
    Group< a,b | [ a^4, b^6, (a * b^-1)^4, (b * a^-1 * b)^3, a^-1 * b^-3 * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b^-2,b^-1 * a^-1 * b * a * b^-1 * a^-1 * b * a^2 * b^3 * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta + 3,x1 + 4,xm1 + 4,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 5)(3, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1)^6, a * b^-1 * a^-2 * b^-1 *a^-1 * b^-1 * a * b^-1 * a^-1 * b * a * b^-1, b * a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 2,x1 + 4,xm1 + 4,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 5, 3, 7, 6) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a^-1 * b^2 * a^-1 * b^-1 * a * b^2 * a^2 * b] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 5, 6, 3, 7) >,
    Group< a,b | [ a^4, b^7, (a * b^-2)^2, (a * b^-1 * a^-1 * b^-1)^2, (a^-1 * b^-1)^6, (a^-1 * b^-1 * a^-1 *b^-2)^3, a * b^2 * a^-2 * b^-1 * a^-1 * b^3 * a^-1 * b^-1 * a^2 * b * a * b^-2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 2,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7, 6, 2, 5) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-2)^2, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b, (a * b^-1)^6, (a^-1 * b* a^-1 * b^2)^3, a^-1 * b^2 * a^-2 * b^-1 * a * b^3 * a * b^-1 * a^2 * b * a^-1 * b^-2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + zeta + 1,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4*zeta,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7)(2, 5) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a^-1 * b^-2 * a * b^-1 * a^-1 * b^-1 *a^-1 * b^2 * a * b^-1 * a^-1 * b^-1, a * b * a^-2 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a^2 * b^-1, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 1,xm12 + 3,xm21 + 3,xm2m1 + 2*zeta + 3,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7, 2, 5, 6) >,
    Group< a,b | [ a^4, b^7, (a * b^-1)^4, (b * a^-1 * b)^3, a * b^2 * a * b^-1 * a^-1 * b^2 * a^2 * b ] >,
    ideal<R | [5,xcom + zeta + 1,x12 + 3*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 3, 7, 2, 5) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, a^-1 * b^-2 * a^-1 * b^-1* a^-1 * b^-1 * a * b^-3, b * a^-2 * b^-1 * a * b^-1 * a^-1 * b * a^-1 * b^-2 * a, b * a^-1 * b * a * b^-1 * a^-1 * b * a^-1 * b * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 3,x1 + 4,xm1 + 4,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6)(2, 5)(3, 7) >,
    Group< a,b | [ a^4, b^6, b * a^-2 * b^2 * a^2 * b, a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b * a^2 * b, b^-2 * a^-1* b^-3 * a^-1 * b^3 * a^-1 * b^-1, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b * a * b^-1 * a^-1, a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^-1 * a * b^3 * a^-1 * b *a * b^2 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 6, 2, 5, 3, 7) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a * b^-1 * a^-1 *b^-1 * a^-1 * b * a * b^-1 * a^-1 * b^-1, a * b^2 * a^-1 * b^-1 * a^-1 * b * a * b * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 2,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 4,xm1 + 4,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 6, 5)(3, 7) >,
    Group< a,b | [ a^4, b^6, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a * b^2 * a^-2 * b^-1 * a * b^2 * a^2 * b^-1,a^-1 * b^-3 * a^-2 * b * a^-1 * b * a^-1 * b^2, b^-1 * a * b^-1 * a^-2 * b^-1 * a^-1 * b * a * b^-1 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 6)(3, 7, 5) >,
    Group< a,b | [ a^4, b^6, b * a^-2 * b^2 * a^2 * b, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b * a^-1, a^-1 *b^-2 * a^-1 * b^-1 * a * b^2 * a * b^-1, (a * b^-1)^6, b^-2 * a^-1 * b * a^-2 * b^-1 * a * b^-2 * a * b * a, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a *b * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 3,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4)(2, 6, 3, 7) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a^-1 * b^-2 * a * b^-1 * a^-1 * b^-1 *a^-1 * b^2 * a * b^-1 * a * b^-1, a^-1 * b^-1 * a^-1 * b * a * b^-1 * a * b * a^2 * b * a^2 * b, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta + 4,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 6, 3, 7, 5) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a * b^-1 * a^-1 *b^-1 * a^-1 * b^-2 * a^-1 * b^-2, b * a * b^-1 * a * b^-1 * a^-1 * b^-2 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 6, 5, 3, 7) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-3)^2, (a * b^-1)^6, b^-2 * a^-2 *b * a * b^-1 * a^-1 * b * a^2 * b * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + zeta + 1,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 2, 6)(3, 7) >,
    Group< a,b | [ a^4, b^4, a^-1 * b^-2 * a^2 * b^2 * a^-1, (a^-1 * b^-1)^6, a * b^-1 * a^-1 * b^-2 * a^-1 * b^-1 * a* b^-1 * a * b^2 * a * b^-1, a * b^-1 * a^-2 * b^-1 * a * b^-1 * a * b * a^2 * b * a * b^-1, b^-2 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a * b^2 * a * b^2 * a^-1, a^-1 * b^-1 *a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b * a^2 * b^-1 * a^-1, b * a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b * a^2 * b^-1 * a^-1, b * a^-1 * b * a^-1 * b^-1 *a^-1 * b^-1 * a * b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 4,xm1 + 4,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7, 2, 6, 5) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a* b^-1 * a * b^-1, (a * b^-1 * a * b * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7, 5, 2, 6) >,
    Group< a,b | [ a^4, b^7, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-1 * b * a^-1 *b^-1 * a * b * a * b^-2, (a^-1 * b^2 * a * b^-1)^2, b^3 * a^-2 * b^-1 * a^-1 * b^-1 * a * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta + 4,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 3, 7)(2, 6) >,
    Group< a,b | [ a^4, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a * b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a *b^2 * a^-1 * b^-1 * a^-1 * b^-1, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a^2 * b^-1 * a^-1 * b^-1, (b^-1 * a^-1)^7 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 3,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5)(2, 6)(3, 7) >,
    Group< a,b | [ a^4, b^6, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-1)^4, b^-1 * a^-2 * b^-3 * a^-2 * b^3 * a^2 *b^-2, b * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b^3 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta,x1 + 4,xm1 + 4,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 2, 6, 3, 7) >,
    Group< a,b | [ a^4, b^7, (a * b^-1)^4, (b * a^-1 * b)^3, a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1* b^-1 * a * b, (a * b * a^-1 * b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3)(4, 5, 6, 7), (1, 4, 5, 3, 7, 2, 6) >,
    Group< a,b | [ a^4, b^7, (a * b^-1)^4, (b * a^-1 * b)^3, a * b^-2 * a^-2 * b^-1 * a^-1 * b^-2 * a^-1 * b ] >,ideal< R | [5,xcom + zeta + 1,x12 + zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 2,x1 + 4,xm1 + 4,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(4, 5, 6, 7) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a)^5, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1,a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b^2 * a * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 1,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(4, 5, 7, 6) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a^-1)^5, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 *b^-1, a^-1 * b^-1 * a * b * a * b * a^2 * b^-1 * a * b * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 3,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 4, 5)(6, 7) >,
    Group< a,b | [ a^3, b^6, (b^-1 * a^-1)^3, (b^-1 * a)^5, (a * b^-2)^4, b^2 * a^-1 * b^-2 * a * b^-1 * a^-1 * b^3* a^-1 * b * a * b^-1 * a ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12,xm12 + 2,xm21 + 2,xm2m1,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 4, 5, 6) >,
    Group< a,b | [ a^3, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (b^-1 * a)^5, (a^-1 * b^-1)^6, a^-1 * b *a * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b * a * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 2,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 5, 4)(6, 7) >,
    Group< a,b | [ a^3, b^6, (b^-1 * a)^3, (b^-1 * a^-1)^5, (a^-1 * b^-2)^4, a^-1 * b^-2 * a * b * a^-1 * b^-1 *a^-1 * b^2 * a * b^-2 * a * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 3,xm12,xm21,xm2m1 + 2*zeta,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 5, 7, 4) >,
    Group< a,b | [ a^3, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (b^-1 * a^-1)^5, (a * b^-1)^6, a^-1 * b *a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b * a^-1 * b * a * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 5, 6, 7) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a)^5, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1,(a * b^-1 * a * b * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 1,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta + 3,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 5, 7, 6) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a^-1)^5, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 *b^-1, a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b^2 * a * b * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3*zeta + 3,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 5)(4, 6, 7) >,
    Group< a,b | [ a^3, b^6, (a * b^-1)^4, b * a * b^-1 * a^-1 * b^-1 * a^-1 * b^3 * a^-1 * b^-1 * a^-1, (a *b^-2)^4 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta + 2,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 5, 7)(4, 6) >,
    Group< a,b | [ a^3, b^6, (a^-1 * b^-1)^4, b * a^-1 * b * a * b^-1 * a^-1 * b * a^-1 * b^3 * a^-1, (a^-1 *b^-2)^4 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 5)(4, 7, 6) >,
    Group< a,b | [ a^3, b^6, (a^-1 * b^-1)^4, b^-1 * a * b * a^-1 * b * a^-1 * b^3 * a^-1 * b * a^-1, (a^-1 *b^-2)^4 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2)(3, 5, 6)(4, 7) >,
    Group< a,b | [ a^3, b^6, (a * b^-1)^4, b^-1 * a * b * a^-1 * b^-1 * a^-1 * b^3 * a^-1 * b^-1 * a^-1, a * b^-3 *a^-1 * b^-2 * a * b^3 * a^-1 * b^-2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 3,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3)(4, 5)(6, 7) >,
    Group< a,b | [ a^3, b^6, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, (b^-1 * a)^5, a^-1 * b^2 * a^-1 * b^-2 * a *b^-2 * a * b^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3)(4, 5, 6) >,
    Group< a,b | [ a^3, b^3, (b^-1 * a)^5, (a^-1 * b^-1)^6, (a * b^-1 * a^-1 * b^-1)^4, b^-1 * a^-1 * b^-1 * a * b *a^-1 * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b^-1 * a^-1 * b * a * b * a ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta + 2,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 4, 5) >,
    Group< a,b | [ a^3, b^5, (b^-1 * a)^5, (a^-1 * b^-2 * a * b^-1)^2, (a^-1 * b^-2)^4 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 4,x1,xm1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 4, 5, 6, 7) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a)^3, b^-1 * a * b^2 * a^-1 * b^-1 * a^-1 * b^2 * a * b^-2, b * a * b^2 * a *b^-1 * a^-1 * b^-2 * a^-1 * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 3,xm12,xm21,xm2m1 + 4*zeta + 2,x1,xm1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 4, 5, 7, 6) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1)^5, (a * b^-2 * a^-1 * b^-1)^2, (b^-1 * a)^5, (a^-1 * b^3 * a * b^-1)^2 ]>,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 3,x1,xm1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 5, 4) >,
    Group< a,b | [ a^3, b^5, (a * b^-1)^4, (a * b^2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta + 4,x1,xm1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 5, 7, 6, 4) >,
    Group< a,b | [ a^3, b^7, (a * b^-1)^4, (b^-1 * a^-1)^5, (a^-1 * b * a * b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 3,x1,xm1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 5)(6, 7) >,
    Group< a,b | [ a^3, b^4, (a^-1 * b^-1)^4, (b^-1 * a)^5, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a^-1 * b^2 * a^-1 *b^2 * a * b ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 4,xm12 + 2,xm21 + 2,xm2m1 + 4,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 5, 6) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^-2 * a^-1 * b^-1)^2, (b^-1 * a)^5, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1* b * a * b * a * b, b * a^-1 * b^2 * a * b^-1 * a^-1 * b^-1 * a * b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 2,x1,xm1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 5, 7) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, (a^-1 * b^2 * a * b * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1,xm1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 5, 4, 6, 7) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^2 * a^-1 * b^-1)^2, (b^-1 * a)^5, b^-2 * a * b^-1 * a^-1 * b^-1 * a * b^-2 *a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 4,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 2,x1,xm1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 5)(4, 7) >,
    Group< a,b | [ a^3, b^4, (a * b^-1)^4, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a *b^-1 * a^-1 * b, a * b^-2 * a^-1 * b^-1 * a * b^-2 * a^-1 * b^-1 * a * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 3,x1,xm1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 3, 5, 6, 4, 7) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a)^5, b^2 * a * b^-1 * a^-1 * b^-1 * a * b^-2 * a^-1 * b * a, (a^-1 * b^-1 *a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta + 4,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 2,x1,xm1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 5, 3) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^-1)^4, (a^-1 * b^2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4,x1,xm1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 5, 6, 7, 3) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-1)^4, (b^-1 * a)^5, b^-1 * a * b^-2 * a^-1 * b^-1 * a * b * a^-1 * b^2 *a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4*zeta,x1,xm1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 5)(6, 7) >,
    Group< a,b | [ a^3, b^4, (a * b^-1)^4, (b^-1 * a^-1)^5, a^-1 * b * a * b^-1 * a * b^-2 * a^-1 * b^2 * a^-1 * b *a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 5, 6) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, (a * b * a * b^-2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1,xm1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 5, 7) >,
    Group< a,b | [ a^3, b^5, (b^-1 * a^-1)^5, (a * b^-2 * a * b^-1)^2, (a * b^-1 * a * b^-1 * a^-1 * b^-1)^2, b^2 * a^-1* b^-1 * a * b^-1 * a^-1 * b^2 * a * b^2 * a ] >,
    ideal< R | [5,xcom + 3,x12 + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2,x1,xm1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4)(3, 5)(6, 7) >,
    Group< a,b | [ a^3, b^6, (a * b^-1)^4, (b * a^-1 * b)^3, (b^-1 * a^-1)^5, a^-1 * b^-2 * a^-1 * b^-2 * a * b^2 *a * b^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 3,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4)(3, 5, 7) >,
    Group< a,b | [ a^3, b^3, (b^-1 * a^-1)^5, (a * b^-1)^6, (a * b^-1 * a^-1 * b^-1)^4, b * a * b^-1 * a * b^-1 * a^-1* b * a^-1 * b^-1 * a * b * a^-1 * b * a^-1 * b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3*zeta + 3,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 3, 5) >,
    Group< a,b | [ a^3, b^5, (b^-1 * a^-1)^5, (a * b^-2 * a^-1 * b^-1)^2, (a * b^-2)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2,x1,xm1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 3, 5, 6, 7) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1)^5, (b^-1 * a)^5, (a^-1 * b^-2 * a * b^-1)^2, (a * b^3 * a^-1 * b^-1)^2 ]>,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta,x1,xm1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 3, 5, 7, 6) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1)^3, b^-1 * a^-1 * b^2 * a * b^-1 * a * b^2 * a^-1 * b^-2, b^-1 * a * b^-2* a * b^-1 * a^-1 * b^2 * a^-1 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1,x1,xm1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 6, 3, 5, 7) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1)^5, (a * b^2 * a * b^-1)^2, (a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1)^2 ] >,ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta,x1,xm1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 7, 6, 3, 5) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1)^5, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b* a^-1 * b^-1 * a * b, b^-1 * a^-1 * b^2 * a^-1 * b^-1 * a^-1 * b^-2 * a * b^-2 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2,x1,xm1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 4, 7)(3, 5) >,
    Group< a,b | [ a^3, b^4, (a^-1 * b^-1)^4, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b *a^-1 * b^-1 * a * b, a^-1 * b^-2 * a * b^-1 * a^-1 * b^-2 * a * b^-1 * a^-1 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + zeta + 1,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4*zeta,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 4, 3) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^-1)^4, (a * b^2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + zeta + 1,x1,xm1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 6, 7, 4, 3) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-1)^4, (b^-1 * a)^5, (a * b * a^-1 * b * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4,xm12 + 2,xm21 + 2,xm2m1 + 4,x1,xm1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 6, 3) >,
    Group< a,b | [ a^3, b^5, (b^-1 * a)^3, (a^-1 * b^-1)^6, (a^-1 * b^-2)^4, a * b^-2 * a^-1 * b^2 * a^-1 * b^-1 * a^-1 *b^2 * a * b^-2 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta + 2,xm12,xm21,xm2m1 + 3*zeta,x1,xm1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 7, 3) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, (a * b^-1)^6, a^-1 * b^2 * a^-1 * b * a^-1 * b^-1 *a * b^-2 * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4,xm12 + 3,xm21 + 3,xm2m1 + 4,x1,xm1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 3)(4, 6) >,
    Group< a,b | [ a^3, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, (a^-1 * b^-1)^6, a^-1 * b * a^-1 *b^-2 * a * b^-1 * a^-1 * b * a^-1 * b^2 * a * b^-1, b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 3,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 4, 6, 7, 3) >,
    Group< a,b | [ a^3, b^7, (a * b^-1)^4, a * b^-2 * a^-1 * b^-1 * a^-1 * b^-3 * a^-1 * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta,x1,xm1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 3)(4, 7) >,
    Group< a,b | [ a^3, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, (a^-1 * b^-1)^6, a * b^-2 * a^-1 * b* a^-1 * b^-1 * a * b^2 * a^-1 * b * a^-1 * b^-1, b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a * b^-1 * a ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3*zeta,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 6, 4, 7, 3) >,
    Group< a,b | [ a^3, b^7, (a * b^-1)^4, b^-3 * a^-1 * b^-1 * a^-1 * b^-2 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta + 2,x1,xm1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 6, 4) >,
    Group< a,b | [ a^3, b^5, (a * b^-1)^4, (b * a^-1 * b)^3, (a^-1 * b^-1)^6, a^-1 * b^-1 * a^-1 * b^-2 * a^-1 * b^-1 * a* b * a * b^2 * a * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta,x1,xm1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 7, 4) >,
    Group< a,b | [ a^3, b^5, (b^-1 * a^-1)^3, (a * b^-1)^6, (a * b^-2)^4, a^-1 * b^-2 * a^-1 * b^2 * a * b^-1 * a * b^2 *a * b^-2 * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12,xm12 + 3,xm21 + 3,xm2m1,x1,xm1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5) >,
    Group< a,b | [ a^3, b^3, (b^-1 * a^-1)^7, (b^-1 * a)^7, a * b * a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b * a^-1* b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3*zeta + 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 6, 7) >,
    Group< a,b | [ a^3, b^5, (a * b^-2 * a^-1 * b^-1)^2, (b^-1 * a)^5, (a^-1 * b^-2)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 2,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta + 4,x1,xm1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 7, 6) >,
    Group< a,b | [ a^3, b^5, (b^-1 * a^-1)^5, (a^-1 * b^-2 * a * b^-1)^2, (a * b^-2)^4 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta,x1,xm1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 4, 6) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a * b^-1 * a^-1 * b,(a^-1 * b^-2)^4, (a * b^-2)^4, b^-1 * a * b^-2 * a^-1 * b^-1 * a^-1 * b * a^-1 * b * a * b * a ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta + 4,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3*zeta + 2,x1,xm1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 7)(4, 6) >,
    Group< a,b | [ a^3, b^4, (a^-1 * b^-1)^4, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b *a * b^-1 * a^-1 * b, a * b^-2 * a^-1 * b^-1 * a * b^-2 * a^-1 * b^-1 * a * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4*zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + zeta + 1,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 4, 7) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^2 * a^-1 * b^-1)^2, (a * b * a * b^-1 * a^-1 * b^-1)^2, b^-1 * a * b^-2 * a^-1 *b^-1 * a * b^-1 * a * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta + 4,x1,xm1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 3, 4) >,
    Group< a,b | [ a^3, b^5, (a * b^-1)^4, (a^-1 * b^2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 2,x1,xm1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 7, 6, 3, 4) >,
    Group< a,b | [ a^3, b^7, (a * b^-1)^4, (b^-1 * a^-1)^5, (a * b * a^-1 * b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1,xm1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5)(3, 4)(6, 7) >,
    Group< a,b | [ a^3, b^6, b^-3 * a^-1 * b^3 * a^-1, (b^-1 * a^-1)^5, b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^-1 *a^-1 * b^2 * a^-1 * b^-1 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta,x1,xm1,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 6)(3, 4) >,
    Group< a,b | [ a^3, b^4, (a^-1 * b^-1)^4, (b^-1 * a)^5, a^-1 * b * a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b * a^-1 *b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta,x1,xm1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 7)(3, 4) >,
    Group< a,b | [ a^3, b^4, (a * b^-1)^4, (b^-1 * a^-1)^5, a^-1 * b * a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b * a^-1 *b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 3*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta,x1,xm1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 3, 4, 6, 7) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a)^5, b^-2 * a * b^-1 * a^-1 * b^-1 * a * b^2 * a * b * a^-1, (a^-1 * b^-1 *a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a^-1 * b^-1 * a * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 4,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 2,x1,xm1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 7, 3, 4, 6) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, (a * b^3 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta,x1,xm1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 6, 3, 4, 7) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a)^5, (a * b^2 * a * b^-1)^2, a * b^-2 * a * b^-1 * a^-1 * b^-3 * a^-1 * b^-1] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 2,xm21 + 2,xm2m1 + zeta + 3,x1,xm1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 4)(3, 6) >,
    Group< a,b | [ a^3, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-1 * b^-2 * a * b * a^-1 * b^-1 *a^-1 * b^2 * a * b * a^-1 * b^-1, (a * b^-1)^6, (b^-1 * a^-1)^7, b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b^-1 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 3,xm12 + 3,xm21 + 3,xm2m1 + 3*zeta + 1,x1,xm1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 7, 3, 6, 4) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-1)^4, a * b^-1 * a * b^-2 * a^-1 * b * a * b^-3 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 4,x1,xm1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 7, 4, 3, 6) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1)^5, (a^-1 * b^2 * a^-1 * b^-1)^2, b^-3 * a * b^-1 * a^-1 * b^-2 * a^-1 *b^-1 * a ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta,x1,xm1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 3, 6) >,
    Group< a,b | [ a^3, b^5, (a * b^2 * a * b^-1)^2, a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-2 * a^-1 * b^-2, (a^-1* b * a^-1 * b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 4,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 3*zeta + 2,x1,xm1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5)(3, 6)(4, 7) >,
    Group< a,b | [ a^3, b^6, a * b^-3 * a^-1 * b^-1 * a * b^3 * a^-1 * b^-1, a^-1 * b^-3 * a * b^-1 * a^-1 * b^3 *a * b^-1, b^-2 * a^-1 * b^-3 * a^-1 * b^3 * a^-1 * b^-1, (a^-1 * b^-1 * a * b^-1)^3, (b^-1 * a^-1)^7, (b^-1 * a)^7 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta + 4,x1,xm1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 3, 6, 4, 7) >,
    Group< a,b | [ a^3, b^7, (b * a^-1 * b)^3, (a^-1 * b^-1)^6, (a, b)^3, (a * b^-3 * a * b^-1)^2, a * b^3 * a^-1 *b^-1 * a^-1 * b^3 * a * b^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 2,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 3*zeta,x1,xm1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 4, 7, 3, 6) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1 * b^-1)^3, (a^-1 * b^-3 * a^-1 * b^-1)^2, (a * b^-1)^6, b^-2 * a * b^-3 *a^-1 * b * a^-1 * b^-3 * a ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 3,xm21 + 3,xm2m1 + zeta + 3,x1,xm1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 3, 7, 6, 4) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-1)^4, a^-1 * b^2 * a * b^-1 * a^-1 * b^3 * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta,xm12 + 3,xm21 + 3,xm2m1 + zeta + 1,x1,xm1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 4)(3, 7) >,
    Group< a,b | [ a^3, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-1 * b * a * b^-2 * a^-1 * b^-1 *a^-1 * b * a * b^2 * a^-1 * b^-1, (a * b^-1)^6, (b^-1 * a^-1)^7, b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b^-1 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 2,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta + 4,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 4, 3, 7, 6) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1)^5, b^-1 * a * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^-2, (a^-1 *b^-1 * a^-1 * b)^3 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 3*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta,x1,xm1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 6, 4, 3, 7) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1* b^-1 * a * b * a * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1,xm1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 3, 7) >,
    Group< a,b | [ a^3, b^5, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a^-1 * b^-1 * a * b,(a^-1 * b^-2)^4, (a * b^-2)^4, a * b^-1 * a * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b^2 * a * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta + 1,x1,xm1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 6)(3, 7) >,
    Group< a,b | [ a^3, b^4, (a * b^-1)^4, (a^-1 * b^-1 * a^-1 * b)^3, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b *a^-1 * b^-1 * a * b, a^-1 * b^-2 * a * b^-1 * a^-1 * b^-2 * a * b^-1 * a^-1 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 3,x1,xm1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5)(3, 7)(4, 6) >,
    Group< a,b | [ a^3, b^6, a^-1 * b^-3 * a^-1 * b^-1 * a^-1 * b^3 * a^-1 * b^-1, a * b^-3 * a * b^-1 * a * b^3 *a * b^-1, (a^-1 * b^-1)^6, a * b^-2 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^3 * a^-1 * b^-1 * a * b^-1, b^-1 * a * b * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a * b^-1 * a^-1 * b^2 * a^-1] >,
    ideal< R | [5,xcom + 3,x12 + 2*zeta + 2,xm12 + 3,xm21 + 3,xm2m1 + 3*zeta,x1,xm1,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 3, 7, 4, 6) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-2 * a * b^-1)^2, (a^-1 * b^-1 * a^-1 * b)^3, (b^-1 * a^-1)^7, b * a^-1 *b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b * a^-1 * b^2 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 2*zeta + 4,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3*zeta + 2,x1,xm1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (2, 3, 4)(5, 6, 7), (1, 2, 5, 4, 6, 3, 7) >,
    Group< a,b | [ a^3, b^7, (a * b^-2 * a^-1 * b^-1)^2, (a^-1 * b^-1 * a^-1 * b)^3, (b^-1 * a^-1)^7, b * a^-1 *b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b^-1 * a * b^-1 * a * b^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 2*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta + 1,x1,xm1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3)(4, 5) >,
    Group< a,b | [ a^6, b^2, (a * b * a)^4, (a^-1 * b * a * b)^3, (b * a^-1)^7, b * a^2 * b * a^-3 * b * a^-1 * b * a^-1* b * a^3 * b * a * b * a * b * a^-1 ] >,
    ideal< R | [5,xcom,x12 + zeta + 3,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta + 4,xm2 + zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3)(4, 5, 6, 7) >,
    Group< a,b | [ a^6, b^4, (a * b * a)^2, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, (b^-1 * a)^5, (a,b)^3, b * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b^2 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3)(4, 5, 7, 6) >,
    Group< a,b | [ a^6, b^4, (a * b^-1 * a)^2, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, (b^-1 *a^-1)^5, (a, b)^3, b * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a^-1 * b^2 * a ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 4, 5)(6, 7) >,
    Group< a,b | [ a^6, b^4, a^-1 * b^-2 * a * b * a^2 * b^-1 * a * b^2 * a^-1, (b^-1 * a^-1)^5, a^-1 * b^-2 * a^-3* b^-1 * a^3 * b * a^-2, (b * a^-1)^5, a^-1 * b^-1 * a^-3 * b^-2 * a^-1 * b^2 * a^3 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 4, 5, 6) >,
    Group< a,b | [ a^6, b^5, (a^-1 * b^-1)^4, (b^-1 * a)^5, a * b^-1 * a^-1 * b^-1 * a^3 * b * a^3 * b^-1 * a, (a * b* a^-2 * b^-1 * a)^2, (a * b^2 * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 4, 5, 7) >,
    Group< a,b | [ a^6, b^5, (a * b^-1)^4, (b^-1 * a^-1)^5, b * a^-3 * b^-1 * a^3 * b * a^-1 * b * a^2, (a * b * a^-2* b^-1 * a)^2, b^-2 * a^-3 * b^-1 * a^2 * b^-2 * a * b * a ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5, 4)(6, 7) >,
    Group< a,b | [ a^6, b^4, (b^-1 * a^-1)^3, (b^-1 * a)^3, a^-1 * b^-2 * a^-3 * b^-2 * a^3 * b^2 * a^-2, b^-1 *a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1 * b^-1, (a * b * a^-2 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12,xm12,xm21,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5, 6, 4) >,
    Group< a,b | [ a^6, b^5, (b^-1 * a)^3, (b^-1 * a^-1 * b^-1)^3, a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b * a * b * a^-1,(a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3,xm12,xm21,xm2m1 + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5, 7, 4) >,
    Group< a,b | [ a^6, b^5, (b^-1 * a^-1)^3, (b * a^-1 * b)^3, a^-1 * b^-1 * a * b^-1 * a^2 * b * a^-1 * b * a^-1, (a* b * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5) >,
    Group< a,b | [ a^6, b^3, (b, a^-1, b), (a * b^-1 * a^-2 * b^-1 * a)^2, (a * b * a^2 * b^-1 * a)^2, (b^-1 * a^-1)^7 ] >,ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5, 6, 7) >,
    Group< a,b | [ a^6, b^5, (a * b^-2 * a)^2, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^3 * b, (b^-1 * a^-1 * b^-1)^3] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 4,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5, 7, 6) >,
    Group< a,b | [ a^6, b^5, (a * b^2 * a)^2, b^-1 * a^-3 * b^-1 * a^-1 * b * a^-1 * b * a^-1, (b * a^-1 * b)^3 ] >,ideal< R | [5,xcom,x12 + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5)(4, 6, 7) >,
    Group< a,b | [ a^6, b^3, (a * b^-1)^4, b^-1 * a * b * a^-1 * b^-1 * a^-1 * b^-1 * a^3 * b^-1 * a^-1, (a * b^-1* a)^4 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5, 4, 6) >,
    Group< a,b | [ a^6, b^5, (a^-2 * b)^3, b^2 * a^-1 * b * a^2 * b * a * b * a, b^-1 * a * b^-1 * a^-1 * b^-1 * a *b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 2,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5, 7)(4, 6) >,
    Group< a,b | [ a^6, b^4, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, a * b * a^-1 * b^-2 * a^2 * b * a^-1 * b^2 * a, a *b^-2 * a^-3 * b^-1 * a^2 * b^-1 * a * b^-1, a^-1 * b^-2 * a^-1 * b * a^-2 * b^2 * a^-1 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5)(4, 7, 6) >,
    Group< a,b | [ a^6, b^3, (a^-1 * b^-1)^4, a^-1 * b * a^-3 * b * a^-1 * b * a^-1 * b^-1 * a * b, (a * b * a)^4 ]>,
    ideal< R | [5,xcom + zeta + 1,x12 + 4,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5, 4, 7) >,
    Group< a,b | [ a^6, b^5, (a^-2 * b^-1)^3, a * b^-1 * a * b^-1 * a^2 * b^-1 * a^-1 * b^-2, b^-1 * a * b^-1 * a^-1 *b^-1 * a^-1 * b * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 4*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 3, 5, 6)(4, 7) >,
    Group< a,b | [ a^6, b^4, (a * b^-1)^4, (a^-2 * b)^3, a * b^-2 * a^-1 * b^-1 * a^2 * b^2 * a^-1 * b^-1 * a, a^-2* b^-1 * a^-1 * b^-1 * a^-1 * b^2 * a^3 * b^-1, a * b^-1 * a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 4, 3)(6, 7) >,
    Group< a,b | [ a^6, b^4, a^-1 * b^-2 * a * b^-1 * a^2 * b * a * b^2 * a^-1, (b^-1 * a^-1)^5, a^-1 * b * a^-3 *b^-1 * a^3 * b^2 * a^-2, a^-1 * b * a^-3 * b^-2 * a^-1 * b^2 * a^3 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 6, 4, 3) >,
    Group< a,b | [ a^6, b^5, (a^-1 * b^-1)^4, (b^-1 * a)^5, b^-1 * a^2 * b^-1 * a^3 * b * a^3 * b^-1 * a^-1, (a * b *a^-2 * b^-1 * a)^2, b^-1 * a * b * a^-1 * b^-1 * a^2 * b^-1 * a * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 7, 4, 3) >,
    Group< a,b | [ a^6, b^5, (a * b^-1)^4, (b^-1 * a^-1)^5, b^-1 * a^-2 * b^-1 * a^3 * b * a^3 * b^-1 * a, (a * b *a^-2 * b^-1 * a)^2, b^2 * a^-3 * b^-1 * a^2 * b^-2 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 3)(4, 6, 7) >,
    Group< a,b | [ a^6, b^3, (a * b^-1)^4, a^-1 * b^-1 * a^-3 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b^-1, (a * b^-1* a)^4 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 4, 6, 3) >,
    Group< a,b | [ a^6, b^5, (a^-2 * b)^3, a * b * a * b * a^2 * b * a^-1 * b^2, b^-1 * a * b^-1 * a^-1 * b^-1 * a *b^-1 * a^-1 * b * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 7, 3)(4, 6) >,
    Group< a,b | [ a^6, b^4, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, a * b^-2 * a^-1 * b * a^2 * b^2 * a^-1 * b * a, a *b^-1 * a^2 * b^-1 * a^3 * b^2 * a * b^-1, a * b * a^-1 * b^-2 * a^-2 * b * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + zeta + 1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 3)(4, 7, 6) >,
    Group< a,b | [ a^6, b^3, (a^-1 * b^-1)^4, b * a * b^-1 * a^-1 * b * a^-1 * b * a^3 * b * a^-1, a * b * a^-3 *b^-1 * a^2 * b * a^3 * b^-1 * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 4, 7, 3) >,
    Group< a,b | [ a^6, b^5, (a^-2 * b^-1)^3, b^-2 * a^-1 * b^-1 * a^2 * b^-1 * a * b^-1 * a, b * a^-1 * b^-1 * a^-1 *b^-1 * a * b^-1 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 3,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta + 1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 6, 3)(4, 7) >,
    Group< a,b | [ a^6, b^4, (a * b^-1)^4, (a^-2 * b)^3, a * b^-1 * a^-1 * b^-2 * a^2 * b^-1 * a^-1 * b^2 * a, a^-1* b^-1 * a^-2 * b^-1 * a^3 * b^2 * a^-1 * b^-1, a^-1 * b^-2 * a^-1 * b^-1 * a^-2 * b^2 * a^-1 * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5)(4, 6) >,
    Group< a,b | [ a^6, b^2, a^-1 * b * a^-3 * b * a^3 * b * a^-2, (b * a^-1)^7, (a^-2 * b)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + 2*zeta + 4,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 3*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta,xm2 + 4*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 4, 6, 7) >,
    Group< a,b | [ a^6, b^5, (a * b * a)^2, (b^-1 * a)^3, b^-1 * a^-1 * b^2 * a * b^-1 * a^-1 * b^-1 * a * b^2 * a^-1* b^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 4*zeta + 2,xm12,xm21,xm2m1 + zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 7, 4, 6) >,
    Group< a,b | [ a^6, b^5, (a * b^-1 * a)^2, (b^-1 * a^-1)^3, b^2 * a^-1 * b^-1 * a * b^-1 * a^-1 * b^2 * a * b^-2 *a ] >,
    ideal< R | [5,xcom + 3,x12,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5)(3, 4, 6, 7) >,
    Group< a,b | [ a^6, b^4, (a^-1 * b^-1)^4, (a^-2 * b)^3, a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b * a^3 * b, (b^-1 *a)^5, a * b * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b^2 * a * b^-1 * a ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 3, 4, 6) >,
    Group< a,b | [ a^6, b^5, (b^-1 * a^-1)^3, (a * b^-1)^4, (a^-2 * b^-1)^3, b^-1 * a^-1 * b * a^-2 * b^-1 * a^2 * b^2* a * b^-1 * a^2 ] >,
    ideal< R | [5,xcom + zeta + 3,x12,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 7)(3, 4, 6) >,
    Group< a,b | [ a^6, b^3, (b^-1 * a)^3, (b^-1 * a^-1)^5, (a * b * a)^4, b * a^-2 * b^-1 * a * b * a^-2 * b * a^2* b^-1 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5)(3, 4, 7, 6) >,
    Group< a,b | [ a^6, b^4, (a * b^-1)^4, (a^-2 * b^-1)^3, a * b^-1 * a^-2 * b^-1 * a * b * a^3 * b, (b^-1 *a^-1)^5, b * a^-1 * b^-2 * a^-1 * b^-1 * a^-2 * b^2 * a^-2 * b * a^-2 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 3, 4, 7) >,
    Group< a,b | [ a^6, b^5, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a^-2 * b)^3, a^-1 * b^2 * a^-2 * b^-1 * a^2 * b * a *b^-1 * a^-2 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 6)(3, 4, 7) >,
    Group< a,b | [ a^6, b^3, (b^-1 * a^-1)^3, (b^-1 * a)^5, (a * b^-1 * a)^4, b * a^-1 * b * a^2 * b^-1 * a^-2 *b^-1 * a * b * a^-2 * b^-1 * a ] >,
    ideal< R | [5,xcom + zeta + 3,x12,xm12 + 2,xm21 + 2,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5)(3, 6, 4, 7) >,
    Group< a,b | [ a^6, b^4, b^-2 * a^-1 * b^2 * a^-1, a * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b * a, b^-1 * a^-1* b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a^-1 * b^-1 * a^-1, b^-1 * a^2 * b^-1 * a^-1 * b^-1 * a^-2 * b * a^-1 * b * a^2 * b * a ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 1,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 3, 6)(4, 7) >,
    Group< a,b | [ a^6, b^4, a * b^-2 * a^2 * b^2 * a, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a * b^2 * a, (a * b^-1 *a^-1 * b^-1 * a)^2, b^-1 * a * b^-2 * a^-1 * b^-1 * a^2 * b * a^-1 * b^-1 * a^-2, (a^-1 * b^-1)^6, b * a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a * b^-1 * a * b^-1 * a ] >,ideal< R | [5,xcom + 2,x12 + 2*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (2, 5, 4, 7)(3, 6) >,
    Group< a,b | [ a^6, b^4, a * b^-2 * a^2 * b^2 * a, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a * b^2 * a, a^-1 * b^-1 *a^-1 * b * a^2 * b * a^-1 * b^-1 * a^-1, a^2 * b^-1 * a^-1 * b^-1 * a^2 * b * a^-1 * b^2 * a * b^-1, (a * b^-1)^6, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b *a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 1,xm12 + 3,xm21 + 3,xm2m1 + 2*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3)(4, 5)(6, 7) >,
    Group< a,b | [ a^6, b^6, a^-1 * b^-2 * a^2 * b^2 * a^-1, (a^-2 * b^-1)^3, (b^-1 * a^-1 * b^-1)^3, (b^-1 *a^-1)^5, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3*zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3)(4, 5, 6) >,
    Group< a,b | [ a^6, b^3, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, (b^-1 * a)^5, a^-1 * b * a^-2 * b^-1 * a^2 * b^-1 *a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3)(4, 5, 7) >,
    Group< a,b | [ a^6, b^3, (a * b^-1)^4, (a^-2 * b)^3, (b^-1 * a^-1)^5, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2* b * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 4, 5) >,
    Group< a,b | [ a^6, b^5, (a * b^-1 * a^-1 * b^-1)^2, a * b * a * b^-1 * a^2 * b^-1 * a * b * a, (b^-1 * a^-1)^5 ]>,
    ideal< R | [5,xcom,x12 + 2*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 4, 5, 6, 7) >,
    Group< a,b | [ a^6, b^7, (b^-1 * a)^3, b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b, (b^-1 * a^-1 * b^-1)^3,(b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 4, 5, 7, 6) >,
    Group< a,b | [ a^6, b^7, (b^-1 * a^-1)^3, b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1, (b * a^-1 * b)^3, a *b^-1 * a^-3 * b^-1 * a * b^-1 * a^3 * b^-1 ] >,
    ideal< R | [5,xcom,x12,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 5, 4) >,
    Group< a,b | [ a^6, b^5, a^-1 * b^-1 * a^3 * b^-1 * a^-2, (a^-1 * b^-1)^4, (a, b)^3, (a^-1 * b^-2)^4, b^-2 * a^-1* b * a^-1 * b^-1 * a^-2 * b^-1 * a * b^-2 * a * b * a ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 5, 6, 7, 4) >,
    Group< a,b | [ a^6, b^7, (a * b^-1)^2, (a^-1 * b^-1)^4, b^-1 * a * b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b *a * b^-1, b * a^-1 * b^-1 * a^2 * b * a^-3 * b^-3 * a^3 * b^2 ] >,
    ideal< R | [5,xcom,x12 + 4,xm12 + 1,xm21 + 1,xm2m1 + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 5, 7, 6, 4) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-1)^2, (a * b^-1)^4, b * a * b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1 * a* b, b * a^-2 * b * a^2 * b^-1 * a^-2 * b^-3 * a^3 * b^2 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 5)(4, 6) >,
    Group< a,b | [ a^6, b^4, (b^-1 * a)^3, (a^-1 * b^-1)^4, a * b^-1 * a^-2 * b^-1 * a^2 * b^-1 * a^-1 * b^2 * a^-1* b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 5, 4, 6, 7) >,
    Group< a,b | [ a^6, b^7, (b^-1 * a^-1)^3, a * b^2 * a^-2 * b^2 * a^-1 * b^-1, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 5, 7, 4, 6) >,
    Group< a,b | [ a^6, b^7, (a * b^-1)^4, b^-1 * a * b^-1 * a^-2 * b^-1 * a^-1 * b^-2, (b^-1 * a^-1)^5 ] >,ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12 + 4,xm21 + 4,xm2m1 + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 5)(4, 7) >,
    Group< a,b | [ a^6, b^4, (b^-1 * a^-1)^3, (a * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b * a^2 * b * a^-2 * b * a] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 5, 4, 7, 6) >,
    Group< a,b | [ a^6, b^7, (b^-1 * a)^3, a^-1 * b^-2 * a^-2 * b^-2 * a * b, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 3, 5, 6, 4, 7) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-1)^4, b * a^-1 * b * a^-2 * b * a * b^2, a^-1 * b^-1 * a^-3 * b^-1 * a^3* b^-1 * a^-2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 3)(4, 6) >,
    Group< a,b | [ a^6, b^4, (b^-1 * a^-1)^3, (a * b^-1)^4, a * b * a^-3 * b^-1 * a^2 * b * a^3 * b^-1 * a, a * b *a^-2 * b * a^2 * b * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 4, 6, 7, 3) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-1)^4, b * a * b * a^-2 * b * a^-1 * b^2, a^-1 * b^-1 * a^-3 * b^-1 * a^3* b^-1 * a^-2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 7, 4, 6, 3) >,
    Group< a,b | [ a^6, b^7, (b^-1 * a)^3, a * b^-2 * a^-2 * b^-2 * a^-1 * b, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 3)(4, 7) >,
    Group< a,b | [ a^6, b^4, (b^-1 * a)^3, (a^-1 * b^-1)^4, b * a^-1 * b^-2 * a^-1 * b^-1 * a^2 * b^-1 * a^-2 *b^-1 * a ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta,xm12,xm21,xm2m1 + zeta + 1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 4, 7, 6, 3) >,
    Group< a,b | [ a^6, b^7, (a * b^-1)^4, b^-1 * a^-1 * b^-1 * a^-2 * b^-1 * a * b^-2, (b^-1 * a^-1)^5 ] >,ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 6, 4, 7, 3) >,
    Group< a,b | [ a^6, b^7, (b^-1 * a^-1)^3, a^-1 * b^2 * a^-2 * b^2 * a * b^-1, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5)(3, 4, 6) >,
    Group< a,b | [ a^6, b^3, a^-1 * b^-1 * a^3 * b^-1 * a^-2, (b^-1 * a^-1)^5, a * b^-1 * a * b * a * b^-1 * a^-2 *b^-1 * a * b * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 3,x12 + 2*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 3, 4, 6, 7) >,
    Group< a,b | [ a^6, b^7, (a * b^-1)^2, (a^-2 * b^-1)^3, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + 2,xm12 + 1,xm21 + 1,xm2m1 + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 7, 3, 4, 6) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-1)^2, (a^-2 * b)^3, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + 4*zeta + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5)(3, 6)(4, 7) >,
    Group< a,b | [ a^6, b^6, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-1)^4, b * a^-3 * b^2 * a^3 *b, a^-1 * b * a^-3 * b^-1 * a^2 * b^2 * a * b^2, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 3, 6, 4, 7) >,
    Group< a,b | [ a^6, b^7, (a * b^-2)^2, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b^-1)^2, b^-1 * a^2 * b^2 * a^-3* b * a^3 * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 2, 5, 4, 7, 3, 6) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-2)^2, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b, (a * b^-1)^4, a^-1 *b * a^-3 * b^-1 * a^-3 * b^-2 * a^2 * b^2 ] >,
    ideal< R | [5,xcom + 2,x12 + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3)(2, 4, 5)(6, 7) >,
    Group< a,b | [ a^6, b^6, a * b^-3 * a^2 * b^3 * a, (a^-1 * b^-1)^4, (a^-1 * b * a^-1 * b^-1)^2, (a * b *a^-2 * b^-1 * a)^2, (a * b^-1 * a)^4, b^-2 * a^2 * b^-1 * a * b^3 * a^-1 * b^-1 * a^-2, (b^-1 * a^-2 * b^-1 * a)^3 ] >,
    ideal< R | [5,xcom + 2,x12 + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3)(2, 4, 5, 6) >,
    Group< a,b | [ a^6, b^4, (a^-1 * b * a^-1 * b^-1)^2, (a * b^-1)^4, a^-1 * b^-2 * a^-3 * b^-2 * a^3 * b^2 *a^-2, a^-1 * b^-1 * a^-3 * b^-1 * a^-1 * b^2 * a^-1 * b^2 * a * b ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3)(2, 4, 5, 7) >,
    Group< a,b | [ a^6, b^4, (a^-1 * b^-1)^4, (a^-1 * b * a^-1 * b^-1)^2, a^-1 * b^-2 * a^-3 * b^-2 * a^3 * b^2 *a^-2, a^-1 * b * a^-3 * b * a^-1 * b^2 * a^-1 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta,xm12 + 3,xm21 + 3,xm2m1 + zeta + 1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 2, 4, 5) >,
    Group< a,b | [ a^6, b^5, (a^-1, b^-1)^2, (a * b^-1 * a * b^-1 * a)^2, (a * b * a * b * a)^2, a * b^-2 * a^-1 *b^-1 * a^2 * b * a^-1 * b^2 * a, a^-1 * b^-1 * a^2 * b^-1 * a^-2 * b^2 * a^-1 * b^2 * a^-1 ] >,
    ideal< R | [5,xcom + 1,x12 + 2*zeta + 4,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 3*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 2, 4, 5, 6, 7) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-2)^2, (a^-1, b^-1)^2, (b^-1 * a)^5, a * b^-1 * a^-3 * b^-1 * a^2 * b^-1* a^3 * b^-1 * a ] >,
    ideal< R | [5,xcom + 1,x12 + 4*zeta + 2,xm12 + 2,xm21 + 2,xm2m1 + zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 2, 4, 5, 7, 6) >,
    Group< a,b | [ a^6, b^7, (a * b^-2)^2, (a^-1, b^-1)^2, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 1,x12 + 3*zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 5)(2, 4, 6) >,
    Group< a,b | [ a^6, b^3, a^-1 * b^-1 * a^-3 * b^-1 * a^3 * b^-1 * a^-2, a^-1 * b * a^-3 * b^-1 * a^-1 * b * a^3* b^-1, (a^-1 * b^-1 * a^-1 * b)^3, (b^-1 * a^-1)^7, (b^-1 * a)^7 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 3*zeta + 1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 5, 2, 4, 6, 7) >,
    Group< a,b | [ a^6, b^7, (b^-1 * a)^3, (a^-2 * b^-1)^3, b * a^-3 * b^-1 * a^-1 * b^-1 * a^3 * b, a * b^3 *a^-2 * b^3 * a * b ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12,xm21,xm2m1 + 2*zeta + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 5, 7, 2, 4, 6) >,
    Group< a,b | [ a^6, b^7, (b^-1 * a^-1)^3, (a^-2 * b)^3, b^-1 * a^-3 * b * a^-1 * b * a^3 * b^-1, a * b^-3 *a^-2 * b^-3 * a * b^-1 ] >,
    ideal< R | [5,xcom,x12,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3)(2, 5)(4, 6, 7) >,
    Group< a,b | [ a^6, b^6, (b^-1 * a)^3, (a * b^2 * a)^2, a * b * a^-3 * b^-1 * a^-1 * b^3 * a^2 * b^-1, b^-1* a * b^-2 * a^-3 * b * a * b^3 * a^-1, a * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b * a, a^-1 * b^-2 * a^-1 * b^-2 * a * b^2 * a * b^-2 ] >,
    ideal< R | [5,xcom + 3,x12 + 2*zeta + 4,xm12,xm21,xm2m1 + 3*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3)(2, 5, 4, 6) >,
    Group< a,b | [ a^6, b^4, a * b^-2 * a^2 * b^2 * a, a^-1 * b^-2 * a^-1 * b^-1 * a * b^2 * a * b^-1, a^-1 * b^-1* a^-3 * b^-1 * a^3 * b^-1 * a^-2, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b * a * b * a^-1, b^-1 * a^-2 * b^-1 * a^-2 * b^-1 * a^2 * b * a * b^-1 * a^3 * b* a^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3)(2, 5, 7)(4, 6) >,
    Group< a,b | [ a^6, b^6, (b^-1 * a^-1)^3, (a * b^-2 * a)^2, a^-1 * b^-3 * a * b^-1 * a^-3 * b^2 * a * b, b *a * b^2 * a^-3 * b^-1 * a * b^3 * a^-1, (a * b^-1 * a^-2 * b^-1 * a)^2, a^-1 * b^2 * a^-1 * b^-2 * a * b^-2 * a * b^-2 ] >,
    ideal< R | [5,xcom + 3,x12,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 2, 5)(4, 6) >,
    Group< a,b | [ a^6, b^4, a^-1 * b^-2 * a * b^-1 * a^-1 * b^2 * a * b^-1, a * b * a^-1 * b^-1 * a^2 * b^2 * a^2* b, a^-1 * b^-2 * a^-3 * b^-2 * a^3 * b^2 * a^-2, a * b^-1 * a^-3 * b^-1 * a^-2 * b * a^2 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 1,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 2, 5, 4, 6, 7) >,
    Group< a,b | [ a^6, b^7, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a * b * a^-1 * b * a^2 * b^-1 * a^-1 * b^2 ]>,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 2, 5, 7, 4, 6) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, a * b^-1 * a^-1 * b^-1 * a^2 * b * a^-1 * b^-2 ]>,
    ideal< R | [5,xcom + zeta + 3,x12 + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 2, 5)(4, 7) >,
    Group< a,b | [ a^6, b^4, a * b^-2 * a^-1 * b^-1 * a * b^2 * a^-1 * b^-1, a^-1 * b^-1 * a * b^-1 * a^2 * b^2 *a^2 * b, a^-1 * b^-2 * a^-3 * b^-2 * a^3 * b^2 * a^-2, a * b^-1 * a^2 * b^-1 * a^-2 * b * a^3 * b * a * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 4,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 3*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 2, 5, 4, 7, 6) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, b^-2 * a^-1 * b * a^2 * b^-1 * a^-1 * b^-1 * a ]>,
    ideal< R | [5,xcom + zeta + 3,x12 + zeta + 1,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 4*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 2, 5, 6, 4, 7) >,
    Group< a,b | [ a^6, b^7, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, b^2 * a^-1 * b^-1 * a^2 * b * a^-1 * b * a ]>,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 6, 7, 4, 2, 5) >,
    Group< a,b | [ a^6, b^7, (a * b^-1 * a^-1 * b^-1)^2, (a * b^-1)^4, (a * b^-3)^2, (a^-2 * b^-1)^3, b^-1 *a^-3 * b^2 * a^-3 * b * a * b * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 6)(2, 5, 4) >,
    Group< a,b | [ a^6, b^3, a^-1 * b^-1 * a^-3 * b^-1 * a^-1 * b^-1 * a^3 * b^-1, a * b^-1 * a^-3 * b^-1 * a *b^-1 * a^3 * b^-1, (a^-1 * b^-1)^6, b^-1 * a^-1 * b * a^-3 * b^-1 * a^2 * b^-1 * a * b^-1 * a * b^-1 * a^-1, a * b^-1 * a^-1 * b * a * b^-1 * a^-2 * b^-1 * a * b * a^-1 * b^-1 * a* b ] >,
    ideal< R | [5,xcom + 3,x12 + 3,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 6, 4, 2, 5, 7) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-1)^4, (a * b^-1 * a^-1 * b^-1)^2, (a^-1 * b^-3)^2, (a^-2 * b)^3, b *a^-3 * b^-2 * a^-3 * b^-1 * a * b^-1 * a^2 * b ] >,
    ideal< R | [5,xcom + 3,x12 + zeta + 1,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4*zeta,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 6, 4, 7, 2, 5) >,
    Group< a,b | [ a^6, b^7, (b * a^-1 * b)^3, a^2 * b^-2 * a^2 * b * a^3 * b, a^-1 * b^-1 * a^-1 * b^-1 * a^-2* b * a^-2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 1,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta + 3,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 6)(2, 5)(4, 7) >,
    Group< a,b | [ a^6, b^6, a^2 * b^-2 * a^2 * b * a^3 * b, b^-1 * a^2 * b^-2 * a^-1 * b^3 * a^-1 * b^-1, a^-1* b^-1 * a^-1 * b^-1 * a^-2 * b * a^-2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 6, 2, 5, 4, 7) >,
    Group< a,b | [ a^6, b^7, (a^-1 * b^-3)^2, a^2 * b^-2 * a^2 * b * a^3 * b ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2*zeta + 4,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 7, 4, 6, 2, 5) >,
    Group< a,b | [ a^6, b^7, (b^-1 * a^-1 * b^-1)^3, b^-1 * a^-3 * b^-1 * a^2 * b^2 * a^2, b^-1 * a^-2 * b^-1 *a^-2 * b * a^-1 * b * a^-2 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 3,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 4*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 7)(2, 5)(4, 6) >,
    Group< a,b | [ a^6, b^6, b^-1 * a^-3 * b^-1 * a^2 * b^2 * a^2, b^-1 * a^-2 * b^-2 * a * b^3 * a * b^-1, b^-1* a^-2 * b^-1 * a^-2 * b * a^-1 * b * a^-2 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 4,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2)(3, 4)(5, 6, 7), (1, 3, 7, 2, 5, 4, 6) >,
    Group< a,b | [ a^6, b^7, (a * b^-3)^2, b^-1 * a^-3 * b^-1 * a^2 * b^2 * a^2 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 3*zeta,xm1 + 2*zeta + 2,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (5, 6, 7) >,
    Group< a,b | [ a^7, b^3, (a * b^-1 * a^-1 * b^-1)^2, (a^-2 * b^-1)^3, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (5, 7, 6) >,
    Group< a,b | [ a^7, b^3, (a * b^-1 * a^-1 * b^-1)^2, (a^-2 * b)^3, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (4, 5)(6, 7) >,
    Group< a,b | [ a^7, b^2, (b * a^-1)^5, (a * b * a^-2 * b * a)^2, (b * a^3 * b * a^-1)^3 ] >,
    ideal< R | [5,xcom + 2,x12 + 2,xm12 + 2,xm21 + 2,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (4, 5, 7) >,
    Group< a,b | [ a^7, b^3, (a * b^-1)^4, (a * b^-1 * a)^4, b^-1 * a * b^-1 * a^-1 * b^-1 * a^3 * b * a^-2 * b^-1 * a^-2,a^-1 * b * a^2 * b^-1 * a^3 * b * a * b * a^-2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (4, 6, 7) >,
    Group< a,b | [ a^7, b^3, (a * b^-1)^4, (a * b^-1 * a)^4, a^-1 * b^-1 * a^-2 * b * a^3 * b^-1 * a^-1 * b^-1 * a * b^-1 *a^-1, a^-2 * b^-1 * a^-1 * b * a^3 * b * a^2 * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (4, 6)(5, 7) >,
    Group< a,b | [ a^7, b^2, (a^-1 * b * a * b)^3, (a * b * a^-1 * b * a^-1 * b * a)^2, (b * a^-1)^7, (a^-2 * b)^5 ] >,ideal< R | [5,xcom,x12 + 3*zeta + 1,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (4, 7, 5) >,
    Group< a,b | [ a^7, b^3, (a^-1 * b^-1)^4, (a * b * a)^4, a^-1 * b * a^2 * b^-1 * a^3 * b^-1 * a^-1 * b * a^-2 * b^-1 ]>,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (4, 7, 6) >,
    Group< a,b | [ a^7, b^3, (a^-1 * b^-1)^4, (a * b * a)^4, a^-1 * b * a^-2 * b^-1 * a^3 * b * a^-1 * b * a * b * a^-1,a^-2 * b * a^-1 * b^-1 * a^3 * b^-1 * a^2 * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 1,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (4, 7)(5, 6) >,
    Group< a,b | [ a^7, b^2, (a^-1 * b)^4, (a * b * a^2)^4, (a^-1 * b * a^2 * b * a^-1)^3, a^-1 * b * a^-2 * b * a * b *a^-1 * b * a^-2 * b * a^2 * b * a * b * a^-1 * b * a * b ] >,
    ideal< R | [5,xcom + 2,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 4)(6, 7) >,
    Group< a,b | [ a^7, b^2, (b * a^-1)^5, (a^-1 * b * a * b)^3, (b * a^-2 * b * a)^3 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 4, 5, 6, 7) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a)^3, (a * b^-2 * a)^2, (a^-1 * b^-2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12,xm21,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 4, 5, 7, 6) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, (a * b^-1 * a^-1 * b * a)^2, (b^-1 * a)^5, (a^-1 *b^-2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 4, 6, 7, 5) >,
    Group< a,b | [ a^7, b^5, (a * b^-1 * a^-1 * b^-1)^2, (a^-2 * b)^3, (a * b^-2 * a^2)^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 4, 6, 5, 7) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a)^3, (a^-1 * b^-1)^4, a^-2 * b^-2 * a^2 * b * a * b^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 4, 7, 6, 5) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, (a * b^-1 * a^-1 * b * a)^2, (b^-1 * a^-1)^5, (a *b^-2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 4, 7) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a)^3, a * b^-1 * a^-2 * b^-1 * a^2 * b * a^-2 * b * a, b * a^3 * b^-1 * a^3 * b * a *b^-1 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 1,xm12,xm21,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 4, 7, 5, 6) >,
    Group< a,b | [ a^7, b^5, a^2 * b^-1 * a^-2 * b * a * b^-2, (b^-1 * a^-1 * b^-1)^3, (a^-1 * b^2 * a * b^-1)^2 ] >,ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 4,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 5, 6, 7, 4) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, (a * b * a^-1 * b^-1 * a)^2, (a * b^-2 * a^-1 *b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 5, 7, 6, 4) >,
    Group< a,b | [ a^7, b^5, (a * b^-1 * a^-1 * b^-1)^2, (a^-2 * b^-1)^3, (a * b^2 * a^2)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 5, 7) >,
    Group< a,b | [ a^7, b^3, (b, a^-1, b), (a^3 * b^-1)^3, (a * b^-1 * a^-2 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 5, 4, 6, 7) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a * b * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 5, 7, 4, 6) >,
    Group< a,b | [ a^7, b^5, (a * b^-1 * a)^2, (b^-1 * a^-1 * b^-1)^3, (a^-1 * b^2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 5, 4, 7, 6) >,
    Group< a,b | [ a^7, b^5, b * a * b^-1 * a^-2 * b * a^2 * b, (b * a^-1 * b)^3, (a * b^2 * a^-1 * b^-1)^2 ] >,ideal< R | [5,xcom + zeta + 1,x12 + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 5, 6, 4, 7) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a)^3, (a * b^2 * a^-1 * b^-1)^2, a * b^-1 * a^-1 * b * a^-2 * b^-1 * a^-1 * b * a* b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 3,xm12,xm21,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 6, 7, 5, 4) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, (a * b * a^-1 * b^-1 * a)^2, (b^-1 * a^-1)^5, (a^-1* b^-2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 6, 5, 7, 4) >,
    Group< a,b | [ a^7, b^5, a^2 * b^-1 * a^-2 * b^-2 * a^-1 * b, (b * a^-1 * b)^3, (a^-1 * b^2 * a * b^-1)^2 ] >,ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 6, 7, 4, 5) >,
    Group< a,b | [ a^7, b^5, a^-1 * b^2 * a^-2 * b * a^2 * b^-1, (b^-1 * a^-1 * b^-1)^3, (a * b^2 * a^-1 * b^-1)^2 ]>,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta + 4,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 6, 4, 5, 7) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a)^3, (a^-1 * b^2 * a * b^-1)^2, a * b * a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a* b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 3,xm12,xm21,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 6, 4, 7, 5) >,
    Group< a,b | [ a^7, b^5, (a * b * a)^2, (b * a^-1 * b)^3, (a * b^2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 6, 5, 4, 7) >,
    Group< a,b | [ a^7, b^5, (a * b^-1 * a^2)^2, (a^-1, b^-1)^2, (b * a^2 * b)^3 ] >,
    ideal< R | [5,xcom + 1,x12 + 3*zeta + 3,xm12 + 3,xm21 + 3,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 6)(4, 7) >,
    Group< a,b | [ a^7, b^2, (a * b * a^-1 * b)^2, (b * a^-1)^7, (a * b * a)^6 ] >,
    ideal< R | [5,xcom + 1,x12 + 3*zeta + 2,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 7, 6, 5, 4) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a^-1)^3, (a * b^2 * a)^2, (a * b^-2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom,x12,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 7, 4) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a^-1)^3, a * b^-1 * a^-2 * b^-1 * a^2 * b * a^-2 * b * a, b * a^-1 * b * a * b^-1 * a^3* b * a^3 * b^-1 * a ] >,
    ideal< R | [5,xcom + 2,x12,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 7, 5, 6, 4) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a^-1)^3, (a * b^-1)^4, (a * b * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 7, 5) >,
    Group< a,b | [ a^7, b^3, (b, a^-1, b), (a^3 * b)^3, (a * b^-1 * a^-2 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 7, 6, 4, 5) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a^-1)^3, (a * b^-1)^4, b^-2 * a * b^-1 * a^2 * b^2 * a^-2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 7, 4, 5, 6) >,
    Group< a,b | [ a^7, b^5, (a * b * a^2)^2, (a^-1, b^-1)^2, (b^-1 * a^2 * b^-1)^3 ] >,
    ideal< R | [5,xcom + 1,x12 + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 7, 4, 6, 5) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a^-1)^3, (a * b^2 * a^-1 * b^-1)^2, a * b * a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1* a * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 7, 5, 4, 6) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a^-1)^3, (a^-1 * b^2 * a * b^-1)^2, a * b^-1 * a^-1 * b * a^-2 * b^-1 * a^-1 * b* a * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (3, 7)(4, 6) >,
    Group< a,b | [ a^7, b^2, (a * b * a)^4, (a^-1 * b)^6, (a^-1 * b * a * b)^3, b * a^-2 * b * a * b * a * b * a^-3 * b *a * b * a * b * a^-1 * b * a^-1 * b * a ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 2,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 3*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3)(5, 7) >,
    Group< a,b | [ a^7, b^2, (a^-1 * b)^4, (a * b * a)^4, a * b * a^-1 * b * a * b * a^-2 * b * a^-3 * b * a * b * a^-1 *b * a^2 * b * a^-2 * b ] >,
    ideal< R | [5,xcom + 3,x12 + zeta + 1,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3)(4, 5, 6, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a)^3, (a^-1 * b^-1)^4, a * b^-2 * a^-1 * b^-2 * a^-2 * b^2 * a * b * a^2 ] >,ideal< R | [5,xcom + 3*zeta + 3,x12 + 4,xm12,xm21,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3)(4, 5, 7, 6) >,
    Group< a,b | [ a^7, b^4, (a^-2 * b)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, (b^-1 * a^-1)^5,a^-2 * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a^2 * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3)(4, 6, 7, 5) >,
    Group< a,b | [ a^7, b^4, (a^-2 * b^-1)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, (b^-1 * a^-1)^5,a^-1 * b^-2 * a^2 * b^-1 * a^-2 * b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 3*zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3)(4, 6, 5, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a)^3, a * b^-1 * a^-1 * b^-2 * a^2 * b^-1 * a^-1 * b^2 * a, (b^-1 * a^-1)^5, b* a^-1 * b^-1 * a^-3 * b * a * b * a^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3)(4, 7, 6, 5) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a^-1)^3, (a * b^-1)^4, a * b^-2 * a^-1 * b^-2 * a^-2 * b^2 * a * b^-1 * a^2 ]>,
    ideal< R | [5,xcom + 2*zeta,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3)(4, 7, 5, 6) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a^-1)^3, a * b * a^-1 * b^-2 * a^2 * b * a^-1 * b^2 * a, (b^-1 * a)^5, b^-1 *a^-1 * b * a^-3 * b^-1 * a * b^-1 * a^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 4)(5, 6, 7) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a)^3, b * a^-2 * b^-1 * a^3 * b^-1 * a^-2 * b * a, a * b^-1 * a^-2 * b^-1 *a^-2 * b^-1 * a * b * a^2 * b ] >,
    ideal< R | [5,xcom + 2,x12 + zeta + 3,xm12,xm21,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 4)(5, 7, 6) >,
    Group< a,b | [ a^7, b^3, (a * b^-1 * a * b * a)^2, (b^-1 * a^-1)^5, (b^-1 * a)^5, (a * b * a^-1 * b^-1 * a^2)^2] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 4, 5)(6, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a)^3, (a^-1 * b^-1)^4, a * b^-2 * a^-1 * b^-1 * a^-3 * b^2 * a * b^2 * a ] >,ideal< R | [5,xcom + 2*zeta,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 4, 5, 7) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^2, b * a^-2 * b^-1 * a^3 * b^-1 * a^-2 * b * a, b^-1 * a^-1 * b^-1 * a^-1 *b^2 * a^2 * b * a^2 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta + 1,xm12 + zeta,xm21 + 4*zeta + 4,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 4, 6, 7) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^2, a^-1 * b^2 * a^-1 * b^-1 * a^2 * b^-2 * a^2 * b^-1, b^2 * a * b * a^-3 * b* a * b^2 * a^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 4*zeta + 4,xm21 + zeta,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 4, 6)(5, 7) >,
    Group< a,b | [ a^7, b^4, a * b^-2 * a * b^-1 * a^2 * b^2 * a * b^-1 * a, (a * b^-1 * a^-1 * b * a)^2, (b^-1 *a)^5, a^-1 * b^-2 * a^-1 * b^-1 * a^-2 * b^2 * a * b * a * b ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 4, 7, 5) >,
    Group< a,b | [ a^7, b^5, (a^-2 * b^-1)^3, b * a * b^-1 * a^-2 * b * a * b * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 4, 7, 6) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a^-1)^3, (a * b^-2 * a)^2, (a * b * a^-1 * b * a)^2 ] >,
    ideal< R | [5,xcom,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 5, 4)(6, 7) >,
    Group< a,b | [ a^7, b^4, (a^-2 * b^-1)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-1 * b^-2 *a^-2 * b^-1 * a^2 * b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 5, 7, 4) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, b^-1 * a * b^-1 * a^-3 * b^-1 * a^-1 * b^2 * a^-1, b^-1 * a^-1 * b * a^-3 *b * a^2 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 3*zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 5, 7, 6) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, b * a^2 * b^-1 * a^-2 * b * a^-1 * b^-2 * a^-1, a^-1 *b^-1 * a * b^-1 * a^-2 * b^2 * a^2 * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 5)(4, 6, 7) >,
    Group< a,b | [ a^7, b^3, (a * b^-1 * a^-1 * b^-1 * a)^2, (b^-1 * a)^5, (a * b^-1 * a * b^-1 * a^2)^2 ] >,ideal< R | [5,xcom,x12 + 3*zeta + 2,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 5, 7)(4, 6) >,
    Group< a,b | [ a^7, b^4, (a * b^-1)^4, (a^-2 * b)^3, a * b^-2 * a^-1 * b^-1 * a^3 * b^2 * a^-1 * b^-1 * a^2, a* b^-1 * a^-1 * b * a^3 * b^2 * a * b * a^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 5, 4, 7) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a^-1)^3, (a * b^-1)^4, a^-3 * b^-1 * a^3 * b * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + zeta + 3,x12,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 5, 6)(4, 7) >,
    Group< a,b | [ a^7, b^4, a^-1 * b^-2 * a * b^-1 * a^-1 * b^2 * a * b^-1, a * b^-2 * a^-1 * b^-1 * a^2 * b^2 *a^-1 * b^-1 * a, (b^-1 * a)^5, a^-1 * b^-1 * a * b * a^-2 * b^-1 * a^-1 * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 6, 7, 4) >,
    Group< a,b | [ a^7, b^5, b * a^-1 * b^-1 * a^3 * b^-2 * a * b, (b^-1 * a)^5, a^-1 * b * a * b^-1 * a^-2 * b^-1 * a* b^-1 * a^-1 * b, (a * b^-1 * a^-1 * b * a^2)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4*zeta + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 6, 7, 5) >,
    Group< a,b | [ a^7, b^5, a * b^-2 * a^3 * b^-1 * a^-1 * b^2, (b^-1 * a)^5, a^-1 * b^-1 * a * b^-1 * a^-2 * b^-1 *a * b * a^-1 * b, (a * b * a^-1 * b^-1 * a^2)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta + 1,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 6, 5, 7) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, b * a^2 * b^-1 * a^-2 * b^-1 * a * b^-2 * a^-1, b^2 * a *b^-1 * a^-2 * b * a^2 * b^-1 * a ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 6, 7)(4, 5) >,
    Group< a,b | [ a^7, b^4, (a * b^-1)^2, (a^-1 * b^-1)^4, a^2 * b^-1 * a^-1 * b^-2 * a^-2 * b^-1 * a^3 * b^2 * a* b * a^-1 * b^-1 * a^2 * b * a ] >,
    ideal< R | [5,xcom + 3,x12 + 4*zeta,xm12 + 1,xm21 + 1,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 6)(4, 5, 7) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a)^5, b^-1 * a^-2 * b^-1 * a^3 * b * a^2 * b^-1 * a, (a * b^-1 * a)^4 ] >,ideal< R | [5,xcom + zeta + 3,x12 + 2*zeta + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 6, 5)(4, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a^-1)^3, (a * b^-1)^4, a * b * a^-1 * b^-2 * a^2 * b * a^-1 * b^2 * a, a^-1 *b^-1 * a * b * a^4 * b * a^-1 * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 6, 4, 7) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, b^2 * a^-3 * b^-1 * a^-1 * b * a ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 7, 5, 4) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a)^3, (a^-1 * b^-1)^4, b * a^2 * b^-1 * a^3 * b * a^-3 * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 7, 6, 4) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, b^2 * a^-1 * b^-1 * a^-2 * b * a^2 * b^-1 * a^-1, b^-1 *a^2 * b^-1 * a^-2 * b * a * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 7, 4)(5, 6) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-2 * a^-1* b^-1 * a^2 * b * a^-1 * b * a, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 4,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 7, 6, 5) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a)^3, (a * b^2 * a)^2, (a * b^-1 * a^-1 * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12,xm21,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 7, 4, 5) >,
    Group< a,b | [ a^7, b^5, (a * b * a^2)^2, (b * a^-1 * b)^3, (a^-1 * b^-2 * a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3,x12 + zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 7, 6)(4, 5) >,
    Group< a,b | [ a^7, b^4, b^-1 * a^-1 * b * a^3 * b^2 * a^-1 * b^-1 * a, b * a^-1 * b^-2 * a^3 * b^-1 * a^-1 * b* a ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 7, 5)(4, 6) >,
    Group< a,b | [ a^7, b^4, (a * b^-1)^4, (a^-2 * b)^3, a * b^-1 * a^-1 * b * a^2 * b * a * b^2 * a ] >,
    ideal< R| [5,xcom + zeta + 1,x12 + 3*zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 7)(4, 6, 5) >,
    Group< a,b | [ a^7, b^3, (a * b^-1)^4, (b^-1 * a^-1)^5, b^-1 * a^-1 * b * a * b^-1 * a^2 * b * a * b^-1 * a^-2] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 3, 7, 4, 6) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, a^-1 * b^-2 * a^-3 * b^-1 * a^-1 * b^-1 * a^-1 * b, a * b^-1 * a^-1 * b^-1* a^3 * b * a^2 * b * a ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 2*zeta + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 3)(5, 6, 7) >,
    Group< a,b | [ a^7, b^3, (a * b * a * b^-1 * a)^2, (b^-1 * a^-1)^5, (b^-1 * a)^5, (a * b^-1 * a^-1 * b * a^2)^2] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 3)(5, 7, 6) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a^-1)^3, b^-1 * a^-2 * b * a^3 * b * a^-2 * b^-1 * a, a * b * a^-2 * b * a^-2* b * a * b^-1 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 5, 3)(6, 7) >,
    Group< a,b | [ a^7, b^4, (a^-2 * b)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-2 * a^-2 *b^-1 * a^2 * b^2 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 3*zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 5, 7, 3) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a^-1)^3, (a * b^-1)^4, a^-2 * b^2 * a^3 * b * a^-3 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7, 5, 3) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, b * a^-1 * b^-1 * a^-3 * b^-1 * a^2 * b * a^-1, b * a * b * a^-3 * b *a^-1 * b^-2 * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7, 6, 3) >,
    Group< a,b | [ a^7, b^5, b^-1 * a^-1 * b * a^3 * b^2 * a * b^-1, (b^-1 * a^-1)^5, a^-1 * b^-1 * a * b * a^-2 * b *a * b * a^-1 * b^-1, (a * b * a^-1 * b^-1 * a^2)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 3*zeta + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7, 3)(5, 6) >,
    Group< a,b | [ a^7, b^4, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-1 * a^-1 *b^-1 * a^2 * b^2 * a^-1 * b * a, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4)(5, 7) >,
    Group< a,b | [ a^7, b^2, (a^-1 * b)^6, (a^-2 * b)^5, (b * a^-2 * b * a^-1)^3 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta,xm2 + 4*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 6, 7, 5) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, b * a^-1 * b^-1 * a^-3 * b^-1 * a * b^-1 * a^-1 * b, a^2 * b * a^-3 * b *a^-1 * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 6, 5, 7) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a^-1)^3, (a^-2 * b)^3, b * a^-1 * b^-1 * a^3 * b^-1 * a^-1 * b * a^-1 ] >,
    ideal<R | [5,xcom,x12,xm12 + 3,xm21 + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7, 6, 5) >,
    Group< a,b | [ a^7, b^5, b^-1 * a * b^-1 * a^-2 * b * a * b^-1 * a^-1, (a^-2 * b)^3 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7, 5, 6) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, (a^-2 * b^-1)^3, (b * a^-1 * b)^3, (a * b * a * b^-1 * a)^2 ] >,
    ideal< R |[5,xcom + 2*zeta + 2,x12 + 4*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4)(3, 5, 6, 7) >,
    Group< a,b | [ a^7, b^4, (a * b * a^-1 * b^-1 * a)^2, a * b^-1 * a * b^-2 * a^2 * b^-1 * a * b^2 * a, (b^-1 *a)^5, a * b * a * b^-2 * a^-2 * b^-1 * a^-1 * b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta + 4,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 3, 5)(6, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a)^3, a * b^-2 * a^-1 * b^-1 * a^2 * b^2 * a^-1 * b^-1 * a, (b^-1 * a^-1)^5, b* a * b * a^-3 * b^-1 * a^-1 * b * a^2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 6, 7)(3, 5) >,
    Group< a,b | [ a^7, b^4, (a * b^-1)^4, (a^-2 * b)^3, a * b * a^-1 * b^-1 * a^3 * b * a * b^2 * a^2 ] >,
    ideal<R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 6)(3, 5, 7) >,
    Group< a,b | [ a^7, b^3, (a^-2 * b)^3, (a * b^-1 * a * b^-1 * a^2)^2, (a^-1 * b^-1)^6, b^-1 * a^-2 * b^-1 *a^-3 * b * a * b * a^-3 ] >,
    ideal< R | [5,xcom,x12 + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7, 3, 5) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-2)^2, (a * b^-1 * a * b^-1 * a^2)^2, (a^3 * b)^3 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 4,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7, 6)(3, 5) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, a * b^-2 * a * b^-1 * a^2 * b^-1 * a^-1 * b * a ] >,ideal< R | [5,xcom + zeta + 1,x12 + 4,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4)(3, 6, 5, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a^-1)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^2 *b^-2 * a^2 * b^2 * a^2 * b^-1, a^-1 * b * a * b^-1 * a^-2 * b * a^-1 * b^2 * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 3, 6)(5, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a^-1)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^2 *b^-2 * a^2 * b^2 * a^2 * b^-1, a * b^-2 * a * b^-1 * a^-2 * b^-1 * a * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 5)(3, 6, 7) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a)^5, b^-1 * a^2 * b * a^3 * b^-1 * a^-2 * b^-1 * a ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + zeta + 3,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 5, 7)(3, 6) >,
    Group< a,b | [ a^7, b^4, (a * b^-1 * a)^2, a^-1 * b * a^-1 * b^-1 * a * b^-1 * a * b^-1, (a^-1 * b^-1)^6, (b^-1* a^-2 * b^-1 * a^-1)^3, a * b * a^-3 * b^-1 * a^-2 * b^-2 * a^-1 * b^2 * a^3 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 2*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7, 5)(3, 6) >,
    Group< a,b | [ a^7, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^-1 * b^-1 * a^3 * b *a^-1 * b * a, (a * b^-1 * a^-1 * b * a)^2, a^2 * b * a^-3 * b^2 * a * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 1,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7)(3, 6, 5) >,
    Group< a,b | [ a^7, b^3, (a^-1 * b^-1)^4, b * a^-1 * b * a^-3 * b * a * b^-1 * a^-2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 1,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 7, 3, 6) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-2)^2, (a^-2 * b)^3, b^-1 * a^-1 * b * a^-3 * b * a^-1 * b^-1 * a^2 ] >,
    ideal<R | [5,xcom + 2,x12 + 3*zeta + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4)(3, 7, 6, 5) >,
    Group< a,b | [ a^7, b^4, (a * b^-1 * a^-1 * b * a)^2, a * b * a * b^-2 * a^2 * b * a * b^2 * a, (b^-1 *a^-1)^5, a * b^-1 * a * b^-2 * a^-2 * b * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4)(3, 7, 5, 6) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^2 * b^-2 *a^2 * b^2 * a^2 * b^-1, a^-1 * b^-1 * a * b * a^-2 * b * a * b^2 * a * b ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta + 3,xm12,xm21,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 3, 7, 5) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, (a^-2 * b)^3, (b^-1 * a^-1 * b^-1)^3, (a * b * a * b^-1 * a)^2 ] >,ideal< R | [5,xcom + 2*zeta + 2,x12 + 4*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 3, 7, 6) >,
    Group< a,b | [ a^7, b^5, a * b^2 * a^3 * b * a^-1 * b^-2, (b^-1 * a^-1)^5, a^-1 * b * a * b * a^-2 * b * a * b^-1* a^-1 * b^-1, (a * b^-1 * a^-1 * b * a^2)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 3, 7)(5, 6) >,
    Group< a,b | [ a^7, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a * b^-1)^4, (a * b * a * b^-1 * a)^2,(b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 3*zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 5, 6)(3, 7) >,
    Group< a,b | [ a^7, b^4, (a^-2 * b)^3, (a * b * a * b^-1 * a)^2, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 6, 5)(3, 7) >,
    Group< a,b | [ a^7, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1)^4, a^-1 * b^-1 * a * b^-1* a^2 * b * a^2 * b, b^-1 * a * b * a^3 * b * a * b^2 * a^3 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 6)(3, 7, 5) >,
    Group< a,b | [ a^7, b^3, (a * b * a * b^-1 * a)^2, (a^-1 * b^-1 * a * b^-1)^3, (a * b * a^-2 * b^-1 * a^2)^2,b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^3 * b * a^-1 * b * a^-1 * b * a^-1, b * a * b^-1 * a * b^-1 * a^3 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 2*zeta + 4,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 4, 6, 3, 7) >,
    Group< a,b | [ a^7, b^5, (a * b^-1 * a)^2, (b * a^-1 * b)^3, (a * b * a * b * a)^2 ] >,
    ideal< R | [5,xcom + 3,x12 + zeta + 3,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 4, 3)(6, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a^-1)^3, (a * b^-1)^4, a^-1 * b^-2 * a * b^-1 * a^-2 * b^2 * a * b^2 * a *b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 7, 4, 3) >,
    Group< a,b | [ a^7, b^5, (a^-2 * b)^3, b^-1 * a * b * a^-2 * b^-1 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 7, 3)(4, 6) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, a * b * a^-1 * b^-1 * a^2 * b^-1 * a * b^2 * a ] >,ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 3)(4, 7, 6) >,
    Group< a,b | [ a^7, b^3, (a * b * a^-1 * b * a)^2, (b^-1 * a^-1)^5, (a * b * a * b * a^2)^2 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 4, 7, 3) >,
    Group< a,b | [ a^7, b^5, (a * b^-1 * a^2)^2, (b^-1 * a^-1 * b^-1)^3, (a * b^-2 * a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 6, 3)(4, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a)^3, (a^-1 * b^-1)^4, a * b^-1 * a^-1 * b^-2 * a^2 * b^-1 * a^-1 * b^2 * a,a^-1 * b * a * b^-1 * a^4 * b^-1 * a^-1 * b * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta,xm12,xm21,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 6, 7, 4) >,
    Group< a,b | [ a^7, b^5, (a^-2 * b^-1)^3, b * a * b * a^-2 * b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 7, 6, 4) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, a^2 * b^-1 * a^-3 * b^-1 * a^-1 * b * a^-1 * b, b^-1 * a^-1 * b * a^-3 *b * a * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5)(4, 7) >,
    Group< a,b | [ a^7, b^2, (b * a^-1)^7, (b * a^-2 * b * a)^3, a^-2 * b * a^-2 * b * a^-3 * b * a * b * a^-1 * b * a *b * a^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 2*zeta + 3,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 6, 4, 7) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, (a^-2 * b^-1)^3, (b * a^-1 * b)^3, (a * b^-1 * a * b * a)^2 ] >,
    ideal< R |[5,xcom + 3*zeta,x12 + 4*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 3, 4)(6, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a^-1)^3, a * b^-2 * a^-1 * b * a^2 * b^2 * a^-1 * b * a, (b^-1 * a)^5, b^-1 *a * b^-1 * a^-3 * b * a^-1 * b^-1 * a^2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 7, 6)(3, 4) >,
    Group< a,b | [ a^7, b^4, (a * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b^-1 * a^-1 *b^-1 * a^2 * b * a^-1 * b^2 * a, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 3*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5)(3, 4, 6, 7) >,
    Group< a,b | [ a^7, b^4, a * b^-2 * a^-1 * b^-1 * a * b^2 * a^-1 * b^-1, a * b^-1 * a^-1 * b^-2 * a^2 * b^-1 *a^-1 * b^2 * a, (b^-1 * a)^5, a^-1 * b * a^-1 * b^-1 * a^-2 * b * a * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 3*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5)(3, 4, 7, 6) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a)^3, (a^-1 * b^-1)^4, a * b^-2 * a^-1 * b^-1 * a^2 * b^2 * a^-1 * b^-1 * a, a* b * a^-1 * b^-1 * a^4 * b^-1 * a * b * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 6)(3, 4, 7) >,
    Group< a,b | [ a^7, b^3, (a * b * a^-1 * b * a)^2, (b^-1 * a)^5, b * a^-1 * b^-1 * a^-3 * b^-1 * a^-1 * b *a^-2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 1,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 7, 4)(3, 6) >,
    Group< a,b | [ a^7, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b * a^-1 * b * a^3 * b^-1 * a^-1* b^-1 * a, (a * b * a^-1 * b^-1 * a)^2, a^2 * b^-1 * a^-3 * b^2 * a * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5)(3, 6, 7, 4) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a^-1)^3, (a * b^-1)^4, a * b^-2 * a^-1 * b * a^2 * b^2 * a^-1 * b * a, b^-1 *a^-2 * b^-1 * a^3 * b^-1 * a * b * a^-2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 4,xm21 + 4,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 7)(3, 6, 4) >,
    Group< a,b | [ a^7, b^3, (a^-1 * b^-1)^4, b^-1 * a * b * a^-3 * b * a^-1 * b * a^-2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 3, 6, 7) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, a^-1 * b^-1 * a^-3 * b^2 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3,xm12 + 4,xm21 + 4,xm2m1 + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5)(3, 6, 4, 7) >,
    Group< a,b | [ a^7, b^4, a^-1 * b * a^-1 * b^-1 * a^2 * b^2 * a^-1 * b^-1 * a^-1, a * b^-1 * a * b^-2 * a^2 *b^-1 * a * b^2 * a, b^-1 * a^-1 * b^-2 * a^3 * b * a^-1 * b^2 * a^-2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 3, 6)(4, 7) >,
    Group< a,b | [ a^7, b^4, a * b^-2 * a * b^-1 * a^2 * b^2 * a * b^-1 * a, a^-1 * b^-2 * a * b * a^2 * b^-1 * a *b * a^-1, b * a * b^-2 * a^-3 * b^-1 * a * b^2 * a^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta + 4,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 4, 7)(3, 6) >,
    Group< a,b | [ a^7, b^4, (a * b^-1 * a^2)^2, (a^-1 * b * a^-1 * b^-1)^2, (a * b^-1)^6, b^-1 * a^-1 * b^-2 *a^-1 * b * a^-2 * b^2 * a * b^2 * a * b^-1 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 4,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 3, 7, 4) >,
    Group< a,b | [ a^7, b^5, (a * b^-2)^2, (a^3 * b^-1)^3, (a * b * a * b * a^2)^2 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 4)(3, 7, 6) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a^-1)^5, b * a^2 * b^-1 * a^3 * b * a^-2 * b * a, (a * b * a)^4 ] >,
    ideal< R| [5,xcom + zeta + 3,x12 + 2*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 6, 4)(3, 7) >,
    Group< a,b | [ a^7, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a * b^-1)^4, b * a^2 * b^-1 * a^2 *b^-1 * a^-1 * b * a, b * a * b^-1 * a^3 * b * a^-1 * b^2 * a^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 2*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5)(3, 7, 6, 4) >,
    Group< a,b | [ a^7, b^4, a * b^-2 * a^-1 * b^-1 * a * b^2 * a^-1 * b^-1, a * b * a^-1 * b^-2 * a^2 * b * a^-1 *b^2 * a, (b^-1 * a^-1)^5, a^-1 * b^-1 * a^-1 * b * a^-2 * b^-1 * a * b * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 3,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 6)(3, 7, 4) >,
    Group< a,b | [ a^7, b^3, (a^-1 * b^-1)^4, (a * b^-1)^4, (a * b^-1 * a^-1 * b * a^2)^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 3, 7, 6) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, b * a^-1 * b * a^-3 * b^2 * a^-1 * b^-1 * a^-1, a^-1 * b * a^-1 * b^-1 *a^3 * b^-2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 4,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5)(3, 7, 4, 6) >,
    Group< a,b | [ a^7, b^4, a^-1 * b^-1 * a^-1 * b * a^2 * b^2 * a^-1 * b * a^-1, a * b * a * b^-2 * a^2 * b * a *b^2 * a, b * a^-1 * b^-2 * a^3 * b^-1 * a^-1 * b^2 * a^-2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 1,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 5, 3, 7)(4, 6) >,
    Group< a,b | [ a^7, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b * a^-1 * b^-1 * a^-3 * b * a^-2* b * a^-1, a * b * a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 2,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 4, 3)(5, 7) >,
    Group< a,b | [ a^7, b^4, (a * b * a^-1 * b^-1 * a)^2, a * b^-2 * a * b * a^2 * b^2 * a * b * a, (b^-1 *a^-1)^5, a^-1 * b^-2 * a^-1 * b * a^-2 * b^2 * a * b^-1 * a * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 3,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 7, 5, 3) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, (a * b^-1)^4, b * a^2 * b^-1 * a^-2 * b * a * b^-2 * a, a^-1 * b^-1 * a* b * a^-2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 7, 3)(4, 5) >,
    Group< a,b | [ a^7, b^4, b * a^-1 * b^-1 * a^3 * b^2 * a^-1 * b * a, b^-1 * a^-1 * b^-2 * a^3 * b * a^-1 * b^-1* a ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 5, 3)(4, 7) >,
    Group< a,b | [ a^7, b^4, a^-1 * b^-2 * a * b^-1 * a^-1 * b^2 * a * b^-1, a * b^-2 * a^-1 * b * a^2 * b^2 * a^-1* b * a, (b^-1 * a^-1)^5, a^-1 * b * a * b^-1 * a^-2 * b * a^-1 * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 3)(4, 7, 5) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a^-1)^5, b * a^-2 * b * a^3 * b^-1 * a^2 * b * a ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 2*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 4, 7, 3) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, a^-1 * b^2 * a^-3 * b * a^-1 * b * a^-1 * b^-1, a^2 * b^-2 * a^3 * b^-1* a^-1 * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + zeta + 1,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 7, 5, 4) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a)^3, (a^-1 * b^-1)^4, a^-3 * b^-1 * a^3 * b^-2 * a^-2 * b ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + zeta + 1,xm12,xm21,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 5, 7, 4) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, (a^-2 * b)^3, (b^-1 * a^-1 * b^-1)^3, (a * b^-1 * a * b * a)^2 ] >,ideal< R | [5,xcom + 3*zeta,x12 + zeta + 1,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 3, 4)(5, 7) >,
    Group< a,b | [ a^7, b^4, (b^-1 * a)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^2 * b^-2 *a^2 * b^2 * a^2 * b^-1, a^-1 * b^-2 * a^-1 * b^-1 * a^-2 * b * a * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta + 3,xm12,xm21,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 7, 5)(3, 4) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a * b * a^-1 * b* a^2 * b^-1 * a^-1 * b^2 * a, b^-1 * a^2 * b^-2 * a^2 * b^2 * a^2 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 5, 7)(3, 4) >,
    Group< a,b | [ a^7, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a * b^-1)^4, (a * b^-1 * a * b * a)^2,(b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 2*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6)(3, 4, 5, 7) >,
    Group< a,b | [ a^7, b^4, (a^-2 * b)^3, a^-1 * b^-1 * a * b^-1 * a^2 * b^2 * a^-1 * b * a^-1, (b^-1 * a)^5 ] >,ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 5)(3, 4, 7) >,
    Group< a,b | [ a^7, b^3, (a^-1 * b^-1)^4, (a * b^-1)^4, (a * b * a^-1 * b^-1 * a^2)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6)(3, 4, 7, 5) >,
    Group< a,b | [ a^7, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a * b^-1)^4, a * b * a^-1 * b^-1 * a^2* b^-1 * a^2 * b, b^-1 * a^-1 * b * a^-3 * b * a^-1 * b^2 * a^-3 ] >,
    ideal< R | [5,xcom + 3*zeta + 1,x12 + 2*zeta + 4,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 3, 4, 7) >,
    Group< a,b | [ a^7, b^5, (a * b^-1)^4, b^-1 * a^-1 * b^-1 * a^-3 * b^-2 * a^-1 * b * a^-1, a^2 * b^-2 * a^3 * b^-1* a * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 2*zeta + 3,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 7, 4)(3, 5) >,
    Group< a,b | [ a^7, b^4, (a * b^-1)^4, (a^-2 * b)^3, a * b * a^-1 * b^-1 * a^2 * b^2 * a * b * a ] >,
    ideal< R| [5,xcom + 4*zeta,x12 + 3*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 4)(3, 5, 7) >,
    Group< a,b | [ a^7, b^3, (a * b^-1 * a * b * a)^2, (a^-1 * b^-1 * a * b^-1)^3, b^-1 * a^-1 * b^-1 * a^-1 * b^-1* a^3 * b^-1 * a * b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 7)(3, 5, 4) >,
    Group< a,b | [ a^7, b^3, (a * b^-1)^4, (b^-1 * a^-1)^5, a^-2 * b^-1 * a^-1 * b * a^2 * b * a * b^-1 * a^-1 * b] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2,xm12 + 4,xm21 + 4,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6)(3, 5, 7, 4) >,
    Group< a,b | [ a^7, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1)^4, a * b^-1 * a^-1 * b *a^2 * b * a^2 * b^-1, b * a^-1 * b^-1 * a^-3 * b * a * b^2 * a^-2 ] >,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 3, 5)(4, 7) >,
    Group< a,b | [ a^7, b^4, a^-1 * b^-2 * a * b^-1 * a^2 * b * a * b^-1 * a^-1, a * b^-2 * a * b * a^2 * b^2 * a *b * a, b^-1 * a * b^-2 * a^-3 * b * a * b^2 * a^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 4, 7)(3, 5) >,
    Group< a,b | [ a^7, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-2 * b * a^-3 * b^-1 * a^-1 * b* a^-1 * b, a^-1 * b^-2 * a * b^-1 * a^-2 * b * a * b * a^-1 * b^-1, a^-1 * b^-1 * a^-1 * b * a^-2 * b^-1 * a^-1 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 2,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 4)(3, 7, 5) >,
    Group< a,b | [ a^7, b^3, (a^-2 * b^-1)^3, (a * b * a * b * a^2)^2, (a * b^-1)^6, a^-1 * b^-1 * a * b^-1 * a^-3* b * a^-2 * b * a^-2 ] >,
    ideal< R | [5,xcom,x12 + zeta + 3,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 5, 4)(3, 7) >,
    Group< a,b | [ a^7, b^4, (a^-2 * b^-1)^3, (a * b^-1 * a * b * a)^2, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 3*zeta + 3,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 3, 7, 4) >,
    Group< a,b | [ a^7, b^5, (a * b^-2)^2, (a^-2 * b^-1)^3, b * a^-1 * b^-1 * a^-3 * b^-1 * a^-1 * b * a^2 ] >,
    ideal<R | [5,xcom + 2,x12 + 3*zeta + 1,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 5)(3, 7, 4) >,
    Group< a,b | [ a^7, b^3, (a * b^-1 * a^-1 * b^-1 * a)^2, (b^-1 * a^-1)^5, b^-1 * a^-1 * b * a^-3 * b * a^-1 *b^-1 * a^-2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6)(3, 7, 5, 4) >,
    Group< a,b | [ a^7, b^4, (a^-2 * b^-1)^3, a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b * a * b^2 * a^-1, (b^-1 * a^-1)^5] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 4, 3, 7) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, a^-1 * b * a^-3 * b^-2 * a * b^-1 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 1,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 5, 3, 7) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^4, b^-2 * a^-3 * b * a^-1 * b^-1 * a, (a^-2 * b^-1)^3 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4,xm12 + 3,xm21 + 3,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 6, 3, 7)(4, 5) >,
    Group< a,b | [ a^7, b^4, (a * b * a^2)^2, (a^-1 * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1* b^2 * a^-1 * b^-1, (a^-1 * b^-1 * a^-1 * b)^3, b^-1 * a * b^-2 * a^-1 * b * a^-2 * b^2 * a * b^2 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 5, 4, 3) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^2, b^-1 * a^-2 * b * a^3 * b * a^-2 * b^-1 * a, b^-1 * a * b^-1 * a^2 *b^-1 * a^2 * b^-1 * a * b^-2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta,xm2 + 3*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 6, 4, 3) >,
    Group< a,b | [ a^7, b^5, (a^-1 * b^-1)^2, b * a^2 * b^2 * a^2 * b * a^-1 * b^-2 * a^-1, b^-2 * a * b^-1 * a^-3 *b^-1 * a * b^-2 * a^2 ] >,
    ideal< R | [5,xcom,x12 + zeta,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 4*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 6, 3)(4, 5) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^2, (a * b^-1)^4, a^2 * b * a^-1 * b^-2 * a^-2 * b * a^3 * b^2 * a * b^-1* a^-1 * b * a^2 * b^-1 * a ] >,
    ideal< R | [5,xcom + 3,x12 + zeta,xm12 + 4,xm21 + 4,xm2m1 + 4*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 3)(4, 5, 6) >,
    Group< a,b | [ a^7, b^3, (a^-1 * b^-1)^4, (b^-1 * a)^5, b^-1 * a^-1 * b * a * b^-1 * a^2 * b^-1 * a^-1 * b *a^-2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 5, 3)(4, 6) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, a * b * a^-1 * b^-1 * a^3 * b^2 * a * b^-1 * a^2 ]>,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 5, 6, 4) >,
    Group< a,b | [ a^7, b^5, (b^-1 * a)^3, (a^-2 * b^-1)^3, (a * b^-2 * a^2)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta,xm12,xm21,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 3,xm2 + 2*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 3, 4)(5, 6) >,
    Group< a,b | [ a^7, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1)^4, (a * b^-1 * a * b *a)^2, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 4*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 5, 6)(3, 4) >,
    Group< a,b | [ a^7, b^4, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, (a^-1 * b^-1)^4, (a * b * a * b^-1 *a)^2, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 4*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 6)(3, 4, 5) >,
    Group< a,b | [ a^7, b^3, (a^-1 * b^-1)^4, (b^-1 * a)^5, a^-2 * b * a^-1 * b^-1 * a^2 * b^-1 * a * b * a^-1 *b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7)(3, 4, 5, 6) >,
    Group< a,b | [ a^7, b^4, (a * b^-1)^2, (a * b * a)^4, (a^-1 * b^-1)^6, b^-1 * a^-2 * b * a * b^-2 * a^-2 * b^2* a^-1 * b^-1 * a^-1 * b^-1 * a * b * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta,xm12 + zeta,xm21 + 4*zeta + 4,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 5)(3, 4, 6) >,
    Group< a,b | [ a^7, b^3, (a * b^-1)^4, b * a * b^-1 * a^-3 * b^-1 * a^-1 * b^-1 * a^-2 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7)(3, 4, 6, 5) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b * a^-1 * b^-2 * a * b^2 * a^-1 * b^-1, b^-2 *a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^2 * b^-1 * a^-2 * b^2 * a^-1 * b * a^-2 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 6, 4)(3, 5) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, a * b^-1 * a^-1 * b * a^3 * b^-1 * a * b^2 * a^2 ]>,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 4)(3, 5, 6) >,
    Group< a,b | [ a^7, b^3, (a * b^-1)^4, b^-1 * a^-1 * b^-1 * a^-3 * b^-1 * a * b * a^-2 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7)(3, 5, 6, 4) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b^-1 * a^-1 * b^-2 * a * b^2 * a^-1 * b, b^-2 *a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-1 * b^-2 * a^-1 * b^-1 * a^-2 * b * a^2 * b * a^-1 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 3, 5)(4, 6) >,
    Group< a,b | [ a^7, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, b^-1 * a^-1 * b * a^-3 * b^-1 *a^-2 * b^-1 * a^-1, a^-1 * b^-1 * a * b^-1 * a^-2 * b * a * b^2 * a^-1 * b, a * b^-1 * a^-1 * b * a^-2 * b^-1 * a^-1 * b * a^-1 * b ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 4, 6)(3, 5) >,
    Group< a,b | [ a^7, b^4, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^2 * a^-1, a^-2 * b^-1 * a^-3 * b * a^-1 *b^-1 * a^-1 * b^-1, a^-1 * b * a^-1 * b^-1 * a^-2 * b * a^-1 * b^-1 * a * b ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7)(3, 5, 4, 6) >,
    Group< a,b | [ a^7, b^4, (a * b^-1 * a)^2, (a^-1 * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 *a^-1 * b^2 * a^-1 * b^-1, b * a^-1 * b * a * b * a^-1 * b^-1 * a * b^2 * a^-1 * b * a * b^2 * a ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 5, 4)(3, 6) >,
    Group< a,b | [ a^7, b^4, (a * b * a)^2, a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1, (a * b^-1)^6, (b * a^-2 *b * a^-1)^3, a^-1 * b * a^3 * b^-1 * a^2 * b^-2 * a * b^2 * a^-3 * b^2 * a * b^-1 ] >,
    ideal< R | [5,xcom + 3,x12 + 4*zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 3, 6, 4) >,
    Group< a,b | [ a^7, b^5, (a * b * a)^2, (b^-1 * a^-1 * b^-1)^3, (a * b^-1 * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2,xm2 + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7)(3, 6, 5, 4) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^2, (a * b^-1 * a)^4, (a * b^-1)^6, a * b * a^-1 * b * a^-1 * b^-2 * a^-2* b^2 * a * b^-1 * a^-1 * b * a * b^-1 * a ] >,
    ideal< R | [5,xcom + 2,x12 + zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 4*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 4, 5)(3, 6) >,
    Group< a,b | [ a^7, b^4, (a * b * a^2)^2, (a^-1 * b * a^-1 * b^-1)^2, (a^-1 * b^-1)^6, b * a^-1 * b^-2 * a^-1 *b^-1 * a^-2 * b^2 * a * b^2 * a * b * a ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7)(3, 6, 4, 5) >,
    Group< a,b | [ a^7, b^4, (a * b * a)^2, (a * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 *b^2 * a^-1 * b^-1, b * a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^2 * a * b^-1 * a^-1 * b^2 * a ] >,
    ideal< R | [5,xcom,x12 + 3*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4,xm2 + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (2, 7, 3, 6)(4, 5) >,
    Group< a,b | [ a^7, b^4, (a * b^-1 * a^2)^2, (a * b^-1)^4, b^-1 * a^-1 * b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a^-1* b^2 * a^-1 * b^-1, (a^-1 * b^-1 * a^-1 * b)^3, b * a * b^-2 * a^-1 * b^-1 * a^-2 * b^2 * a * b^2 * a * b * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 1,xm2 + 4*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 4)(5, 6, 7) >,
    Group< a,b | [ a^7, b^6, (b^-1 * a)^3, b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b, (a^-2 * b^-1)^3, (b^-1 *a^-1)^5 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 4)(5, 7, 6) >,
    Group< a,b | [ a^7, b^6, (b^-1 * a^-1)^3, b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1, (a^-2 * b)^3, (b^-1 *a)^5 ] >,
    ideal< R | [5,xcom,x12,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 4, 6)(5, 7) >,
    Group< a,b | [ a^7, b^6, (b^-1 * a^-1)^3, b * a * b^-1 * a^-2 * b^2 * a^-2, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + zeta + 1,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 4, 7)(5, 6) >,
    Group< a,b | [ a^7, b^6, (a * b^-1)^2, (b^-1 * a^-1 * b^-1)^3, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 3,xm12 + zeta,xm21 + 4*zeta + 4,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 5)(4, 6, 7) >,
    Group< a,b | [ a^7, b^6, (b^-1 * a^-1)^3, b^-1 * a * b * a^-2 * b^2 * a^-2, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 5, 7)(4, 6) >,
    Group< a,b | [ a^7, b^6, (a * b^-1 * a)^2, (a^-1 * b^-1)^4, a^-1 * b * a^-1 * b^-1 * a * b^-1 * a * b^-1,b^2 * a^-2 * b^-1 * a^-2 * b^3 * a^-1 * b^3 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 4,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 5)(4, 7, 6) >,
    Group< a,b | [ a^7, b^6, (b^-1 * a)^3, b * a * b^-1 * a^-2 * b^-2 * a^-2, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 5, 6)(4, 7) >,
    Group< a,b | [ a^7, b^6, (a^-1 * b^-1)^4, a^-1 * b^-1 * a^-3 * b * a^-1 * b^2, (b^-1 * a)^5 ] >,
    ideal< R |[5,xcom + 4*zeta,x12 + 4*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 6, 4)(5, 7) >,
    Group< a,b | [ a^7, b^6, (b^-1 * a)^3, a^-1 * b^-2 * a^-2 * b^-1 * a * b * a^-1, (b^-1 * a^-1)^5 ] >,
    ideal<R | [5,xcom + 4*zeta,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 6)(4, 5, 7) >,
    Group< a,b | [ a^7, b^6, (a^-1 * b^-1)^4, a^-1 * b * a^-3 * b^-1 * a^-1 * b^2, (b^-1 * a)^5 ] >,
    ideal< R |[5,xcom + zeta + 1,x12 + 4*zeta,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 6, 5)(4, 7) >,
    Group< a,b | [ a^7, b^6, (a * b^-1)^4, a^-1 * b * a^-3 * b^-1 * a^-1 * b^-2, (b^-1 * a^-1)^5 ] >,
    ideal< R |[5,xcom + zeta + 1,x12 + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 6)(4, 7, 5) >,
    Group< a,b | [ a^7, b^6, (a * b^-1)^4, a^-1 * b^-1 * a^-3 * b * a^-1 * b^-2, (b^-1 * a^-1)^5 ] >,
    ideal< R |[5,xcom + 4*zeta,x12 + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 7, 4)(5, 6) >,
    Group< a,b | [ a^7, b^6, (a^-1 * b^-1)^2, (b * a^-1 * b)^3, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + zeta,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 7)(4, 5, 6) >,
    Group< a,b | [ a^7, b^6, (a * b^-1)^2, (a^-1 * b^-1)^4, b^-1 * a * b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b *a * b^-1, a * b^-3 * a * b * a^-3 * b^3 * a^3 * b^2 ] >,
    ideal< R | [5,xcom,x12 + zeta + 1,xm12 + 4*zeta + 4,xm21 + zeta,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 7, 5)(4, 6) >,
    Group< a,b | [ a^7, b^6, (a * b * a)^2, a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1, (a * b^-1)^4, b^-2 *a^-2 * b * a^-2 * b^3 * a^-1 * b^3 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 4*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2)(3, 7)(4, 6, 5) >,
    Group< a,b | [ a^7, b^6, (a^-1 * b^-1)^2, (a * b^-1)^4, (a * b^-1 * a)^4, b * a * b^-1 * a^-1 * b * a^2 * b* a^-1 * b^-1 * a * b, a * b^-3 * a * b^-1 * a^-3 * b^3 * a^3 * b^-2 ] >,
    ideal< R | [5,xcom,x12 + 1,xm12 + 4,xm21 + 4,xm2m1 + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3)(4, 6)(5, 7) >,
    Group< a,b | [ a^7, b^6, (a * b * a)^2, (a^-1, b^-1)^2, (b^-1 * a)^5, (b^-1 * a^2 * b^-1)^3 ] >,
    ideal< R |[5,xcom + 1,x12 + 2*zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 4, 5, 7, 6) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, (b^-1 * a)^3, (a * b^-2 * a)^2 ] >,
    ideal< R | [5,xcom,x12,xm12,xm21,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 4, 6, 7, 5) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, a^-1 * b^-1 * a * b * a^3 * b^3 * a * b, b^-1 * a * b^2 * a^3 * b^-1* a^-2 * b^-2, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 3,xm12,xm21,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 4, 7, 6, 5) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^2, (b^-1 * a^-1)^5, b * a^-1 * b^-2 * a^3 * b^-3 * a^2 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 1,xm21 + 1,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 4, 7, 5, 6) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, b^-1 * a^-2 * b^-1 * a^3 * b^2 * a * b^-2, a * b^3 * a^3 * b * a *b^-1 * a^-1 * b, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta + 3,xm12,xm21,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 5, 6, 7, 4) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, (a^-2 * b)^3, b * a^-2 * b^-1 * a^3 * b^-1 * a^-2 * b * a, (a * b^3 *a^2)^2 ] >,
    ideal< R | [5,xcom + 2,x12 + 3,xm12,xm21,xm2m1 + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 5, 7, 6, 4) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, a * b^-1 * a^-1 * b * a^2 * b^-1 * a^-1 * b^-2,(b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 5, 7, 4, 6) >,
    Group< a,b | [ a^7, b^7, (a * b^-3)^2, (a^-2 * b)^3, (b^-1 * a)^5, a * b * a * b^-1 * a^-2 * b^2 * a^-2 *b^-1 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12 + 2,xm21 + 2,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 5, 4, 7, 6) >,
    Group< a,b | [ a^7, b^7, (a * b^-2 * a)^2, (a * b * a * b * a)^2, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b *a * b * a, (b^-1 * a)^5, (a^3 * b^-1)^3 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 2,xm21 + 2,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 6, 5, 7, 4) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a^-2 * b)^3, b^-2 * a * b * a^2 * b^-1 * a * b * a^-1, (b^-1 *a)^5 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 4*zeta,xm12 + 2,xm21 + 2,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 6, 7, 4, 5) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b, a * b^-1 * a^-1 * b^-1 * a^3* b^-3 * a * b, (a^3 * b)^3 ] >,
    ideal< R | [5,xcom,x12 + 4*zeta + 2,xm12,xm21,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 6, 4, 7, 5) >,
    Group< a,b | [ a^7, b^7, (a * b^-1 * a^2)^2, (b * a^-1 * b)^3, (b^-1 * a)^5, b^-1 * a * b^2 * a^-2 * b^2 * a* b^-1 * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 7, 6, 5, 4) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^2, (b^-1 * a)^5, a * b^3 * a^3 * b^2 * a^-1 * b^-1 * a ] >,
    ideal< R| [5,xcom,x12 + 1,xm12 + 2,xm21 + 2,xm2m1 + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 7, 5, 6, 4) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^2, b * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b, (a^-1 * b^-1)^6 ] >,
    ideal<R | [5,xcom + 1,x12 + 3*zeta,xm12 + 1,xm21 + 1,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 7, 4, 6, 5) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a^-2 * b)^3, a^-1 * b * a * b^-1 * a^2 * b * a * b^-2, (b^-1 *a)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 4*zeta,xm12 + 2,xm21 + 2,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 7, 5, 4, 6) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, b^-2 * a^-1 * b^-1 * a^2 * b * a^-1 * b^-1 * a,(b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 5, 7, 6, 3) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, b^-2 * a^-1 * b * a^2 * b^-2 * a^-1 * b^-1 ] >,ideal< R | [5,xcom + 2*zeta + 3,x12 + 4*zeta,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 6, 7, 5, 3) >,
    Group< a,b | [ a^7, b^7, (a * b * a)^2, (a * b^-3)^2, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 2,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 7, 6, 5, 3) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, b^2 * a^-1 * b * a^2 * b^-1 * a^-1 * b * a,(b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 2*zeta,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 7, 5, 6, 3) >,
    Group< a,b | [ a^7, b^7, a * b^-2 * a^3 * b * a * b * a, b^-1 * a^-1 * b^-2 * a^2 * b^-3 * a^-1, b^-1 * a *b^2 * a^2 * b * a^-1 * b * a, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 3*zeta + 2,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 3, 5, 7, 6) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, (a^-2 * b)^3, (a * b * a * b * a)^2, b^-1 * a^-1 * b^-1 * a^-1 * b^-1* a * b * a * b * a ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 6, 7, 3, 5) >,
    Group< a,b | [ a^7, b^7, (a * b^-1 * a)^2, (a * b^2 * a^2)^2, b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-1 * a *b^-1 * a ] >,
    ideal< R | [5,xcom + 2,x12 + 3*zeta,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 7, 6, 3, 5) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-2 * b^-1 * a^3 * b^2 * a * b^-1, (a * b^-1 * a^-1* b * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 7, 3, 5, 6) >,
    Group< a,b | [ a^7, b^7, (a * b^-1 * a)^2, (b^-1 * a^-1 * b^-1)^3, b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-1* a * b^-1 * a, b * a^-1 * b^2 * a^3 * b^2 * a^-1 * b * a ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 4,xm12 + 2,xm21 + 2,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4)(3, 6)(5, 7) >,
    Group< a,b | [ a^7, b^6, (a * b^-1)^4, (a^-2 * b^-1)^3, a * b^-1 * a * b * a^2 * b^-1 * a^-1 * b^2 ] >,ideal< R | [5,xcom + zeta + 3,x12 + 3*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 3, 6, 7, 5) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, b^-1 * a^-1 * b * a^3 * b * a^2 * b^-1 ]>,
    ideal< R | [5,xcom + 2*zeta + 3,x12 + zeta + 1,xm12 + 2*zeta,xm21 + 3*zeta + 3,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 7, 3, 6, 5) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b^-3 * a^2 * b^-1 * a^-1 * b^2, (a * b^2 *a^-1 * b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 7, 5, 3, 6) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, (a * b^-2 * a^2)^2, (a * b * a * b * a)^2, (a^-1 * b^2 * a^-1 *b^-1)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 1,xm12,xm21,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 5, 3, 7, 6) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3, b^-1 * a^-1 * b^-2 * a^2 * b * a^-1 * b^-2 ] >,ideal< R | [5,xcom + 3*zeta + 1,x12 + 4,xm12 + 2,xm21 + 2,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 4, 6, 3, 7, 5) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, a^-1 * b^-1 * a^-1 * b * a^-2 * b^-1 * a * b * a * b, b^-1 * a^-2 * b* a^3 * b^2 * a^-1 * b^-2, b * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b^2 * a^2 * b ] >,
    ideal< R | [5,xcom + zeta + 3,x12 + 3,xm12,xm21,xm2m1 + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 7, 6, 4, 3) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (a^-2 * b)^3, b * a^-1 * b^2 * a^2 * b^-1 * a^-1 * b^2 ] >,
    ideal< R| [5,xcom + 2*zeta + 3,x12 + 2,xm12 + 4,xm21 + 4,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 4, 6, 7, 3) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a^2 * b * a^3 * b * a^-1 * b^-2 ] >,ideal< R | [5,xcom + 3*zeta + 1,x12 + 4,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 7, 4, 6, 3) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, (a * b * a * b^-1 * a)^2, (a^3 * b^-1)^3, (a* b^-1 * a^-1 * b * a^2)^2, a^-2 * b^2 * a^3 * b^3 * a * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 2*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 4, 7, 6, 3) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, (a * b * a * b^-1 * a)^2, (b^-1 * a^-1)^5, b^-1 * a^-1 * b^-2 * a^3 *b * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12 + 2,xm12,xm21,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 6, 4, 7, 3) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-2)^2, (a * b^-1 * a^2)^2, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 7, 6, 3, 4) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, (a * b * a * b^-1 * a)^2, (b^-1 * a)^5, b * a^2 * b^-1 * a^3 * b^2* a^-1 * b^2 ] >,
    ideal< R | [5,xcom + 2*zeta + 2,x12,xm12 + 2,xm21 + 2,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 3, 6, 7, 4) >,
    Group< a,b | [ a^7, b^7, (a * b^-2)^2, (a^-2 * b^-1)^3, b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b* a^-1, (a * b^-1 * a^-1 * b^-1 * a^2)^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 7, 4, 3, 6) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, a * b^2 * a^3 * b^-1 * a^-2 * b^-1, (a * b * a^-1 *b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5)(3, 6)(4, 7) >,
    Group< a,b | [ a^7, b^6, (b^-1 * a)^3, a * b^-3 * a^-2 * b^3 * a * b, b^-1 * a^-1 * b^-1 * a^-3 * b^2 * a^-3] >,
    ideal< R | [5,xcom,x12 + zeta + 3,xm12,xm21,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 4, 7, 3, 6) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, b^2 * a^-1 * b^-1 * a^2 * b^-3 * a^-1, (a^-1 * b^2 *a * b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 3, 7, 6, 4) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, a * b^-2 * a^3 * b * a^-2 * b, (a * b^-1 * a^-1 * b* a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + zeta + 1,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 6, 3, 7, 4) >,
    Group< a,b | [ a^7, b^7, (a * b^-2)^2, (a * b^3 * a)^2, b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b* a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 3,xm12 + 2,xm21 + 2,xm2m1 + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5)(3, 7)(4, 6) >,
    Group< a,b | [ a^7, b^6, (a * b^-1 * a^2)^2, (a^-1 * b * a^-1 * b^-1)^2, (a * b^-1)^4, (b^-1 * a^-1 *b^-1)^3, a^-1 * b^-1 * a^-1 * b^-3 * a^-2 * b^3 * a^2 * b^-2 ] >,
    ideal< R | [5,xcom + 3,x12 + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 5, 3, 7, 4, 6) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, a * b * a * b^-1 * a^-2 * b * a^-1 * b^-1 * a^-1 * b, b^-1 * a^-1 *b^2 * a^3 * b * a^-2 * b^-2, a^-1 * b^2 * a^-1 * b^-1 * a^2 * b^-1 * a^-1 * b * a * b^-1 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12 + 3*zeta,xm12,xm21,xm2m1 + 2*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 7, 5, 4, 3) >,
    Group< a,b | [ a^7, b^7, (a * b^2 * a)^2, (a * b^-1 * a * b^-1 * a)^2, (b^-1 * a^-1)^5, b * a^-1 * b * a^-1* b^-1 * a * b^-1 * a * b^-1 * a^-1, (a * b^-1 * a^-1 * b^-1 * a^2)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 5, 7, 4, 3) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (b * a^-1 * b)^3, a^2 * b^-1 * a^3 * b^-1 * a^-1 * b^2 ] >,
    ideal< R| [5,xcom + 2*zeta + 3,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 7, 4, 5, 3) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^2, (b * a^2 * b)^3, b * a * b * a * b * a^3 * b * a * b * a * b^2 ] >,ideal< R | [5,xcom + 3,x12 + 4*zeta + 2,xm12 + zeta,xm21 + 4*zeta + 4,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 4, 7, 5, 3) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (a^-2 * b^-1)^3, (a * b^-2 * a^-1 * b^-1)^2, b^-2 * a^-1 * b * a^3 *b^3 * a^2, a * b * a^2 * b^-1 * a^2 * b^-1 * a * b^-1 * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta + 2,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 5, 4, 7, 3) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (a^-2 * b^-1)^3, b^2 * a * b^-1 * a^2 * b * a * b^-1 * a^-1, (b^-1 *a^-1)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 5, 7, 3, 4) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, (a * b^-1 * a * b * a)^2, (b^-1 * a)^5, b * a^-1 * b^2 * a^3 *b^-1 * a^2 * b^2 ] >,
    ideal< R | [5,xcom + 3*zeta,x12,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 3, 5, 7, 4) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, (a * b^-1 * a^-1 * b^-1 * a)^2, (a * b^-3 * a)^2, (a^-1 * b^-2 * a^-1* b^-1)^2 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12,xm21,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6)(3, 5)(4, 7) >,
    Group< a,b | [ a^7, b^6, (a * b^-1)^4, (a^-2 * b^-1)^3, b^2 * a^-1 * b^-1 * a^2 * b * a * b^-1 * a ] >,ideal< R | [5,xcom + 4*zeta + 2,x12 + 3*zeta + 2,xm12 + 4,xm21 + 4,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 5, 3, 7, 4) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, b^-2 * a^-1 * b * a^2 * b^3 * a^-1, (a^-1 * b^2 * a* b^-1)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 3, 7, 5, 4) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-1 * b^3 * a^2 * b * a^-1 * b^-2, (a * b^2 * a^-1* b^-1)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 4,xm21 + 4,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 6, 4, 3, 7, 5) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a * b^-1)^4, a^-2 * b * a^3 * b^-2 * a * b, (a * b * a^-1 * b^-1* a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4,xm12 + 4,xm21 + 4,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 6, 5, 4, 3) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, (b^-1 * a)^3, (a * b^2 * a)^2 ] >,
    ideal< R | [5,xcom,x12,xm12,xm21,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 5, 6, 4, 3) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, (a^-2 * b^-1)^3, (a * b^-1 * a * b^-1 * a)^2, b * a^-1 * b * a^-1* b^-1 * a * b^-1 * a * b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12,xm12 + 3*zeta + 3,xm21 + 2*zeta,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 6, 3, 5, 4) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (b * a^-1 * b)^3, b * a^-1 * b^-1 * a^3 * b^-1 * a^2 * b ] >,
    ideal<R | [5,xcom + 3*zeta + 1,x12 + 2*zeta,xm12 + 4,xm21 + 4,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 3, 5, 6, 4) >,
    Group< a,b | [ a^7, b^7, b * a * b * a^3 * b^-2 * a^2, a^-1 * b^-3 * a^2 * b^-2 * a^-1 * b^-1, a * b * a^-1* b * a^2 * b^2 * a * b^-1, (b^-1 * a)^5 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 3*zeta + 1,xm12 + 2,xm21 + 2,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 6, 4, 3, 5) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (a^-2 * b)^3, b^2 * a^-1 * b^-1 * a^2 * b^2 * a^-1 * b ] >,
    ideal< R| [5,xcom + 3*zeta + 1,x12 + 3*zeta + 3,xm12 + zeta + 1,xm21 + 4*zeta,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 4, 6, 3, 5) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, (a * b^-1 * a * b * a)^2, (a * b * a^-1 *b^-1 * a^2)^2, (a^3 * b^-1)^3 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 2*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 5, 3, 6, 4) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (a^-2 * b^-1)^3, (a^-1 * b^-2 * a * b^-1)^2, a * b^3 * a^3 * b * a^-1* b^-2 * a, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^2 * b^-1 * a * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 3*zeta + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 3, 6, 5, 4) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (a^-2 * b^-1)^3, a^-1 * b^-1 * a * b * a^2 * b^-1 * a * b^2, (b^-1 *a^-1)^5 ] >,
    ideal< R | [5,xcom + zeta + 1,x12 + 3*zeta + 3,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 4, 3, 6, 5) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, (a * b^-1 * a * b * a)^2, (b^-1 * a^-1)^5, b^-1 * a^2 * b * a^3 *b^-2 * a^-1 * b^-2, a * b^2 * a^-1 * b^-1 * a^2 * b^2 * a * b * a ] >,
    ideal< R | [5,xcom + 3*zeta,x12 + 2*zeta,xm12,xm21,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 2, 7, 5, 4, 3, 6) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^4, (b^-1 * a^-1 * b^-1)^3, a * b * a^-1 * b^-1 * a^2 * b * a^-1 * b^2,(b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 4*zeta,x12 + 2,xm12 + 4*zeta,xm21 + zeta + 1,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 2)(4, 6)(5, 7) >,
    Group< a,b | [ a^7, b^6, (a * b^-1 * a)^2, (a^-1, b^-1)^2, (b^-1 * a^-1)^5, (b * a^2 * b)^3 ] >,
    ideal< R |[5,xcom + 1,x12 + 2*zeta,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 5, 7, 6, 4, 2) >,
    Group< a,b | [ a^7, b^7, (a * b^-1 * a)^2, (a^-1 * b^-3)^2, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 5, 7, 4, 6, 2) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a^-2 * b)^3, (a * b^-2 * a^-1 * b^-1)^2, b^2 * a^-1 * b^-1 * a^3* b^-3 * a^2, a^-2 * b * a^-1 * b^-1 * a^2 * b * a * b * a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4*zeta,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 5, 4, 7, 6, 2) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^2, (b^-1 * a^2 * b^-1)^3, b^-1 * a * b^-1 * a * b^-1 * a^3 * b^-1 * a* b^-1 * a * b^-2 ] >,
    ideal< R | [5,xcom + 3,x12 + zeta,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 4*zeta + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 6, 5, 7, 4, 2) >,
    Group< a,b | [ a^7, b^7, a * b^2 * a^3 * b^-1 * a * b^-1 * a, b * a * b^-2 * a^2 * b^-1 * a^-1 * b^-1 * a, b* a^-1 * b^2 * a^2 * b^3 * a^-1, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 2*zeta + 4,x12 + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 6, 4, 7, 5, 2) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, (a * b^-1 * a * b * a)^2, (a * b * a^-1 * b^-1 *a^2)^2, a^-2 * b^-2 * a^3 * b^-3 * a * b, (a^3 * b)^3 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + 4*zeta,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 6, 5, 4, 7, 2) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^2, b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1, (a * b^-1)^6 ] >,
    ideal<R | [5,xcom + 1,x12 + 4*zeta + 4,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 7, 6, 5, 4, 2) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, a * b^-3 * a^3 * b^-1 * a * b * a^-1 * b^-1, b * a^-2 * b * a^3 *b^-2 * a * b^2, (a * b^-1 * a)^4, (a * b^-2 * a * b^-1 * a)^2 ] >,
    ideal< R | [5,xcom + 2*zeta,x12,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 7, 4, 6, 5, 2) >,
    Group< a,b | [ a^7, b^7, (a * b^-2)^2, (a * b * a^2)^2, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 3,x12 + 3*zeta + 3,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3)(2, 4, 6)(5, 7) >,
    Group< a,b | [ a^7, b^6, (a^-2 * b)^3, (a * b * a * b * a)^2, b^-1 * a^2 * b^-2 * a^-1 * b^3 * a^-1 * b^-1,a^-2 * b^-1 * a^-3 * b^-1 * a^-2 * b^2 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 5, 7, 6, 2, 4) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (a^-2 * b)^3, (a^-1 * b^-2 * a * b^-1)^2, a * b^-3 * a^3 * b^-1 *a^-1 * b^2 * a, b * a^-1 * b * a^-1 * b * a^2 * b * a * b^-1 * a^-1 * b ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12 + zeta + 1,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 6, 2, 4, 7, 5) >,
    Group< a,b | [ a^7, b^7, (a^-2 * b^-1)^3, (b^-1 * a^-1 * b^-1)^3, b^-1 * a^-1 * b^-1 * a^-3 * b^2 * a^-3, a* b^3 * a^-2 * b^3 * a * b, (a^3 * b^-1)^3 ] >,
    ideal< R | [5,xcom,x12 + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 7, 6, 5, 2, 4) >,
    Group< a,b | [ a^7, b^7, (a * b * a^2)^2, (b^-1 * a^-1 * b^-1)^3, (b^-1 * a^-1)^5, b * a * b^-2 * a^-2 *b^-2 * a * b * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 7, 5, 2, 4, 6) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-3)^2, (a^-2 * b^-1)^3, (a^-2 * b)^3, b * a^-1 * b^-1 * a^3 * b^-1 * a^-1* b * a^-1 ] >,
    ideal< R | [5,xcom,x12 + 2*zeta + 3,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 3*zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3)(2, 5)(4, 7, 6) >,
    Group< a,b | [ a^7, b^6, (a^-1 * b^-1)^4, (a^-2 * b)^3, b^-2 * a^-1 * b * a^2 * b^-1 * a * b * a ] >,
    ideal<R | [5,xcom + zeta + 3,x12 + 4*zeta,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + zeta + 1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 2, 5, 7, 6, 4) >,
    Group< a,b | [ a^7, b^7, b^-1 * a * b^-1 * a^3 * b^2 * a^2, a * b^-1 * a^-1 * b^-1 * a^2 * b^-2 * a * b,a^-1 * b^3 * a^2 * b^2 * a^-1 * b, (b^-1 * a^-1)^5 ] >,
    ideal< R | [5,xcom + 3*zeta + 2,x12 + 2,xm12 + 2*zeta + 3,xm21 + 3*zeta + 1,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 6, 2, 5, 7, 4) >,
    Group< a,b | [ a^7, b^7, (a * b^-1 * a^2)^2, (b^-1 * a^-1 * b^-1)^3, (b * a^-1 * b)^3, (a * b^-3 * a)^2 ] >,ideal< R | [5,xcom,x12 + 3*zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 6)(2, 5)(4, 7) >,
    Group< a,b | [ a^7, b^6, (a * b^-1 * a^2)^2, (a * b * a^-1 * b * a)^2, b^-1 * a^-2 * b^-2 * a * b^3 * a *b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 2,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 7, 6, 2, 5, 4) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-2)^2, (a^-2 * b)^3, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b* a^-1, (a * b * a^-1 * b * a^2)^2 ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + 4*zeta + 2,xm21 + zeta + 3,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 7, 6, 4, 2, 5) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, a * b^-1 * a * b * a^-2 * b^-1 * a^-1 * b * a^-1 * b^-1, b * a^-1* b^-2 * a^3 * b^-1 * a^-2 * b^2, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + zeta + 3,x12,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3)(2, 6, 4)(5, 7) >,
    Group< a,b | [ a^7, b^6, (a^-2 * b^-1)^3, (a * b^-1 * a * b^-1 * a)^2, b^-1 * a^-2 * b^-2 * a * b^3 * a *b^-1, b * a^-1 * b^-1 * a^-3 * b^-1 * a^-1 * b * a^2, a^-2 * b * a^-3 * b * a^-2 * b^-2 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3)(2, 6, 5)(4, 7) >,
    Group< a,b | [ a^7, b^6, (a * b * a^2)^2, (a^-1 * b^-1)^4, (a^-1 * b * a^-1 * b^-1)^2, (b * a^-1 * b)^3,a^-1 * b * a^-1 * b^-3 * a^-2 * b^3 * a^2 * b^2 ] >,
    ideal< R | [5,xcom + 3,x12 + 4,xm12 + 2*zeta + 2,xm21 + 3*zeta,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 2,xm2 + 3*zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3)(2, 6)(4, 7, 5) >,
    Group< a,b | [ a^7, b^6, (a^-1 * b^-1)^4, (a^-2 * b)^3, a * b * a * b^-1 * a^2 * b * a^-1 * b^-2 ] >,
    ideal<R | [5,xcom + 4*zeta + 2,x12 + zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 4*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 2, 6, 4, 7, 5) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^4, (b * a^-1 * b)^3, (a * b * a * b^-1 * a)^2, a * b^-3 * a^3 * b^-2* a^-2 * b, (a * b^-1 * a^-1 * b * a^2)^2, (a^3 * b)^3 ] >,
    ideal< R | [5,xcom + 2*zeta,x12 + 4,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 4,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 7, 5, 2, 6, 4) >,
    Group< a,b | [ a^7, b^7, (a^-2 * b)^3, (b * a^-1 * b)^3, a^-1 * b^-2 * a^-3 * b * a^-1 * b * a^-2, a * b^-3* a^-2 * b^-3 * a * b^-1, (a^3 * b)^3 ] >,
    ideal< R | [5,xcom,x12 + zeta + 3,xm12 + 3,xm21 + 3,xm2m1 + 4*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 7, 5, 4, 2, 6) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, (a * b^2 * a^2)^2, (a * b^-1 * a * b^-1 * a)^2, (a * b^2 * a *b^-1)^2, a^-1 * b * a^-1 * b^-1 * a^-2 * b^2 * a^-2 * b^-1 ] >,
    ideal< R | [5,xcom,x12,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 2, 7, 6, 5, 4) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, a^-1 * b * a * b^-1 * a^3 * b^-3 * a * b^-1, b * a * b^-2 * a^3 *b * a^-2 * b^2, (a * b^-1 * a)^4, (a * b^-1 * a * b^-2 * a)^2 ] >,
    ideal< R | [5,xcom + 3*zeta + 3,x12,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 6, 2, 7, 5, 4) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, a^-1 * b * a^-1 * b^-1 * a^-2 * b * a * b^-1 * a * b^-1, b * a^-2* b^-1 * a^3 * b^-2 * a^-1 * b^2, (a * b^-1 * a)^4 ] >,
    ideal< R | [5,xcom + 4*zeta + 2,x12,xm12 + 3,xm21 + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 4*zeta + 2,xm2 + zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 3, 6, 4, 2, 7, 5) >,
    Group< a,b | [ a^7, b^7, (a * b^-3)^2, (a^-2 * b^-1)^3, (a^-2 * b)^3, (a * b^-2 * a^2)^2 ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 1,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 4, 7, 6, 5, 3, 2) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, (a^-2 * b^-1)^3, (a * b^-3 * a^2)^2, b^-1 * a^-2 * b * a^3 * b *a^-2 * b^-1 * a ] >,
    ideal< R | [5,xcom + 2,x12,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + zeta + 3,xm2 + 4*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 4, 7, 3, 6, 5, 2) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-2)^2, (a * b^-3 * a)^2, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a* b * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 4, 7, 5, 3, 6, 2) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, (a * b^3 * a)^2, (a * b * a^-1 * b * a)^2, (a * b^-2 * a * b^-1)^2] >,
    ideal< R | [5,xcom,x12,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 3,xm2 + 3*zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 4, 3, 7, 6, 5, 2) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, b^-1 * a^-1 * b * a^2 * b * a^-1 * b^-1, (a^3 * b^-1)^3 ] >,ideal< R | [5,xcom,x12,xm12 + 2*zeta + 4,xm21 + 3*zeta + 2,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 2,xm2 + 2*zeta + 4,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 4)(2, 5)(3, 7, 6) >,
    Group< a,b | [ a^7, b^6, (b^-1 * a^-1)^3, a * b^-3 * a^-2 * b^3 * a * b^-1, a^-1 * b^-2 * a^-3 * b * a^-1 *b * a^-2 ] >,
    ideal< R | [5,xcom,x12,xm12 + 3*zeta + 2,xm21 + 2*zeta + 4,xm2m1,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta,xm2 + 2*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 4, 7, 5, 2, 6, 3) >,
    Group< a,b | [ a^7, b^7, (a * b * a^2)^2, (b^-1 * a^-1 * b^-1)^3, (b * a^-1 * b)^3, (a * b^3 * a)^2 ] >,ideal< R | [5,xcom,x12 + 3*zeta + 1,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 4)(2, 6)(3, 7, 5) >,
    Group< a,b | [ a^7, b^6, (a * b * a^2)^2, (a * b^-1 * a^-1 * b^-1 * a)^2, b^-1 * a^2 * b^-2 * a^-1 * b^3 *a^-1 * b^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta + 4,xm12 + 3*zeta,xm21 + 2*zeta + 2,xm2m1 + 3*zeta + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3,xm2 + 3,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 4, 2, 7, 6, 5, 3) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-3)^2, (a^-2 * b^-1)^3, (b^-1 * a^-1)^5, a^-2 * b^-2 * a^-2 * b * a *b^-1 * a * b ] >,
    ideal< R | [5,xcom,x12 + 2,xm12 + zeta + 3,xm21 + 4*zeta + 2,xm2m1 + 2,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 5, 3, 7, 6, 4, 2) >,
    Group< a,b | [ a^7, b^7, (a * b * a)^2, (a * b^-2 * a^2)^2, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a *b^-1 * a^-1 ] >,
    ideal< R | [5,xcom + 2,x12 + 2*zeta,xm12 + 3,xm21 + 3,xm2m1 + 3*zeta + 3,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 2*zeta + 4,xm2 + 3*zeta + 2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 7 | (1, 2, 3, 4, 5, 6, 7), (1, 5, 2, 7, 6, 4, 3) >,
    Group< a,b | [ a^7, b^7, (a * b * a)^2, (b * a^-1 * b)^3, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a *b^-1 * a^-1, b^-1 * a^-1 * b^-2 * a^3 * b^-2 * a^-1 * b^-1 * a ] >,
    ideal< R | [5,xcom,x12 + 3*zeta + 3,xm12 + 3*zeta + 1,xm21 + 2*zeta + 3,xm2m1 + 2*zeta,x1 + 2*zeta + 3,xm1 + 3*zeta + 1,x2 + 3*zeta + 1,xm2 + 2*zeta + 3,zeta^2 + zeta + 1] >
>
];

