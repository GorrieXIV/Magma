freeze;

import "../l3.m": R, x1, xm1, x2, xm2, x12, xm12, xm21, xm2m1, xcom, zeta;

l27presentations := [
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 2, 3)(5, 6, 7) >,
    Group< a,b | [ a^3, b^3, (a * b^-1)^4, (a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [xcom,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12 - 1,xm21 - 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 2, 3, 5)(4, 8, 7, 6) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a^-1)^3, a * b^-2 * a * b^-1 * a * b^2 * a * b^-1 ] >,
    ideal< R | [xcom,xm21^2 + xm21 + 2,x12,xm12 + xm21 + 1,xm2m1,x1,xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 2, 3, 6, 8, 4, 7) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a)^3, (a^-1 * b^-1)^4, (a^-1 * b^-3)^2 ] >,
    ideal< R | [xcom,xm2^2 + xm2 + 2,x12 - 1,xm12,xm21,xm2m1 - 1,x1,xm1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 2)(5, 7, 6) >,
    Group< a,b | [ a^3, b^3, (a^-1 * b^-1)^4, a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a * b ] >,ideal< R | [xcom,xm21^2 + xm21 + 2,x12 - 1,xm12 + xm21 + 1,xm2m1 - 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 6, 4, 8, 5, 2) >,
    Group< a,b | [ a^3, b^7, (b^-1 * a^-1)^3, (a * b^-1)^4, (a * b^-3)^2 ] >,
    ideal< R | [xcom,xm2^2 + xm2 + 2,x12,xm12 - 1,xm21 - 1,xm2m1,x1,xm1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 7, 2)(4, 5, 6, 8) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a)^3, a^-1 * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R |[xcom,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12,xm21,x1,xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3)(2, 5)(4, 7)(6, 8) >,
    Group< a,b | [ a^3, b^2, (b * a^-1)^7, (a * b * a^-1 * b)^4 ] >,
    ideal< R | [xcom - 1,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12 - xm2m1,xm21 + xm2m1 + 1,x1,xm1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 2, 5, 4, 8, 7) >,
    Group< a,b | [ a^3, b^7, (a * b^-1)^2, (a^-1 * b^-2)^4 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12 - xm2,xm12 + 1,xm21 + 1,xm2m1 + xm2 + 1,x1,xm1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 4, 6, 7, 2, 5) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-1)^2, (a * b^-2)^4 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12 + 1,xm12 - xm2,xm21 + xm2 + 1,xm2m1 + 1,x1,xm1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 2, 6)(4, 7, 5, 8) >,
    Group< a,b | [ a^3, b^4, b^-2 * a^-1 * b^2 * a^-1, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b* a * b * a^-1 * b^-1 * a^-1 ] >,
    ideal< R | [xcom - 1,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12 + xm2m1 + 1,xm21 - xm2m1,x1,xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 5, 2, 6, 7, 8) >,
    Group< a,b | [ a^3, b^7, (a^-1 * b^-2)^2, a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a * b ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12 - 1,xm12 + xm2 + 1,xm21 - xm2,xm2m1 - 1,x1,xm1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 8, 7, 2, 6, 4) >,
    Group< a,b | [ a^3, b^7, (a * b^-2)^2, (a * b^-1 * a^-1 * b^-1)^2 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12 + xm2 + 1,xm12 - 1,xm21 - 1,xm2m1 - xm2,x1,xm1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 4, 8)(2, 7, 5, 6) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a^-1)^3, (a * b^-1)^4 ] >,
    ideal< R | [xcom^2 + xcom + 2,x12,xm12 - 1,xm21 - 1,xm2m1,x1,xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 5, 4)(2, 7, 6, 8) >,
    Group< a,b | [ a^3, b^4, (b^-1 * a)^3, (a^-1 * b^-1)^4 ] >,
    ideal< R | [xcom^2 + xcom + 2,x12 - 1,xm12,xm21,xm2m1 - 1,x1,xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (3, 5, 7)(4, 6, 8), (1, 3, 6)(2, 7, 4) >,
    Group< a,b | [ a^3, b^3, (a^-1 * b^-1)^4, (a * b^-1)^4 ] >,
    ideal< R | [xcom^2 + xcom + 2,x12 - 1,xm12 - 1,xm21 - 1,xm2m1 - 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2)(3, 4)(5, 8)(6, 7) >,
    Group< a,b | [ a^7, b^2, (a^-1 * b)^4, (a^-2 * b)^3 ] >,
    ideal< R | [xcom - 1,xm1^2 + xm1 + 2,x12 - 1,xm12 - 1,xm21 - 1,xm2m1 - 1,x1 + xm1 + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2)(3, 6)(4, 5)(7, 8) >,
    Group< a,b | [ a^7, b^2, (b * a^-1)^3, (a * b * a^2)^4 ] >,
    ideal< R | [xcom - 1,xm1^2 + xm1 + 2,x12,xm12,xm21,xm2m1,x1 + xm1 + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2)(3, 8)(4, 7)(5, 6) >,
    Group< a,b | [ a^7, b^2, a^-1 * b * a * b * a^-2 * b * a * b * a^-1 * b ] >,
    ideal< R | [xcom,xm1^2 + xm1 + 2,x12 - xm1,xm12 + xm1 + 1,xm21 - xm1,xm2m1 + xm1 + 1,x1 + xm1 + 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 3)(5, 6, 7) >,
    Group< a,b | [ a^7, b^3, (a^-1 * b^-1)^2, (a * b^-1 * a)^4 ] >,
    ideal< R | [xcom - 1,xm1^2 + xm1 + 2,x12 + 1,xm12 + xm1 + 1,xm21 - xm1,xm2m1 + 1,x1 + xm1 + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 3, 5)(4, 8, 7, 6) >,
    Group< a,b | [ a^7, b^4, (a * b * a)^2, (b^-1 * a)^3 ] >,
    ideal< R | [xcom,xm1^2 + xm1 + 2,x12 + xm1 + 1,xm12,xm21,xm2m1 - xm1,x1 + xm1 + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 3, 6, 8, 4, 7) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a)^3, (a * b^-1 * a^2)^2, (a^-1 * b * a^-1 * b^-1)^2 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12 - xm2,xm12,xm21,xm2m1 + xm2 + 1,x1 + xm2 + 1,xm1 - xm2,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 4)(6, 7, 8) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a)^3, (a * b * a^2)^2, (a^-1 * b^-1)^4 ] >,
    ideal< R | [xcom,xm1^2 + xm1 + 2,x12 - 1,xm12,xm21,xm2m1 - 1,x1 + xm1 + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 4, 7, 3, 5, 8) >,
    Group< a,b | [ a^7, b^7, (a * b^-1 * a)^2, b * a^-1 * b^-1 * a * b^-1 * a^-1, (a^-1 * b^-1)^4 ] >,
    ideal< R| [xcom - 1,xm2^2 + xm2 + 2,x12 - 1,xm12,xm21,xm2m1 - 1,x1 - xm2,xm1 + xm2 + 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 4, 6)(3, 8, 7, 5) >,
    Group< a,b | [ a^7, b^4, (a * b^-1)^2, (b^-1 * a^-1)^3 ] >,
    ideal< R | [xcom - 1,xm1^2 + xm1 + 2,x12,xm12 + 1,xm21 + 1,xm2m1,x1 + xm1 + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 5, 8, 4, 6, 3) >,
    Group< a,b | [ a^7, b^7, (a^-1 * b^-1)^2, (a * b^-1)^4, (a^-2 * b)^3 ] >,
    ideal< R | [xcom,xm2^2 + xm2 + 2,x12 + 1,xm12 - 1,xm21 - 1,xm2m1 + 1,x1 + xm2 + 1,xm1 - xm2,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 5)(3, 7, 8) >,
    Group< a,b | [ a^7, b^3, (a * b * a)^2, a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 ] >,
    ideal< R | [xcom - 1,xm1^2 + xm1 + 2,x12 - 1,xm12 - xm1,xm21 + xm1 + 1,xm2m1 - 1,x1 + xm1 + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 5, 7)(3, 8, 6, 4) >,
    Group< a,b | [ a^7, b^4, a * b * a^-2 * b * a * b^-1, (a * b^-1 * a^2)^2 ] >,
    ideal< R | [xcom - 1,xm1^2 + xm1 + 2,x12 - 1,xm12 - xm1,xm21 + xm1 + 1,xm2m1 - 1,x1 + xm1 + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 6)(3, 4, 8) >,
    Group< a,b | [ a^7, b^3, (a * b^-1)^2, (a * b * a)^4 ] >,
    ideal< R | [xcom - 1,xm1^2 + xm1 + 2,x12 - xm1,xm12 + 1,xm21 + 1,xm2m1 + xm1 + 1,x1 + xm1 + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 6, 3, 5, 7, 4) >,
    Group< a,b | [ a^7, b^7, (b^-1 * a^-1)^3, (a * b * a^2)^2, (a^-1 * b * a^-1 * b^-1)^2 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12,xm12 - xm2,xm21 + xm2 + 1,xm2m1,x1 - xm2,xm1 + xm2 + 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 6, 8)(3, 7, 5, 4) >,
    Group< a,b | [ a^7, b^4, (a * b^-1 * a)^2, (b^-1 * a^-1)^3 ] >,
    ideal< R | [xcom,xm1^2 + xm1 + 2,x12,xm12 - xm1,xm21 + xm1 + 1,xm2m1,x1 + xm1 + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 7, 3)(4, 8, 6, 5) >,
    Group< a,b | [ a^7, b^4, (a^-1 * b^-1)^2, (b^-1 * a)^3 ] >,
    ideal< R | [xcom - 1,xm1^2 + xm1 + 2,x12 + 1,xm12,xm21,xm2m1 + 1,x1 + xm1 + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 7, 4, 6, 8, 5) >,
    Group< a,b | [ a^7, b^7, (a * b * a)^2, b^-1 * a^-1 * b^-1 * a * b * a, (a * b^-1)^4 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12,xm12 - 1,xm21 - 1,xm2m1,x1 + xm2 + 1,xm1 - xm2,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 7)(3, 4, 5) >,
    Group< a,b | [ a^7, b^3, (b^-1 * a^-1)^3, (a * b^-1 * a^2)^2, (a * b^-1)^4 ] >,
    ideal< R | [xcom,xm1^2 + xm1 + 2,x12,xm12 - 1,xm21 - 1,xm2m1,x1 + xm1 + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 8)(4, 5, 6) >,
    Group< a,b | [ a^7, b^3, (a * b^-1 * a)^2, a^-1 * b * a^-1 * b^-1 * a * b^-1 * a * b^-1 ] >,
    ideal< R | [xcom - 1,xm1^2 + xm1 + 2,x12 + xm1 + 1,xm12 - 1,xm21 - 1,xm2m1 - xm1,x1 + xm1 + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 8, 5, 7, 3, 6) >,
    Group< a,b | [ a^7, b^7, (a * b^-1)^2, (a^-1 * b^-1)^4, (a^-2 * b^-1)^3 ] >,
    ideal< R | [xcom,xm2^2 + xm2 + 2,x12 - 1,xm12 + 1,xm21 + 1,xm2m1 - 1,x1 - xm2,xm1 + xm2 + 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (2, 3, 5, 4, 7, 8, 6), (1, 2, 8, 4)(3, 7, 6, 5) >,
    Group< a,b | [ a^7, b^4, a * b^-1 * a^-2 * b^-1 * a * b, a^-1 * b^-1 * a^3 * b^-1 * a^-1 * b ] >,
    ideal<R | [xcom - 1,xm1^2 + xm1 + 2,x12 + xm1 + 1,xm12 - 1,xm21 - 1,xm2m1 - xm1,x1 + xm1 + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2)(3, 4)(5, 8)(6, 7), (2, 3, 5, 4, 7, 8, 6) >,
    Group< a,b | [ a^2, b^7, (b^-1 * a)^4, (b^-2 * a)^3 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12 - 1,xm12 - 1,xm21 - 1,xm2m1 - 1,x1 + 1,xm1 + 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2)(3, 4)(5, 8)(6, 7), (2, 3, 8)(4, 6, 7) >,
    Group< a,b | [ a^2, b^3, (a * b^-1)^7, (b * a * b^-1 * a)^4 ] >,
    ideal< R | [xcom - 1,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12 + xm2m1 + 1,xm21 - xm2m1,x1 + 1,xm1 + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2)(3, 4)(5, 8)(6, 7), (2, 4, 6, 5, 8, 3, 7) >,
    Group< a,b | [ a^2, b^7, b^-1 * a * b * a * b^-2 * a * b * a * b^-1 * a ] >,
    ideal< R | [xcom,xm2^2 + xm2 + 2,x12 - xm2,xm12 - xm2,xm21 + xm2 + 1,xm2m1 + xm2 + 1,x1 + 1,xm1 + 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2)(3, 4)(5, 8)(6, 7), (2, 5, 7, 6, 3, 4, 8) >,
    Group< a,b | [ a^2, b^7, (a * b^-1)^3, (b * a * b^2)^4 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12,xm12,xm21,xm2m1,x1 + 1,xm1 + 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2)(3, 4)(5, 8)(6, 7), (1, 2, 4, 6)(3, 8, 7, 5) >,
    Group< a,b | [ a^2, b^4, b^-2 * a * b^2 * a * b^2 * a, (a * b^-1)^7 ] >,
    ideal< R | [xcom - 1,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12 + xm2m1 + 1,xm21 - xm2m1,x1 + 1,xm1 + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (3, 5, 7)(4, 6, 8) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a^-1)^3, a * b^-1 * a^-2 * b^-1 * a * b^-1 * a^2 * b^-1 ] >,
    ideal< R | [xcom,xm21^2 + xm21 + 2,x12,xm12 + xm21 + 1,xm2m1,x1 - 1,xm1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (3, 7, 5)(4, 8, 6) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b^-1 ] >,
    ideal< R |[xcom,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12,xm21,x1 - 1,xm1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (2, 3, 4)(5, 8, 7) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a)^3, (a^-1 * b^-1)^4 ] >,
    ideal< R | [xcom^2 + xcom + 2,x12 - 1,xm12,xm21,xm2m1 - 1,x1 - 1,xm1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (2, 3, 5, 4, 7, 8, 6) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a)^3, (a^-1 * b^-2)^2 ] >,
    ideal< R | [xcom,xm2^2 + xm2 + 2,x12 + xm2 + 1,xm12,xm21,xm2m1 - xm2,x1 - 1,xm1 - 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (2, 4, 3)(5, 7, 8) >,
    Group< a,b | [ a^4, b^3, (b^-1 * a^-1)^3, (a * b^-1)^4 ] >,
    ideal< R | [xcom^2 + xcom + 2,x12,xm12 - 1,xm21 - 1,xm2m1,x1 - 1,xm1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (2, 4, 6, 5, 8, 3, 7) >,
    Group< a,b | [ a^4, b^7, b * a * b^-1 * a^-1 * b^-1 * a * b, b^2 * a^-1 * b^-1 * a * b^-1 * a^-1 * b ] >,ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12 + xm2 + 1,xm12 - 1,xm21 - 1,xm2m1 - xm2,x1 - 1,xm1 - 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (2, 5, 7, 6, 3, 4, 8) >,
    Group< a,b | [ a^4, b^7, (a^-1 * b^-1)^2, (b^-1 * a)^3 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12 + 1,xm12,xm21,xm2m1 + 1,x1 - 1,xm1 - 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (2, 6, 8, 7, 4, 5, 3) >,
    Group< a,b | [ a^4, b^7, (b^-1 * a^-1)^3, (a * b^-2)^2 ] >,
    ideal< R | [xcom,xm2^2 + xm2 + 2,x12,xm12 + xm2 + 1,xm21 - xm2,xm2m1,x1 - 1,xm1 - 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (2, 6, 7)(4, 8, 5) >,
    Group< a,b | [ a^4, b^3, a^-1 * b^-1 * a^2 * b^-1 * a^-1, b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a* b * a * b^-1 * a * b * a ] >,
    ideal< R | [xcom - 1,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12 - xm2m1,xm21 + xm2m1 + 1,x1 - 1,xm1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (2, 7, 3, 8, 5, 6, 4) >,
    Group< a,b | [ a^4, b^7, b^-1 * a * b^-1 * a^-1 * b^2 * a^-1, (a^-1 * b^-1)^4 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12 - 1,xm12 + xm2 + 1,xm21 - xm2,xm2m1 - 1,x1 - 1,xm1 - 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (2, 8, 4, 3, 6, 7, 5) >,
    Group< a,b | [ a^4, b^7, (a * b^-1)^2, (b^-1 * a^-1)^3 ] >,
    ideal< R | [xcom - 1,xm2^2 + xm2 + 2,x12,xm12 + 1,xm21 + 1,xm2m1,x1 - 1,xm1 - 1,x2 + xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (1, 2)(3, 8)(4, 7)(5, 6) >,
    Group< a,b | [ a^4, b^2, a^-2 * b * a^2 * b * a^2 * b, (b * a^-1)^7 ] >,
    ideal< R | [xcom - 1,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12 - xm2m1,xm21 + xm2m1 + 1,x1 - 1,xm1 - 1,x2 + 1,xm2 + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (1, 2, 5, 7)(3, 8, 6, 4) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [xcom^2 + xcom + 2,x12 - 1,xm12,xm21,xm2m1 - 1,x1 - 1,xm1 - 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (1, 2, 6, 8)(3, 7, 5, 4) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-2 * a^-1 * b^2 * a^2 * b^-1, (a^-1 * b^-1)^4, a^-1 * b^-2 * a^-1 *b^-1 * a * b^-1 * a * b^-1 ] >,
    ideal< R | [xcom - 1,xm21^2 + xm21 + 2,x12 - 1,xm12 + xm21 + 1,xm2m1 - 1,x1 - 1,xm1 - 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (1, 3, 7, 2)(4, 5, 6, 8) >,
    Group< a,b | [ a^4, b^4, (b^-1 * a^-1)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R| [xcom^2 + xcom + 2,x12,xm12 - 1,xm21 - 1,xm2m1,x1 - 1,xm1 - 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 8 | (1, 2, 3, 5)(4, 8, 7, 6), (1, 3, 6, 7)(2, 4, 5, 8) >,
    Group< a,b | [ a^4, b^4, a^-2 * b^-2 * a^-1 * b^2 * a^2 * b, a^-1 * b^-1 * a^-1 * b^-1 * a * b^2 * a *b^-1 ] >,
    ideal< R | [xcom - 1,xm2m1^2 + xm2m1 + 2,x12 + xm2m1 + 1,xm12 - 1,xm21 - 1,x1 - 1,xm1 - 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>
];

