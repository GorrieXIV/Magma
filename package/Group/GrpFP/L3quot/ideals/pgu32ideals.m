freeze;

import "../l3.m": R, x1, xm1, x2, xm2, x12, xm12, xm21, xm2m1, xcom, zeta;

pgu32presentations := [
<
    PermutationGroup< 21 | (3, 4, 5)(10, 18, 14)(11, 19, 15)(12, 20, 16)(13, 21, 17), (1, 6, 16, 12)(2, 10, 9, 3)(4, 14, 19, 15)(5, 18)(7, 21, 20, 13)(8, 11) >,
    Group< a,b | [ a^3,b^4, (b^-1 * a^-1)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a * b^2 * a ] >,
    ideal< R | [xcom - 1,xm12^2 + xm21 - x1,xm12*xm21 - 1,xm21^2 + xm12 - xm1,x1*xm12 - zeta - 2,xm1*xm12 - x1,x1*xm21 - xm1,xm1*xm21 + zeta - 1,xm12*zeta + 2*xm12 - xm1*zeta - xm1,xm21*zeta + 2*xm21 - x1,x1^2 - xm1*zeta - 2*xm1,x1*xm1 - 3,xm1^2 + x1*zeta - x1,x12,3*xm12 - xm1*zeta - 2*xm1,3*xm21 + x1*zeta - x1,xm2m1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(10, 18, 14)(11, 19, 15)(12, 20, 16)(13, 21, 17), (1, 6, 21, 13)(2, 10, 8, 3)(4, 14)(5, 18, 15, 19)(7, 16, 17, 12)(9, 11) >,
    Group< a,b | [ a^3,b^4, (b^-1 * a)^3, b^-2 * a^-1 * b^-2 * a^-1 * b^2 * a * b^2 * a ] >,
    ideal< R | [xcom - 1,x12^2 + xm2m1 - xm1,x12*xm2m1 - 1,xm2m1^2 + x12 - x1,x1*x12 - xm1,xm1*x12 + zeta - 1,x1*xm2m1 - zeta - 2,xm1*xm2m1 - x1,x12*zeta + 2*x12 - x1,xm2m1*zeta + 2*xm2m1 - xm1*zeta - xm1,x1^2 - xm1*zeta - 2*xm1,x1*xm1 - 3,xm1^2 + x1*zeta - x1,3*x12 + x1*zeta - x1,xm12,xm21,3*xm2m1 - xm1*zeta - 2*xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(10, 18, 14)(11, 19, 15)(12, 20, 16)(13, 21, 17), (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20) >,
    Group< a,b | [a^3, b^3, (a * b^-1)^4, (a^-1 * b^-1)^6, a^-1 * b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-1 ] >,
    ideal< R | [xcom - 1,x12^2 + xm2m1 + x1*zeta + x1,x12*xm2m1 - 1,xm2m1^2 + x12 - xm1*zeta,x1*x12 - zeta + 1,xm1*x12 - x1*zeta,x1*xm2m1 + xm1*zeta + xm1,xm1*xm2m1 + zeta + 2,x12*zeta + 2*x12 + xm1,xm2m1*zeta + 2*xm2m1 + x1*zeta + x1,x1^2 - xm1*zeta - 2*xm1,x1*xm1 - 3,xm1^2 + x1*zeta - x1,3*x12 - xm1*zeta + xm1,xm12 - 1,xm21 - 1,3*xm2m1 + x1*zeta + 2*x1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(10, 18, 14)(11, 19, 15)(12, 20, 16)(13, 21, 17), (1, 6, 21, 12, 20, 17)(2, 10, 15, 9, 11, 5)(3, 14, 8)(4, 18)(7, 16) >,
    Group< a,b | [ a^3, b^6,(b^-1 * a^-1)^3, (a * b^-1)^4, b^-1 * a * b^-2 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [xcom - 1,x1^2 - 3*xm2,x1*xm1 - 3,xm1^2 - 3*x2,x1*x2 - xm1,xm1*x2 + zeta - 1,x2^2 - xm1 + xm2,x1*xm2 - zeta - 2,xm1*xm2 - x1,x2*xm2 - 1,xm2^2 - x1 + x2,x12,xm12 - 1,xm21 - 1,xm2m1,x1*zeta - x1 + 3*x2,xm1*zeta + 2*xm1 - 3*xm2,x2*zeta - x1 + 2*x2,xm2*zeta + xm1 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(10, 18, 14)(11, 19, 15)(12, 20, 16)(13, 21, 17), (1, 6, 16, 13, 17, 20)(2, 10, 19, 8, 11, 4)(3, 18, 9)(5, 14)(7, 21) >,
    Group< a,b | [ a^3, b^6,(b^-1 * a)^3, (a^-1 * b^-1)^4, b * a^-1 * b^-2 * a^-1 * b^2 * a * b ] >,
    ideal< R | [xcom - 1,x1^2 - 3*x2,x1*xm1 - 3,xm1^2 - 3*xm2,x1*x2 - zeta - 2,xm1*x2 - x1,x2^2 - x1 + xm2,x1*xm2 - xm1,xm1*xm2 + zeta - 1,x2*xm2 - 1,xm2^2 - xm1 + x2,x12 - 1,xm12,xm21,xm2m1 - 1,x1*zeta - x1 + 3*xm2,xm1*zeta + 2*xm1 - 3*x2,x2*zeta + xm1 - x2,xm2*zeta - x1 + 2*xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(10, 18, 14)(11, 19, 15)(12, 20, 16)(13, 21, 17), (1, 6, 21)(2, 10, 4)(3, 18, 8)(5, 14, 15)(7, 16, 20)(9, 11, 19)(12, 17, 13) >,
    Group< a,b | [a^3, b^3, (a^-1 * b^-1)^4, a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b^-1 * a^-1 * b * a^-1 * b ] >,
    ideal< R | [xcom - 1,xm12^2 + xm21 - xm1*zeta,xm12*xm21 - 1,xm21^2 + xm12 + x1*zeta + x1,x1*xm12 + xm1*zeta + xm1,xm1*xm12 + zeta + 2,x1*xm21 - zeta + 1,xm1*xm21 - x1*zeta,xm12*zeta + 2*xm12 + x1*zeta + x1,xm21*zeta + 2*xm21 + xm1,x1^2 - xm1*zeta - 2*xm1,x1*xm1 - 3,xm1^2 + x1*zeta - x1,x12 - 1,3*xm12 + x1*zeta + 2*x1,3*xm21 - xm1*zeta + xm1,xm2m1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 6, 16, 12)(2, 10, 9, 3)(4, 14, 19, 15)(5, 18)(7, 21, 20, 13)(8, 11) >,
    Group<a,b | [ a^6, b^4, (b^-1 * a)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a^-3 * b^-1 * a^-1 * b^2 * a * b ] >,
    ideal< R | [xcom - zeta,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12 - x1,xm12,xm21,xm2m1 - xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 6, 21, 13)(2, 10, 8, 3)(4, 14)(5, 18, 15, 19)(7, 16, 17, 12)(9, 11) >,
    Group<a,b | [ a^6, b^4, (b^-1 * a^-1)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a^-3 * b^-1 * a * b^2 * a^-1 * b ] >,
    ideal< R | [xcom - zeta,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12,xm12 - xm1,xm21 - x1,xm2m1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20) >,Group< a,b | [ a^6, b^3, (b^-1 * a^-1)^3, (a * b^-1)^4, b^-1 * a^-2 * b^-1 * a^2 * b * a^-1 * b * a ] >,
    ideal< R | [xcom - zeta,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12,xm12 + zeta + 1,xm21 - zeta,xm2m1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 6, 21, 12, 20, 17)(2, 10, 15, 9, 11, 5)(3, 14, 8)(4, 18)(7, 16) >,
    Group< a,b |[ a^6, b^6, b^-1 * a^-1 * b^-1 * a^2 * b * a * b^-1, b * a * b^-1 * a^2 * b^2 * a, a^-1 * b^-3 * a^2 * b^-1 * a * b^-1, b * a^-3 * b^-1 * a^-1 * b * a^-1 * b ] >,
    ideal< R | [xcom - zeta,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12 + xm2*zeta + xm2,xm12 - 1,xm21 - 1,xm2m1 - x2*zeta,x1 - x2,xm1 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 6, 16, 13, 17, 20)(2, 10, 19, 8, 11, 4)(3, 18, 9)(5, 14)(7, 21) >,
    Group< a,b |[ a^6, b^6, b * a * b^-1 * a^2 * b * a^-1 * b, a^-1 * b^-2 * a^2 * b^-1 * a * b^-1, b * a * b * a^2 * b^3 * a^-1, b * a^-3 * b^-1 * a * b * a * b ] >,
    ideal< R | [xcom - zeta,x2^2 - xm2*zeta - xm2,x2*xm2 - 1,xm2^2 + x2*zeta,x12 - 1,xm12 - xm2*zeta,xm21 + x2*zeta + x2,xm2m1 - 1,x1 - xm2,xm1 - x2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 6, 21)(2, 10, 4)(3, 18, 8)(5, 14, 15)(7, 16, 20)(9, 11, 19)(12, 17, 13) >,Group< a,b | [ a^6, b^3, (b^-1 * a)^3, (a^-1 * b^-1)^4, a * b^-1 * a^-1 * b^-1 * a^2 * b * a^-2 * b ] >,
    ideal< R | [xcom - zeta,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12 - zeta,xm12,xm21,xm2m1 + zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 16, 6)(2, 3, 9, 10)(4, 15, 19, 14)(5, 18)(7, 13, 20, 21)(8, 11) >,
    Group<a,b | [ a^6, b^4, (b^-1 * a^-1)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, b^-1 * a^-3 * b^-1 * a * b^2 * a^2 ] >,
    ideal< R | [xcom + zeta + 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12,xm12 - xm1,xm21 - x1,xm2m1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 20, 7)(2, 3, 9, 11)(4, 15)(5, 18, 14, 19)(6, 13, 16, 17)(8, 10) >,
    Group<a,b | [ a^6, b^4, (b^-1 * a)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, b^-2 * a^-1 * b^-1 * a^3 * b * a ] >,
    ideal< R | [xcom + zeta + 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12 - x1*zeta,xm12,xm21,xm2m1 + xm1*zeta + xm1,x2 - zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 21, 17, 20, 6)(2, 3, 15, 8, 11, 14)(4, 18)(5, 9, 10)(7, 13) >,
    Group< a,b |[ a^6, b^6, b^-1 * a * b^-1 * a^2 * b^3 * a^-1, b^-1 * a * b * a^2 * b^-1 * a^-1 * b^-1, a^-1 * b^2 * a^2 * b * a * b, a^-1 * b * a^-1 * b^-1 * a^3 * b^2 ] >,
    ideal< R | [xcom + zeta + 1,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12 + xm2*zeta + xm2,xm12 - 1,xm21 - 1,xm2m1 - x2*zeta,x1 - x2,xm1 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 7)(2, 3, 15)(4, 18, 19)(5, 9, 11)(6, 13, 21)(8, 10, 14)(16, 20, 17) >,Group< a,b | [ a^6, b^3, (b^-1 * a^-1)^3, (a * b^-1)^4, a^-1 * b^-1 * a * b^-1 * a^2 * b^-1 * a^3 * b ] >,
    ideal< R | [xcom + zeta + 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12,xm12 - 1,xm21 - 1,xm2m1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 6)(2, 3, 18)(4, 9, 10)(5, 15, 14)(7, 13, 17)(8, 11, 19)(16, 21, 20) >,Group< a,b | [ a^6, b^3, (b^-1 * a)^3, (a^-1 * b^-1)^4, b * a^-2 * b^-1 * a^2 * b^-1 * a^-1 * b * a ] >,
    ideal< R | [xcom + zeta + 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12 - zeta,xm12,xm21,xm2m1 + zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 17, 21, 16, 7)(2, 3, 18, 8, 10, 19)(4, 9, 11)(5, 15)(6, 13) >,
    Group< a,b |[ a^6, b^6, b^-1 * a * b^-1 * a^2 * b^-2 * a^-1, b * a^-1 * b * a^2 * b^-1 * a * b, a^-1 * b^-3 * a^2 * b * a * b, a * b * a * b^-1 * a^3 * b^2 ] >,
    ideal< R | [xcom + zeta + 1,x1^2 + x2,x1*xm1 - 1,xm1^2 + xm2,x1*x2 - zeta,xm1*x2 + x1,x2^2 - x1 - xm2,x1*xm2 + xm1,xm1*xm2 + zeta + 1,x2*xm2 - 1,xm2^2 - xm1 - x2,x12 - zeta,xm12 - xm2,xm21 - x2,xm2m1 + zeta + 1,x1*zeta + x1 + xm2,xm1*zeta - x2,x2*zeta + xm1 + x2,xm2*zeta - x1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12)(2, 15, 4, 9, 5, 18)(6, 7, 21, 20, 16, 17)(8, 14, 19)(10, 11) >,
    Group< a,b |[ a^6, b^6, b^2 * a^-2 * b^2 * a, a^2 * b^-1 * a^2 * b * a * b ] >,
    ideal< R | [xcom - 1,x1^2 + xm2,x1*xm1 - 1,xm1^2 + x2,x1*x2 + xm1,xm1*x2 + zeta + 1,x2^2 - xm1 - xm2,x1*xm2 - zeta,xm1*xm2 + x1,x2*xm2 - 1,xm2^2 - x1 - x2,x12 + xm1 + xm2,xm12 - zeta,xm21 + zeta + 1,xm2m1 + x1 + x2,x1*zeta + x1 + x2,xm1*zeta - xm2,x2*zeta - x1,xm2*zeta + xm1 + xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 13)(2, 15, 19)(4, 9, 14)(5, 18, 8)(6, 21, 16) >,
    Group< a,b | [ a^6, b^3,(b^-1 * a^-1)^3, (a * b^-1)^4, a^2 * b^-1 * a^-2 * b * a^-2 * b^-1 ] >,
    ideal< R | [xcom - 1,x1^2 - 2*xm1 - xm2,x1*xm1 - 1,xm1^2 - 2*x1 - x2,x1*x2 + 3*xm1 + 2*xm2,xm1*x2 - zeta + 1,x2^2 - 3*xm1 - 3*xm2,x1*xm2 + zeta + 2,xm1*xm2 + 3*x1 + 2*x2,x2*xm2 - 3,xm2^2 - 3*x1 - 3*x2,x12,xm12 - zeta,xm21 + zeta + 1,xm2m1,x1*zeta - x1 - x2,xm1*zeta + 2*xm1 + xm2,x2*zeta + 3*x1 + 2*x2,xm2*zeta - 3*xm1 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 16)(2, 15, 10)(3, 9, 5)(4, 18, 19)(6, 7, 21)(8, 14, 11)(13, 20, 17) >,Group< a,b | [ a^6, b^3, (b^-1 * a)^3, (a^-1 * b^-1)^4, a^-2 * b * a^-2 * b^-1 * a^3 * b^-1 ] >,
    ideal< R | [xcom - 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12 - 1,xm12 - x1*zeta + x1,xm21 + xm1*zeta + 2*xm1,xm2m1 - 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 20, 6, 21, 17)(2, 15, 11)(3, 9, 14, 10, 8, 5)(4, 18)(13, 16) >,
    Group< a,b |[ a^6, b^6, b^-2 * a^-2 * b * a^-2, (a^-1 * b^-1)^4, b^-1 * a^-3 * b^-1 * a * b^-2 * a ] >,
    ideal< R | [xcom - 1,x1^2 - xm1 - x2,x1*xm1 - 1,xm1^2 - x1 - xm2,x1*x2 + zeta + 1,xm1*x2 + xm2,x2^2 + x1,x1*xm2 + x2,xm1*xm2 - zeta,x2*xm2 - 1,xm2^2 + xm1,x12 - zeta,xm12 + x1 + xm2,xm21 + xm1 + x2,xm2m1 + zeta + 1,x1*zeta - xm2,xm1*zeta + xm1 + x2,x2*zeta - xm1,xm2*zeta + x1 + xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 17, 20)(2, 15, 8, 14)(3, 18, 11, 4)(5, 9)(6, 7, 21, 13)(10, 19) >,
    Group<a,b | [ a^6, b^4, (b^-1 * a^-1)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, a^2 * b^-1 * a^2 * b * a^-1 * b ] >,
    ideal< R | [xcom - 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12 - x1*zeta + x1,xm12 + xm1*zeta + xm1,xm21 - x1*zeta,xm2m1 + xm1*zeta + 2*xm1,x2 - zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 6, 21)(2, 15)(3, 18, 10, 4)(5, 9, 14, 8)(11, 19)(13, 17, 16, 20) >,
    Group<a,b | [ a^6, b^4, a^-1 * b^-2 * a^2 * b^2 * a^-1, (b^-1 * a)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [xcom - 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12 - x1*zeta,xm12,xm21,xm2m1 + xm1*zeta + xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 13)(2, 18, 14)(4, 15, 8)(5, 9, 19)(7, 17, 20) >,
    Group< a,b | [ a^6, b^3,(b^-1 * a)^3, (a^-1 * b^-1)^4, a^-2 * b^-1 * a^-2 * b * a^2 * b ] >,
    ideal< R | [xcom - 1,x1^2 + xm1 - x2,x1*xm1 - 1,xm1^2 + x1 - xm2,x1*x2 + zeta - 1,xm1*x2 - xm2,x2^2 - 3*x1,x1*xm2 - x2,xm1*xm2 - zeta - 2,x2*xm2 - 3,xm2^2 - 3*xm1,x12 - 1,xm12,xm21,xm2m1 - 1,x1*zeta + 2*x1 - xm2,xm1*zeta - xm1 + x2,x2*zeta - 3*xm1 + 2*x2,xm2*zeta + 3*x1 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12)(2, 18, 5, 9, 4, 15)(6, 17, 16, 20, 21, 7)(8, 19, 14)(10, 11) >,
    Group< a,b |[ a^6, b^6, b^-2 * a^-2 * b^-2 * a, b^-1 * a * b^-1 * a^2 * b * a^2 ] >,
    ideal< R | [xcom - 1,x2^2 - xm2*zeta - xm2,x2*xm2 - 1,xm2^2 + x2*zeta,x12 - zeta,xm12 - xm2,xm21 - x2,xm2m1 + zeta + 1,x1 - xm2,xm1 - x2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 16, 7, 17, 21)(2, 18, 10)(3, 9, 19, 11, 8, 4)(5, 15)(13, 20) >,
    Group< a,b |[ a^6, b^6, a^-1 * b^-1 * a^-2 * b^2 * a^-1, b^-2 * a^-1 * b^-1 * a^3 * b^-1 * a^-1 ] >,
    ideal< R | [xcom - 1,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12 - xm2,xm12 - zeta,xm21 + zeta + 1,xm2m1 - x2,x1 - x2,xm1 - xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 20)(2, 18, 11)(3, 9, 4)(5, 15, 14)(6, 17, 7)(8, 19, 10)(13, 16, 21) >,Group< a,b | [ a^6, b^3, (b^-1 * a^-1)^3, (a * b^-1)^4, a^-2 * b^-1 * a^-2 * b * a^3 * b ] >,
    ideal< R | [xcom - 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12 - 2*xm1*zeta - xm1,xm12 + zeta + 1,xm21 - zeta,xm2m1 + 2*x1*zeta + x1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 7, 17)(2, 18)(3, 15, 11, 5)(4, 9, 19, 8)(10, 14)(13, 21, 20, 16) >,
    Group<a,b | [ a^6, b^4, a^-1 * b^-2 * a^2 * b^2 * a^-1, (b^-1 * a^-1)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1 ] >,
    ideal< R | [xcom - 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12,xm12 - xm1*zeta,xm21 + x1*zeta + x1,xm2m1,x2 + zeta + 1,xm2 - zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17), (1, 12, 21, 16)(2, 18, 8, 19)(3, 15, 10, 5)(4, 9)(6, 17, 13, 7)(11, 14) >,
    Group<a,b | [ a^6, b^4, (b^-1 * a)^3, b^-1 * a^-1 * b^-2 * a^-1 * b^2 * a^-1 * b^-1, b^-1 * a^-1 * b^-1 * a^2 * b * a^2 ] >,
    ideal< R | [xcom - 1,x1^2 + xm1*zeta,x1*xm1 - 1,xm1^2 - x1*zeta - x1,x12 - x1,xm12 - 2*xm1*zeta - xm1,xm21 + 2*x1*zeta + x1,xm2m1 - xm1,x2 - zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6)(3, 14, 4, 10, 5, 18)(8, 9)(11, 15, 19)(12, 13, 20, 21, 16, 17) >,
    Group<a,b | [ a^4, b^6, (b^-1 * a^-1)^3, b^-1 * a^-2 * b^2 * a^2 * b^-1, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 ] >,
    ideal< R | [xcom - 1,x2^2 - xm2*zeta - xm2,x2*xm2 - 1,xm2^2 + x2*zeta,x12,xm12 - x2*zeta,xm21 + xm2*zeta + xm2,xm2m1,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 7)(3, 14, 19)(4, 10, 15)(5, 18, 11)(12, 20, 16) >,
    Group< a,b | [ a^4,b^3, (b^-1 * a)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b * a^-1 ] >,
    ideal< R | [xcom - 1,x12^2 + xm2m1 + xm2*zeta + xm2,x12*xm2m1 - 1,xm2m1^2 + x12 - x2*zeta,x2*x12 - xm2*zeta,xm2*x12 - zeta + 1,x2*xm2m1 + zeta + 2,xm2*xm2m1 + x2*zeta + x2,x12*zeta + 2*x12 + x2,xm2m1*zeta + 2*xm2m1 + xm2*zeta + xm2,x2^2 + xm2*zeta - xm2,x2*xm2 - 3,xm2^2 - x2*zeta - 2*x2,3*x12 - x2*zeta + x2,xm12,xm21,3*xm2m1 + xm2*zeta + 2*xm2,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6)(3, 18, 5, 10, 4, 14)(8, 9)(11, 19, 15)(12, 17, 16, 21, 20, 13) >,
    Group<a,b | [ a^4, b^6, (b^-1 * a)^3, b^-1 * a^-2 * b^2 * a^2 * b^-1, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1 ] >,
    ideal< R | [xcom - 1,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12 + x2*zeta + x2,xm12,xm21,xm2m1 - xm2*zeta,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 7)(3, 18, 15)(4, 14, 11)(5, 10, 19)(13, 17, 21) >,
    Group< a,b | [ a^4,b^3, (b^-1 * a^-1)^3, a^-1 * b^-1 * a^-2 * b^-1 * a^2 * b * a^2 * b * a^-1 ] >,
    ideal< R | [xcom - 1,xm12^2 + xm21 - xm2*zeta,xm12*xm21 - 1,xm21^2 + xm12 + x2*zeta + x2,x2*xm12 + xm2*zeta + xm2,xm2*xm12 + zeta + 2,x2*xm21 - zeta + 1,xm2*xm21 - x2*zeta,xm12*zeta + 2*xm12 + x2*zeta + x2,xm21*zeta + 2*xm21 + xm2,x2^2 - xm2*zeta - 2*xm2,x2*xm2 - 3,xm2^2 + x2*zeta - x2,x12,3*xm12 + x2*zeta + 2*x2,3*xm21 - xm2*zeta + xm2,xm2m1,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20) >,Group< a,b | [ a^4, b^3, (b^-1 * a)^3, b^-1 * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b * a^-1 ] >,
    ideal< R | [xcom - zeta,x12^2 + xm2m1*zeta,x12*xm2m1 - 1,xm2m1^2 - x12*zeta - x12,xm12,xm21,x1 - zeta,xm1 + zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 21, 12, 20, 17)(2, 10, 15, 9, 11, 5)(3, 14, 8)(4, 18)(7, 16) >,
    Group< a,b| [ a^4, b^6, (b^-1 * a^-1)^3, b^-1 * a^-2 * b * a^-1 * b^3 * a ] >,
    ideal< R | [xcom - zeta,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12,xm12 + x2*zeta + x2,xm21 - xm2*zeta,xm2m1,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 16, 13, 17, 20)(2, 10, 19, 8, 11, 4)(3, 18, 9)(5, 14)(7, 21) >,
    Group< a,b| [ a^4, b^6, (b^-1 * a)^3, a * b^-3 * a^-1 * b^-1 * a^2 * b ] >,
    ideal< R | [xcom - zeta,x2^2 - xm2*zeta - xm2,x2*xm2 - 1,xm2^2 + x2*zeta,x12 - x2*zeta,xm12,xm21,xm2m1 + xm2*zeta + xm2,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 21)(2, 10, 4)(3, 18, 8)(5, 14, 15)(7, 16, 20)(9, 11, 19)(12, 17, 13) >,Group< a,b | [ a^4, b^3, (b^-1 * a^-1)^3, b^-1 * a^-2 * b^-1 * a^-2 * b^-1 * a * b^-1 * a^2 * b * a ] >,
    ideal< R | [xcom - zeta,xm12^2 - xm21*zeta - xm21,xm12*xm21 - 1,xm21^2 + xm12*zeta,x12,xm2m1,x1 - zeta,xm1 + zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 13)(2, 14, 3)(4, 18, 19)(5, 10, 8)(7, 20, 12)(9, 15, 11)(16, 21, 17) >,Group< a,b | [ a^4, b^3, (b^-1 * a^-1)^3, a^-1 * b * a^-2 * b^-1 * a * b^-1 * a^2 * b ] >,
    ideal< R | [xcom - 1,x12^2 + xm2m1*zeta - xm2m1,x12*xm12 + xm2m1*zeta + xm2m1,xm12^2 + xm2m1*zeta - 2*xm21 + xm2m1,x12*xm21 - 2*zeta - 1,xm12*xm21 - 1,xm21^2 + xm12*zeta,x12*xm2m1 - 3,xm12*xm2m1 + 2*zeta + 1,xm21*xm2m1 + xm12*zeta + 2*xm12,xm2m1^2 + xm12*zeta - 2*x12 + 2*xm12,x12*zeta + xm12*zeta + 2*xm12,2*xm12*zeta - x12 + xm12,xm21*zeta + xm2m1*zeta - xm21 + xm2m1,2*xm2m1*zeta - 3*xm21 + xm2m1,x1 - zeta,xm1 + zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 20, 17, 21, 12)(2, 14, 11, 8, 15, 3)(4, 18)(5, 10, 9)(7, 13) >,
    Group< a,b| [ a^4, b^6, (b^-1 * a)^3, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, b^2 * a^-1 * b^-1 * a^-1 * b^2 * a ] >,
    ideal< R | [xcom - 1,x2^2 - xm2*zeta - xm2,x2*xm2 - 1,xm2^2 + x2*zeta,x12 + x2*zeta + x2,xm12 + x2*zeta + 2*x2,xm21 - xm2*zeta + xm2,xm2m1 - xm2*zeta,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 13, 16, 12, 21)(2, 14, 19, 9, 15, 4)(3, 10)(5, 18, 8)(7, 20) >,
    Group< a,b| [ a^4, b^6, (b^-1 * a)^3, b * a^-2 * b^-1 * a^-1 * b^3 * a ] >,
    ideal< R | [xcom - zeta,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12 - x2*zeta,xm12,xm21,xm2m1 + xm2*zeta + xm2,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 20)(2, 14, 4)(3, 10, 11)(5, 18, 9)(7, 13, 21)(8, 15, 19)(12, 16, 17) >,Group< a,b | [ a^4, b^3, (b^-1 * a^-1)^3, b^-1 * a^-2 * b^-1 * a^-2 * b^-1 * a * b * a^2 * b^-1 * a ] >,
    ideal< R | [xcom - zeta,xm12^2 + xm21*zeta,xm12*xm21 - 1,xm21^2 - xm12*zeta - xm12,x12,xm2m1,x1 - zeta,xm1 + zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 12)(2, 18, 3)(4, 10, 9)(5, 14, 15)(7, 17, 13)(8, 19, 11)(16, 20, 21) >,Group< a,b | [ a^4, b^3, (b^-1 * a)^3, a * b * a^-2 * b^-1 * a^-1 * b^-1 * a^2 * b ] >,
    ideal< R | [xcom - 1,x12^2 + xm2m1*zeta,x12*xm12 + xm2m1*zeta + 2*xm2m1,xm12^2 + xm2m1*zeta - 2*xm21 + 2*xm2m1,x12*xm21 - 2*zeta - 1,xm12*xm21 - 3,xm21^2 + xm12*zeta - xm12,x12*xm2m1 - 1,xm12*xm2m1 + 2*zeta + 1,xm21*xm2m1 + xm12*zeta + xm12,xm2m1^2 + xm12*zeta - 2*x12 + xm12,x12*zeta + xm12*zeta - x12 + xm12,2*xm12*zeta - 3*x12 + xm12,xm21*zeta + xm2m1*zeta + 2*xm2m1,2*xm2m1*zeta - xm21 + xm2m1,x1 - zeta,xm1 + zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 17, 20, 16, 13)(2, 18, 11, 9, 19, 3)(4, 10, 8)(5, 14)(7, 12) >,
    Group< a,b| [ a^4, b^6, (b^-1 * a^-1)^3, a^-2 * b^-1 * a^2 * b^-1 * a^2 * b^-1, b^2 * a * b^-1 * a * b^2 * a^-1 ] >,
    ideal< R | [xcom - 1,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12 - x2*zeta + x2,xm12 - x2*zeta,xm21 + xm2*zeta + xm2,xm2m1 + xm2*zeta + 2*xm2,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 12, 21, 13, 16)(2, 18, 15, 8, 19, 5)(3, 10)(4, 14, 9)(7, 17) >,
    Group< a,b| [ a^4, b^6, (b^-1 * a^-1)^3, a * b^-3 * a^-1 * b * a^2 * b^-1 ] >,
    ideal< R | [xcom - zeta,x2^2 - xm2*zeta - xm2,x2*xm2 - 1,xm2^2 + x2*zeta,x12,xm12 + x2*zeta + x2,xm21 - xm2*zeta,xm2m1,x1 - zeta,xm1 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 17)(2, 18, 5)(3, 10, 11)(4, 14, 8)(7, 12, 16)(9, 19, 15)(13, 21, 20) >,Group< a,b | [ a^4, b^3, (b^-1 * a)^3, b^-1 * a^-2 * b^-1 * a^-2 * b^-1 * a^-1 * b * a^2 * b^-1 * a^-1 ] >,
    ideal< R | [xcom - zeta,x12^2 - xm2m1*zeta - xm2m1,x12*xm2m1 - 1,xm2m1^2 + x12*zeta,xm12,xm21,x1 - zeta,xm1 + zeta + 1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (3, 4, 5)(10, 18, 14)(11, 19, 15)(12, 20, 16)(13, 21, 17) >,
    Group< a,b | [a^3, b^3, (a * b^-1)^4, (a^-1 * b^-1)^6, a * b^-1 * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a * b ] >,
    ideal< R | [xcom - 1,x12^2 + xm2m1 + x2*zeta + x2,x12*xm2m1 - 1,xm2m1^2 + x12 - xm2*zeta,x2*x12 - zeta + 1,xm2*x12 - x2*zeta,x2*xm2m1 + xm2*zeta + xm2,xm2*xm2m1 + zeta + 2,x12*zeta + 2*x12 + xm2,xm2m1*zeta + 2*xm2m1 + x2*zeta + x2,x2^2 - xm2*zeta - 2*xm2,x2*xm2 - 3,xm2^2 + x2*zeta - x2,3*x12 - xm2*zeta + xm2,xm12 - 1,xm21 - 1,3*xm2m1 + x2*zeta + 2*x2,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (3, 4, 5)(6, 7)(8, 9)(10, 19, 14, 11, 18, 15)(12, 21, 16, 13, 20, 17) >,Group< a,b | [ a^3, b^6, (b^-1 * a^-1)^3, (a * b^-1)^4, b * a^-1 * b * a^-1 * b^-1 * a * b^3 * a^-1 * b ] >,
    ideal< R | [xcom + zeta + 1,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12,xm12 - zeta,xm21 + zeta + 1,xm2m1,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (3, 5, 4)(10, 14, 18)(11, 15, 19)(12, 16, 20)(13, 17, 21) >,
    Group< a,b | [a^3, b^3, (a^-1 * b^-1)^4, a^-1 * b^-1 * a * b^-1 * a^-1 * b^-1 * a * b * a^-1 * b * a * b ] >,
    ideal< R | [xcom - 1,xm12^2 + xm21 - x2*zeta,xm12*xm21 - 1,xm21^2 + xm12 + xm2*zeta + xm2,x2*xm12 + zeta + 2,xm2*xm12 + x2*zeta + x2,x2*xm21 - xm2*zeta,xm2*xm21 - zeta + 1,xm12*zeta + 2*xm12 + xm2*zeta + xm2,xm21*zeta + 2*xm21 + x2,x2^2 + xm2*zeta - xm2,x2*xm2 - 3,xm2^2 - x2*zeta - 2*x2,x12 - 1,3*xm12 + xm2*zeta + 2*xm2,3*xm21 - x2*zeta + x2,xm2m1 - 1,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (3, 5, 4)(6, 7)(8, 9)(10, 15, 18, 11, 14, 19)(12, 17, 20, 13, 16, 21) >,Group< a,b | [ a^3, b^6, (b^-1 * a)^3, (a^-1 * b^-1)^4, b^-1 * a * b * a^-1 * b^-1 * a^-1 * b^2 * a * b^-1 ] >,
    ideal< R | [xcom - zeta,x2^2 - xm2*zeta - xm2,x2*xm2 - 1,xm2^2 + x2*zeta,x12 - 1,xm12,xm21,xm2m1 - 1,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21) >,Group< a,b | [ a^3, b^4, (b^-1 * a)^3, b^-1 * a^-1 * b^-1 * a^-1 * b * a^-2 * b^2 * a^-1 * b^2 * a^-1 ] >,
    ideal< R | [xcom + zeta + 1,x12^2 + xm2m1*zeta,x12*xm2m1 - 1,xm2m1^2 - x12*zeta - x12,xm12,xm21,x1,xm1,x2 - zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 3)(4, 5)(6, 13, 7, 12)(8, 11, 9, 10)(14, 19, 15, 18)(16, 21, 17, 20) >,Group< a,b | [ a^3, b^4, (b^-1 * a^-1)^3, b * a^-1 * b * a^-1 * b^-1 * a * b^2 * a^-1 * b^2 * a^-1 ] >,
    ideal< R | [xcom - zeta,xm12^2 - xm21*zeta - xm21,xm12*xm21 - 1,xm21^2 + xm12*zeta,x12,xm2m1,x1,xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 3, 4)(6, 12, 20, 7, 13, 21)(8, 10, 18, 9, 11, 19)(14, 15)(16, 17) >,Group< a,b | [ a^3, b^6, (b^-1 * a)^3, (a^-1 * b^-1)^4, a^-1 * b^2 * a^-1 * b^-1 * a * b * a * b^-2 ] >,
    ideal< R | [xcom + zeta + 1,x2^2 - xm2*zeta - xm2,x2*xm2 - 1,xm2^2 + x2*zeta,x12 + zeta + 1,xm12,xm21,xm2m1 - zeta,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 4, 3)(6, 21, 13, 7, 20, 12)(8, 19, 11, 9, 18, 10)(14, 15)(16, 17) >,Group< a,b | [ a^3, b^6, (b^-1 * a^-1)^3, (a * b^-1)^4, b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^2 * a * b^-1 ] >,
    ideal< R | [xcom - zeta,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12,xm12 + zeta + 1,xm21 - zeta,xm2m1,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 4, 5)(6, 20, 16, 7, 21, 17)(8, 18, 14, 9, 19, 15)(10, 11)(12, 13) >,Group< a,b | [ a^3, b^6, (b^-1 * a)^3, (a^-1 * b^-1)^4, a^-1 * b * a^-1 * b^-1 * a^-1 * b^3 * a^-1 * b^-1 ] >,
    ideal< R | [xcom - 1,x2^2 - xm2*zeta - xm2,x2*xm2 - 1,xm2^2 + x2*zeta,x12 - 1,xm12 - xm2*zeta + xm2,xm21 + x2*zeta + 2*x2,xm2m1 - 1,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 4)(3, 5)(6, 20, 7, 21)(8, 18, 9, 19)(10, 14, 11, 15)(12, 16, 13, 17) >,Group< a,b | [ a^3, b^4, (b^-1 * a^-1)^3, b^-1 * a * b^-1 * a * b * a^2 * b^2 * a * b^2 * a ] >,
    ideal< R | [xcom + zeta + 1,xm12^2 - xm21*zeta - xm21,xm12*xm21 - 1,xm21^2 + xm12*zeta,x12,xm2m1,x1,xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 4)(3, 5)(6, 21, 7, 20)(8, 19, 9, 18)(10, 15, 11, 14)(12, 17, 13, 16) >,Group< a,b | [ a^3, b^4, (b^-1 * a)^3, b * a^-1 * b^-1 * a^-1 * b^-1 * a^-1 * b^2 * a^-1 * b^2 * a ] >,
    ideal< R | [xcom - zeta,x12^2 + xm2m1*zeta,x12*xm2m1 - 1,xm2m1^2 - x12*zeta - x12,xm12,xm21,x1,xm1,x2 + zeta + 1,xm2 - zeta,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 5, 4)(6, 17, 21, 7, 16, 20)(8, 15, 19, 9, 14, 18)(10, 11)(12, 13) >,Group< a,b | [ a^3, b^6, (b^-1 * a^-1)^3, (a * b^-1)^4, a^-1 * b^-1 * a^-1 * b * a^-1 * b^3 * a^-1 * b ] >,
    ideal< R | [xcom - 1,x2^2 + xm2*zeta,x2*xm2 - 1,xm2^2 - x2*zeta - x2,x12 + xm2*zeta - xm2,xm12 + zeta + 1,xm21 - zeta,xm2m1 - x2*zeta - 2*x2,x1,xm1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 5)(3, 4)(6, 16, 7, 17)(8, 14, 9, 15)(10, 19, 11, 18)(12, 21, 13, 20) >,Group< a,b | [ a^3, b^4, (b^-1 * a)^3, a * b^-2 * a^-1 * b^-1 * a^-1 * b^2 * a * b ] >,
    ideal< R | [xcom - 1,x12^2 - xm12 - 2*xm2m1,x12*xm12 + zeta + 2,xm12^2 - 3*x12 - 3*xm21,x12*xm21 + 2*xm12 + 3*xm2m1,xm12*xm21 - 3,xm21^2 - 3*xm12 - 3*xm2m1,x12*xm2m1 - 1,xm12*xm2m1 + 3*x12 + 2*xm21,xm21*xm2m1 - zeta + 1,xm2m1^2 - 2*x12 - xm21,x12*zeta - x12 - xm21,xm12*zeta - xm12 - 3*xm2m1,xm21*zeta + 3*x12 + 2*xm21,xm2m1*zeta + xm12 + 2*xm2m1,x1,xm1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (2, 5)(3, 4)(6, 17, 7, 16)(8, 15, 9, 14)(10, 18, 11, 19)(12, 20, 13, 21) >,Group< a,b | [ a^3, b^4, (b^-1 * a^-1)^3, a^-1 * b^-2 * a * b^-1 * a * b^2 * a^-1 * b ] >,
    ideal< R | [xcom - 1,x12^2 - 3*xm12,x12*xm12 - zeta - 2,xm12^2 - x12 + xm21,x12*xm21 - xm2m1,xm12*xm21 - 1,xm21^2 + xm12 - xm2m1,x12*xm2m1 - 3,xm12*xm2m1 - x12,xm21*xm2m1 + zeta - 1,xm2m1^2 - 3*xm21,x12*zeta - x12 + 3*xm21,xm12*zeta - xm12 + xm2m1,xm21*zeta - x12 + 2*xm21,xm2m1*zeta - 3*xm12 + 2*xm2m1,x1,xm1,x2 - zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (1, 6, 21)(2, 10, 4)(3, 18, 8)(5, 14, 15)(7, 16, 20)(9, 11, 19)(12, 17, 13) >,Group< a,b | [ a^3, b^3, (a^-1 * b^-1)^4, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b^-1 * a * b * a^-1 * b ] >,
    ideal< R | [xcom + zeta + 1,xm12^2 + xm21*zeta,xm12*xm21 - 1,xm21^2 - xm12*zeta - xm12,x12 - 1,xm2m1 - 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (1, 6, 20)(2, 14, 4)(3, 10, 11)(5, 18, 9)(7, 13, 21)(8, 15, 19)(12, 16, 17) >,Group< a,b | [ a^3, b^3, (a * b^-1)^4, (a^-1 * b^-1)^6, a * b * a^-1 * b^-1 * a^-1 * b^-1 * a * b * a * b^-1 * a^-1 * b ] >,
    ideal< R | [xcom - zeta,x12^2 - xm2m1*zeta - xm2m1,x12*xm2m1 - 1,xm2m1^2 + x12*zeta,xm12 - 1,xm21 - 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (1, 6, 12)(2, 18, 3)(4, 10, 9)(5, 14, 15)(7, 17, 13)(8, 19, 11)(16, 20, 21) >,Group< a,b | [ a^3, b^3, (a * b^-1)^4, (a^-1 * b^-1)^6, a^-1 * b * a * b^-1 * a^-1 * b^-1 * a * b * a * b * a^-1 * b^-1 ] >,
    ideal< R | [xcom + zeta + 1,x12^2 - xm2m1*zeta - xm2m1,x12*xm2m1 - 1,xm2m1^2 + x12*zeta,xm12 - 1,xm21 - 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (1, 6, 16)(2, 10, 5)(3, 14, 9)(4, 18, 19)(7, 21, 17)(8, 11, 15)(12, 13, 20), (1, 6, 17)(2, 18, 5)(3, 10, 11)(4, 14, 8)(7, 12, 16)(9, 19, 15)(13, 21, 20) >,Group< a,b | [ a^3, b^3, (a^-1 * b^-1)^4, a * b^-1 * a^-1 * b * a^-1 * b^-1 * a * b * a^-1 * b * a * b^-1 ] >,
    ideal< R | [xcom - zeta,xm12^2 + xm21*zeta,xm12*xm21 - 1,xm21^2 - xm12*zeta - xm12,x12 - zeta,xm2m1 + zeta + 1,x1,xm1,x2,xm2,zeta^2 + zeta + 1] >
>
];

