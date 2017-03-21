freeze;

import "../l3.m": R, x1, xm1, x2, xm2, x12, xm12, xm21, xm2m1, xcom, zeta;

psu32presentations := [
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 13, 17)(2, 14, 8, 5)(3, 18)(4, 10, 19, 11)(7, 20, 21, 16)(9, 15) >,
    Group<a,b | [ a^4, b^4, b^-1 * a^-2 * b * a * b^2 * a^-1, a^-1 * b^-2 * a^-2 * b * a^-1 * b^-1 ] >,
    ideal< R | [xcom + zeta,x12 + zeta + 1,xm12 + zeta + 1,xm21 - zeta,xm2m1 - zeta,x1 - zeta,xm1 + zeta + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 20, 16)(2, 14, 9, 5)(3, 18, 11, 19)(4, 10)(7, 13, 12, 17)(8, 15) >,
    Group<a,b | [ a^4, b^4, b * a^-2 * b^-1 * a^-1 * b^2 * a, a^-1 * b^-2 * a^-2 * b * a * b ] >,
    ideal< R | [xcom - zeta - 1,x12 - 1,xm12 - 1,xm21 - 1,xm2m1 - 1,x1 - zeta,xm1 + zeta + 1,x2 - zeta,xm2 + zeta + 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 12, 20)(2, 18, 9, 4)(3, 14)(5, 10, 15, 11)(7, 17, 16, 21)(8, 19) >,
    Group<a,b | [ a^4, b^4, b^-1 * a^-2 * b * a^-1 * b^2 * a, a^-1 * b^-2 * a^-2 * b^-1 * a * b^-1 ] >,
    ideal< R | [xcom + zeta,x12 - zeta,xm12 - zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 - zeta,xm1 + zeta + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>,
<
    PermutationGroup< 21 | (2, 3)(4, 5)(6, 12, 7, 13)(8, 10, 9, 11)(14, 18, 15, 19)(16, 20, 17, 21), (1, 6, 17, 21)(2, 18, 8, 4)(3, 14, 11, 15)(5, 10)(7, 12, 13, 20)(9, 19) >,
    Group<a,b | [ a^4, b^4, b * a^-2 * b^-1 * a * b^2 * a^-1, a^-1 * b^-2 * a^-2 * b^-1 * a^-1 * b ] >,
    ideal< R | [xcom - zeta - 1,x12 - zeta,xm12 - zeta,xm21 + zeta + 1,xm2m1 + zeta + 1,x1 - zeta,xm1 + zeta + 1,x2 - 1,xm2 - 1,zeta^2 + zeta + 1] >
>
];

