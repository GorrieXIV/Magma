freeze;

import "l2.m":
    x,
    characteristic,
    dimensionOverField,
    quotientDimensionOverField;

/* check whether the trace tuple defined by P is dihedral.
 *
 * Cf. Proposition~6.3.
 */
isDihedral := function(P)
    R := Generic(P);
    m := Round(Log(2, Rank(R) + 1));

    for j in [SetToSequence(s) : s in Subsets({1..m}) | #s ne 0] do
        dihedral := true;
        for i in [[k] : k in [1..m]]
                cat [[1,k] : k in [2..m]]
                cat [[2,k] : k in [3..m]]
                cat [[1,2,k] : k in [3..m]] do
            intersection := [k : k in j | k in i];

            if (#intersection mod 2) eq 1 and not x(R, i) in P then
                dihedral := false;
                break;
            end if;
        end for;

        if dihedral then
            return true;
        end if;
    end for;

    return false;
end function;


/* Let Delta: F_m \to \SL(2, K) be the representation corresponding to P.
 * Return the trace polynomials (reduced modulo P) describing
 * theta_B(X) = (tr(X), tr(B[1]*X), tr(B[2]*X), tr(B[1]*B[2]*X)).
 * This four-tuple describes X uniquely.
 *
 * Cf. Section~10 in the paper.
 */
theta := function(B, X, P)
    F := Parent(X);
    R := Generic(P);

    return [NormalForm(R!L2TracePolynomial(b*X : I := P), P) :
        b in [B[1]^0, B[1], B[2], B[1]*B[2]]];
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  (true, b) if the first two generators generate a Klein four group, with
 *      b = (G.1, G.2)
 *  false otherwise.
 */
subgroupIsV4 := function(P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := FreeGroup(m);

    x1 := NormalForm(x(R, [1]), P);
    x2 := NormalForm(x(R, [2]), P);
    x12 := NormalForm(x(R, [1,2]), P);

    if x1 in P and x2 in P and x12 in P then
        return true, [F.1, F.2];
    else
        return false, _;
    end if;
end function;

/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  (true, b)
 *      if the first two generators generate a symmetric group on 3 letters,
 *      with b a pair of words which map onto generators of D_6,
 *      both of order 2, such that the product has trace 1
 *  false
 *      otherwise.
 */
subgroupIsS3 := function(P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := FreeGroup(m);

    x1 := NormalForm(x(R, [1]), P);
    x2 := NormalForm(x(R, [2]), P);
    x12 := NormalForm(x(R, [1,2]), P);

    // Up to automorphisms, there are three generating sets of S_3 on two
    // elements.
    if x1 in P and x2 in P and x12^2 - 1 in P then
        // < (1,2), (2,3) >
        if x12 - 1 in P then
            B := [F.1, F.2];
        else
            // F_1^2 maps onto -I_2
            B := [F.1^3, F.2];
        end if;
    elif x1 in P and x2^2 - 1 in P and x12 in P then
        // < (1,2), (1,2,3) >
        if x2-1 in P then
            B := [F.1^3, F.1*F.2];
        else
            B := [F.1, F.1*F.2];
        end if;
    elif x1^2 - 1 in P and x2 in P and x12 in P then
        // < (1,2,3), (1,2) >
        if x1 - 1 in P then
            B := [F.1*F.2, F.2^3];
        else
            B := [F.1*F.2, F.2];
        end if;
    else
        return false, _;
    end if;

    return true, B;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  (true, b)
 *      if the first two generators generate a dihedral group of order 8,
 *      with b a pair of words which map onto generators of V_4
 *      (although there are two non-conjugate subgroups of D_8 isomorphic to
 *      V_4, it suffices to consider only one of them; this is taken care of in
 *      the isS4 function, which checks for every possible V4)
 *  false
 *      otherwise.
 */
subgroupIsD8 := function(P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := FreeGroup(m);

    x1 := NormalForm(x(R, [1]), P);
    x2 := NormalForm(x(R, [2]), P);
    x12 := NormalForm(x(R, [1,2]), P);

    // Up to automorphisms, there are three generating sets of D_8 on two
    // elements.
    if x1 in P and x2 in P and x12^2 - 2 in P then
        // < (1,3), (1,2)(3,4) >
        B := [F.1, (F.1*F.2)^2];
    elif x1 in P and x2^2 - 2 in P and x12 in P then
        // < (1,3), (1,2,3,4) >
        B := [F.1, F.2^2];
    elif x1^2 - 2 in P and x2 in P and x12 in P then
        // < (1,2,3,4), (1,3) >
        B := [F.2, F.1^2];
    else
        return false, _;
    end if;

    return true, B;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  (true, b)
 *      if the first two generators generate a dihedral group of order 10,
 *      with b a pair of words which map onto involutions generating D_{10}
 *      such that tr(b[1]*b[2]) is a zero of x^2 + x - 1
 *  false
 *      otherwise.
 */
subgroupIsD10 := function(P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := FreeGroup(m);

    x1 := NormalForm(x(R, [1]), P);
    x2 := NormalForm(x(R, [2]), P);
    x12 := NormalForm(x(R, [1,2]), P);

    // Up to automorphisms, there are three generating sets of D_10 on two
    // elements.
    if x1 in P and x2 in P and x12^4 - 3*x12^2 + 1 in P then
        if x12^2 + x12 - 1 in P then
            B := [F.1, F.2];
        else
            B := [F.1^3, F.2];
        end if;
    elif x1 in P and x2^4 - 3*x2^2 + 1 in P and x12 in P then
        if x2^2 + x2 - 1 in P then
            B := [F.1^3, F.1*F.2];
        else
            B := [F.1, F.1*F.2];
        end if;
    elif x1^4 - 3*x1^2 + 1 in P and x2 in P and x12 in P then
        if x1^2 + x1 - 1 in P then
            B := [F.1*F.2, F.2^3];
        else
            B := [F.1*F.2, F.2];
        end if;
    else
        return false, _;
    end if;

    return true, B;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  (true, b)
 *      if the first two generators generate an algernating group on four
 *      letters, with b a pair of words which map onto generators of V_4
 *  false
 *      otherwise.
 */
subgroupIsA4 := function(P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := FreeGroup(m);

    x1 := NormalForm(x(R, [1]), P);
    x2 := NormalForm(x(R, [2]), P);
    x12 := NormalForm(x(R, [1,2]), P);

    // Up to automorphisms, there are four generating sets of A_4 on two
    // elements.
    if x1 in P and x2^2 - 1 in P and x12^2 - 1 in P then
        // < (1,2)(3,4), (1,2,3) >
        B := [F.1, F.2^-1*F.1*F.2];
    elif x1^2-1 in P and x2 in P and x12^2 - 1 in P then
        // < (1,2,3), (1,2)(3,4) >
        B := [F.2, F.1^-1*F.2*F.1];
    elif x1^2-1 in P and x2^2-1 in P and x12 in P then
        // < (1,2,3), (2,3,4) >
        B := [F.1*F.2, F.2*F.1];
    elif x1^2-1 in P and x2^2-1 in P and x12^2-1 in P then
        // < (1,2,3), (2,4,3) >
        B := [F.1*F.2^-1, F.2^-1*F.1];
    else
        return false, _;
    end if;

    return true, B;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  (true, b)
 *      if the first two generators generate a symmetric group on four letters,
 *      with b a pair of words which map onto generators of V_4
 *  false
 *      otherwise.
 */
subgroupIsS4 := function(P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := FreeGroup(m);

    x1 := NormalForm(x(R, [1]), P);
    x2 := NormalForm(x(R, [2]), P);
    x12 := NormalForm(x(R, [1,2]), P);

    // Up to automorphisms, there are nine generating sets of S_4 on two
    // elements.
    if x1 in P and x2^2 - 1 in P and x12^2 - 2 in P then
        // < (1,2), (2,3,4) >
        B := [(F.1*F.2)^2, (F.1*F.2^-1)^2];
    elif x1^2 - 1 in P and x2 in P and x12^2 - 2 in P then
        // < (2,3,4), (1,2) >
        B := [(F.1*F.2)^2, (F.1^-1*F.2)^2];
    elif x1 in P and x2^2 - 2 in P and x12^2 - 1 in P then
        // < (1,2), (1,2,3,4) >
        B := [F.2^2, F.1*F.2^2*F.1];
    elif x1^2 - 2 in P and x2 in P and x12^2 - 1 in P then
        // < (1,2,3,4), (1,2) >
        B := [F.1^2, F.2*F.1^2*F.2];
    elif x1^2 - 1 in P and x2^2 - 2 in P and x12 in P then
        // < (1,2,3), (1,4,3,2) >
        B := [F.2^2, F.1*F.2^2*F.1^-1];
    elif x1^2 - 2 in P and x2^2 - 1 in P and x12 in P then
        // < (1,4,3,2), (1,2,3) >
        B := [F.1^2, F.2*F.1^2*F.2^-1];
    elif x1^2 - 1 in P and x2^2 - 2 in P and x12 - x1*x2 in P then
        // < (1,2,3), (1,2,3,4) >
        B := [F.2^2, F.1*F.2^2*F.1^-1];
    elif x1^2 - 2 in P and x2^2 - 1 in P and x12 - x1*x2 in P then
        // < (1,2,3,4), (1,2,3) >
        B := [F.1^2, F.2*F.1^2*F.2^-1];
    elif x1^2 - 2 in P and x2 - x1*x12 in P and x12^2 - 1 in P then
        // < (1,2,3,4), (1,2,4,3) >
        B := [F.1^2, F.2^2];
    else
        return false, _;
    end if;

    return true, B;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  (true, b)
 *      if the first two generators generate a alternating group on five
 *      letters, with b a pair of words which map onto generators of a V_4
 *  false
 *      otherwise.
 */
subgroupIsA5 := function(P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := FreeGroup(m);

    x1 := NormalForm(x(R, [1]), P);
    x2 := NormalForm(x(R, [2]), P);
    x12 := NormalForm(x(R, [1,2]), P);

    // Up to automorphisms, there are 19 generating sets of A_5 on two elements.
    if x1^2 - 1 in P and x2^4 - 3*x2^2 + 1 in P
            and x12 - x2^3*x1 + 2*x2*x1 in P then
        // (1, 2, 3), (1, 4, 5, 3, 2)
        B := [ F.1^-1 * F.2^2, F.1 * F.2 * F.1^-1 * F.2 * F.1^-1 ];
    elif x1^2 - 1 in P and x2 in P and x12^4 - 3*x12^2 + 1 in P then
        // (1, 2, 3), (1, 4)(3, 5)
        B := [F.1*F.2*F.1^-1,F.1^-1*F.2*F.1^-1*F.2*F.1*F.2*F.1^-1*F.2];
    elif x1^2 - 1 in P and x2^2 - 1 in P and x12^2 - x12*x2*x1 - 1 in P then
        // (1, 2, 3), (1, 5, 4)
        B := [F.1*F.2*F.1*F.2*F.1,F.1*F.2^-1*F.1*F.2^-1*F.1];
    elif x1^2 - 1 in P and x2^4 - 3*x2^2 + 1 in P and x12 - x2*x1 in P then
        // (1, 2, 3), (1, 4, 2, 5, 3)
        B := [ F.1^-1 * F.2, F.1 * F.2 * F.1 * F.2^-2 * F.1^-1 * F.2^-1 ];
    elif x1^2 - 1 in P and x2^4 - 3*x2^2 + 1 in P
            and x12 + x2^3*x1 - 3*x2*x1 in P then
        // (1, 2, 3), (1, 5, 4, 2, 3)
        B := [ F.1 * F.2^2, F.1^-1 * F.2 * F.1 * F.2 * F.1 ];
    elif x1^2 - 1 in P and x2^4 - 3*x2^2 + 1 in P and x12 in P then
        // (1, 2, 3), (1, 5, 3, 2, 4)
        B := [ F.1 * F.2^-1 * F.1, F.2^2 * F.1^-1 * F.2^2 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2^2 - 1 in P
            and x12 - x2*x1^3 + 2*x2*x1 in P then
        // (1, 4, 5, 3, 2), (1, 2, 3)
        B := [ F.1^-2 * F.2, F.1 * F.2^-1 * F.1^-1 * F.2 * F.1 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2^2 - 1 in P
            and x12 + x2*x1^3 - 3*x2*x1 in P then
        // (1, 4, 5, 3, 2), (1, 3, 2)
        B := [ F.1^-2 * F.2^-1, F.1 * F.2 * F.1^-1 * F.2^-1 * F.1 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2^2 + x1^2 - 3 in P and x12 in P then
        // (1, 4, 5, 3, 2), (1, 5, 4, 3, 2)
        B := [ F.1^2 * F.2 * F.1^-1, F.1^-2 * F.2^2 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2^2 - 1 in P and x12 in P then
        // (1, 4, 5, 3, 2), (2, 3, 4)
        B := [ F.1^-2 * F.2^-1 * F.1, F.1 * F.2 * F.1^-1 * F.2 * F.1^-1 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2 in P and x12^2 - 1 in P then
        // (1, 4, 5, 3, 2), (1, 4)(3, 5)
        B := [ F.2^F.1, F.1^2 * F.2 * F.1^2 * F.2 * F.1^-1 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2^2 - 1 in P and x12 - x2*x1 in P then
        // (1, 4, 5, 3, 2), (2, 4, 3)
        B := [ F.1^-2 * F.2 * F.1, F.1 * F.2 * F.1^2 * F.2^-1 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2 in P and x12^2 + x1^2 - 3 in P then
        // (1, 4, 5, 3, 2), (1, 3)(2, 4)
        B := [ F.1^2 * F.2 * F.1^-2, F.2 * F.1^-1 * F.2 * F.1 * F.2 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2^2 - x1^2 in P
            and x12 - x2*x1^3 + 2*x2*x1 in P then
        // (1, 4, 5, 3, 2), (1, 4, 2, 5, 3)
        B := [ F.1^-2 * F.2, F.2 * F.1 * F.2^2 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2^2 - x1^2 in P
            and x12 + x2*x1^3 - 3*x2*x1 in P then
        // (1, 4, 5, 3, 2), (1, 5, 4, 2, 3)
        B := [ F.1 * F.2 * F.1, F.1 * F.2^-1 * F.1 * F.2^-1 * F.1 ];
    elif x1^4 - 3*x1^2 + 1 in P and x2^2 + x1^2 - 3 in P
            and x12 - x2*x1 in P then
        // (1, 4, 5, 3, 2), (1, 3, 2, 5, 4)
        B := [ F.1^2 * F.2^2, F.1^-2 * F.2 * F.1 ];
    elif x1 in P and x2^4 - 3*x2^2 + 1 in P and x12^2 - 1 in P then
        // (1, 2)(3, 4), (1, 5, 4, 3, 2)
        B := [ F.2 * F.1 * F.2^-1, F.1 * F.2^2 * F.1 * F.2^-2 * F.1 ];
    elif x1 in P and x2^2 - 1 in P and x12^4 - 3*x12^2 + 1 in P then
        // (1, 2)(3, 4), (1, 5, 4)
        B := [F.2*F.1*F.2^-1,F.1*F.2*F.1*F.2^-1*F.1*F.2*F.1*F.2];
    elif x1 in P and x2^4 - 3*x2^2 + 1 in P and x12^2 + x2^2 - 3 in P then
        // (1, 2)(3, 4), (1, 4, 2, 5, 3)
        B := [ F.1 * F.2 * F.1 * F.2^-1 * F.1, F.1 * F.2^2 * F.1 * F.2^-1 ];
    else
        return false, _;
    end if;

    return true, B;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 *  t: Quadruple of trace polynomials describing theta_B(X).
 * Output:
 *  If B is absolutely irreducible and projectively generates a Klein four
 *  group, return true if X is in <B_1, B_2>, otherwise return false.
 *
 * Cf. Proposition 10.1, 1).
 */
isV4TracesByV4 := function(t, P)
    v4traces := [NormalForm(f, P) :
            f in [[Generic(P)!2,0,0,0],[0,Generic(P)!2,0,0],
                [0,0,Generic(P)!2,0],[0,0,0,Generic(P)!2]]];
    return [NormalForm(f, P) : f in t] in v4traces
        or [NormalForm(-f, P) : f in t] in v4traces;
end function;

/* Input:
 *  P: Prime ideal in \Phi_m.
 *  t: Quadruple of trace polynomials describing theta_B(X).
 * Output:
 *  If B is absolutely irreducible and projectively generates a Klein four
 *  group, return true if X is in the unique A_4 containing <B_1, B_2>,
 *  otherwise return false.
 *
 * Cf. Proposition 10.1, 1).
 */
isA4TracesByV4 := function(t, P)
    if isV4TracesByV4(t, P) then
        return true;
    elif t[1]^2 - 1 in P and t[2]^2 - 1 in P and t[3]^2 - 1 in P
            and t[4]^2 - 1 in P then
        return true;
    else
        return false;
    end if;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 *  t: Quadruple of trace polynomials describing theta_B(X).
 *         [we assume (tr(B_1), tr(B_2), tr(B_1*B_2)) = (0,0,1)]
 * Output:
 *  If B is absolutely irreducible and projectively generates a dihedral group
 *  of order 6, return true if X is in <B_1, B_2>, otherwise return false.
 */
isS3TracesByS3 := function(t, P)
    s3traces := [NormalForm(f, P) :
            f in [[Generic(P)!2,0,0,1],[1,0,0,-1],[-1,0,0,-2],
            [0,-2,1,0],[0,1,-2,0],[0,-1,-1,0]]];

    return [NormalForm(f, P) : f in t] in s3traces
        or [NormalForm(-f, P) : f in t] in s3traces;
end function;

/* Input:
 *  P: Prime ideal in \Phi_m.
 *  t: Quadruple of trace polynomials describing theta_B(X).
 *  alpha: a root of x^2 + x - 1
 *         [we assume (tr(B_1), tr(B_2), tr(B_1*B_2)) = (0,0,alpha)]
 * Output:
 *  If B is absolutely irreducible and projectively generates a dihedral group
 *  of order 10, return true if X is in <B_1, B_2>, otherwise return false.
 */
isD10TracesByD10 := function(t, P, alpha)
    d10traces := [NormalForm(f, P) :
            f in [[2,0,0,alpha],[alpha,0,0,-alpha-1],[-alpha-1,0,0,-alpha-1],
            [-alpha-1,0,0,alpha],[alpha,0,0,2],[0,-2,alpha,0],[0,alpha,-2,0],
            [0,-alpha-1,-alpha,0],[0,-alpha-1,alpha+1,0],[0,alpha,alpha+1,0]]];

    return [NormalForm(f, P) : f in t] in d10traces
        or [NormalForm(-f, P) : f in t] in d10traces;
end function;

/* Input:
 *  P: Prime ideal in \Phi_m.
 *  t: Quadruple of trace polynomials describing theta_B(X).
 *  alpha: a root of X^2 - 2
 * Output:
 *  We assume B is absolutely irreducible and projectively generates a symmetric
 *  group on three letters, otherwise the output is undefined.
 *  (true, i) if X lies in one of the two S_4's that contain the S_3 generated
 *      by B_1 and B_2; i specifies the type
 *  false otherwise.
 */
isStrictS4TracesByS3 := function(t, P, a)
    s4traces := [NormalForm(f, P) :
        f in [[1,-a,a,0],[-1,-a,a,-1],[a,1,-1,0],[a,-1,0,0],[a,1,0,a],[a,0,1,0],
        [0,-1,1,-a],[a,-1,1,a],[-a,0,1,-a],[0,a,0,1],[1,a,0,0],[-1,a,0,-1],
        [0,a,-a,-1],[1,0,-a,0],[1,0,a,1],[0,0,a,-1],[0,0,1,a],[0,1,0,-a]]];

    if [NormalForm(f, P) : f in t] in s4traces
            or [NormalForm(-f, P) : f in t] in s4traces then
        return true, 1;
    end if;

    s := [t[1], -t[2], -t[3], t[4]];
    if [NormalForm(f, P) : f in s] in s4traces
            or [NormalForm(-f, P) : f in s] in s4traces then
        return true, 2;
    end if;

    return false, _;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 *  t: Quadruple of trace polynomials describing theta_B(X).
 *  a: a root of X^2 - 2
 * Output:
 *  We assume B is absolutely irreducible and projectively generates a Klein
 *  four group, otherwise the output is undefined.
 *  (true, i) if X lies in one of the four S_4's that contain the Klein four
 *      group generated by B_1 and B_2 but not in V_4;
 *      i is an integer in [1..4] and specifies the type of the V_4
 *          1: < (1,2)(3,4), (1,3)(2,4) >
 *          2: < (1,2)(3,4), (1,2) >
 *          3: < (1,2), (1,2)(3,4) >
 *          4: < (1,2), (3,4) >
 *          5: 1 or 2
 *          6: 1 or 3
 *          7: 1 or 4
 *  false otherwise.
 *
 * Cf. Proposition 10.1, 1).
 */
isStrictS4TracesByV4 := function(t, P, a)
    // < (12)(34), (13)(24) >
    s4traces := [NormalForm(f, P) :
            f in [[Generic(P)!1,1,1,1],[-1,1,1,1],[1,-1,1,-1],[1,-1,1,1],
            [-1,-1,1,-1],[1,-1,-1,1],[1,1,1,-1],[-1,-1,1,1]]];
    if [NormalForm(f, P) : f in t] in s4traces
            or [NormalForm(-f, P) : f in t] in s4traces then
        return true, 1;
    end if;

    // < (12), (12)(34) >
    s4traces := [NormalForm(f, P) :
            f in [[1,a,-1,0],[-1,a,-1,0],[a,-1,0,-1],[a,1,0,-1],[a,-1,0,1],
            [0,1,-a,-1],[a,1,0,1],[0,1,-a,1],[1,-a,-1,0],[1,0,-1,-a],
            [-1,-a,-1,0],[1,0,1,-a],[1,0,-1,a],[-1,0,-1,-a],[0,-1,-a,1],
            [0,-1,-a,-1]]];
    if [NormalForm(f, P) : f in t] in s4traces
            or [NormalForm(-f, P) : f in t] in s4traces then
        return true, 2;
    end if;

    s4traces := [NormalForm(f, P) :
            f in [[a,0,-a,0],[-a,0,-a,0],[0,-a,0,a],[0,-a,0,-a]]];
    if [NormalForm(f, P) : f in t] in s4traces
            or [NormalForm(-f, P) : f in t] in s4traces then
        return true, 5;
    end if;


    // < (12)(34), (12) >
    s4traces := [NormalForm(f, P) :
            f in [[1,-1,a,0],[-1,-1,a,0],[a,0,-1,1],[a,0,1,1],[a,0,-1,-1],
            [0,-a,1,1],[a,0,1,-1],[0,-a,1,-1],[1,-1,-a,0],[1,-1,0,a],
            [-1,-1,-a,0],[1,1,0,a],[1,-1,0,-a],[-1,-1,0,a],[0,-a,-1,-1],
            [0,-a,-1,1]]];
    if [NormalForm(f, P) : f in t] in s4traces
            or [NormalForm(-f, P) : f in t] in s4traces then
        return true, 3;
    end if;
    s4traces := [NormalForm(f, P) :
            f in [[a,-a,0,0],[-a,-a,0,0],[0,0,-a,-a],[0,0,-a,a]]];
    if [NormalForm(f, P) : f in t] in s4traces
            or [NormalForm(-f, P) : f in t] in s4traces then
        return true, 6;
    end if;

    // < (12), (34) >
    s4traces := [NormalForm(f, P) :
            f in [[1,a,0,1],[-1,a,0,1],[a,-1,-1,0],[a,1,-1,0],[a,-1,1,0],
            [0,1,-1,a],[a,1,1,0],[0,1,1,a],[1,-a,0,1],[1,0,-a,1],[-1,-a,0,1],
            [1,0,-a,-1],[1,0,a,1],[-1,0,-a,1],[0,-1,1,a],[0,-1,-1,a]]];
    if [NormalForm(f, P) : f in t] in s4traces
            or [NormalForm(-f, P) : f in t] in s4traces then
        return true, 4;
    end if;
    s4traces := [NormalForm(f, P) :
            f in [[a,0,0,a],[-a,0,0,a],[0,-a,a,0],[0,-a,-a,0]]];
    if [NormalForm(f, P) : f in t] in s4traces
            or [NormalForm(-f, P) : f in t] in s4traces then
        return true, 7;
    end if;

    return false, _;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 *  t: Quadruple of trace polynomials describing theta_B(X).
 * Output:
 *  We assume B is absolutely irreducible and projectively generates a Klein
 *  four group, otherwise the output is undefined.
 *  (true, alpha) if X lies in one of the two A_5's that contain the Klein four
 *      generated by B_1 and B_2, but not in the unique A_4 containing V_4;
 *      alpha is one of the four roots of (X^2 + X - 1)*(X^2 - X - 1), and
 *      specifies which of the two A_5's the element belongs to
 *  false otherwise.
 */
isStrictA5TracesByV4 := function(t, P, a)
    // < (1,2)(3,4), (1,3)(2,4) >
    a5traces := [NormalForm(f, P) :
            f in [[1,a,0,-a-1],[1,-a,0,a+1],[a,-1,a+1,0],[-a,-1,-a-1,0],
            [-1,-a,0,-a-1],[-a-1,-a,1,0],[a,0,-1,-a-1],[-a,a+1,0,-1],
            [-a-1,a,-1,0],[-a,-1,a+1,0],[0,a,a+1,1],[-a,-a-1,0,-1],
            [a,0,1,-a-1],[a+1,-1,0,-a],[a,0,1,a+1],[a+1,1,0,a],[a,-1,-a-1,0],
            [a,-a-1,0,-1],[0,a,-a-1,1],[-a-1,-a,-1,0],[-a,-a-1,0,1],
            [-1,a,0,a+1],[a,0,-1,a+1],[-a-1,a,1,0],[0,-a,a+1,1],[-1,-a-1,a,0],
            [0,-a,-a-1,1],[1,-a-1,-a,0],[-a-1,-1,0,a],[0,-1,a,a+1],
            [-a-1,0,-a,-1],[0,-1,a,-a-1],[1,0,-a-1,a],[-1,-a-1,-a,0],
            [0,-a-1,1,a],[-1,0,-a-1,-a], [-a-1,0,a,-1],[-a-1,0,a,1],
            [1,-a-1,a,0],[1,0,a+1,-a],[0,-a-1,-1,a],[1,0,-a-1,-a],[0,1,a,a+1],
            [-a-1,1,0,-a],[-a-1,0,-a,1],[0,1,a,-a-1],[0,a+1,-1,a],[0,a+1,1,a]]];
    if [NormalForm(f, P) : f in t] in a5traces
            or [NormalForm(-f, P) : f in t] in a5traces then
        return true, 1;
    end if;

    // < (1,2)(3,4), (1,4)(2,3) >
    a5traces := [NormalForm(f, P) :
            f in [[1,a,-a-1,0],[1,-a,a+1,0],[a,-1,0,-a-1],[-a,-1,0,a+1],
            [-1,-a,-a-1,0],[-a-1,-a,0,-1],[a,0,-a-1,1],[-a,a+1,-1,0],
            [-a-1,a,0,1],[-a,-1,0,-a-1],[0,a,1,-a-1],[-a,-a-1,-1,0],
            [a,0,-a-1,-1],[a+1,-1,-a,0],[a,0,a+1,-1],[a+1,1,a,0],[a,-1,0,a+1],
            [a,-a-1,-1,0],[0,a,1,a+1],[-a-1,-a,0,1],[-a,-a-1,1,0],[-1,a,a+1,0],
            [a,0,a+1,1],[-a-1,a,0,-1], [0,-a,1,-a-1],[-1,-a-1,0,-a],
            [0,-a,1,a+1],[1,-a-1,0,a],[-a-1,-1,a,0],[0,-1,a+1,-a],
            [-a-1,0,-1,a],[0,-1,-a-1,-a],[1,0,a,a+1],[-1,-a-1,0,a],
            [0,-a-1,a,-1],[-1,0,-a,a+1], [-a-1,0,-1,-a],[-a-1,0,1,-a],
            [1,-a-1,0,-a],[1,0,-a,-a-1],[0,-a-1,a,1],[1,0,-a,a+1],[0,1,a+1,-a],
            [-a-1,1,-a,0],[-a-1,0,1,a],[0,1,-a-1,-a],[0,a+1,a,1],[0,a+1,a,-1]]];
    if [NormalForm(f, P) : f in t] in a5traces
            or [NormalForm(-f, P) : f in t] in a5traces then
        return true, 2;
    end if;

    return false, _;
end function;


/* Input:
 *  t: Quadruple of trace polynomials describing theta_B(X).
 *  P: Prime ideal in \Phi_m.
 *  a: a root of x^2 + x - 1
 * Output:
 *  We assume B is absolutely irreducible and projectively generates a symmetric
 *  group on three letters, otherwise the output is undefined.
 *  (true, i) if X lies in one of the two A_5's that contain the symmetric group
 *      generated by B_1 and B_2, but not in S_3
 *      i specifies which of the two A_5's X belongs to.
 *  false otherwise.
 */
isStrictA5TracesByS3 := function(t, P, a)
    a5traces := [NormalForm(f, P):
            f in [[1,0,1,-a],[1,0,-1,a+1],[0,0,-a-1,-a],[a,-a-1,0,0],
            [-a,a+1,-a-1,-a],[-a-1,-1,0,-1],[a,1,0,-1],[-a,0,a+1,-a],
            [-a-1,1,0,-a],[1,-1,a+1,0],[-a,-a-1,0,-a],[0,-a-1,1,1],
            [-a,0,-1,-a-1],[a,-1,1,-1],[-1,-1,a+1,-1], [a+1,0,-a,0],
            [a,-1,0,a+1],[a+1,0,a,a+1],[-1,-1,-a,0],[a,a+1,-a-1,0],[a,0,-1,-1],
            [0,a+1,-a,1],[-a-1,1,-1,-1],[-a,0,-a-1,0],[-1,1,a,-1],[a,1,-1,a+1],
            [-a-1,-1,1,-a],[0,-a-1,0,a],[1,-1,1,a+1],[-1,-a,-1,-1],
            [0,a+1,-a-1,a],[1,a,-a-1,0],[-1,1,0,a],[-a-1,0,-1,-a],[0,-a,-1,1],
            [-a-1,a,0,-a-1],[1,1,-1,-a],[0,-a,0,-a-1],[1,a+1,-1,1],
            [-1,a,-a-1,-1],[-1,a+1,-a,-1],[-a-1,-a,a,-a-1],[-a-1,-a,0,0],
            [0,0,a,-a-1],[1,-a,-1,0], [1,-a-1,1,0],[1,1,0,a+1],[1,a+1,-a,0],
            [0,-a,a,a+1],[-a-1,0,1,-1],[-a-1,a,-a,0],[0,-a,a+1,-1],[0,1,a,1],
            [0,-1,a+1,1]]];

    if [NormalForm(f, P) : f in t] in a5traces
            or [NormalForm(-f, P) : f in t] in a5traces then
        return true, 1;
    end if;

    s := [t[1], -t[2], -t[3], t[4]];
    if [NormalForm(f, P) : f in s] in a5traces
            or [NormalForm(-f, P) : f in s] in a5traces then
        return true, 2;
    end if;

    return false, _;
end function;

/* Input:
 *  t: Quadruple of trace polynomials describing theta_B(X).
 *  P: Prime ideal in \Phi_m.
 *  a: a root of x^2 + x - 1
 * Output:
 *  We assume B is absolutely irreducible and projectively generates a dihedral
 *  group of order 10, otherwise the output is undefined.
 *  (true, i) if X lies in one of the four A_5's that contain the dihedral group
 *      generated by B_1 and B_2, but not in D_10
 *      i specifies which of the four A_5's X belongs to.
 *  false otherwise.
 */
isStrictA5TracesByD10 := function(t, P, a)
    a5traces := [NormalForm(f, P) :
            f in [[1,a,a,-1],[1,-a,-a,a+1],[a,-1,a+1,1],[-a,-1,-1,-1],
            [-1,-a,1,-a-1],[-a-1,-a,1,0],[-a,a+1,0,-1],[-a-1,a,-1,-1],[1,1,1,0],
            [-a,-1,a+1,a],[0,a,a,a+1],[-a,-a-1,1,-1],[a,0,a+1,-a],[-1,1,1,-a],
            [a+1,-1,a,0], [a+1,1,-a,1],[-1,-1,a,1],[a,-1,-1,-a],[a,-a-1,1,-a],
            [-a-1,-a,-a,-1],[-a,-a-1,0,a],[-1,1,-a,-a-1],[-1,a,-1,1],
            [a,0,-a-1,1],[-a-1,a,a,0],[0,-a,1,a+1],[1,1,0,a+1],[-1,-a-1,1,0],
            [1,-a-1,0,0],[-1,1,-a-1,0], [-a-1,-1,0,0],[0,-1,0,a+1],[1,-1,0,-1],
            [0,-1,a+1,-1],[1,0,-a-1,0],[-1,-a-1,0,-a],[0,-a-1,1,1],
            [-1,0,-1,-a-1],[-a-1,0,1,-1],[0,0,1,-a-1],[1,-a-1,1,a],[1,0,a+1,a],
            [1,1,-a-1,a],[1,0,-1,-1], [0,1,-a,a+1],[-a-1,1,0,-1],[-a-1,0,-1,0],
            [0,1,1,-1],[0,0,-a-1,-1],[0,a+1,0,1]]];

    if [NormalForm(f, P) : f in t] in a5traces
            or [NormalForm(-f, P) : f in t] in a5traces then
        return true, 1;
    end if;

    s := [t[1], -t[2], -t[3], t[4]];
    if [NormalForm(f, P) : f in s] in a5traces
            or [NormalForm(-f, P) : f in s] in a5traces then
        return true, 2;
    end if;

    a5traces := [NormalForm(f, P) :
            f in [[1,a,0,0],[1,-a,0,-a-1],[a,-1,-a-1,-1],[-a,-1,0,1],
            [-1,-a,-1,a+1],[-a-1,-a,-1,1],[-a,a+1,1,1],[-a-1,a,1,a+1],
            [1,1,0,-a],[-a,-1,-a-1,0],[0,a,0,-1],[-a,-a-1,-a-1,1],[a,0,-1,0],
            [-1,1,0,1],[a+1,-1,-1,-1], [a+1,1,1,-a-1],[-1,-1,-1,0],[a,-1,0,0],
            [a,-a-1,-a-1,0],[-a-1,-a,0,a+1],[-a,-a-1,-1,0],[-1,1,1,a+1],
            [-1,a,1,0],[a,0,1,-1],[-a-1,a,0,1],[0,-a,-1,-1],[1,1,a,-a-1],
            [-1,-a-1,-a-1,a],[1,-a-1,-1,-a],[-1,1,a+1,a], [-a-1,-1,-a,1],
            [0,-1,-a,-1],[1,-1,-a,0],[0,-1,-a-1,a],[1,0,1,-a],[-1,-a-1,-1,1],
            [0,-a-1,-a-1,-a],[-1,0,a,a+1],[-a-1,0,-a,a+1],[0,0,-a,1],
            [1,-a-1,-a-1,-1],[1,0,-1,-1],[1,1,a+1,-1],[1,0,a,0],[0,1,1,-1],
            [-a-1,1,a,a+1],[-a-1,0,a,1],[0,1,0,a],[0,0,1,a],[0,a+1,1,-a]]];

    if [NormalForm(f, P) : f in t] in a5traces
            or [NormalForm(-f, P) : f in t] in a5traces then
        return true, 3;
    end if;

    s := [t[1], -t[2], -t[3], t[4]];
    if [NormalForm(f, P) : f in s] in a5traces
            or [NormalForm(-f, P) : f in s] in a5traces then
        return true, 4;
    end if;

    return false, _;
end function;



/* Input:
 *  t: a quadruple of polynomials
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  alpha: a root of X^2 - 2 (if one of the four entries is a root of X^2 - 2),
 *      or zero
 */
rootOfPsi4 := function(t, P)
    for i in [1..4] do
        if t[i]^2 - 2 in P then
            return t[i];
        end if;
    end for;

    return 0;
end function;

/* Input:
 *  t: a quadruple of polynomials
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  alpha: a root of X^2 + X - 1 (if one of the four entries is a root of
 *      (X^2 + X - 1)*(X^2 - X - 1)), or zero
 */
rootOfPsi5 := function(t, P)
    alpha := 0;
    for i in [1..4] do
        if t[i]^2 + t[i] - 1 in P then
            return t[i];
        elif t[i]^2 - t[i] - 1 in P then
            return -t[i];
        end if;
    end for;

    return 0;
end function;

isS4ByV4 := function(B, P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := Parent(B[1]);

    // find the first generator that is not in the subgroup V_4
    k := 0;
    for i in [1..m] do
        if not isV4TracesByV4(theta(B, F.i, P), P) then
            k := i;
            break;
        end if;
    end for;

    t := theta(B, F.k, P);
    // find a generator which is not in A4, to get a root of X^2 - 2
    // if there is a generator which is in A4 without V4, then the only possible
    // type is 1
    typ := 0;
    while isA4TracesByV4(t, P) do
        typ := 1;
        k +:= 1;
        t := theta(B, F.k, P);
    end while;

    // if the group is 2.S4, then at least one of the entries must be a root of
    // X^2 - 2
    alpha := rootOfPsi4(t, P);

    if alpha eq 0 then
        return false;
    end if;

    for i in [k..m] do
        // generator i should be either in V_4 or in S_4 without V_4
        // in the latter case, we have to check that the type of S_4 matches
        // with that of the other generators
        if isV4TracesByV4(theta(B, F.i, P), P) then
            continue;
        end if;

        ins4, typ2 := isStrictS4TracesByV4(theta(B, F.i, P), P, alpha);

        if not ins4 then
            return false;
        end if;

        if typ eq typ2 then
            continue;
        elif typ eq 0 then
            // this was the first generator in S4 without V4
            typ := typ2;
            continue;
        elif (typ eq 5 and typ2 in [1,2]) or (typ eq 6 and typ2 in [1,3])
                or (typ eq 7 and typ2 in [1,4]) then
            // the first generator didn't uniquely specify the type, but now we
            // know
            typ := typ2;
            continue;
        elif (typ eq 5 and typ2 in [6,7]) or (typ eq 6 and typ2 in [7,5])
                or (typ eq 7 and typ2 in [5,6]) then
            // the first generator didn't uniquely specify the type, but now we
            // know
            typ := 1;
            continue;
        elif (typ in [1,2] and typ2 eq 5) or (typ in [1,3] and typ2 eq 6)
                or (typ in [1,4] and typ2 eq 7) then
            continue;
        else
            return false;
        end if;
    end for;

    return true;
end function;

isS4ByS3 := function(B, P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := Parent(B[1]);

    // find the first generator that is not in the subgroup S_3
    k := 0;
    for i in [3..m] do
        if not isS3TracesByS3(theta(B, F.i, P), P) then
            k := i;
            break;
        end if;
    end for;

    t := theta(B, F.k, P);

    // if the group is 2.S4, then at least one of the entries must be a root of
    // x^2 - 2
    alpha := rootOfPsi4(t, P);

    if alpha eq 0 then
        return false;
    end if;

    ins4, typ := isStrictS4TracesByS3(t, P, alpha);

    if not ins4 then
        return false;
    end if;

    for i in [k+1..m] do
        // generator i should be either in S_3 or in S_4 without S_3;
        // in the latter case, we have to check that the type of S_4 matches
        // with that of the other generators
        if isS3TracesByS3(theta(B, F.i, P), P) then
            continue;
        end if;

        ins4, typ2 := isStrictS4TracesByS3(theta(B, F.i, P), P, alpha);

        if not ins4 then
            return false;
        end if;

        // ensure that the generators lie in the _same_ S_4, by checking that
        // the alpha's are the same
        if typ ne typ2 then
            return false;
        end if;
    end for;

    return true;
end function;

isA5ByV4 := function(B, P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := Parent(B[1]);

    // find the first generator that is not in the subgroup A_4
    k := 0;
    for i in [1..m] do
        if not isA4TracesByV4(theta(B, F.i, P), P) then
            k := i;
            break;
        end if;
    end for;

    t := theta(B, F.k, P);
    alpha := rootOfPsi5(t, P);
    if alpha eq 0 then
        return false;
    end if;

    ina5, typ := isStrictA5TracesByV4(t, P, alpha);

    if not ina5 then
        return false;
    end if;


    for i in [k+1..m] do
        // generator i should be either in A_4 or in A_5 without A_4;
        // in the latter case, we have to check that the type of A_5 matches
        // with that of the other generators
        if isA4TracesByV4(theta(B, F.i, P), P) then
            continue;
        end if;

        ina5, typ2 := isStrictA5TracesByV4(theta(B, F.i, P), P, alpha);

        // ensure that the generators lie in the _same_ A_5
        if not ina5 or typ ne typ2 then
            return false;
        end if;
    end for;

    return true;
end function;


isA5ByS3 := function(B, P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := Parent(B[1]);

    // find the first generator that is not in the subgroup S_3
    k := 0;
    for i in [1..m] do
        if not isS3TracesByS3(theta(B, F.i, P), P) then
            k := i;
            break;
        end if;
    end for;

    t := theta(B, F.k, P);

    // if the group is 2.A5, then at least one of the entries must be a root of
    // x^2 + x - 1 or x^2 - x - 1;
    // set alpha to be one of the roots of x^2 + x + 1
    alpha := rootOfPsi5(t, P);

    if alpha eq 0 then
        return false;
    end if;

    ina5, typ := isStrictA5TracesByS3(t, P, alpha);

    if not ina5 then
        return false;
    end if;


    for i in [k+1..m] do
        // generator i should be either in S_3 or in S_4 without S_3;
        // in the latter case, we have to check that the type of S_4 matches
        // with that of the other generators
        if isS3TracesByS3(theta(B, F.i, P), P) then
            continue;
        end if;

        ina5, typ2 := isStrictA5TracesByS3(theta(B, F.i, P), P, alpha);

        // ensure that the generators lie in the _same_ A_5
        if not ina5 or typ ne typ2 then
            return false;
        end if;
    end for;

    return true;
end function;

isA5ByD10 := function(B, P)
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));
    F := Parent(B[1]);

    alpha := NormalForm(R!L2TracePolynomial(B[1]*B[2]), P);
    if alpha^2 - alpha - 1 in P then
        alpha := -alpha;
    end if;

    // find the first generator that is not in the subgroup D10
    k := 0;
    for i in [1..m] do
        if not isD10TracesByD10(theta(B, F.i, P), P, alpha) then
            k := i;
            break;
        end if;
    end for;

    ina5, typ := isStrictA5TracesByD10(theta(B, F.k, P), P, alpha);

    if not ina5 then
        return false;
    end if;

    for i in [k+1..m] do
        // generator i should be either in D10 or in A_5 without D_10;
        // in the latter case, we have to check that the type of A_5 matches
        // with that of the other generators
        if isD10TracesByD10(theta(B, F.i, P), P, alpha) then
            continue;
        end if;

        ina5, typ2 := isStrictA5TracesByD10(theta(B, F.i, P), P, alpha);

        // ensure that the generators lie in the _same_ A_5
        if not ina5 or typ ne typ2 then
            return false;
        end if;
    end for;

    return true;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  true, if the corresponding projective representation maps onto A_4,
 *  false otherwise.
 */
isA4 := function(P)
    if characteristic(P) eq 2 then
        return false;
    end if;

    if isDihedral(P) then
        return false;
    end if;

    subv4, B := subgroupIsV4(P);

    if not subv4 then
        suba4, B := subgroupIsA4(P);

        if not suba4 then
            return false;
        end if;
    end if;

    F := Parent(B[1]);
    R := Generic(P);
    m := Round(Log(2, Rank(R)+1));

    for i in [3..m] do
        if not isA4TracesByV4(theta(B, F.i, P), P) then
            return false;
        end if;
    end for;

    return true;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  true, if the corresponding projective representation maps onto S_4,
 *  false otherwise.
 */
isS4 := function(P)
    if characteristic(P) eq 2 then
        return false;
    end if;

    if isDihedral(P) or isA4(P) then
        return false;
    end if;

    subv4, B := subgroupIsV4(P);
    if subv4 then
        return isS4ByV4(B, P);
    end if;

    suba4, B := subgroupIsA4(P);
    if suba4 then
        return isS4ByV4(B, P);
    end if;

    subs4, B := subgroupIsS4(P);
    if subs4 then
        return isS4ByV4(B, P);
    end if;

    subd8, B := subgroupIsD8(P);
    if subd8 then
        return isS4ByV4(B, P);
    end if;

    subs3, B := subgroupIsS3(P);
    if subs3 then
        return isS4ByS3(B, P);
    end if;

    return false;
end function;


/* Input:
 *  P: Prime ideal in \Phi_m.
 * Ouput:
 *  true, if the corresponding projective representation maps onto A_5,
 *  false otherwise.
 */
isA5 := function(P)
    // in characteristic 2, the Klein four group is not absolutely irreducible,
    // so the tests don't work.
    if characteristic(P) eq 2 then
        return dimensionOverField(P) eq 0
            and quotientDimensionOverField(P) eq 2;
    end if;

    if isDihedral(P) or isA4(P) then
        return false;
    end if;

    subv4, B := subgroupIsV4(P);
    if subv4 then
        return isA5ByV4(B, P);
    end if;

    suba4, B := subgroupIsA4(P);
    if suba4 then
        return isA5ByV4(B, P);
    end if;

    suba5, B := subgroupIsA5(P);
    if suba5 then
        return isA5ByV4(B, P);
    end if;

    subs3, B := subgroupIsS3(P);
    if subs3 then
        return isA5ByS3(B, P);
    end if;

    subd10, B := subgroupIsD10(P);
    if subd10 then
        return isA5ByD10(B, P);
    end if;

    return false;
end function;
