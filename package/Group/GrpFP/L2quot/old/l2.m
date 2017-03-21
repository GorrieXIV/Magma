freeze;

import "minass.m": IsSuperset;

R<x1, x2, x12> := PolynomialRing(Integers(), 3, "grevlexw", [1,1,2]);
//R<x1, x2, x12> := PolynomialRing(Integers(), 3, "grevlex");

/* All 9 presentations of S_5 on two generators
 */
s4presentations := [
Group<a,b |  a^2, b^3, a*b^-1*a*b^-1*a*b^-1*a*b^-1, a*b^-1*a*b*a*b^-1*a*b*a*b^-1*a*b >,
Group<a,b |  a^2, b^4, a*b^-1*a*b^-1*a*b^-1 >,
Group<a,b |  b^2, a^3, b*a^-1*b*a^-1*b*a^-1*b*a^-1 >,
Group<a,b |  a^3, b^4, a*b^-1*a*b^-1 >,
Group<a,b |  a^3, b^4, a^-1*b^-1*a^-1*b^-1 >,
Group<a,b |  b^2, a^4, b*a^-1*b*a^-1*b*a^-1 >,
Group<a,b |  b^3, a^-1*b*a^-1*b, a^4 >,
Group<a,b |  b^3, a^-1*b^-1*a^-1*b^-1, a^4 >,
Group<a,b |  a^4, a^2*b*a^-2*b, b^-2*a*b^-2*a, b*a*b*a*b*a >
];


s4ideals := [
ideal< R | [ x1, x2^2 - 1, x12^3 - 2*x12 ] >, 
ideal< R | [ x1, x2^3 - 2*x2, x12^2 - 1 ] >, 
ideal< R | [ x1^2 - 1, x2, x12^3 - 2*x12 ] >, 
ideal< R | [ x1^2 - 1, x1*x2 - x12, x1*x12 - x2, x2^2 - x12^2, x2*x12^2 - 2*x2, x12^3 - 2*x12 ] >, 
ideal< R | [ x1^2 - 1, x2^3 - 2*x2, x12 ] >, 
ideal< R | [ x1^3 - 2*x1, x2, x12^2 - 1 ] >, 
ideal< R | [ x1 - x2*x12, x2^2 - 1, x12^3 - 2*x12 ] >, 
ideal< R | [ x1^3 - 2*x1, x2^2 - 1, x12 ] >, 
ideal< R | [ x1 - x2*x12, x2^3 - 2*x2, x12^2 - 1 ] > 
];

/* All 19 presentations of A_5 on two generators
 */
a5presentations := [
Group<a,b |  a^3, b^3, b*a*b*a^-1*b*a*b*a^-1, a^-1*b^-1*a^-1*b*a^-1*b^-1*a^-1*b >,
Group<a,b |  a^3, b^5, a^-1*b^-2*a^-1*b^-2, b*a^-1*b*a^-1*b*a^-1 >,
Group<a,b |  a^3, b^-1*a^-1*b^-1*a^-1*b^-1*a^-1, b^-2*a*b^-2*a, a^-1*b^-1*a^-1*b^2*a*b^2 >,
Group<a,b |  b^2, a^3, b*a^-1*b*a^-1*b*a^-1*b*a^-1*b*a^-1 >,
Group<a,b |  a^3, b*a^-1*b*a^-1, b^5 >,
Group<a,b |  a^3, b*a*b*a, b^5, a*b^-1*a*b^-2*a*b^-1*a*b^-2*a*b^-1*a*b^-2 >,
Group<a,b |  a^2, b^5, b*a*b*a*b*a >,
Group<a,b |  a^2, b^3, b^-1*a*b^-1*a*b^-1*a*b^-1*a*b^-1*a >,
Group<a,b |  a^2, b^5, b*a*b^2*a*b^2*a*b, b*a*b^-2*a*b*a*b^-2*a >,
Group<a,b |  b^3, a^5, a^2*b*a^2*b, b*a^-1*b*a^-1*b*a^-1 >,
Group<a,b |  b^3, a^2*b^-1*a^2*b^-1, a*b*a*b*a*b, a^-2*b^-1*a^-3*b^-1*a^-1 >,
Group<a,b |  b^2, a^5, b*a^-1*b*a^-1*b*a^-1 >,
Group<a,b |  b^3, a*b^-1*a*b^-1, a^5 >,
Group<a,b |  b^2, a^5, b*a^-2*b*a^-2*b*a^-2, b*a*b*a^-2*b*a*b*a^-2 >,
Group<a,b |  b^3, b*a*b*a, a^5 >,
Group<a,b |  a^-1*b^-1*a^-1*b^-1, a^5, b*a^-1*b^2*a^-1*b^2*a^-1*b, a^2*b^-1*a^2*b^-1*a^2*b^-1 >,
Group<a,b |  a^5, b*a^-1*b*a^-1*b*a^-1, a^-1*b^-1*a*b^-1*a^-1*b, a*b*a^2*b*a^2*b*a >,
Group<a,b |  b^-1*a*b^-1*a, a^5, a*b*a*b*a*b, b^-1*a^-2*b^-2*a^-2*b^-1 >,
Group<a,b |  a^5, b*a^-1*b^-1*a^-1*b*a, a*b*a^2*b*a >
];


a5ideals := [
ideal< R | [ x1 - x2*x12^3 + 2*x2*x12, x2^2 - 1, x12^4 - 3*x12^2 + 1 ] >,
ideal< R | [ x1 - x2*x12, x2^2 + x12^2 - 3, x12^4 - 3*x12^2 + 1 ] >,
ideal< R | [ x1 - x2^3*x12 + 2*x2*x12, x2^4 - 3*x2^2 + 1, x12^2 - 1 ] >,
ideal< R | [ x1^2 - 1, x2, x12^4 - 3*x12^2 + 1 ] >,
ideal< R | [ x1 + x2*x12^3 - 3*x2*x12, x2^2 - x12^2, x12^4 - 3*x12^2 + 1 ]  >,
ideal< R | [ x1^2 - 1, x2^4 - 3*x2^2 + 1, x12 ]  >,
ideal< R | [ x1, x2^4 - 3*x2^2 + 1, x12^2 - 1 ]  >,
ideal< R | [ x1, x2^2 - 1, x12^4 - 3*x12^2 + 1 ]  >,
ideal< R | [ x1, x2^2 + x12^2 - 3, x12^4 - 3*x12^2 + 1 ] >,
ideal< R | [ x1 + x2*x12^3 - 3*x2*x12, x2^2 - 1, x12^4 - 3*x12^2 + 1 ] >,
ideal< R | [ x1^2 - x1*x2*x12 - 1, x2^2 - 1, x12^2 - 1 ] >,
ideal< R | [ x1^4 - 3*x1^2 + 1, x2, x12^2 - 1 ] >,
ideal< R | [ x1 - x2*x12, x2^2 - 1, x12^4 - 3*x12^2 + 1 ] >,
ideal< R | [ x1^2 + x12^2 - 3, x2, x12^4 - 3*x12^2 + 1 ] >,
ideal< R | [ x1^4 - 3*x1^2 + 1, x2^2 - 1, x12 ] >,
ideal< R | [ x1^2 + x2^2 - 3, x2^4 - 3*x2^2 + 1, x12 ] >,
ideal< R | [ x1 - x2*x12^3 + 2*x2*x12, x2^2 - x12^2, x12^4 - 3*x12^2 + 1 ] >,
ideal< R | [ x1 + x2^3*x12 - 3*x2*x12, x2^4 - 3*x2^2 + 1, x12^2 - 1 ] >,
ideal< R | [ x1 - x2*x12, x2^4 - 3*x2^2 + 1, x12^2 - 1 ] >
];




/* check, whether the word is of the form X^2*Y (possibly after rotation), where X and Y
 * are subwords. Always finds the longest possible X.
 *
 * Returns (true, X, Y) if this is possible,
 * (false, _, _) otherwise.
 */
HasSquare := function(word)
    n := #word;
    k := Floor(n/2);

    while k gt 0 do
        for i in [1..n] do
            cand := word[[1..k]];
            if word[[k+1..2*k]] eq cand then
                return true, cand, word[[2*k+1..n]];
            end if;

            word := word[[2..n]] cat [word[1]];
        end for;

        k -:= 1;
    end while;

    return false, _, _;
end function;


/* Tr(x^n*y) = c_n(x)*Tr(x*y) - c_{n-1}(x)*Tr(y), where c_n(y) = sum_{i = 0}^{floor((n-1)/2)} (-1)^i Binomial(n-i-1,i)*Tr(x)^(n-2i-1)
 * This function calculates c_n(x).
 */
PowerWordHelper := function(powers, n : I := ideal< R | > )
    return &+[(-1)^i*Binomial(n-i-1,i)*powers[n-2*i] : i in [0..Floor((n-1)/2)]];
end function;



/* check, whether the word is of the form X^2*Y (possibly after rotation), where X and Y
 * are subwords. Always finds the longest possible X.
 *
 * Returns (true, X, Y) if this is possible,
 * (false, _, _) otherwise.
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


/* Actual computation of the trace polynomial.
 * The word is given as a list of 1, -1, 2, -2, as given by Eltseq.
 */
L2TracePolynomialList := function(word, R : I := ideal< R | > )
    while #word gt 0 and word[1] + word[#word] eq 0 do
        word := word[[2..#word - 1]];
    end while;

    if #word eq 0 then
        return R!2;
    end if;

    if #word eq 1 then
        if Abs(word[1]) eq 1 then
            return R.1;
        else
            return R.2;
        end if;
    end if;

    if #word eq 2 then
        if Abs(word[1] + word[2]) eq 3 then
            // the word is a*b, b*a, or one of the inverses
            return R.3;
        elif Abs(word[1] + word[2]) eq 1 then
            return R.1*R.2-R.3;
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


    F := FreeGroup(2);


    // Use the formula 
    //      Tr(x^n*y) = c_n(x)*Tr(x*y) - c_{n-1}(x)*Tr(y), 
    // where c_n(y) = sum_{i = 0}^{floor((n-1)/2)} (-1)^i Binomial(n-i-1,i)*Tr(x)^(n-2i-1)
    // This is much more efficient if the word contains a letter to a high power.

    base, power, remainder := FindHighestPower(word);

    if power gt 1 then
        x := $$(base, R : I := I);

        // Careful: powersx[1] = 1 = x^0, powersx[2] = x = x^1, etc
        powersx := [R!1];
        for i in [1..power-1] do
            Append(~powersx, NormalForm(powersx[i]*x, I));
        end for;

        return NormalForm(PowerWordHelper(powersx, power : I := I), I)*NormalForm($$(base cat remainder, R), I) 
                - NormalForm(PowerWordHelper(powersx, power-1 : I := I), I)*NormalForm($$(Eltseq(F!remainder), R), I);
    end if;

    // insert a square artificially: replace the first occurence of
    // a negative exponent by a square (a^(-1) -> a^(-2)*a)
    i := 1;
    while word[i] gt 0 do
        i := i + 1;
    end while;
    return NormalForm($$([-word[i]], R)*$$(word[[i+1..#word]] cat word[[1..i-1]], R) - $$([-word[i]] cat word[[i+1..#word]] cat word[[1..i-1]], R), I);
end function;





L2TracePolynomial := function(word : I := ideal< R | > )
    return L2TracePolynomialList(Eltseq(word), R : I := I);
end function;


L2ConditionsForWord := function(rel : I := ideal< R | > )
    result := [];

    F<a,b> := Parent(rel);

    seq := Eltseq(rel);
    k := Floor(#seq/2);
    left := F!seq[[1..k]];
    right := (F!seq[[k+1..#seq]])^(-1);

    for beta in [F!1, a, b, a*b] do
        Append(~result, <L2TracePolynomial(left*beta : I := I), L2TracePolynomial(right*beta : I := I)>);
    end for;

    return result;
end function;


L2TracePresentationIdealPrecomputed := function(conditions, signSystem)
    assert #conditions eq #signSystem;

    result := [];

    for i in [1..#conditions] do
        cond := conditions[i];

        for c in cond do
            Append(~result, c[1] - signSystem[i]*c[2]);
        end for;
    end for;

    return ideal< R | result >;
end function;



/* Compute the trace presentation ideal for the relations
 * with the given sign system (i.e., if A, B \in SL(2, p)
 * are the images of the generators, then rels[i](A, B) = signSystem[i]*IdentityMatrix(2)
 * for all i.
 *
 * If the ideal I is given, then in each step the occuring polynomials are reduced
 * mod I. This can give a good speed-up if the residue class ring of I is small.
 */
L2TracePresentationIdeal := function(rels, signSystem : I := ideal< R | > )
    assert #rels eq #signSystem;

    if #rels gt 0 then
        F<a,b> := Parent(rels[1]);
    else
        F<a,b> := FreeGroup(2);
    end if;

    result := [];

    for i in [1..#rels] do
        for beta in [F!1, a, b, a*b] do
            seq := Eltseq(rels[i]);
            k := Floor(#seq/2);
            left := F!seq[[1..k]];
            right := (F!seq[[k+1..#seq]])^(-1);

            Append(~result, L2TracePolynomial(left*beta : I := I) - signSystem[i]*L2TracePolynomial(right*beta : I := I));
        end for;
    end for;

//    if #result gt 0 then
//        R := Parent(result[1]);
//    else
//        R := R;
//    end if;


    return ideal< R | result >;
end function;


/* the representation is absolutely irreducible if and only if the 
 * irreducibility indicator rho is non-zero.
 */
L2IsAbsolutelyIrreducible := function(I)
    if #Basis(I) eq 0 then
        return true;
    end if;

    R<x1, x2, x12> := Parent(Basis(I)[1]);
    rho := x1^2 + x2^2 + x12^2 - x1*x2*x12 - 4;

    return not rho in I;
end function;


/* The group is dihedral if and only if two of the matrices have order 4
 * (i.e., projectively they have order 2), which is the case if and
 * only if they have trace 0.
 */
L2IsDihedralGroup := function(I)
    if #Basis(I) eq 0 then
        return false;
    end if;
    R<x1, x2, x12> := Parent(Basis(I)[1]);

    return (x1 in I and x2 in I) or (x1 in I and x12 in I) or (x2 in I and x12 in I);
end function;


/* handle A4 differently than S4 and A5, since
 * there is no field extension involved, so the tests are very easy
 * (see the Plesken-Fabianska paper).
 */
L2IsA4 := function(I)
    if #Basis(I) eq 0 then
        return false;
    end if;
    R<x1, x2, x12> := Parent(Basis(I)[1]);

    if x1 in I then
        return (x2 - 1 in I or x2 + 1 in I) and (x12 - 1 in I or x12 + 1 in I);
    elif x2 in I then
        return (x1 - 1 in I or x1 + 1 in I) and (x12 - 1 in I or x12 + 1 in I);
    elif x12 in I then
        return (x1 - 1 in I or x1 + 1 in I) and (x2 - 1 in I or x2 + 1 in I);
    end if;

    return (x1 - 1 in I and x2 - 1 in I and x12 - 1 in I) 
            or (x1 - 1 in I and x2 + 1 in I and x12 + 1 in I)
            or (x1 + 1 in I and x2 - 1 in I and x12 + 1 in I)
            or (x1 + 1 in I and x2 + 1 in I and x12 - 1 in I);
end function;


/* check, whether the representation defined by I satisfies the relation.
 * This is done by checking whether the commutators [rel,a] and [rel,b] are in the center of the group algebra.
 */
SatisfiesRelation := function(I, rel)
    F<a,b> := Parent(rel);
    bas := [F!1, a, b, a*b];
    
    for x in [a,b] do
        for y in bas do
            if not L2TracePolynomial(rel*x*y) - L2TracePolynomial(x*rel*y) in I then
                return false;
            end if;
        end for;
    end for;

    return true;
end function;

SatisfiesPresentation := function(I, G)
    rels := Relations(G);

    for i in [1..#rels] do
        rel := LHS(rels[i])*RHS(rels[i])^(-1);

        if not SatisfiesRelation(I, rel) then
            return false;
        end if;
    end for;

    return true;
end function;

PresentationIdeal := function(G)
    rels := Relations(G);

    if #rels eq 0 then
        return ideal< R | 0 >;
    end if;

    F<a,b> := Parent(LHS(rels[1]));
    bas := [F!1, a, b, a*b];

    result := [];
    for i in [1..#rels] do
        rel := LHS(rels[i])*RHS(rels[i])^(-1);
        for x in [a,b] do
            for y in bas do
                Append(~result, L2TracePolynomial(rel*x*y) - L2TracePolynomial(x*rel*y));
            end for;
        end for;
    end for;

    return ideal< R | result >;
end function;

/* S_4 is checked by running through all presentations of S_4
 */
L2IsS4 := function(I)
//    for pres in s4presentations do
//        if SatisfiesPresentation(I, pres) then
//            return true;
//        end if;
//    end for;
    for id in s4ideals do
        if id subset I then
            return true;
        end if;
    end for;

    return false;
end function;

/* A_5 is checked by running through all presentations of S_4
 */
L2IsA5 := function(I)
//    for pres in a5presentations do
//        if SatisfiesPresentation(I, pres) then
//            return true;
//        end if;
//    end for;
    for id in a5ideals do
        if id subset I then
            return true;
        end if;
    end for;

    return false;
end function;


/* The action of the sign systems on the generators of the group
 * induce an action on the ideals.
 *
 * This is used to recognize PGL, and to avoid unnecessary ideals,
 * since all ideals in an orbit give the same image in PSL(2, q).
 */
SignAction := function(P, sigma)
    R<x1, x2, x12> := Parent(Basis(P)[1]);

    alpha := hom< R -> R | sigma[1]*x1, sigma[2]*x2, (sigma[1]*sigma[2])*x12 >;

    return ideal< R | [alpha(f) : f in Basis(P)]>;
end function;


/* Use Remark 4.3 of Plesken-Fabianska to check for PGL:
 * It is PGL if and only if the action of the sign system
 * induces a Galois automorphism.
 */
L2IsPGL := function(I)
    if 2 in I then
        // in characteristic 2, PGL = PSL
        return false;
    end if;

    for sigma in [[-1,1],[1,-1],[-1,-1]] do
        if SignAction(I, sigma) eq I then
            return true;
        end if;
    end for;

    return false;
end function;


SignMatrix := function(relations)
    F<a, b> := Parent(relations[1]);
    return Matrix(GF(2), 2, #relations, [[Weight(r, x) : r in relations] : x in [a,b]]);
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

L2SignSystems := function(relations)
    /* For a description of the method, cf. L3SignSystems.
     */
    n := #relations;

    if n eq 0 then
        return [[]];
    end if;

    V := VectorSpace(GF(2), n);

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
            if v - g in result then
                isnew := false;
                break;
            end if;
        end for;

        if isnew then
            Append(~result, v);
        end if;
    end for;

    Sort(~result, CompareSignSystems);

    return [[(-1)^(Integers()!r[i]) : i in [1..n]] : r in result];
end function;


/* compute the minimal associated primes of I and remove
 * all ideals which give rise to subgroups not isomorphic
 * to PSL(2, q) or PGL(2, q).
 */
intrinsic L2Ideals(I::RngMPol) -> SeqEnum[RngMPol]
{Compute all L2 ideals containing I}
    IndentPush();
    MA := MinimalPrimes(I);
    vprintf User2: "%o minimal primes\n", #MA;

    result := [P : P in MA | L2IsAbsolutelyIrreducible(P)];
    vprintf User2: "%o primes are absolutely irreducible\n", #result;
    result := [P : P in result | not L2IsDihedralGroup(P)];
    vprintf User2: "%o primes are not dihedral\n", #result;
    result := [P : P in result | not L2IsA4(P)];
    vprintf User2: "%o primes are not A_4\n", #result;
    result := [P : P in result | not L2IsS4(P)];
    vprintf User2: "%o primes are not S_4\n", #result;
    result := [P : P in result | not L2IsA5(P)];
    vprintf User2: "%o primes are not A_5\n", #result;

    IndentPop();
    return result;
end intrinsic;


/* Compute the kernel of the action of the sign systems on the relations.
 * (For each kernel element, there is an ideal; they will all give different
 * representations, which are projectively the same.)
 */
L2SignKernel := function(relations)
    m := SignMatrix(relations);

    result := [x : x in Kernel(m) | not IsZero(x)];

    // cast to integer tuples
    return [[(-1)^(Integers()!x) : x in Eltseq(k)] : k in result];
end function;


/* Check, whether list contains a conjugate of P under an element in Sigma.
 *
 * This method is used when the action has a kernel, so there are different
 * ideals which give the same projective representation.
 */
L2ContainsConjugate := function(list, P, Sigma)
    for sigma in Sigma do
        if SignAction(P, sigma) in list then
            return true;
        end if;
    end for;

    return false;
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


/* This is the main method.
 *
 * For efficiency reasons, the calculation is done in two steps:
 * First, calculate all L2 ideals for G_short, where G_short
 * is the presentation obtained by considering only the short relations
 * (at most 50 letters).
 * 
 * After that, compute the ideals for G = G_short/<long relations> as follows:
 * Let P be an ideal for G_short. Compute the trace presentation ideal I for the long relations, 
 * but reduce each polynomial modulo P during the calculations. If P has a considerably small
 * residue class ring, this drastically reduces the degree of the trace polynomials.
 * After that, call L2Ideals for P + I and remove the unnecessary ideals as usual.
 */
intrinsic L2Quotients(G::GrpFP : short := 100) -> SeqEnum[RngMPol]
{Compute all L2 quotients of G}
    if NumberOfGenerators(G) ne 2 then
        error "Only finitely presented groups on two generators are supported at the moment.";
    end if;

    result := [];
    resultchar2 := [];

    rels := [LHS(r)*RHS(r)^(-1) : r in Relations(G)];

    ker := L2SignKernel(rels);

    shortrels := [r : r in rels | #r le short];
    longrels := [r : r in rels | #r gt short];

    r1 := #shortrels;
    r2 := #longrels;
    r := r1 + r2;

    signSystems := L2SignSystems(shortrels cat longrels);

    vprintf User1: "%o short and %o long relations; %o sign systems in total\n", r1, r2, #signSystems;

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
    shortconditions := [L2ConditionsForWord(r) : r in shortrels];
    for tup in signSystemsAcc do
        vprintf User1: "Sign system %o of %o: %o\n", counter1, #signSystemsAcc, signSystemString(tup[1]);
        t := Cputime();
        tmp1 := L2Ideals(L2TracePresentationIdealPrecomputed(shortconditions, tup[1]));
        t := Cputime(t);
        vprintf User1: "Time: %o; ideals: %o\n", t, #tmp1;
        IndentPush();
        if #tmp1 gt 0 then
            counter2 := 1;
            for P in tmp1 do
                vprintf User1: "ideal %o ...\n", counter2;
                IndentPush();
                longconditions := [L2ConditionsForWord(r : I := P) : r in longrels];
                counter3 := 1;
                for s in tup[2] do
                    vprintf User1: "Sign system %o of %o: %o\n", counter3, #tup[2], signSystemString(s);
                    t := Cputime();
                    if #longrels gt 0 then
                        tmp2 := L2Ideals(P + L2TracePresentationIdealPrecomputed(longconditions, s));
                    else
                        tmp2 := [P];
                    end if;
                    t := Cputime(t);
                    vprintf User1: "Time: %o; ideals: %o\n", t, #tmp2;
                    for Q in tmp2 do
                        if 2 in Q then
                            /* Treat the primes containing 2 differently, since these are the only 
                             * ideals which can contain prime ideals of other sign systems.
                             */
                            Append(~resultchar2, Q);
                        else
                            // don't add ideals which can be created from known ideals by a change of signs.
                            if not L2ContainsConjugate(result, Q, ker) then
                                Append(~result, Q);
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

    // remove ideals which are only added artificially in characteristic 2 (where every sign system
    // is trivial, since 1 = -1).
    resultchar2 := [P : P in resultchar2 | not IsSuperset(P, result)];

    result cat:= resultchar2;

    return result;
end intrinsic;


intrinsic L2Type(P::RngMPol) -> MonStgElt
{Return the L2Type of P}
    // TODO: check if P is prime?

    if not L2IsAbsolutelyIrreducible(P) then
        return "reducible";
    elif L2IsDihedralGroup(P) then
        // TODO: careful with PSL(2,2) = S_3
        return "dihedral";
    elif L2IsA4(P) then
        // TODO: careful with PSL(2,3) = A_4
        return "Alt(4)";
    elif L2IsS4(P) then
        return "Sym(4)";
    elif L2IsA5(P) then
        // TODO: careful with PSL(2,4) = PSL(2,5) = A_5
        return "Alt(5)";
    end if;


    Groebner(P);

    // check, whether P contains a prime number
    integers := [f : f in Basis(P) | f in Integers()];

    if #integers eq 0 then
        return "infinite (characteristic zero)";
    end if;

    p := Integers()!integers[1];

    // check, whether Z[x1, x2, x12]/P is infinite
    Q := ChangeRing(P, GF(p));

    if Dimension(Q) gt 0 then
        return Sprintf("infinite (characteristic %o)", p);
    end if;


    S := Parent(Basis(Q)[1]);

    exp := Dimension(S/Q);

    if L2IsPGL(P) then
        if exp eq 2 then
            return Sprintf("PGL( 2, %o )", p);
        else
            return Sprintf("PGL( 2, %o^%o )", p, exp/2);
        end if;
    else
        if exp eq 1 then
            return Sprintf("PSL( 2, %o )", p);
        else
            return Sprintf("PSL( 2, %o^%o )", p, exp);
        end if;
    end if;
end intrinsic;



intrinsic L2Generators(P::RngMPol) -> GrpMat
{Compute a matrix group representing the L2 quotient}
    // check, whether P contains a prime number
    integers := [f : f in Basis(P) | f in Integers()];

    if #integers eq 0 then
        error "ideal not maximal";
    end if;

    p := Integers()!integers[1];

    // check, whether Z[x1, x2, x12]/P is infinite
    F := GF(p);
    Q := ChangeRing(P, F);

    if Dimension(Q) gt 0 then
        error "ideal not maximal";
    end if;

    R<x1, x2, x12> := Parent(Basis(Q)[1]);

    A := R/Q;

    d := Dimension(A);

    if d eq 1 then
        K := F;
        tr := [K!NormalForm(z, Q) : z in [x1, x2, x12]];
    else
        bas := MonomialBasis(A);

        repeat
            pol := &+[Random(F)*b : b in bas];
            mp := MinimalPolynomial(pol);
        until Degree(mp) eq d;

        K := ext< F | mp >;

        QQ := ChangeRing(Q, K);

        M := RadicalDecomposition(QQ)[1];

        R<x1, x2, x12> := Parent(Basis(M)[1]);

        tr := [K!NormalForm(z, M) : z in [x1, x2, x12]];
    end if;


    Pol := PolynomialRing(K); t := Pol.1;

    pol := t^2 - tr[1]*t + 1;

    if IsIrreducible(pol) then
        tmp := MatrixGroup< 4, K | [0,-1,0,0,1,tr[1],0,0,0,0,0,-1,0,0,1,tr[1]], [0,tr[3] - tr[1]*tr[2],-1,-tr[1],0,tr[2],0,1,1,tr[1],tr[2],tr[3],0,-1,0,0] >;

        m := RModule([tmp.1, tmp.2]);

        v, w, _ := Meataxe(m);

        return MatrixGroup(v);
    else
        alpha := Roots(pol)[1][1];
        return MatrixGroup<2, K | [alpha, tr[2]*(alpha - tr[1]) + tr[3], 0, tr[1] - alpha], [0, -1, 1, tr[2]] >;
    end if;
end intrinsic;

