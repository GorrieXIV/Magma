freeze;

LiftFromQToZ := function(I, R)
//    print "starting to lift from Q to Z";
    Groebner(I);

    denomlcm := Lcm([Denominator(f) : f in Basis(I)]);
    J := ideal<R | [f*Denominator(f) : f in Basis(I)] >;

    return Saturation(J, R!denomlcm);
end function;


LiftFromFpToZ := function(I, R)
    Groebner(I);

    /* use explicit declaration, so the mapping is not returned */
    result := ideal<R | Characteristic(I), Basis(I) >;
    return result;
end function;


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


/* check, whether el divides some element in list
 */
dividesElement := function(el, list)
    for x in list do
        if IsDivisibleBy(x, el) then
            return true;
        end if;
    end for;

    return false;
end function;



/* For every element $e$ in the list, check, whether is divisible by the first element $x$.
 * If this is the case, divide by the highest possible power of $x$.
 * Then check, whether $e$ and $x$ have a common factor; if this is the case, replace $x$ and $e$
 * by their cofactors, add the gcd to the list, and return. The reasoning behind this is
 * that it is desirable to get the smallest possible factors.
 * 
 * The return value indicates whether the list has been changed or not.
 *
 * assumes that all elements are positive (only relevant for sorting)
 */
coprimeStep := function(list)
    tmp := list;
    x := tmp[1];
    modified := false;
    for i in [2..#tmp] do
        while tmp[i] mod x eq 0 do
            tmp[i] /:= x;
            modified := true;
        end while;
        g := Gcd(tmp[i], x);
        if g gt 1 then
            tmp[1] /:= g;
            tmp[i] /:= g;
            Append(~tmp, g);
            tmp := [x : x in {y : y in tmp | y ne 1}];

            return true, tmp;
        end if;
    end for;

    if modified then
        tmp := [x : x in {y : y in tmp | y ne 1}];
    end if;

    return modified, tmp;
end function;
        

/* return a list of integer, such that the prime factors are the same as
 * in the given list, but all entries in the returned list are coprime
 */
toCoprime := function(list)
    result := [];
    /* make positive and remove ones */
    tmp := [Abs(x) : x in list | Abs(x) ne 1];
    while #tmp gt 0 do
        modified := true;
        while modified do
            modified, tmp := coprimeStep(tmp);
        end while;
        Append(~result, tmp[1]);
        Remove(~tmp, 1);
    end while;

    return Sort(result);
end function;

/* Compute all non-trivial gcds between elements in l1 and elements in l2
 */
commonFactors := function(l1, l2)
    result := [];

    for el1 in l1 do
        for el2 in l2 do
            g := Gcd(el1, el2);
            if g ne 1 and not g in result then
                Append(~result, g);
            end if;
        end for;
    end for;

    return result;
end function;


/* Compute the prime factors in l
 * The second parameter specifies an upper bound for the biggest compositie factor.
 * If there is a composite factor bigger than this bound, the list [0] is returned.
 * The default value for this bound is 2^150
 * If composite Bound is 0, then try to factor arbitrarily large numbers
 */
computePrimes := function(list: compositeBound := 2^150)
    composites := toCoprime(list);
    primes := [];

    if #composites gt 0 and compositeBound gt 0 and Max(composites) gt compositeBound then
        return [0];
    end if;

    for c in composites do
        ff := Factorization(c);
        for f in ff do
            Append(~primes, f[1]);
        end for;
    end for;

    return Sort(primes);
end function;



/* 
 */
commonPrimes := function(l1, l2)
    return computePrimes(commonFactors(l1, l2));
end function;


/* compute a list of primes which is sufficient for the calculation 
 * of the minimal associated primes, i.e. a list $S$ of primes, such
 * that $p \in S$ for every associated prime $P \in \MinAss(I)$
 * with $p \in P$.
 * 
 * At the moment, this computes a Gr\"obner basis over the integers.
 * This should be changed, since it is very inefficient.
 */
sufficientPrimes := function(I)
    if #Basis(I) eq 0 then
        return [];
    end if;
    Groebner(I);
    lc := [LeadingCoefficient(f) : f in Basis(I)];

    return computePrimes(lc : compositeBound := 0);
end function;



/* Given an ideal I and a list of primes,
 * check for any prime p in the list primes, whether
 * Groebner(I) mod p != Groebner(I mod p).
 * If this is the case, then the prime is necessary.
 */
necessaryPrimes := function(I, primes)
    if #primes eq 0 then
        return [];
    end if;

//    "changing ring ... ";
    J := ChangeRing(I, Rationals());
//    time Groebner(J);
//    "computing groebner ... ";
//    Basis(J);
    Groebner(J);

//    "computing denoms ... ";
    denoms := [Denominator(f) : f in Basis(J)];

    result := [];

    for p in primes do
//        "checking division for", p , "... ";
        if dividesElement(p, denoms) then
            result cat:= [p];
        else
            /* construct the ideal over the new coefficient ring again, 
             * since otherwise magma won't recognize that both ideals are defined over the same ring.
             */
//            "changing ring to", p , "... ";
            i := ChangeRing(I, GF(p));
            r := Parent(Basis(i)[1]);
            if not ideal< r | Basis(J) > subset i then
//                print p, "is NECESSARY";
                result cat:= [p];
            else
//                print p, "is NOT necessary";
            end if;
        end if;
    end for;


    return result;
end function;

/* given an ideal I in an integer ring,
 * compute the minimal primes above I.
 * 
 * There are two kinds of ideals which are returned.
 * * Either the ideal does not contain a prime number. In this case,
 *   the generators are really a Groebner basis of the ideal tensored
 *   with Q, i.e., to get generators over Z for the ideal, one has
 *   to use saturation. (In particular, the ideal might not be prime)
 * * In the second case, the ideal contains a prime number (and in this
 *   case, we really have a prime ideal). Then the ideal might not be minimal,
 *   i.e., there might exist a prime ideal not containing a prime, which
 *   is contained in the given ideal.
 * Both phenomena have to be taken care of when using this function.
 */
intrinsic MinimalPrimes(I::RngMPol) -> SeqEnum
{Compute the set of minimal associated primes of I}
    if #Basis(I) eq 0 then
        return [I];
    end if;
    vprintf User3: "Computing sufficient primes ... ";
    t := Cputime();
    primes := sufficientPrimes(I);
    t := Cputime(t);
    vprintf User3: "Time: %o; primes: %o\n", t, primes;

//    time np := necessaryPrimes(I, primes);
    np := necessaryPrimes(I, primes);
    vprintf User3: "Necessary primes: %o\n", np;

    t := Cputime();
    R := Parent(Basis(I)[1]);

    vprintf User3: "Computing prime ideals over Q ... ";
    t := Cputime();
    primes_Q := RadicalDecomposition(ChangeRing(I, Rationals()));
    t := Cputime(t);
    vprintf User3: "Time: %o; prime ideals: %o\n", t, #primes_Q;
    primes_Q := [LiftFromQToZ(P, R) : P in primes_Q]; 


    // copy list. 
    // TODO: is there a better way?
    result := [ P : P in primes_Q ];

    for p in np do
        vprintf User3: "Computing prime ideals over GF(%o) ... ", p;
        t := Cputime();
        primes_p := RadicalDecomposition(ChangeRing(I, GF(p)));
        t := Cputime(t);
        vprintf User3: "Time: %o; prime ideals: %o\n", t, #primes_p;

        counter := 0;
        for P in primes_p do
            PZ := LiftFromFpToZ(P, R);
            if not IsSuperset(PZ, primes_Q) then
                result cat:= [PZ];
                counter +:= 1;
            end if;
        end for;
        vprintf User3: "minimal prime ideals: %o\n", counter;
    end for;

    return result;
end intrinsic;


/* compute the set of minimal ideals in the set ideals
 */
MinimalIdeals := function(ideals) 
    result := ideals;

    for i := #result to 1 by -1 do
        for j in [1..#result] do
            if i ne j and result[j] subset result[i] then
                Remove(~result, i);
                break;
            end if;
        end for;
    end for;

    return result;
end function;


