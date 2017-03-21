freeze;

declare verbose MinimalAssociatedPrimes, 3;

LiftFromQToZ := function(I, R)
    Groebner(I);

    denomlcm := Lcm([CoefficientDenominator(f) : f in Basis(I)]);
    J := ideal<R | [f*CoefficientDenominator(f) : f in Basis(I)] >;

    return Saturation(J, R!denomlcm);
end function;


LiftFromFpToZ := function(I, R)
    Groebner(I);

    /* use explicit declaration, so the mapping is not returned */
    result := ideal<R | Characteristic(I), Basis(I) >;
    return result;
end function;


/* test whether the ideal I contains any of the ideals of L
 */
IsSuperset := function(I, L) 
    for J in L do
        if J subset I then
            return true;
        end if;
    end for;

    return false;
end function;


/* check whether el divides some element in list
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

    Sort(~result);
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




/* compute a list of primes which is sufficient for the calculation 
 * of the minimal associated primes, i.e. a list $S$ of primes, such
 * that $p \in S$ for every associated prime $P \in \MinAss(I)$
 * with $p \in P$.
 * 
 * At the moment, this computes a Gr\"obner basis over the integers.
 * This should be changed, since it is very inefficient.
 */
sufficientPrimes := function(I, useRandomTechniques, factorizationBound, trialDivisionBound, groebnerBasisBound)
    zeroNecessary := true;

    if not useRandomTechniques then
        vprintf MinimalAssociatedPrimes: "Computing Groebner basis over Z: ";
        t := Cputime();
        Groebner(I);
        t := Cputime(t);
        vprintf MinimalAssociatedPrimes: "%o\n", t;

        d := [LeadingCoefficient(f) : f in Basis(I)];

        if #[f : f in Basis(I) | f in Integers()] gt 0 then
            zeroNecessary := false;
        end if;
    else
        R := Generic(I);

        vprintf MinimalAssociatedPrimes: "Computing Groebner basis over Q (1): ";
        t := Cputime();
        J, d := GroebnerBasis(Basis(ChangeRing(I, Rationals())) : ReturnDenominators);
        t := Cputime(t);
        vprintf MinimalAssociatedPrimes: "%o\n", t;

        if 1 in J then
            zeroNecessary := false;
        end if;

        grp := Sym(Rank(R));

        for i in [2..groebnerBasisBound] do
            // use trial-division on the big factors
            res := [];

            vprintf MinimalAssociatedPrimes: "%o divisors\n", #d;
            vprintf MinimalAssociatedPrimes: "Trial division: ";
            t := Cputime();
            for x in d do
                vprintf MinimalAssociatedPrimes, 3: "divisor: %o\n", x;

                divisors, remainder := TrialDivision(
		    x, trialDivisionBound: Proof := false
		);
                res cat:= [y[1] : y in divisors] cat remainder;
            end for;
            t := Cputime(t);
            vprintf MinimalAssociatedPrimes: "%o\n", t;

            d := res;

//"Max d:", Maximum(d);

            if
	    //i ge 5 and
	    (#d eq 0 or Maximum(d) le factorizationBound) then
                break;
            else
                vprintf MinimalAssociatedPrimes: "Digits of maximal divisor: %o\n", Floor(Log(10, Maximum(d))) + 1;
            end if;

            sigma := Random(grp);
            vprintf MinimalAssociatedPrimes: "Using random permutation: %o\n", sigma;

	    if 1 eq 1 then
		//RR := PolynomialRing(BaseRing(R), Rank(R), "grevlex");
		//RR := PolynomialRing(BaseRing(R), Grading(R)^sigma);
		w := Grading(R);
		w := [w[i^sigma^-1]: i in [1 .. #w]];
		RR := PolynomialRing(BaseRing(R), w);
//"R:", R;
//"RR:", RR;
		alpha := hom< R -> RR | [RR.j^sigma : j in [1..Rank(R)]]>;
	    else
		alpha := hom< R -> R | [R.j^sigma : j in [1..Rank(R)]]>;
	    end if;

            vprintf MinimalAssociatedPrimes: "Computing Groebner basis over Q (%o): ", i;
            t := Cputime();
            _, d2 := GroebnerBasis(Basis(ChangeRing(Ideal(alpha(Basis(I))), Rationals())) : ReturnDenominators);
            t := Cputime(t);
            vprintf MinimalAssociatedPrimes: "%o\n", t;

            d := commonFactors(d, d2);
        end for;

    end if;

    if #d ne 0 and Maximum(d) gt factorizationBound then
        vprintf MinimalAssociatedPrimes: "Digits of maximal divisor: %o\n", Floor(Log(10, Maximum(d))) + 1;

	if 1 eq 1 and useRandomTechniques then
	    // AKS, Dec 14: Recurse to Z case, since factorization is doomed
	    return $$(
		I, false,
		factorizationBound, trialDivisionBound, groebnerBasisBound
	    );
	end if;
    end if;

    vprintf MinimalAssociatedPrimes: "Integer factorization: ";
    t := Cputime();
    // there has to be a better way to remove doubles from a list
    result := [z : z in {y : y in &cat[PrimeFactors(x) : x in d]}];
    Sort(~result);
    t := Cputime(t);
    vprintf MinimalAssociatedPrimes: "%o\n", t;

    if zeroNecessary then
        Append(~result, 0);
    end if;

    return result;
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

    J := ChangeRing(I, Rationals());
    vprintf MinimalAssociatedPrimes: "Computing Groebner basis over Q: ";
    t := Cputime();
    Groebner(J);
    t := Cputime(t);
    vprintf MinimalAssociatedPrimes: "%o\n", t;

    denoms := [CoefficientDenominator(f) : f in Basis(J)];

    result := [];

    if 0 in primes and not 1 in J then
        Append(~result, 0);
    end if;

    for p in primes do
        if p eq 0 then
            continue;
        end if;

        if dividesElement(p, denoms) then
            vprintf MinimalAssociatedPrimes: "%o is a divisor (neccessary)\n", p;
            result cat:= [p];
        else
            /* construct the ideal over the new coefficient ring again, 
             * since otherwise magma won't recognize that both ideals are defined over the same ring.
             */
            i := ChangeRing(I, GF(p));
            vprintf MinimalAssociatedPrimes: "Computing Groebner basis over GF(%o): ", p;
            t := Cputime();
            Groebner(i);
            t := Cputime(t);
            vprintf MinimalAssociatedPrimes: "%o", t;

            r := Generic(i);
            if not ideal< r | Basis(J) > subset i then
                result cat:= [p];
                vprintf MinimalAssociatedPrimes: " (neccessary)\n";
            else
                vprintf MinimalAssociatedPrimes: " (not neccessary)\n";
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

ofactorizationBound := 10^60;

intrinsic MinimalAssociatedPrimes(I::RngMPol : useRandomTechniques := true, sufficient := [], exclude := [], factorizationBound := 10^60, trialDivisionBound := 10^4, groebnerBasisBound := 20, saturate := 1 ) -> SeqEnum
{Compute the set of minimal associated primes of I}
    require IsField(CoefficientRing(Generic(I))) or CoefficientRing(Generic(I)) eq Integers(): "Coefficient ring must be a field or the ring of integers";
    if IsField(CoefficientRing(Generic(I))) then
        return RadicalDecomposition(I);
    end if;
    if #Basis(I) eq 0 then
        return [I];
    end if;

    if #sufficient eq 0 then
        vprintf MinimalAssociatedPrimes: "Computing sufficient primes.\n";
        t := Cputime();
        IndentPush();
        sufficient := sufficientPrimes(I, useRandomTechniques, factorizationBound, trialDivisionBound, groebnerBasisBound);
        IndentPop();
        t := Cputime(t);
        vprintf MinimalAssociatedPrimes: "Time: %o; primes: %o\n", t, sufficient;
    end if;

    sufficient := [p : p in sufficient | not p in exclude];

    vprintf MinimalAssociatedPrimes: "Computing necessary primes.\n";
    t := Cputime();
    IndentPush();
    necessary := necessaryPrimes(I, sufficient);
    IndentPop();
    t := Cputime(t);
    vprintf MinimalAssociatedPrimes: "Time: %o; primes: %o\n", t, necessary;

    R := Generic(I);

    primes_Q := [];
    if 0 in necessary then
        J := ChangeRing(I, Rationals());
        Groebner(J);
        if saturate ne 1 then
            vprintf MinimalAssociatedPrimes: "Saturating over Q: ";
            t := Cputime();
            J := Saturation(J, Generic(J)!saturate);
            t := Cputime(t);
            vprintf MinimalAssociatedPrimes: "%o\n", t;
        end if;
        vprintf MinimalAssociatedPrimes: "Computing prime ideals over Q\n";
        t := Cputime();
        primes_Q := RadicalDecomposition(J);
        t := Cputime(t);
        vprintf MinimalAssociatedPrimes: "    Time: %o\n    prime ideals: %o\n", t, #primes_Q;
        vprintf MinimalAssociatedPrimes: "Intersection with Z: ";
        t := Cputime();
        primes_Q := [LiftFromQToZ(P, R) : P in primes_Q]; 
        t := Cputime(t);
        vprintf MinimalAssociatedPrimes: "%o\n", t;
    end if;


    // copy list. 
    // TODO: is there a better way?
    result := [ P : P in primes_Q ];

    for p in necessary do
        if p eq 0 then
            continue;
        end if;

        J := ChangeRing(I, GF(p));
        if saturate ne 1 then
            vprintf MinimalAssociatedPrimes: "Saturating over GF(%o): ", p;
            t := Cputime();
            J := Saturation(J, Generic(J)!saturate);
            t := Cputime(t);
            vprintf MinimalAssociatedPrimes: "%o\n", t;
        end if;
        vprintf MinimalAssociatedPrimes: "Computing prime ideals over GF(%o): ", p;
        t := Cputime();
        primes_p := RadicalDecomposition(J);
        t := Cputime(t);
        vprintf MinimalAssociatedPrimes: "%o\n", t;
        vprintf MinimalAssociatedPrimes: "    prime ideals: %o\n", #primes_p;

        counter := 0;
        for P in primes_p do
            PZ := LiftFromFpToZ(P, R);
            if not IsSuperset(PZ, primes_Q) then
                result cat:= [PZ];
                counter +:= 1;
            end if;
        end for;
        vprintf MinimalAssociatedPrimes: "    necessary: %o\n", counter;
    end for;

    return result;
end intrinsic;
