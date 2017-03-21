freeze;

// implementation by Sebastian Jambor (2013) (jambor@math.auckland.ac.nz)
// of [JLNP13] to recognise constructively Alt(n) or Sym (n), and 
// their central extensions 
//
import "anrecog_verify.m": CheckGenerators, VerifyAlternatingOrSymmetric;
declare verbose AnRecog, 5;

/* Input:
 *  c: a three-cycle (1,2,3)
 *  x: a bolstering element (i.e., x = (2,a_1,...,a_alpha)(3,b_1,...,b_beta)(...) or x = (2,a_1,...,a_alpha,3,b_1,...,b_beta)(...)
 *  cw: a word evaluating to c
 *  xw: a word evaluating to x
 *  N: The upper bound for the degree
 *  isEqual: method to test equality in the group
 * Output:
 *  k: 3 + alpha + beta or (3 + alpha + beta-1) (the length of the returned cycle)
 *  g: a k-cycle (1,2,3,a_i,...,b_j)
 *  gw: a word evaluating to g
 */
BuildCycle := function(c, x, cw, xw, N, isEqual)
    m := 0;
    tmp := c^x;     // tmp = (1,a_1,b_1)
    tmpw := cw^xw;
    y := c;         // y = (1,2,3)
    yw := cw;
    tmpc := tmp*c;  // tmpc = (1,a_1,b_1,2,3)
    while not isEqual(tmpc, One(Parent(c))) and isEqual((tmpc)^5, One(Parent(c))) do    
        m +:= 1;
        if m ge N/2 then
            error "BuildCycle (m > N/2)";
        end if;
        y := y*tmp;     // y = (1,2,3,a_1,b_1,...,a_{i-1},b_{i-1})
        yw := yw*tmpw;
        tmp := tmp^x;   // tmp = (1,a_i,b_i)
        tmpw := tmpw^xw;
        tmpc := tmp*c;  // tmpc = (1,a_i,b_i,2,3)
    end while;


    // tmp*c should have order 1,2,3
    if not isEqual((tmpc)^6, One(Parent(c))) then
        error "BuildCycle (|c^{x^{m+1}}| \\nmid 6)";
    end if;

    // now tmp = c^(x^(m+1))

    if isEqual(tmp, c) or isEqual(tmp, c^2) or not isEqual((tmp^x*c)^5, One(Parent(c))) then
        return 2*m+3, y, yw;
    end if;

    samecycle := not isEqual(tmpc^2, One(Parent(c)));

    comm := isEqual(tmp^x*tmp^c, tmp^c*tmp^x);

    alphagtbeta := not (samecycle xor comm);

    if samecycle then
        if alphagtbeta then
            e := tmp^(x*c);
            ew := tmpw^(xw*cw);
        else
            e := (tmp^(x*c^2))^2;
            ew := (tmpw^(xw*cw^2))^2;
        end if;
    else
        if alphagtbeta then
            e := tmp^(x*c^2);
            ew := tmpw^(xw*cw^2);
        else
            e := (tmp^(x*c))^2;
            ew := (tmpw^(xw*cw))^2;
        end if;
    end if;

    z := tmp^e;
    zw := tmpw^ew;
    x2 := x^2;

    md := 0;
    tmp := z^x2;
    tmpw := zw^(xw^2);
    y := y*z;
    yw := yw*zw;
    tmpc := tmp*c;
    while not isEqual(tmpc, One(Parent(c))) and isEqual((tmpc)^5, One(Parent(c))) do 
        md +:= 1;
        if md ge N/2 then
            error "BuildCycle (m' \\geq N/2)";
        end if;
        y := y*tmp;
        yw := yw*tmpw;
        tmp := tmp^x2;
        tmpw := tmpw^(xw^2);
        tmpc := tmp*c;
    end while;



    return 2*m + 2*md + 5, y,yw;
end function;


/* Input:
 *  RP: a random process to compute random elements
 *  c: a three-cycle (1,2,3)
 *  cw: a word that evaluates to c
 *  eps: the failure probability
 *  N: The upper bound for the degree
 *  isEqual: method to test equality in the group
 * Output:
 *  k: a natural number >= 3/4*n, where n is the degree of the alternating group
 *  g: a k-cycle (1,2,3,...,k)
 * Failure:
 *  This method may fail if either c is not a three-cycle, or if not enough bolstering
 *  elements are found.
 */
ConstructLongCycle := function(RP, c, cw, eps, N, isEqual)
    G := Parent(c);

    R := Ceiling(7*Log(2/eps)/4);
    S := 7*N*R;

    c2 := c^2;

    bolst := 0;

    maxk := 0;
    maxg := One(Parent(c));
    maxgw := One(Parent(cw));

    for i in [1..S] do
        if bolst ge R then 
            break;
        end if;

        r,rw := Random(RP);

        cconjr := c^r;
        if isEqual(c*cconjr, cconjr*c) then
            continue;
        end if;
            
        cconjr2 := cconjr^r;
        cconjr2timesc := cconjr2*c;
        ctimesr := c*r;

        if isEqual(cconjr2, c) or isEqual(cconjr2, c2) or not isEqual(c*cconjr2, cconjr2timesc) then
            continue;
        end if;

        bolst +:= 1;

        zr := cconjr^(ctimesr)*cconjr^(cconjr2timesc);

        if isEqual(zr^3, One(G)) then
            x := c2*r;
            xw := cw^2*rw;
        elif isEqual(zr^5, One(G)) then
            x := ctimesr;
            xw := cw*rw;
        else
            error "BolsteringElement (|z_r| \\not\\in \\{3,5\\})";
        end if;

        k, g, gw := BuildCycle(c, x, cw, xw, N, isEqual);
        if k gt maxk then
            maxk := k;
            maxg := g;
            maxgw := gw;
        end if;

        // if the cycle is already long enough, return early
        if maxk gt 3*N/4 then
            return maxk, maxg, maxgw;
        end if;
    end for;

    if bolst lt Ceiling(7*Log(2/eps)/4) then
        // try to find a matching 5-cycle, in case it is A_5 or A_6 (5 tries is somewhat arbitrary!)
        for i in [1..5] do
            r,rw := Random(RP);
            g := c*c^r;
            if isEqual(g^5, One(G)) and not isEqual(g, One(G)) and isEqual((c^2*g)^3, One(G)) then
                return 5, g, cw*cw^rw;
            end if;
        end for;

        error Sprintf("ConstructLongCycle (Not enough bolstering elements, maxk = %o)", maxk);
    end if;

    return maxk, maxg, maxgw;
end function;


/* Input:
 *  x: a group element
 *  H: a list of group elements
 *  isEqual: method to test equality in the group
 * Output:
 *  true, if x commutes with at least two elements of H, false otherwise.
 */
commutesWithTwo := function(x, H, isEqual)
    commutes := 0;

    for i in [1..#H-1] do
        if isEqual(x*H[i], H[i]*x) then
            commutes +:= 1;
        end if;

        if commutes ge 2 then
            return true;
        end if;
    end for;

    if commutes eq 1 then   
        return isEqual(x*H[#H], H[#H]*x);
    end if;

    return false;
end function;


/* If g has order at most M, return this order.
 * Otherwise throw an error.
 */
orderUpTo := function(g, M, isEqual)
    one := One(Parent(g));

    tmp := one;
    for i in [1..M] do
        tmp := tmp*g;
        if isEqual(tmp, one) then
            return i;
        end if;
    end for;

    error "Adjust Cycle (orderUpTo: order is higher than given bound)";
end function;


/* Assumes that g is a 5-cycle and r is a 3-cycle.
 * Compute |supp(g) \cap supp(r)|.
 * May fail or return an incorrect answer if g is not a 5-cycle or r is not a 3-cycle.
 */
getIntersectionSize := function(g, r, isEqual)
    if isEqual(g*r, r*g) then
        return 0;
    end if;

    gr := g*r;

    if isEqual(gr^7, One(Parent(g))) then
        return 1;
    end if;

    w1 := orderUpTo(gr, 5, isEqual);
    w2 := orderUpTo(gr*r, 5, isEqual);

    if {w1, w2} eq {3,4} or {w1, w2} eq {4,5} then
        return 2;
    elif {w1, w2} eq {3,5} or {w1, w2} eq {2,5} then
        return 3;
    end if;

    error "AdjustCycle (getIntersectionSize: incorrect input)";
end function;


/* g = (1,2,3,4,5), c = (1,2,3), r some 3-cycle.
 * returns a list F, where F is the subset of {1,...,5} which is fixed by r
 */
getFixedPoints := function(g, c, r, isEqual)
    sigma := getIntersectionSize(g, r, isEqual);
    c123 := c;
    c234 := c123^g;
    c345 := c234^g;
    c145 := c345^g;
    c125 := c145^g;
    c124 := c123^c345;
    c135 := c125^c234;
    c235 := c234^c145;
    c134 := c234^(c125^-1);
    c245 := c235^c134;

    if sigma eq 3 then
        if isEqual(c123*r, r*c123) then
            return [4,5];
        elif isEqual(c124*r, r*c124) then
            return [3,5];
        elif isEqual(c125*r, r*c125) then
            return [3,4];
        elif isEqual(c134*r, r*c134) then
            return [2,5];
        elif isEqual(c135*r, r*c135) then
            return [2,4];
        elif isEqual(c145*r, r*c145) then
            return [2,3];
        elif isEqual(c234*r, r*c234) then
            return [1,5];
        elif isEqual(c235*r, r*c235) then
            return [1,4];
        elif isEqual(c245*r, r*c245) then
            return [1,3];
        elif isEqual(c345*r, r*c345) then
            return [1,2];
        else
            error "AdjustCycle (getFixedPoints failed)";
        end if;
    elif sigma eq 2 then
        if isEqual(c123*r, r*c123) then
            return [1,2,3];
        elif isEqual(c124*r, r*c124) then
            return [1,2,4];
        elif isEqual(c125*r, r*c125) then
            return [1,2,5];
        elif isEqual(c134*r, r*c134) then
            return [1,3,4];
        elif isEqual(c135*r, r*c135) then
            return [1,3,5];
        elif isEqual(c145*r, r*c145) then
            return [1,4,5];
        elif isEqual(c234*r, r*c234) then
            return [2,3,4];
        elif isEqual(c235*r, r*c235) then
            return [2,3,5];
        elif isEqual(c245*r, r*c245) then
            return [2,4,5];
        elif isEqual(c345*r, r*c345) then
            return [3,4,5];
        else
            error "AdjustCycle (getFixedPoints failed)";
        end if;
    elif sigma eq 1 then
        if not isEqual(c123*r, r*c123) then
            // 1, 2, or 3 is moved
            if isEqual(c124*r, r*c124) then
                return [1,2,4,5];
            elif isEqual(c134*r, r*c134) then
                return [1,3,4,5];
            elif isEqual(c234*r, r*c234) then
                return [2,3,4,5];
            else
                error "AdjustCycle (getFixedPoints failed)";
            end if;
        else
            // 4 or 5 is moved
            if not isEqual(c124*r, r*c124) then
                return [1,2,3,5];
            elif not isEqual(c125*r, r*c125) then
                return [1,2,3,4];
            else
                error "AdjustCycle (getFixedPoints failed)";
            end if;
        end if;
    elif sigma eq 0 then
        return [1,2,3,4,5];
    else
        error "AdjustCycle (getFixedPoints failed)";
    end if;
end function;



/* Input:
 *  g: (1,...,k)
 *  c: (1,2,3)
 *  r: a k0-cycle, such that r has at least two fixed points in {1,...,k} and at least one moved point in {1,...,k}
 *  gw: a word evaluating to g
 *  cw: a word evaluating to c
 *  rw: a word evaluating to r
 *  k: a natural number (length of k)
 * Output:
 *  x: (3,a_1,...,a_{k0-1}) with 1,2 \not\in {a_1,...,a_{k0-1}} and supp(r) \subseteq supp(x) \cup {1,...,k}
 *  xw: a word evaluating to x
 * Failure:
 *  This method fails if r has less than two fixed points or no moved points in {1,...,k}
 *  elements are found.
 */
AdjustCycle := function(g, c, r, gw, cw, rw, k, isEqual)
    if k eq 5 then
        // special handling of this case (to recognise A_5 and A_6)
        F := getFixedPoints(g, c, r, isEqual);

        if #F lt 2 or #F eq 5 then
            error "AdjustCycle (Cycle not adjustable)";
        end if;

        a := F[1];
        b := F[2];

        c123 := c;
        c123w := cw;
        c345 := g*c^2;
        c345w := gw*cw^2;

        x := r;
        xw := rw;

        // first ensure that 1 and 2 are fixed
        if a eq 1 and b ne 2 then
            c12b := c123^(c345^(b-3));
            c12bw := c123w^(c345w^(b-3));
            x := x^c12b;
            xw := xw^c12bw;
        elif a eq 2 then
            c12b := c123^(c345^(b-3));
            c12bw := c123w^(c345w^(b-3));
            x := x^(c12b^-1);
            xw := xw^(c12bw^-1);
        elif a gt 2 then
            c12a := c123^(c345^(a-3));
            c12b := c123^(c345^(b-3));
            c12aw := c123w^(c345w^(a-3));
            c12bw := c123w^(c345w^(b-3));
            x := x^(c12a*c12b);
            xw := xw^(c12aw*c12bw);
        end if;

        // now 1 and 2 are fixed. ensure that 3 is moved
        F := getFixedPoints(g, c, x, isEqual);
        M := [i : i in [1..5] | not i in F];

        a := M[1];
        if a ne 3 then
            c12a := c123^(c345^(a-2));
            c23a := c12a^(c123);
            c12aw := c123w^(c345w^(a-2));
            c23aw := c12aw^(c123w);
            x := x^(c23a^-1);
            xw := xw^(c23aw^-1);
        end if;

        return x, xw;
    end if;


    if k lt 7 then
        error "AdjustCycle (not enough points)";
    end if;


    F := [];
    nrfixedpoints := 0;
    nrmovedpoints := 0;


    t := c^(g^(-2));
    tg := t^g;
    tg2 := tg^g;
    tg3 := tg2^g;
    tg4 := tg3^g;

    ginv := g^-1;

    if k lt 11 then
        H1 := [t^2, t^(tg), t^(tg*tg3), t^(tg*tg3^2), t^(tg*tg3^2*tg4)];
        H2 := [t, tg, t^(g*tg3), t^(g*tg3^2), t^(g*tg3^2*tg4)];
    else
        t2g2 := (t^2*g)^2;
        H := [t, tg2, tg2^(t2g2), tg2^(t2g2^2), tg2^(t2g2^3)];
    end if;


    for j in [1..k] do
        isFixed := true;

        tg := ginv*t*g;
        tg2 := ginv*tg*g;

        if k lt 11 then
            // this is the method in the paper
            tg3 := ginv*tg2*g;
            tg4 := ginv*tg3*g;

            X := [t^r, tg2^r, t^(g^2*tg3*tg4*r)];

            for x in X do
                if commutesWithTwo(x, H1, isEqual) then
                    isFixed := false;
                    break;
                end if;
            end for;

            if isFixed then
                for x in X do
                    if commutesWithTwo(x, H2, isEqual) then
                        isFixed := false;
                        break;
                    end if;
                end for;
            end if;
        else
            // for k >= 11 there is a cheaper version

            X := [t^r, tg2^r];

            for x in X do
                if commutesWithTwo(x, H, isEqual) then
                    isFixed := false;
                    break;
                end if;
            end for;
        end if;


        if isFixed then
            nrfixedpoints +:= 1;
            Append(~F, j);
            if nrfixedpoints eq 1 then
                f1 := j;
            elif nrfixedpoints eq 2 then
                f2 := j;
            end if;
        else
            nrmovedpoints +:= 1;
            if nrmovedpoints eq 1 then
                m := j;
            end if;
        end if;

        if nrmovedpoints ge 1 and nrfixedpoints ge 2 and j ge 4 then
            break;
        end if;

        if k lt 11 then
            H1 := [ginv*z*g : z in H1];
            H2 := [ginv*z*g : z in H2];
            t := H2[1];
        else
            H := [ginv*z*g : z in H];
            t := H[1];
        end if;

    end for;

    if nrfixedpoints lt 2 or nrfixedpoints eq k then
        error "AdjustCycle (Cycle not adjustable)";
    end if;

    m := Minimum([i : i in [1..k] | not i in F]);
    f1 := F[1];
    f2 := F[2];

    if 1 in F then
        if 2 in F then
            if 3 in F then
                x := c^((g*c^2)^(m-3)*c)*c;
                xw := cw^((gw*cw^2)^(m-3)*cw)*cw;
            else
                x := One(Parent(g));
                xw := One(Parent(cw));
            end if;
        elif 3 in F then
            if 4 in F then
                x := c^g;
                xw := cw^gw;
            else
                x := (c^2)^g;
                xw := (cw^2)^gw;
            end if;
        else
            x := c^((g*c^2)^(f2-3)*c);
            xw := cw^((gw*cw^2)^(f2-3)*cw);
        end if;
    else
        if 2 in F then
            if 4 in F then
                x := c^(c^g);
                xw := cw^(cw^gw);
            elif 3 in F then
                x := (c^2)^(c^g);
                xw := (cw^2)^(cw^gw);
            else
                x := c^((g*c^2)^(f2-3)*c^g);
                xw := cw^((gw*cw^2)^(f2-3)*cw^gw);
            end if;
        elif 3 in F then
            x := (c^2)^((g*c^2)^(f2-3))*c^2;
            xw := (cw^2)^((gw*cw^2)^(f2-3))*cw^2;
        else
            x := c^((g*c^2)^(f2-3))*c^((g*c^2)^(f1-3));
            xw := cw^((gw*cw^2)^(f2-3))*cw^((gw*cw^2)^(f1-3));
        end if;
    end if;

    return r^x, rw^xw;
end function;


/* Input:
 *  g: (1,...,k)
 *  c: (1,2,3)
 *  r: (3,a_1,...,a_{k0-1}) a k0-cycle with 1,2, \not \in {a_1,...,a_{k0-1}}
 *  s: either 1 or (1,2,b) with b > k (the storage cycle)
 *  gw: a word evaluating to g
 *  cw: a word evaluating to c
 *  rw: a word evaluating to r
 *  sw: a word evaluating to s
 *  k: length of g
 *  k0: length of r
 *  n: degree
 *  isEqual: method to test equality in the group
 * Output:
 *  t: either 1 or (1,2,c) with c > m
 *  h: (1,...,m) with m >= k, such that supp(h) \cup supp(t) = supp(g) \cup supp(r) \cup supp(s)
 *  tw: a word evaluating to t
 *  hw: a word evaluating to h
 */
AppendPoints := function(g, c, r, s, gw, cw, rw, sw, k, k0, isEqual)
    /* set 
     * xj = (1,2,3),
     * gc2 = (3,...,k)
     */
    xj := c;
    xjw := cw;
    c2 := c^2;
    gc2 := g*c2;
    for j in [1..k0-1] do
        // xj = (1,2,a)
        xj := xj^r;
        xjw := xjw^rw;

        if isEqual(xj*gc2, gc2*xj) then
            // a \not \in supp(g), so a is a new point

            // new points can only be appended in pairs.
            // we use the storage cycle to save points.
            // if the storage cycle non-trivial, we have two points, and append them both
            if isEqual(s, One(Parent(g))) then
                // set s = (1,2,a)
                s := xj;
                sw := xjw;
            elif not isEqual(s, xj) then
                // now xj = (1,2,a) and s = (1,2,b), so s^(xj^2) = (1,b,a)
                k +:= 2;
                // g = (1,2,...,k,b,a)
                g := g*s^(xj^2);
                gw := gw*sw^(xjw^2);
                // gc2 = (3,...,k,b,a)
                gc2 := g*c2;
                s := One(Parent(g));
                sw := One(Parent(gw));
            end if;
        end if;
    end for;

    return g, s, gw, sw, k;
end function;



/* Input:
 *  RP: a random process to generate random words
 *  g: (1,...,k) with k >= 3/4*n, where n is the (unknown) degree of the alternating group
 *  c: (1,2,3)
 *  gw: a word evaluating to g
 *  cw: a word evaluating to c
 *  eps: the failure probability
 *  k: the length of k
 *  N: an upper bound for the degree
 *  isEqual: method to test equality in the group
 * Output:
 *  s: (3,...,n) if n is odd, (1,2)(3,...,n) if n is even
 *  t: (1,2,3)
 *  sw: a word evaluating to s
 *  tw: a word evaluating to t
 *  n: the degree of the group
 */
StandardGenerators := function(RP, g, c, gw, cw, eps, k, N, isEqual)
    s := One(Parent(g));
    sw := One(Parent(gw));
    k0 := k-2;
    x := g*c^2; // r = (3,...,k)
    xw := gw*cw^2;
    K := k;
    G := g;

    for i in [1..Ceiling(Log(10/3)^-1*(Log(N) + Log(1/eps)))] do
        r, rw := Random(RP);
        x := x^r;
        xw := xw^rw;
        m, mw := AdjustCycle(G, c, x, gw, cw, xw, K, isEqual);  // m = (3,a_1,...,a_{k0-1})

        G, s, gw, sw, K := AppendPoints(G, c, m, s, gw, cw, mw, sw, K, k0, isEqual); // G = (1,...,K)

        currentn := K + (isEqual(s, One(Parent(s))) select 0 else 1);

        vprintf AnRecog, 3: "Current n = %o\n", currentn;

        if currentn gt N then
            // group is provably not A_n
            error "Provably not A_n";
        end if;

        if currentn eq N then
            // we already found all points
            break;
        end if;
    end for;

    // K is always odd. If the storage cycle s is non-trivial, the degree is even and we are missing one point.
    // If n is even, then the first standard generator is (1,2)(3,...,K,K+1),
    // otherwise the first standard generator is (3,...,K)
    if isEqual(s, One(Parent(g))) then
        G := c^2*G;
        gw := cw^2*gw;
        C := c;
    else
        K := K + 1;
        G := G*s;
        gw := gw*sw;
        C := s;
        cw := sw;
    end if;

    if not CheckGenerators(G, C, K, isEqual) then
        error "StandardGenerators (Elements do not generate A_n)";
    end if;

    return G, C, gw, cw, K;
end function;


/* Input:
 *  t: a group element of even order
 *  w: a word evaluating to t
 *  N: an upper bound of the degree
 *  isEqual: method to test equality in the group
 * Output:
 *  s: a power of t which is an involution
 *  v: a word evaluating to v
 * Failure:
 *  The highest possible 2-power in A_n with n <= N is 2^Ceiling(Log(2,N))
 *  If t^(2^(Ceiling(Log(2,N)))) is \neq 1, then this method fails.
 */
ToInvolution := function(t, w, N, isEqual)
    tsq := t^2;
    a := 1;
    v := w;

    while not isEqual(tsq, One(Parent(t))) do
        t := tsq;
        v := v^2;
        tsq := tsq^2;
        a +:= 1;
        if a gt Log(2, N) + 1 then
            error "ToInvolution (Element order is too high)";
        end if;
    end while;

    return t,v;
end function;


/* Input:
 *  c: a suspected three-cycle
 *  N: an upper bound of the degree
 *  isEqual: method to test equality in the group
 * Output:
 *  false, if c is provably not a three-cycle, true otherwise.
 */
heuristicThreeCycleTest := function(c, N, isEqual)
    if not isEqual(c^3, One(Parent(c))) then
        return false;
    end if;

    for k in [1..Ceiling(Log(2,N))] do
        r := Random(Parent(c));
        // c*c^r is a product of two three-cycles, so it should have order 1,2, 3 or 5; 
        // in particular, the order should be divisible by 30
        // check (c*c^r)^32 eq (c*c^r)^2 instead, since (c*c^r)^32 can be computed faster than (c*c^r)^30
        y := c*c^r;

        if not isEqual(y^32, y^2) then
            return false;
        end if;
    end for;

    return true;
end function;


/* Compute the next three-cycle candidate.
 * 
 * The order in which the candidates are computed differs from the paper.
 * The method described in the paper is the following:
 * 1.) Compute B involutions.
 * 2.) For every involution t, compute a random conjugates c. 
 *     If (c,t) ne 1, then (c*t)^2 is a new candidate.
 *     For every t, compute at most T candidates, by considering at most C random conjugates.
 *     
 * A straight-forward implementation takes an involution and then considers up to C random conjugates.
 * If none is successful, take the next involution.
 * However, often the involution is a bad choice, i.e., either it has a very small or a very large support.
 * In the first case, it will almost always commute with a random conjugate, in the second case the product
 * with a random conjugate will not square to a three-cycle.
 *
 * Here we follow another approach. For every involution, we first consider only up to T random conjugates.
 * If none is successful, we move to the next involution. We save all involutions considered so far.
 * If this failed (i.e., for all B involutions all T random conjugates failed), we proceed in a linear manner:
 * We consider each involution in turn, and for each compute a new random conjugate.
 *
 * Thus in the end, the set of candidates returned by both approaches is the same, but the order
 * in which the candidates are returned differs.
 */
procedure GetNextThreeCycle(RP, ~c, ~w, ~involutions, ~involutionWords, ~countTries, ~countPutative, M, B, T, C, N, isEqual)
    while true do
        if #countTries gt 0 then
            m,i := Minimum(countTries);
        else
            m := T;
            i := 0;
        end if;

        // give each involutions at least T tries (m ge T)
        if m ge T and #involutions lt B then
            r,w := Random(RP);
            t := r^M;
            w := w^M;
            t, w := ToInvolution(t,w,N, isEqual);

            Append(~involutions, t);
            Append(~involutionWords, w);
            Append(~countTries, 0);
            Append(~countPutative, 0);

            i := #involutions;
            m := 0;
        end if;

        if m lt C then
            countTries[i] +:= 1;
            r,w := Random(RP);
            c := involutions[i]^r;
            w := involutionWords[i]^w;
            if not isEqual(c*involutions[i], involutions[i]*c) then
                countPutative[i] +:= 1;
                
                // if this involution already produced T candiates, set Tries to C, so we won't use it again
                if countPutative[i] eq T then
                    countTries[i] := C;
                end if;
                    
                c := (c*involutions[i])^2;
                w := (w*involutionWords[i])^2;

                break;
            end if;
        else
            vprint AnRecog, 2: "No more three cycles";
            error "GetNextThreeCycle (no more three-cycles)";
        end if;
    end while;
end procedure;



/* Check if G \cong A_n for some n \leq n and return standard generators.
 * This is done with a fixed probability of failure.
 * The method corresponds to Steps 3 -- 5 of Algorithm 4.29 (RecogniseSnAn)
 */
FindStandardGeneratorsAn := function(G, N, isEqual)
    M := Factorial(N);
    while M mod 2 eq 0 do
        M := M div 2;
    end while;

    B := Ceiling(13*Log(N)*Log(12));
    T := Ceiling(3*Log(12));
    C := Ceiling(3*N*T/5);


    W := WordGroup(G);
    RP := RandomProcessWithWords(G : WordGroup := W);

    discardedThreeCycles := 0;
    failedBuildCycle := 0;
    failedBolsteringElement := 0;
    failedConstructLongCycle := 0;
    failedAdjustCycle := 0;
    failedStandardGenerators := 0;

    threeCycleTime := 0;

    involutions := [];
    involutionWords := [];
    countTries := [];
    countPutative := [];

    while true do
        tim := Cputime();
        GetNextThreeCycle(RP, ~c, ~cw, ~involutions, ~involutionWords, ~countTries, ~countPutative, M, B, T, C, N, isEqual);

        if not heuristicThreeCycleTest(c, N, isEqual) then
            discardedThreeCycles +:= 1;
            continue;
        end if;
        tim := Cputime(tim);
        threeCycleTime +:= tim;


        try
            tim := Cputime();
            k, g, gw := ConstructLongCycle(RP, c, cw, 1/8, N, isEqual);
            tim := Cputime(tim);
            vprintf AnRecog: "Time spent to construct long cycle: %o\n", tim;

            IndentPush();
            tim := Cputime();
            g, C, gw, cw, n := StandardGenerators(RP, g, c, gw, cw, 1/8, k, N, isEqual);
            tim := Cputime(tim);
            IndentPop();
            vprintf AnRecog: "Time spent to build up cycle: %o\n", tim;

            failed := failedBuildCycle + failedBolsteringElement + failedConstructLongCycle + failedAdjustCycle + failedStandardGenerators;

            if failed gt 0 then
                vprintf AnRecog, 2: "Failed %o times\n", failed;
                vprintf AnRecog, 2: "Sources of failure:\n";
                if failedBuildCycle gt 0 then
                    vprintf AnRecog, 2: "  BuildCycle: %o\n", failedBuildCycle;
                end if;
                if failedBolsteringElement gt 0 then
                    vprintf AnRecog, 2: "  BolsteringElement: %o\n", failedBolsteringElement;
                end if;
                if failedConstructLongCycle gt 0 then
                    vprintf AnRecog, 2: "  ConstructLongCycle: %o\n", failedConstructLongCycle;
                end if;
                if failedAdjustCycle gt 0 then
                    vprintf AnRecog, 2: "  AdjustCycle: %o\n", failedAdjustCycle;
                end if;
                if failedStandardGenerators gt 0 then
                    vprintf AnRecog, 2: "  StandardGenerators: %o\n", failedStandardGenerators;
                end if;
            end if;
            vprintf AnRecog: "Time spent to construct 3-cycles: %o\n", threeCycleTime;

            return true, g, C, gw, cw, n;
        catch e
            x := e`Object;
            if Regexp("BuildCycle.*", x) then
                failedBuildCycle +:= 1;
            elif Regexp("BolsteringElement.*", x) then
                failedBolsteringElement +:= 1;
            elif Regexp("ConstructLongCycle.*", x) then
                failedConstructLongCycle +:= 1;
            elif Regexp("AdjustCycle.*", x) then
                failedAdjustCycle +:= 1;
            elif Regexp("StandardGenerators.*", x) then
                failedStandardGenerators +:= 1;
            else
                // rethrow any other errors
                error e;
            end if;

            vprint AnRecog, 3: e;
        end try;
    end while;

    return false, _, _, _, _, _;
end function;


isEqualStandard := function(a,b)
    return a eq b;
end function;

isEqualCentral := function(a,b)
    t := a*b^-1;

    for g in Generators(Parent(t)) do
        if g*t ne t*g then
            return false;
        end if;
    end for;

    return true;
end function;


/*
 * Input:
 *  G: a group
 *  N: an upper bound for the degree (default value 0)
 *     if N = 0, then the maximal possible degree is assumed as an upper bound
 *  Epsilon: a number between 0 and 1 (default value 0.01)
 *  Extension: true if G is suspected to be a central extension of Alt(n) or Sym(n) (default value false)
 *             if set, p2e is no longer a homomorphism
 *  Asymptotic: if true, the second map returned will perform better asymptotically, but worse in practice
 * Output:
 *  b: true if G is isomorphic to Alt(n) or Sym(n)
 *     false if not (in which case nothing else is returned)
 *  e2p: an isomorphism from G to Alt(n) or Sym(n)
 *  p2e: an isomorphism from Alt(n) or Sym(n) to G
 *  e2w: an isomorphism from G to WordGroup(G)
 *  w2e: an isomorphism from WordGroup(G) to G
 *  o: true if G is isomorphic to Sym(n), false if G is isomorphic to Alt(n)
 * Probability of incorrectly returning false:
 *  at most Epsilon
 * Side effects:
 *  G`AlternatingOrSymmetricData is set to a tuple with the following contents:
 *   o: true iff G contains an odd permutation, whence G is isomorphic to Sym(n)
 *   n: the degree of G as a permutation group
 *   s: an element of G corresponding to (3, 4, ..., n) (n odd) or (1, 2)(3, 4, ..., n) (n even)
 *   t: an element of G corresponding to (1, 2, 3)
 *   y: a word in the generators of G which evaluates to s
 *   z: a word in the generators of G which evaluates to t
 *   Z: the centre of G
 */
intrinsic RecogniseAlternatingOrSymmetric(G::Grp : N := 0, Epsilon := 0.01, Extension := false, Asymptotic := false) -> BoolElt, Map, Map, Map, Map, BoolElt
{ If G is isomorphic to the alternating or symmetric group of degree n >= 5, 
the function returns true, a homomorphism from G to Alt(n) or Sym(n), 
a homomorphism from Alt(n) or Sym(n) to G, a map from G to its word group, 
a map from the word group to G, and a boolean to indicate if G is either 
alternating or symmetric. Otherwise, the function returns false. 
The algorithm is that of Jambor, Leuner, Niemeyer, and Plesken [JLNP13], so there is a small probability
(controlled by Epsilon) that it will return false incorrectly. 
If Extension is true, the function decides whether G/Z(G) is isomorphic to 
the alternating or symmetric group of degree n; now the second map is 
not a homomorphism, but induces a natural homomorphism from Alt(n) or Sym(n) 
to G/Z(G).}
    require Type (G) in {GrpPerm, GrpMat}: "Input group type incorrect";

    if N lt 5 then
        if Type (G) eq GrpPerm then
            N := Degree(G);
        else 
            /* If n >= 10, then the smallest irreducible A_n-module is the 
             * fully deleted permutation module (Kleidman-Liebeck, Proposition 5.3.5).
             * It has dimension n-2 if p|n and dimension n-1 otherwise.
             */
            p := Characteristic(CoefficientRing(G));
            d := Degree(G);
            if (d+2) mod p eq 0 then
                N := d+2;
            else
                N := d+1;
            end if;

            N := Maximum(9, N);
        end if;
    end if;

    vprintf AnRecog: "Using upper bound N = %o\n", N;

	if assigned G`AlternatingOrSymmetricData then
        T := G`AlternatingOrSymmetricData;
        o := T[1];
        n := T[2];
        if n gt N then
            return false, _, _, _, _, _;
        end if;
        P := o select Sym(n) else Alt(n);
        W := Parent(T[5]);

        E2P := T[9];
        P2E := T[10];
        E2W := T[11];

        e2p := hom<G -> P | g :-> P ! E2P(g)>;
        p2e := hom<P -> G | a :-> P2E(a)>;
        e2w := hom<G -> W | g :-> E2W(g)>;
        w2e := hom<W -> G | w :-> Evaluate(w, G)>;
        return true, e2p, p2e, e2w, w2e, o;
    end if;

    if Extension then
        isEqual := isEqualCentral;
    else
        isEqual := isEqualStandard;
    end if;

    try
        for TT in [1..Ceiling(Log(2, Epsilon^-1))] do
            T := Cputime();
            b,s,t,x,y,n := FindStandardGeneratorsAn(G, N, isEqual);
            T := Cputime(T);

            vprintf AnRecog: "Total time spent to compute standard generators: %o\n", T;

            if b then
                T := Cputime();
                b,a1,a2,a3,a4,o := VerifyAlternatingOrSymmetric(s,t,x,y,n : Extension := Extension, Asymptotic := Asymptotic);
                T := Cputime(T);
                vprintf AnRecog: "Time to verify standard generators: %o\n", T;
                if b then
                    return b,a1,a2,a3,a4,o;
                end if;
                vprintf AnRecog: "Verification failed\n";
            end if;
        end for;
    catch e
        x := e`Object;
        if Regexp("ToInvolution.*", x) or Regexp("GetNextThreeCycle.*", x) or Regexp("Provably not A_n.*", x) then
            // GetNextThreeCycle failed, so G is definitely not A_n for n \leq N
            return false, _, _, _, _, _;
        else
            error e;
        end if;
    end try;

    return false, _, _, _, _, _;
end intrinsic;
