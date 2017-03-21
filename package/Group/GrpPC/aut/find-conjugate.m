freeze;

/*  Find an elt of T which conjugates K to give the action
    of m (an automorphism of K) on K.
*/
FindConjugate := function (T, K, m)

    C := T;
    t := Id(T);

    for i in [1..NDgens(K)] do
        k := K.i;
        b, c := IsConjugate(C, k ^ t, k @ m);
        error if not b, "Action does not appear to be by conjugation on generator:", k;
        t *:= c;
        C := Centraliser(C, k @ m);
    end for;

    return t;

end function;

intrinsic FindConjugate ( T :: GrpPC, K :: GrpPC, m :: Map ) -> GrpPCElt
{Find an elt of T which conjugates K to give the action of m (an automorphism of K) on K.}
    return FindConjugate(T, K, m);
end intrinsic;

/* Equivalent to FindConjugate defined above, but uses Generators instead of
   PCGenerators in search
*/
FindConjugateGrpPerm := function (T, K, m)

    C := T;
    t := Id(T);

    for k in Generators(K) do
        b, c := IsConjugate(C, k ^ t, k @ m);
        error if not b, "Action does not appear to be by conjugation on generator: ", k;
        t *:= c;
        C := Centraliser(C, k @ m);
    end for;

    return t;

end function;


/* Equivalent to FindConjugate, but returns two values: true/false on finding
   a conjugating element, and then the conjugating element.
*/
FindConjugate_ := function (T, K, m)

    C := T;
    t := Id(T);

    for k in PCGenerators(K) do
        b, c := IsConjugate(C, k ^ t, k @ m);
        if not b then return false, _; end if;
        t *:= c;
        C := Centraliser(C, k @ m);
    end for;

    return true, t;

end function;

intrinsic IsConjugateInSubgroup ( G :: GrpPC, S :: GrpPC, H :: GrpPC, K :: GrpPC ) -> BoolElt, GrpPCElt
{Look at the conjugates of H by S and see if H^s = K for some s\in S.  All are subgroups of G.}

    vprint AutomorphismGroupSolubleGroup : "IsConjugateInSubgroup...";
    IndentPush();

    /* check for identity */
    if H eq K then
        IndentPop();
        return true, Id(S);
    end if;

    vprint AutomorphismGroupSolubleGroup : "Attempting to use internal IsConjugate...";
    vtime AutomorphismGroupSolubleGroup : b, x := IsConjugate(G, H, K);

    if not b then
        vprint AutomorphismGroupSolubleGroup : "Subgroups are not conjugate in G";
        IndentPop();
        return false, _;
    end if;

    if x in S then
        IndentPop();
        return true, x;
    else
        vprint AutomorphismGroupSolubleGroup : "IsConjugate returned non-S elt, constructing orbit...";
    end if;

    orbit := {@ PowerGroup(G) | H @};

    /* list of generator indices which construct orbit */
    orbit_gens_indices := [ Integers() | ];
    relative_orders := PCPrimes(S);

    vprint AutomorphismGroupSolubleGroup : "Computing orbit...";
    vtime AutomorphismGroupSolubleGroup : for i in [NPCgens(S)..1 by -1] do
        s := S.i;
        imgH := H ^ s;

        if imgH eq K then
            IndentPop();
            return true, s;
        end if;

        /* only check if it's in the orbit, if not then generate the new
           bit for testing finding K */
        if imgH notin orbit then
            /* take a snapshot of the orbit size before adding stuff */
            _orbit_len := #orbit;
            /* go through each of the non-trivial orders of the map */
            for j in [1..(relative_orders[i]-1)] do
                for k in [1.._orbit_len] do
                    nelt := orbit[k] ^ s;
                    if nelt eq K then
                        /* So orbit[k] ^ s eq K */
                        /* work out which element conjugates H to orbit[k] */
                        _index := k - 1;
                        _pow := 0;
                        _len := _orbit_len;
                        s := s^-1;
                        for l in Reverse(orbit_gens_indices) do
                            if _index eq 0 then break; end if;
                            /* find the order of the last orbit extending generator */
                            /* need to split the orbit into r_j parts */
                            _len div:= relative_orders[l];
                            /* and determine the power that was applied */
                            _pow := _index div _len;
                            /* apply the inverse */
                            s *:= S.l^-_pow;
                            /* shift the index for the next value */
                            _index -:= _pow * _len;
                        end for;
                        assert H^(s^-1) eq K;

                        IndentPop();
                        return true, s^-1;
                    end if;
                    assert nelt notin orbit;
                    Include(~orbit, nelt);
                end for;
                /* do the next power */
                s *:= S.i;
            end for;
            Append(~orbit_gens_indices, i);
        end if;
    end for;

    IndentPop();
    return false, _;

end intrinsic;
