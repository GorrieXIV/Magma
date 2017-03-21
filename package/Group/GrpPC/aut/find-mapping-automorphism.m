freeze;

/* Find an element a in A such that (H @ a) eq K, uses naive orbit stabiliser method. */
FindMappingAutomorphism_OrbitStabiliser := function (A, H, K)

    /* Use the power group for the orbit set type */
    if Type(H) eq GrpPC then
        /* use the powergroup for the orbit if H is PC */
        orbit := {@ PowerGroup(A`Group) | H @};
    else
        orbit := {@ H @};
    end if;
    gens := [ A | Id(A) ];

    i := 1;
    while i le #orbit do
        Horb := orbit[i];
        for a in [ A.i : i in [1..Ngens(A)]] do
            Himg := Horb @ a;
            if Himg eq K then
                return true, gens[i] * a;
            else
                if not Himg in orbit then
                    Include(~orbit, Himg);
                    Append(~gens, gens[i] * a);
                end if;
            end if;
        end for;
        i +:= 1;
    end while;

    return false, _;

end function;


/* Find an element a in A such that (H @ a) eq K, assumes that A is polycyclic and uses specialised
   orbit stabiliser method */
FindMappingAutomorphism_Polycyclic := function (A, H, K)

    IndentPush();
    vprint AutomorphismGroupSolubleGroup : "Using PC orbit stabilizer method";

    /* use power group for universe of orbit set */
    if Type(H) eq GrpPC then
        /* use the powergroup for the orbit if H is PC */
        orbit := {@ PowerGroup(A`Group) | H @};
    else
        orbit := {@ H @};
    end if;
    orbit_gens := [ Identity(A) ];

    gens := PCGenerators(A);
    relative_orders := PCPrimes(A`PCGroup[1]);

    vprint AutomorphismGroupSolubleGroup : "Computing orbit...";
    vtime AutomorphismGroupSolubleGroup : for i in [#gens..1 by -1] do
        a := gens[i];
        imgH := H @ a;

        if imgH eq K then
            IndentPop();
            return true, a;
        elif imgH notin orbit then
            for k in [1..#orbit] do
                an := orbit_gens[k];

                for j in [1..(relative_orders[i]-1)] do
                    an *:= a;

                    imgH := H @ an;

                    if imgH eq K then
                        IndentPop();
                        return true, an;
                    end if;

                    /* Should not be already here in polycyclic rep */
                    assert imgH notin orbit;

                    Include(~orbit, imgH);
                    Append(~orbit_gens, an);
                end for;
            end for;
        end if;
    end for;

    IndentPop();
    return false, _;

end function;


NewFindMappingAutomorphism_Polycyclic := function (A, H, K)

    IndentPush();
    vprint AutomorphismGroupSolubleGroup : "Using new PC orbit stabilizer method";

    if Type(H) eq GrpPC then
        /* use the powergroup for the orbit if H is PC */
        orbit := {@ PowerGroup(A`Group) | H @};
    else
        orbit := {@ H @};
    end if;

    /* list of generator indices which construct orbit */
    orbit_gens_indices := [ Integers() | ];

    gens := PCGenerators(A);
    relative_orders := PCPrimes(A`PCGroup[1]);

    vprint AutomorphismGroupSolubleGroup : "Computing orbit...";
    vtime AutomorphismGroupSolubleGroup : for i in [#gens..1 by -1] do
        a := gens[i];
        imgH := H @ a;

        if imgH eq K then
            IndentPop();
            return true, a;
        end if;

        if imgH notin orbit then
            /* take a snapshot of the orbit size before adding stuff */
            _orbit_len := #orbit;
            /* go through each of the non-trivial orders of the map */
            for j in [1..(relative_orders[i]-1)] do
                for k in [1.._orbit_len] do
                    nelt := orbit[k] @ a;
                    if nelt eq K then
                        /* work out which element maps H -> orbit[k] */
                        _a := a^-1;
                        _index := k - 1;
                        _pow := 0;
                        _len := _orbit_len;
                        for l in Reverse(orbit_gens_indices) do
                            if _index eq 0 then break; end if;
                            /* find the order of the last orbit extending generator */
                            /* need to split the orbit into r_j parts */
                            _len div:= relative_orders[l];
                            /* and determine the power that was applied */
                            _pow := _index div _len;
                            /* apply the inverse */
                            _a *:= gens[l]^-_pow;
                            /* shift the index for the next value */
                            _index -:= _pow * _len;
                            assert K @ _a eq orbit[_index+1];
                        end for;
                        assert (H @@ _a) eq K;
                        IndentPop();
                        return true, _a;
                    end if;
                    assert nelt notin orbit;
                    Include(~orbit, nelt);
                end for;
                /* do the next power */
                a *:= gens[i];
            end for;
            Append(~orbit_gens_indices, i);
        end if;
    end for;

    IndentPop();
    return false, _;

end function;


/* FindMappingAutomorphism general function which finds the automorphism a in A which sends H -> K.  If A is soluble,
   then it is assumed to have PC presentation, and we use the polycyclic method */

FindMappingAutomorphism := function (A, H, K)

    if H eq K then return true, Id(A); end if;

    /* Require PCGenerators for A and A`PCGroup for PC orbit-stab algorithm */
    if assigned A`PCGenerators and assigned A`PCGroup then
        return FindMappingAutomorphism_Polycyclic(A, H, K);
    end if;

    return FindMappingAutomorphism_OrbitStabiliser(A, H, K);

end function;