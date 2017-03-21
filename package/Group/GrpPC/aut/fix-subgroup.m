freeze;

/* Testing the new polycyclic orbit stabiliser code */
declare verbose TestNewPolycyclicOrbitStabiliser, 1;

/* Testing the polycyclic orbit stabiliser code against standard method */
declare verbose TestPolycyclicOrbitStabiliser, 1;

/*  Computes the subgroup of A which fixes H.  Uses standard orbit-stabiliser method
    - no optimisations.

    A - automorphism group of some group G
    H - subgroup of G
*/
FixSubgroup_NormalOrbitStabilizer := function (A, H : orbit_limit := 0)

    IndentPush();

    vprint AutomorphismGroupSolubleGroup : "Using normal orbit stabilizer method";

    id := Identity(A);

    if Type(H) eq GrpPC then
        /* use the powergroup for the orbit if H is PC */
        orbit := {@ PowerGroup(A`Group) | H @};
    else
        orbit := {@ H @};
    end if;

    gens := [ A | id ];
    fixH := {@ A | @};

    i := 1;
    vprint AutomorphismGroupSolubleGroup : "Computing orbit...";
    vtime AutomorphismGroupSolubleGroup : while i le #orbit do
        Hc := orbit[i];
        for j in [1..Ngens(A)] do
            a := A.j;
            Hca := Hc @ a;
            if Hca in orbit then
                na := gens[Index(orbit, Hca)] * a^-1 * gens[i]^-1;
                if na ne id then
                    Include(~fixH, na);
                end if;
            else
                Include(~orbit, Hca);
                if orbit_limit gt 0 and #orbit gt orbit_limit then
                    IndentPop(); return false;
                end if;
                Append(~gens, gens[i] * a);
            end if;
        end for;
        i +:= 1;
    end while;

    /* Check if we needed to do this calculation (returned same group) */
    if #orbit eq 1 then
        vprint AutomorphismGroupSolubleGroup : "Same group, don't need to construct subgroup!";
        IndentPop();
        return A;
    end if;

    vprint AutomorphismGroupSolubleGroup : "Orbit length: ", #orbit;

    vprint AutomorphismGroupSolubleGroup : "Constructing subgroup of automorphism group...";
    vtime AutomorphismGroupSolubleGroup : Stab_A := sub < A | [a : a in fixH] >;

    /* this will prompt the construction of a rep, so set to assertion level 2 */
    assert2 #orbit * #Stab_A eq #A;

    /* need to set this here for later checks - maybe verify that it
       isn't actually soluble... */
    Stab_A`Soluble := false;

    IndentPop();

    return Stab_A;

end function;


/*  Computes the subgroup of A which fixes H, assumes that A is polycylic and
    has the attributes A`PCGenerators and A`PCGroup defined.

    A - polycyclic automorphism group of some group G
    H - subgroup of G
*/
FixSubgroup_PolycyclicOrbitStabilizer := function (A, H : orbit_limit := 0)

    IndentPush();

    vprint AutomorphismGroupSolubleGroup : "Using PC orbit stabilizer method";

    _, phi_A, R_A := RepresentationAutomorphismGroupPGroup(A);

    if Type(H) eq GrpPC then
        /* use the powergroup for the orbit if H is PC */
        orbit := {@ PowerGroup(A`Group) | H @};
    else
        orbit := {@ H @};
    end if;

    orbit_gens := [ Identity(A) ];

    gens := PCGenerators(A);
    relative_orders := PCPrimes(A`PCGroup[1]);

    stabH := {@ A | @};

    vprint AutomorphismGroupSolubleGroup : "Computing orbit...";
    vtime AutomorphismGroupSolubleGroup : for i in [#gens..1 by -1] do
        a := gens[i];
        imgH := H @ a;

        if imgH in orbit then
            orbit_index := Index(orbit, imgH);
            Include(~stabH, a * orbit_gens[orbit_index]^-1);
        else
            for k in [1..#orbit] do
                an := orbit_gens[k];

                for j in [1..(relative_orders[i]-1)] do
                    an *:= a;

                    imgH := H @ an;
                    /* Should not be already here in polycyclic rep */
                    assert imgH notin orbit;

                    Include(~orbit, imgH);
                    if orbit_limit gt 0 and #orbit gt orbit_limit then
                        IndentPop(); return false;
                    end if;
                    Append(~orbit_gens, an);
                end for;
            end for;
        end if;
    end for;

    if #orbit eq 1 then
        vprint AutomorphismGroupSolubleGroup : "Same group, don't need to construct new rep or subgroup...";
        IndentPop();
        return A;
    end if;

    vprint AutomorphismGroupSolubleGroup : "Orbit length: ", #orbit;

    /* Construct the representation first, and then use the generators of this
       to construct the automorphism group - to ensure that the generators of the
       rep match. */
    vprint AutomorphismGroupSolubleGroup : "Computing PC rep...";
    vtime AutomorphismGroupSolubleGroup : R_A_stabH, R_A_stabHtoR_A := sub < R_A | [ a @ phi_A : a in stabH ] >;
    //R_A_stabH, R_A_stabHtoR_A := sub < R_A | R_stabH >;

    /* check that the stabiliser is the correct size */
    assert #R_A_stabH * #orbit eq #R_A;

    vprintf AutomorphismGroupSolubleGroup : "Order of stabiliser: %o (%o)\n", #R_A_stabH, FactoredOrder(R_A_stabH);

    vprint AutomorphismGroupSolubleGroup : "Mapping rep generators back to automorphisms...";
    vtime AutomorphismGroupSolubleGroup : A_stabH_PCGenerators := {@ r_a @@ phi_A : r_a in PCGenerators(R_A_stabH) @};

    vprint AutomorphismGroupSolubleGroup : "Constructing subgroup of automorphism group";
    vtime AutomorphismGroupSolubleGroup : A_stabH := sub < A | [ a : a in A_stabH_PCGenerators ] >;

    map_to_rep_elt := function (m)
        /* check that m fixes H */
        error if (H @ m) ne H, "Map does not fix H";

        /* coerce result from rep of A into rep for A_ */
        return R_A_stabH!(m @ A`MapToRepElt);
    end function;

    A_stabH`MapToRepElt := map_to_rep_elt;

    h := hom < A_stabH -> R_A_stabH | x :-> R_A_stabH!(x @ phi_A), y :-> (R_A!y) @@ phi_A >;
    A_stabH`PCGroup := < R_A_stabH, h >;

    A_stabH`Soluble := true;
    A_stabH`PCGenerators := A_stabH_PCGenerators;

    A_stabH`RepMap := A_stabH`PCGroup[2];
    A_stabH`RepGroup := A_stabH`PCGroup[1];

    A_stabH`Order := #A_stabH`RepGroup;

    assert2 CheckPCRepresentation(A_stabH);

    IndentPop();

    return A_stabH;

end function;

/* New FixSubgroup which doesn't store all the automorphisms */
NewFixSubgroup_PolycyclicOrbitStabilizer := function (A, H : orbit_limit := 0)

    IndentPush();

    vprint AutomorphismGroupSolubleGroup : "Using new PC orbit stabilizer method";

    _, phi_A, R_A := RepresentationAutomorphismGroupPGroup(A);

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

    stabH := {@ A | @};

    vprint AutomorphismGroupSolubleGroup : "Computing orbit...";
    vtime AutomorphismGroupSolubleGroup : for i in [#gens..1 by -1] do
        a := gens[i];
        imgH := H @ a;

        orbit_index := Index(orbit, imgH);
        if orbit_index ne 0 then
            /* compute the map which sends H -> imgH */
            _index := orbit_index - 1;
            _pow := 0;
            _len := #orbit;
            for j in Reverse(orbit_gens_indices) do
                if _index eq 0 then break; end if;
                /* need to split the orbit into chunks */
                _len div:= relative_orders[j];
                /* and determine the power that was applied */
                _pow := _index div _len;
                /* apply the inverse */
                a *:= gens[j]^-_pow;
                /* shift the index for the next value */
                _index -:= _pow * _len;
            end for;
            assert (H @ a) eq H;
            Include(~stabH, a);
        else
            Append(~orbit_gens_indices, i);
            _len := #orbit;
            for j in [1..(relative_orders[i]-1)] do
                for k in [1.._len] do
                    nelt := orbit[k] @ a;
                    assert nelt notin orbit;
                    Include(~orbit, nelt);
                    if orbit_limit gt 0 and #orbit gt orbit_limit then
                        IndentPop(); return false;
                    end if;
                end for;
                a *:= gens[i];
            end for;
        end if;
    end for;

    /* check to see if any non-trivial subgroups are in the orbit */
    if #orbit eq 1 then
        vprint AutomorphismGroupSolubleGroup : "Same group, don't need to construct new rep or subgroup...";
        IndentPop();

        return A, orbit, orbit_gens_indices;
    end if;

    vprint AutomorphismGroupSolubleGroup : "Orbit length: ", Factorisation(#orbit);

    /* Construct the representation first, and then use the generators of this
       to construct the automorphism group - to ensure that the generators of the
       rep match. */
    vprint AutomorphismGroupSolubleGroup : "Computing PC rep...";
    vtime AutomorphismGroupSolubleGroup : R_A_stabH, R_A_stabHtoR_A := sub < R_A | [ a @ phi_A : a in stabH ] >;

    /* check that the stabiliser is the correct size */
    assert #R_A_stabH * #orbit eq #R_A;

    vprintf AutomorphismGroupSolubleGroup : "Order of stabiliser: %o (%o)\n", #R_A_stabH, FactoredOrder(R_A_stabH);

    vprint AutomorphismGroupSolubleGroup : "Mapping rep generators back to automorphisms...";
    vtime AutomorphismGroupSolubleGroup : A_stabH_PCGenerators := {@ r_a @@ phi_A : r_a in PCGenerators(R_A_stabH) @};

    vprint AutomorphismGroupSolubleGroup : "Constructing subgroup of automorphism group";
    vtime AutomorphismGroupSolubleGroup : A_stabH := sub < A | [ a : a in A_stabH_PCGenerators ] >;

    map_to_rep_elt := function (m)
        /* check that m fixes H */
        error if (H @ m) ne H, "Map does not fix H";

        /* coerce result from rep of A into rep for A_ */
        return R_A_stabH!(m @ A`MapToRepElt);
    end function;

    A_stabH`MapToRepElt := map_to_rep_elt;

    h := hom < A_stabH -> R_A_stabH | x :-> R_A_stabH!(x @ phi_A), y :-> (R_A!y) @@ phi_A >;
    A_stabH`PCGroup := < R_A_stabH, h >;

    A_stabH`Soluble := true;
    A_stabH`PCGenerators := A_stabH_PCGenerators;

    A_stabH`RepMap := A_stabH`PCGroup[2];
    A_stabH`RepGroup := A_stabH`PCGroup[1];

    A_stabH`Order := #A_stabH`RepGroup;

    assert2 CheckPCRepresentation(A_stabH);

    IndentPop();

    return A_stabH, orbit, orbit_gens_indices;

end function;


/*  Computes the subgroup of the automorphism group A fixing subgroup H using
    a matrix rep of A.  Assumes that A`MatrixGroup is set and is a GL(n,p) matrix
    group.
*/
FixSubgroup_GL := function (A, H)

    vprint AutomorphismGroupSolubleGroup : "Using GL stabiliser method";

    M := A`MatrixGroup;
    V := VectorSpace(M);

    P := A`Group;
    Hgens := [ P!h : h in PCGenerators(H) ];

    W := sub < V | [ V!Eltseq(h) : h in Hgens ] >;

    W_stab := GLSubspaceStabiliser(A`MatrixGroup, W);
    A_stab := AutomorphismGroup(P, [ p : p in PCGenerators(P) ], [ [ P!ChangeUniverse(Eltseq((V!Eltseq(P.i)) * W_stab.j), Integers()) : i in [1..NPCgens(P)] ] : j in [1..Ngens(W_stab)] ]);

    A_stab`MatrixGroup := W_stab;
    A_stab`Soluble := false;

    return A_stab;

end function;


/*  Computes the subgroup of A which fixes H.  The optional parameter 'reduce_before_orbit'
    can attempt to reduce the size of the orbit in the orbit-stabiliser computation by
    computing the subgroup of A which fixes H.Z(G) using a normaliser calculation.

    A - automorphism group of some group G
    H - subgroup of G
    reduce_before_orbit - true/false
    orbit_limit - if > 0 then this stops the calculation if the orbit exceeds the value

    NB. Orbit reduction code assumes that A is an automorphism group of a p-group.
*/
FixSubgroup := function (A, H : reduce_before_orbit := false, orbit_limit := 0)

    /* Check A`Group is elementary abelian and we have a matrix representation of A */
    if IsElementaryAbelian(A`Group) and assigned A`MatrixGroup then
        return FixSubgroup_GL(A, H);
    end if;

    P := A`Group;

    if reduce_before_orbit then
        if not IsAbelian(P) then
            IndentPush();
            vprint AutomorphismGroupSolubleGroup : "Attempting to reduce orbit of fix subgroup calculation.";

            /* construct a rep if there isn't one already */
            MapToRepElt, phi_A, R_A := RepresentationAutomorphismGroupPGroup(A);

            InnHgens := [ MapToRepElt(hom < P -> P | [ P.i^h : i in [1..NPCgens(P)] ] : Check := false>) : h in PCGenerators(H) ];
            R_N := Normaliser(R_A, sub < R_A | InnHgens >);
            R_Ngens := [ R_N.i : i in [1..NDgens(R_N)] ];

            Pgens := [ p : p in PCGenerators(P) ];

            A_ := AutomorphismGroup2(P, Pgens, [ Pgens @ (r_n @@ phi_A) : r_n in R_Ngens ]);

            if Type(R_A) eq GrpPC then
                map_to_rep_elt := function ( m )
                    r := m @ MapToRepElt;
                    assert2 r in R_N;
                    return R_N!r;
                end function;
                A_`MapToRepElt := map_to_rep_elt;

                /* TODO: this is slow! */
                // R_N_to_A_ := hom < R_N -> A_ | [ A_.i : i in [1..Ngens(A_)] ] >;
                F, phi_F := FPGroup(R_N); F_to_A_ := hom < F -> A_ | [ A_.i : i in [1..Ngens(A_)] ] >;
                phi_A_ := hom < A_ -> R_N | x :-> map_to_rep_elt(x), y :-> (y @@ phi_F) @ F_to_A_ >;

                A_`PCGroup := < R_N, phi_A_ >;
                A_`Order := #R_N;
                A_`PCGenerators := {@ A_.i : i in [1..Ngens(A_)] @};

                A_`RepMap := A_`PCGroup[2];
                A_`RepGroup := A_`PCGroup[1];

                A_`Soluble := true;
                A_`Order := #A_`RepGroup;

                assert CheckPCRepresentation(A_);
            else
                A_`Soluble := false;
            end if;

            IndentPop();
        else
            A_ := A;
        end if;
    else
        A_ := A;
    end if;

    /*if assigned A_`PCGroup then
        if IsVerbose("TestPolycyclicOrbitStabiliser") then
            print "Running normal orbit stabiliser...";
            time MA := FixSubgroup_NormalOrbitStabilizer(A_, H);
        end if;

        print "Running polycyclic orbit stabiliser...";
        time NA := NewFixSubgroup_PolycyclicOrbitStabilizer(A_, H);
        return NA;
    end if;*/

    if not IsVerbose("TestPolycyclicOrbitStabiliser") and assigned A_`PCGroup then
        vprint TestNewPolycyclicOrbitStabiliser : "New PolycyclicOrbit";
        vtime TestNewPolycyclicOrbitStabiliser : NA := NewFixSubgroup_PolycyclicOrbitStabilizer(A_, H : orbit_limit := orbit_limit);

        if IsVerbose("TestNewPolycyclicOrbitStabiliser") then
            print "Old PolycyclicOrbit";
            time MA := FixSubgroup_PolycyclicOrbitStabilizer(A_, H);
            print "Normal Orbit";
            time GA := FixSubgroup_NormalOrbitStabilizer(A_, H);
            phi_NA, R_NA := PermutationRepresentation(NA);
            phi_GA, R_GA := PermutationRepresentation(GA);
            phi_MA, R_MA := PermutationRepresentation(MA);
            assert #R_MA eq #R_NA;
            assert #R_NA eq #R_GA;
        end if;
        return NA;
    end if;

    return FixSubgroup_NormalOrbitStabilizer(A_, H : orbit_limit := orbit_limit);

end function;