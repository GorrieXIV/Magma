freeze;

///////////////////////////////////////////////////////
//                                                   // 
// Compute the new and old parts, and inner twists,  //
// of a "principal space" (using Hecke action)       //
//                                                   //
// November 2013, SRD                                //
//                                                   //
///////////////////////////////////////////////////////


// For a newform space M, this stores a subgroup of 
// ClassGroup(Integers(BaseField(M))) on which M is
// known to have some nonzero Hecke operators.
// It is not necessarily the largest such subgroup.
// The value is a set of ideals generating the group.

declare attributes ModFrmHil : InnerTwistSubgroup; 


Q := RationalField();


intrinsic NewAndOldSubspaces(M::ModFrmBianchi) -> ModTupFld, ModTupFld

{The new subspace and old subspace of M, returned as vector spaces}

    require not assigned M`Ambient :
        "The argument must be a full space (defined using BianchiCuspForms)";

    V := VectorSpace(Q, Dimension(M));

    if Dimension(M) eq 0 then
        return V, V;
    end if;

    assert IsOne(NewLevel(M));
    N0 := Level(M);

    F := BaseField(M);
    ZF := Integers(F);
    C, mC := ClassGroup(ZF);
    C2 := 2*C;

    // Currently only initialize here, so ensure plenty
    // (can afford it)
    // TO DO: re-init when run out of PPrimes or Ideals
    B := #C * 1000;
    Primes  := PrimesUpTo(B, F : coprime_to := N0);
    PPrimes := [ P : P in Primes | IsPrincipal(P) ];
    Ideals  := [ P : P in Primes | P @@ mC in C2 ] cat
               [ Pi*Pj : i in [1 .. j-1], j in [1 .. n]
               | ci notin C2 and cj notin C2 and ci + cj in C2
                 where ci is Pi @@ mC where cj is Pj @@ mC
                 where Pi is Primes[i] where Pj is Primes[j] ]
               where n is Min(100, #Primes);
    NIdeals := [Norm(I) : I in Ideals];
    ParallelSort(~NIdeals, ~Ideals);
    Lcount := {* PowerIdeal(ZF) | *}; // counts primes used in L

    function done(dimo, Cf, D, Mf)
        dim := Dimension(Mf) * #{d : d in D | (d @@ mC) in Cf};
        assert dimo ge dim;
        return dimo eq dim;
    end function;

    Vn := V;
    Vo := sub< V | >;

    NN := [I : I in Divisors(N0) | I ne N0];

    for N in NN do
        D := Divisors(N0/N);

        MN := BianchiCuspForms(F, N : VorData := VoronoiData(M));

        for Mf in NewformDecomposition(NewSubspace(MN)) do

// printf "N : %o\nD : %o\n", Norm(N), [Norm(d) : d in D];
// Mf;
            bool, S := HasAttribute(Mf, "InnerTwistSubgroup");
            if bool then
                Cf := sub< C | [I @@ mC : I in S] >;
// "#Cf =", #Cf;
            else
                Cf := sub< C | >;
            end if;

            Wn := sub< V | >;
            Wo := V;
            p := 0;
            i := 0;
            safety := 1;

            while true do

                // Action of T_P for a principal prime P
                //  -->  upper bound for old space of Mf

                p +:= 1;
                P := PPrimes[p];
// "P =", Norm(P);

// time
                TfP := HeckeOperator(Mf, P);
// time
                TP  := HeckeOperator(M, P);
                TP  := MatrixAlgebra(Q, Nrows(TP))! TP;
                xTP := Evaluate(CharacteristicPolynomial(TfP), TP);

                Wn := Wn + Image(xTP);
                Wo := Wo meet Kernel(xTP);
// "Dimensions:", Dimension(Wn), Dimension(Wo);
                assert Dimension(Wn) + Dimension(Wo) eq Dimension(V);

                if done(Dimension(Wo), Cf, D, Mf) then
                    if safety eq 0 then
                        break;
                    end if;
                    safety -:= 1;
                    continue;
                end if;

                // Lower bound on Mf`InnerTwistSubgroup
                //  -->  lower bound for # of images of Mf

                if Cf ne C then
                 
                    repeat
                        i +:= 1;
                        L  := Ideals[i];
                        FL := {t[1] : t in Factorization(L)};
                        CL := {P @@ mC : P in FL};
                    until not CL subset Cf and 
                        Max([Multiplicity(Lcount, P) : P in FL]) lt 3;

                    for P in FL do
                        Include(~Lcount, P);
                    end for;

// "L :", [Norm(t[1]) : t in Factorization(L)];
// time
                    if not IsZero(HeckeOperator(Mf, L)) then

                        Cf := sub< C | Cf, CL >;
// "#Cf =", #Cf;

                        if done(Dimension(Wo), Cf, D, Mf) then
                            if safety eq 0 then
                                break;
                            end if;
                            safety -:= 1;
                        end if;
                    end if;

                end if;

            end while;

            Mf_ := Mf;
            Mf_`InnerTwistSubgroup :=
                {PowerIdeal(ZF) | c @ mC : c in Generators(Cf)};

            Vn := Vn meet Wn;
            Vo := Vo + Wo;

        end for;
    end for;

    return Vn, Vo;
end intrinsic;

