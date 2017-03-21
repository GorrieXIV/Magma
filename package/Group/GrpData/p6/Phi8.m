freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


//list for Phi8

//list for Phi8 case1
Phi8case1 := function(p)

    Z := Integers ();
    la := Z ! (NonQuadraticResidue (p)); // lambda

    F := FreeGroup (6);

    Alpha := [F.1, F.2, F.3, F.4, F.5];
    Beta1 := F.6;

    family := [
    (Alpha[2],Alpha[3]) = Id(F),
    (Alpha[2],Alpha[4]) = Id(F),
    (Alpha[3],Alpha[4]) = Alpha[1],
    (Alpha[2],Alpha[5]) = Alpha[1],
    (Alpha[3],Alpha[5]) = Id(F),
    (Alpha[4],Alpha[5]) = Alpha[2],
    Beta1^p = Alpha[1],
    Alpha[5]^p = Alpha[3]^-1]
    cat [(Beta1, Alpha[j]) = Id(F) : j in [1..5]];

    Pres := [];

    Q := quo < F | family, [
                   Alpha[5]^(p^2) = Id(F),
                   Alpha[4]^p*Alpha[2]^-1 = Beta1^-1
               ] >;
    Append (~Pres, Q);

    for x in [0..(p-2)] do
    Q := quo < F | family, [
                   Alpha[5]^(p^2) = Id(F),
                   Alpha[4]^p*Alpha[2]^-1 = Beta1^x
               ] >;
    Append (~Pres, Q);
    end for;

    Q := quo < F | family, [
                   Alpha[5]^(p^2) = Beta1^p,
                   Alpha[4]^p*Alpha[2]^-1 = Beta1^-1
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[5]^(p^2) = Beta1,
                   Alpha[4]^p*Alpha[2]^-1 = Id(F)
               ] >;
    Append (~Pres, Q);

    return [pQuotient(q,p,4):q in Pres];
end function;

//List for Phi8 case2
Phi8case2 := function(p)

    Z := Integers ();
    la := Z ! (NonQuadraticResidue (p)); // lambda

    F := FreeGroup (7);

    Alpha := [F.1, F.2, F.3, F.4, F.5];
    Beta := [F.6, F.7];

    family := [
    (Alpha[2],Alpha[3]) = Id(F),
    (Alpha[2],Alpha[4]) = Id(F),
    (Alpha[3],Alpha[4]) = Alpha[1],
    (Alpha[2],Alpha[5]) = Alpha[1],
    (Alpha[3],Alpha[5]) = Id(F),
    (Alpha[4],Alpha[5]) = Alpha[2],
    Beta[1]^p = Id(F),
    Beta[2]^p = Id(F),
//    Alpha[5]^(p^3) = Id(F),
//    (Alpha[4]^p*Alpha[2]^-1)^p^2 = Id(F),
    Beta[1] = Alpha[1],
    Alpha[5]^p = Alpha[3]^-1] cat
    &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]])
    cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..2]]: i in [1..2]]);

    Pres := [];

    Q := quo < F | family, [
                   Alpha[5]^(p^2) = Id(F),
                   Alpha[4]^p*Alpha[2]^-1 = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[5]^(p^2) = Id(F),
                   Alpha[4]^p*Alpha[2]^-1 = Beta[2]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[5]^(p^2) = Beta[2],
                   Alpha[4]^p*Alpha[2]^-1 = Id(F)
               ] >;
    Append (~Pres, Q);

    return [pQuotient(q,p,3):q in Pres];
end function;

EasterfieldPhi8 := function(p)
    return Phi8case1(p) cat Phi8case2(p);
end function;
