freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


//List for Phi5

//list for Phi5 case 1
Phi5case1 := function(p)

    F := FreeGroup (6);

    Alpha := [F.1, F.2, F.3, F.4, F.5];
    Beta1 := F.6;

    family := [
    (Alpha[2],Alpha[3]) = Id(F),
    (Alpha[2],Alpha[4]) = Id(F),
    (Alpha[3],Alpha[4]) = Alpha[1],
    (Alpha[2],Alpha[5]) = Alpha[1],
    (Alpha[3],Alpha[5]) = Id(F),
    (Alpha[4],Alpha[5]) = Id(F),
    Beta1^(p^2) = Id(F),
    Beta1^p = Alpha[1]]
    cat [(Beta1, Alpha[j]) = Id(F) : j in [1..5]];

    Pres := [];

    Q := quo < F | family, [
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Beta1
               ] >;
    Append (~Pres, Q);

  return [pQuotient(q,p,3):q in Pres];
end function;

//List for Phi5 case 2
Phi5case2 := function(p)

    F := FreeGroup (7);

    Alpha := [F.1, F.2, F.3, F.4, F.5];
    Beta := [F.6, F.7];

    family := [
    (Alpha[2],Alpha[3]) = Id(F),
    (Alpha[2],Alpha[4]) = Id(F),
    (Alpha[3],Alpha[4]) = Alpha[1],
    (Alpha[2],Alpha[5]) = Alpha[1],
    (Alpha[3],Alpha[5]) = Id(F),
    (Alpha[4],Alpha[5]) = Id(F),
    Beta[1]^p = Id(F),
    Beta[2]^p = Id(F),
    Beta[1] = Alpha[1]] cat
    &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]])
    cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..2]]: i in [1..2]]);

    Pres := [];

    Q := quo < F | family, [
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Beta[2],
                   Alpha[5]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    return [pQuotient(q,p,2):q in Pres];
end function;

EasterfieldPhi5 := function(p)
   return Phi5case1(p) cat Phi5case2(p);
end function;
