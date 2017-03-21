freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


//List for Phi3 case 1
Phi3case1 := function(p)

    Z := Integers ();
    la := Z ! (NonQuadraticResidue (p)); // lambda

    F := FreeGroup (5);

    Alpha := [F.1, F.2, F.3, F.4];
    Beta1 := F.5;

    family := [
    (Alpha[2],Alpha[3]) = Id(F),
    (Alpha[2],Alpha[4]) = Alpha[1],
    (Alpha[3],Alpha[4]) = Alpha[2],
//    Alpha[2]^(p^4) = Id(F),
//    Beta1^(p^3) = Id(F),
    Beta1^(p^2) = Alpha[1]]
    cat [(Beta1, Alpha[j]) = Id(F) : j in [1..4]];

    Pres := [];

    //Z1 is of type (3)

    Q := quo < F | family, [
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    for x in [1,la] do
    Q := quo < F | family, [
                   Alpha[3]^p = Beta1^x,
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);
    end for;

    Q := quo < F | family, [
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Beta1
               ] >;
    Append (~Pres, Q);

  return [pQuotient(q,p,4):q in Pres];
end function;

//list for Phi3 case 2 and 3
Phi3case2case3 := function(p)

    Z := Integers ();
    la := Z ! (NonQuadraticResidue (p)); // lambda

    F := FreeGroup (6);

    Alpha := [F.1, F.2, F.3, F.4];
    Beta := [F.5, F.6];

    family := [
    (Alpha[2],Alpha[3]) = Id(F),
    (Alpha[2],Alpha[4]) = Alpha[1],
    (Alpha[3],Alpha[4]) = Alpha[2],
    Beta[2]^(p) = Id(F)] cat 
    &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..2]])
    cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..2]]: i in 
[1..2]]);

    Pres := [];
    //for Z1 of type (2 1);Alpha[1] in Agemo(Z1)
    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    for x in [1,la] do
    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[3]^p = Beta[1]^x,
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);
    end for;

    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[3]^p = Beta[2],
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[3]^p = Beta[2],
                   Alpha[4]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    for x in [1,la] do
    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[3]^p = Beta[1]^x,
                   Alpha[4]^p = Beta[2]
               ] >;
    Append (~Pres, Q);
    end for;

    //for Z1 of type (2 1);Alpha[1] not in Agemo(Z1)
    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[3]^p = Beta[1],
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    for x in [1,la] do
    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[3]^p = Beta[2]^x,
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);
    end for;

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    for x in [1,la] do
    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[3]^p = Beta[2]^x,
                   Alpha[4]^p = Beta[1]
               ] >;
    Append (~Pres, Q);
    end for;

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[3]^p = Beta[1],
                   Alpha[4]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    return [pQuotient(q,p,3) : q in Pres];
end function;

//list for Phi3 case 4
Phi3case4 := function(p)

     F := FreeGroup(7);

     Alpha := [F.1, F.2, F.3, F.4];
     Beta := [F.5, F.6, F.7];

    Z := Integers ();
    la := Z ! (NonQuadraticResidue (p)); // lambda

     family := [
    (Alpha[2],Alpha[3]) = Id(F),
    (Alpha[2],Alpha[4]) = Alpha[1],
    (Alpha[3],Alpha[4]) = Alpha[2],
    Beta[1]^p = Id(F),
    Beta[2]^p = Id(F),
    Beta[3]^p = Id(F),
    Beta[1] = Alpha[1]] cat
    &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..4]]: i in [1..3]])
    cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in 
       [1..3]]);

    Pres := [];

    Q := quo < F | family, [
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    for x in [1,la] do
    Q := quo < F | family, [
                   Alpha[3]^p = Beta[1]^x,
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);
    end for;

    Q := quo < F | family, [
                   Alpha[3]^p = Beta[2],
                   Alpha[4]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[3]^p = Id(F),
                   Alpha[4]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[3]^p = Beta[2],
                   Alpha[4]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    for x in [1,la] do
    Q := quo < F | family, [
                   Alpha[3]^p = Beta[1]^x,
                   Alpha[4]^p = Beta[2]
               ] >;
    Append (~Pres, Q);
    end for;

    Q := quo < F | family, [
                   Alpha[3]^p = Beta[3],
                   Alpha[4]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    return [pQuotient(q,p,5) : q in Pres];
end function;

EasterfieldPhi3 := function (p)

   return Phi3case1 (p) cat Phi3case2case3 (p) cat Phi3case4 (p); 

end function;
