freeze;
 


import "misc.m": NonQuadraticResidue, EasterfieldPair;


//List for Phi2 case one
Phi2case1 := function(p)

    F := FreeGroup (4);

    Alpha := [F.1, F.2, F.3];
    Beta1 := F.4;

    family := [
    (Alpha[2], Alpha[3]) = Alpha[1],
    (Alpha[1],Beta1) = Id(F),
    (Alpha[2],Beta1) = Id(F),
    (Alpha[3],Beta1) = Id(F),
    Beta1^(p^3) = Alpha[1]
    ]
    cat [(Beta1, Alpha[j]) = Id(F) : j in [1..3]];

    Pres := [];

    //Z1 is of type (4)

    Q := quo < F | family, [
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[2]^p = Beta1,
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

  return [pQuotient(q,p,5):q in Pres];
end function;

//list for Phi2 case 2 & 3 
Phi2case2and3 := function(p)

    Pres := [];

    F := FreeGroup(5);

    Alpha := [F.1, F.2, F.3];
    Beta := [F.4, F.5];

    family := [
    (Alpha[2], Alpha[3]) = Alpha[1]
    ] cat 
    &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..2]])
    cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..2]]: i in [1..2]]);

    //Using the relations stated for Alpha[1] in Agemo(Z)
    Q := quo < F | family, [
                   Beta[1]^(p^2) = Alpha[1],
    //               Beta[1]^(p^3) = Id(F),
                   Beta[2]^p = Id(F),
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Alpha[1],
                   Beta[2]^p = Id(F),
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);


    Q := quo < F | family, [
                   Beta[1]^(p^2) = Alpha[1],
                   Beta[2]^p = Id(F),
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);


    Q := quo < F | family, [
                   Beta[1]^(p^2) = Alpha[1],
                   Beta[2]^p = Id(F),
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    //Using the relations stated for Alpha[1] not in Agemo(Z)
    Q := quo < F | family, [
                   Beta[1]^(p^3) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^3) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^3) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^3) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    return [pQuotient(q,p,5):q in Pres];
end function;

//list for Phi2 case4
Phi2case4 := function(p)

    Pres := [];

    F := FreeGroup(5);

    Alpha := [F.1, F.2, F.3];
    Beta := [F.4, F.5];

    family := [
    (Alpha[2], Alpha[3]) = Alpha[1],
    Beta[1]^(p^2) = Id(F),
//    Beta[2]^(p^2) = Id(F),
    Beta[2]^p = Alpha[1]] cat 
    &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..2]])
    cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..2]]: i in [1..2]]);

    Q := quo < F | family, [
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    return [pQuotient(q,p,4):q in Pres];
end function;

//list for Phi2 case 5 and 6 
Phi2case5and6 := function(p)

    Pres := [];

    F := FreeGroup(6);

    Alpha := [F.1, F.2, F.3];
    Beta := [F.4, F.5, F.6];

    family := [
    (Alpha[2], Alpha[3]) = Alpha[1],
//    Beta[1]^(p^2) = Id(F),
    Beta[2]^p = Id(F),
    Beta[3]^p = Id(F)
     ] cat 
    &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..3]])
    cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

    //using the relations stated for Alpha[1] in Agemo(Z)
    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^p = Alpha[1],
                   Alpha[2]^p = Beta[3],
                   Alpha[3]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    //using the relations stated for Alpha[1] not  in Agemo(Z)
    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Beta[3],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Beta[3]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1]^(p^2) = Id(F),
                   Beta[2] = Alpha[1],
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Beta[3]
               ] >;
    Append (~Pres, Q);

   return [pQuotient(q,p,4):q in Pres];
end function;

//list for Phi2 case seven
Phi2case7 := function(p)

    Pres := [];

    F := FreeGroup(7);

    Alpha := [F.1, F.2, F.3];
    Beta := [F.4, F.5, F.6, F.7];

    family := [
    (Alpha[2], Alpha[3]) = Alpha[1],
    Beta[1]^p = Id(F),
    Beta[2]^p = Id(F),
    Beta[3]^p = Id(F),
    Beta[4]^p = Id(F)
  ] cat
    &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..4]])
    cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..4]]: i in [1..4]]);

    Q := quo < F | family, [
                   Beta[1] = Alpha[1],
                   Alpha[2]^p = Id(F),
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1] = Alpha[1],
                   Alpha[2]^p = Beta[1],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1] = Alpha[1],
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1] = Alpha[1],
                   Alpha[2]^p = Beta[2],
                   Alpha[3]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Beta[1] = Alpha[1],
                   Alpha[2]^p = Beta[3],
                   Alpha[3]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

   return [pQuotient(q,p,2):q in Pres];
end function;


EasterfieldPhi2 := function (p)

   return Phi2case1 (p) cat Phi2case2and3 (p) cat Phi2case4 (p) cat Phi2case5and6(p) cat Phi2case7(p);

end function;
