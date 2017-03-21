freeze;
 

import "misc.m": NonQuadraticResidue, EasterfieldPair;


//list for Phi9

//list for Phi9 case1
Phi9case1 := function(p)

    w := PrimitiveRoot(p);

    F := FreeGroup (6);

    Alpha := [F.1, F.2, F.3, F.4, F.5];
    Beta1 := F.6;

    family := [
    (Alpha[2],Alpha[3]) = Id(F),
    (Alpha[2],Alpha[4]) = Id(F),
    (Alpha[3],Alpha[4]) = Id(F),
    (Alpha[2],Alpha[5]) = Alpha[1],
    (Alpha[3],Alpha[5]) = Alpha[2],
    (Alpha[4],Alpha[5]) = Alpha[3],
    Beta1^(p^2) = Id(F),
    Beta1^p = Alpha[1]]
    cat [(Beta1, Alpha[j]) = Id(F) : j in [1..5]];

    Pres := [];

    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Beta1
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[4]^p = Beta1,
                   Alpha[5]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    if p mod 3 eq 1 then
     for x in [w,w^2] do
      Q := quo < F | family, [
                     Alpha[4]^p = Beta1^(x mod p),
                     Alpha[5]^p = Id(F)
                 ] >;
      Append (~Pres, Q);
     end for;
    end if;

    return [pQuotient(q,p,4):q in Pres];
end function;

//List for Phi9 case2
Phi9case2 := function(p)

    w := PrimitiveRoot(p);

    F := FreeGroup (7);

    Alpha := [F.1, F.2, F.3, F.4, F.5];
    Beta := [F.6, F.7];

    family := [
    (Alpha[2],Alpha[3]) = Id(F),
    (Alpha[2],Alpha[4]) = Id(F),
    (Alpha[3],Alpha[4]) = Id(F),
    (Alpha[2],Alpha[5]) = Alpha[1],
    (Alpha[3],Alpha[5]) = Alpha[2],
    (Alpha[4],Alpha[5]) = Alpha[3],
    Beta[1]^p = Id(F),
    Beta[2]^p = Id(F),
    Beta[1] = Alpha[1]] cat
    &cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..2]])
    cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..2]]: i in [1..2]]);

    Pres := [];

    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[4]^p = Id(F),
                   Alpha[5]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[4]^p = Beta[1],
                   Alpha[5]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    if p mod 3 eq 1 then
     for x in [w,w^2] do
      Q := quo < F | family, [
                     Alpha[4]^p = Beta[1]^(x mod p),
                     Alpha[5]^p = Id(F)
                  ] >;
      Append (~Pres, Q);
     end for;
    end if;

    Q := quo < F | family, [
                   Alpha[4]^p = Beta[2],
                   Alpha[5]^p = Id(F)
               ] >;
    Append (~Pres, Q);

    Q := quo < F | family, [
                   Alpha[4]^p = Beta[1],
                   Alpha[5]^p = Beta[2]
               ] >;
    Append (~Pres, Q);

    if p mod 3 eq 1 then
     for x in [w,w^2] do
      Q := quo < F | family, [
                     Alpha[4]^p = Beta[1]^(x mod p),
                     Alpha[5]^p = Beta[2]
                  ] >;
      Append (~Pres, Q);
     end for;
    end if;

    Q := quo < F | family, [
                   Alpha[4]^p = Beta[2],
                   Alpha[5]^p = Beta[1]
               ] >;
    Append (~Pres, Q);

    return [pQuotient(q,p,4):q in Pres];
end function;

EasterfieldPhi9 := function(p)
    return Phi9case1(p) cat Phi9case2(p);
end function;
