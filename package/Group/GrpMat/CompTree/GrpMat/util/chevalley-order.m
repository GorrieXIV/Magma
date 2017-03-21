freeze;

//$Id:: order.m 2037 2010-11-14 22:27:42Z eobr007                          $:

// Centre orders of SL, SU, Sp, Omega^(\epsilon)
ClassicalCentreOrder := AssociativeArray();
ClassicalCentreOrder["linear"] := func<d, q | GCD(d, q - 1)>;
ClassicalCentreOrder["symplectic"] := func<d, q | GCD(2, q - 1)>;
ClassicalCentreOrder["unitary"] := func<d, q |
    (d eq 3 and qq eq 2) select 3 else GCD(d, qq + 1) where qq is Isqrt(q)>;
ClassicalCentreOrder["orthogonalcircle"] := func<d, q | 1>;
ClassicalCentreOrder["orthogonalplus"] := func<d, q |
    IsEven(q) select 1 else (IsEven(d * (q - 1) div 4) select 2 else 1)>;
ClassicalCentreOrder["orthogonalminus"] := func<d, q |
    IsEven(q) select 1 else (IsOdd(d * (q - 1) div 4) select 2 else 1)>;

