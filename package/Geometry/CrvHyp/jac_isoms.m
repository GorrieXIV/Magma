freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//         Hyperelliptic Isomorphisms applied to Jacobians        //
//                       David Kohel, 2002                        //
//                                                                //
////////////////////////////////////////////////////////////////////


/*
intrinsic '@'(P::JacHypPt,f::MapIsoSch) -> JacHypPt
    {The image of P under f.}
    C := Domain(f);
    require Type(C) eq CrvHyp and Type(Domain(f)) eq CrvHyp :
       "The domain and codomain of argument 1 must be hyperelliptic curves"; 
    require Parent(P) eq Jacobian(C) : 
       "Argument 1 must be a point on the jacobian of " * 
       "the domain of argument 2";
    return Evaluate(f,P);
end intrinsic;
*/

/*
//This intrinsic is being shadowed by the one in isomorphisms.m,
//so I've disable thisone -- DR 02 Nov 2010.
intrinsic Evaluate(f::MapIsoSch,P::JacHypPt) -> JacHypPt
    {The image of P under f.}

    C1 := Domain(f); C2 := Codomain(f);
    require Type(C1) eq CrvHyp and Type(C2) eq CrvHyp :
       "The domain and codomain of argument 1 must be hyperelliptic curves"; 
    J1 := Jacobian(C1); J2 := Jacobian(C2);
    require Parent(P) eq J1 :  
        "Argument 2 must be a point of the " *
        "Jacobian of the domain of argument 1.";
    R := BaseRing(J1);
    P1 := PolynomialRing(R); x := P1.1;
    P2 := PolynomialRing(R, 2); x1 := P2.1; z1 := P2.2;
    d1 := Dimension(J2)+1;
    J2odd := IsOdd(#PointsAtInfinity(C2));
    O1 := CoordinateRing(Ambient(C1));
    eqns := DefiningPolynomials(Inverse(f));
    mat := [ Evaluate(eqns[1],[x,0,1]), Evaluate(eqns[3],[x,0,1]) ];
    e := MonomialCoefficient(eqns[2],O1.2);
    u1 := Evaluate(eqns[2],[x,0,1]);
    homogen := func< pol, deg |
        &+[ Coefficient(pol,i)*x1^i*z1^(deg-i) : i in [0..deg] ] >;
    pta := Evaluate(homogen(P[1], P[3]), mat);
    ptb := (1/e)*(Evaluate(homogen(P[2], d1), mat) - u1);
    deg := J2odd select Degree(pta) else P[3];
    return elt< J2 | pta, ptb, deg >;
end intrinsic;
*/

/*
intrinsic '@@'(P::JacHypPt,f::MapIsoSch) -> JacHypPt
    {The inverse image of P under f.}

    C := Codomain(f);
    require Type(C) eq CrvHyp and Type(Domain(f)) eq CrvHyp :
       "The domain and codomain of argument 1 must be hyperelliptic curves"; 
    require Parent(P) eq Jacobian(C) : 
       "Argument 1 must be a point on the jacobian of " * 
       "the codomain of argument 2";
    return Pullback(f,P);
end intrinsic;
*/

intrinsic Pullback(f::MapIsoSch,P::JacHypPt) -> JacHypPt
    {The preimage of P under f.}

    C1 := Domain(f); C2 := Codomain(f);
    require Type(C1) eq CrvHyp and Type(C2) eq CrvHyp :
       "The domain and codomain of argument 1 must be hyperelliptic curves"; 
    J1 := Jacobian(C1); J2 := Jacobian(C2);
    require Parent(P) eq J2 :  
        "Argument 2 must be a point of the " *
        "Jacobian of the codomain of argument 1.";

    R := BaseRing(J1);
    P1 := PolynomialRing(R); x := P1.1;
    P2 := PolynomialRing(R, 2); x1 := P2.1; z1 := P2.2;
    O1 := CoordinateRing(Ambient(C1));

    J1odd := IsOdd(#PointsAtInfinity(Domain(f)));
    d1 := Dimension(J1)+1;
    
    eqns := DefiningPolynomials(f);
    mat := [ Evaluate(eqns[1],[x,0,1]), Evaluate(eqns[3],[x,0,1]) ];
    e := MonomialCoefficient(eqns[2],O1.2);
    u1 := Evaluate(eqns[2],[x,0,1]);
    homogen := func< pol, deg |
        &+[ Coefficient(pol,i)*x1^i*z1^(deg-i) : i in [0..deg] ] >;
    pta := Evaluate(homogen(P[1], P[3]), mat);
    ptb := (1/e)*(Evaluate(homogen(P[2], d1), mat) - u1);
    deg := J1odd select Degree(pta) else P[3];
    return elt< J1 | pta, ptb, deg >;
end intrinsic;

