freeze;
// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   Hyperelliptic Curve Morphisms                    //
//                 Magma types created by David Kohel                 //
//                   based on code by Michael Stoll                   //
//                         Created June 2001                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

/***********************************************************************

  changes:
  --------

  2001-07:

  Scheme merge. Paulette Lieby

  2001-07-20:

  Fix return values for the Transformation intrinsics
  Nicole Sutherland

  2001-07: Paulette
  Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)

  2001-08
  Fit into scheme maps
  Nicole Sutherland
   
  2001-09: David Kohel
  Modifications and corrections
  Specification of inverse maps at construction time, with kernel
  support for verification.
  
  2002-10: Nils Bruin
  Changed calls to HyperellipticCurve to new interface

  2004-10: Michael Stoll
  Reinstalled application of CrvHyp isomorphisms to JacHypPts (end of file)
  
***********************************************************************/
  
function HyperellipticIsomorphism(C1,C2,t,e,u)
    P1 := CoordinateRing(Ambient(C1));
    x1 := P1.1; y1 := P1.2; z1 := P1.3;
    P2 := CoordinateRing(Ambient(C2));
    x2 := P2.1; y2 := P2.2; z2 := P2.3;
    g := Genus(C1);
    a,b,c,d := Explode(t);
    S := Eltseq(u);
    X2 := a*x1+b*z1; Z2 := c*x1+d*z1;
    Y2 := e*y1 + &+[ P1 | S[i+1]*x1^i*z1^(g+1-i) : i in [0..#S-1] ];    
    det := a*d-b*c;
    X1 := d*x2-b*z2; Z1 := -c*x2+a*z2;
    Y1 := (1/e)*(det^(g+1)*y2
        - &+[ P2 | S[i+1]*X1^i*Z1^(g+1-i) : i in [0..#S-1] ]);
    /*
    print "[X2,Y2,Z2] =", [X2,Y2,Z2];
    print "[X1,Y1,Z1] =", [X1,Y1,Z1];
    */
return iso< C1 -> C2 | [ X2, Y2, Z2 ], [ X1, Y1, Z1 ] : Check:=false>;
end function;

////////////////////////////////////////////////////////////////////////
//                  Isomorphism Creation and Coercion                 //
////////////////////////////////////////////////////////////////////////

intrinsic HyperellipticInvolution(C::CrvHyp) -> MapIsoSch
    {The hyperelliptic involution on C as a transformation.}

    PP := AmbientSpace(C);
    x := PP.1; y := PP.2; z := PP.3;
    y1 := -y;
    g := Genus(C);
    _, h := HyperellipticPolynomials(C);
    if h ne 0 then
	y1 -:= &+[ Coefficient(h,i)*x^i*z^(g+1-i) : i in [0..g+1] ];
    end if;
    return iso<C -> C | [ x, y1, z ], [ x, y1, z ] >;
end intrinsic;

////////////////////////////////////////////////////////////////////////
// Curve transformations -- create the codomain with the isomorphism. //
////////////////////////////////////////////////////////////////////////

function TransformationCodomain(C,mat,e,u)
    // Transforms C by the transformation <mat,e,u>.
    g := Genus(C);
    R := CoefficientRing(C);
    P := PolynomialRing(R); x := P.1;
    a,b,c,d := Explode(mat);
    d1 := g+1;
    d2 := 2*d1;
    mu := (a*d-b*c)^-d1;
    /* Get new polynomials by replacing x1, y1, and z1 in old. */
    f, h := HyperellipticPolynomials(C);
    x1 := d*x-b; z1 := -c*x+a;
    u1 := &+[ Coefficient(u,i)*x1^i*z1^(d1-i) : i in [0..d1] ];
    h1 := &+[ Coefficient(h,i)*x1^i*z1^(d1-i) : i in [0..d1] ];
    f1 := &+[ Coefficient(f,i)*x1^i*z1^(d2-i) : i in [0..d2] ];
    h2 := mu*(e*h1-2*u1);
    f2 := mu^2*(e^2*f1+(e*h1-u1)*u1);
    return Ambient(C)!!HyperellipticCurve([f2,h2]);
end function;

intrinsic Transformation(C::CrvHyp, t::[RngElt], e::RngElt, u ::RngUPolElt)
    -> CrvHyp, MapIsoSch
    {The transformation of C given by the matrix sequence t, the
    scaling factor e, and the polynomial u, returning the codomain
    curve followed by the isomorphism.}
    R := BaseRing(C);
    bool, t := CanChangeUniverse(t,R);
    require bool : "Argument 1 must be coercible to a sequence over " *
                   "the base ring of argument 1.";
    bool, e := IsCoercible(R,e);
    require bool :
       "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(e) :
       "Argument 2 must be a unit in the base ring of argument 1.";
    C1 := TransformationCodomain(C,t,e,u);
    return C1, HyperellipticIsomorphism(C, C1, t, e, u);
end intrinsic;

intrinsic Transformation(C::CrvHyp, t::[RngElt], e::RngElt)
    -> CrvHyp, MapIsoSch
    {The transformation of C given by the matrix sequence t and 
    scaling factor e, returning the codomain curve followed by
    the isomorphism.}

    R := BaseRing(C);
    bool, t := CanChangeUniverse(t,R);
    require bool : "Argument 1 must be coercible to a sequence over " *
                   "the base ring of argument 1.";
    bool, e := IsCoercible(R,e);
    require bool :
       "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(e) :
       "Argument 2 must be a unit in the base ring of argument 1.";
    u := PolynomialRing(R)!0;
    C1 := TransformationCodomain(C,t,e,u);
    return C1, HyperellipticIsomorphism(C, C1, t, e, u);
end intrinsic;

intrinsic Transformation(C::CrvHyp, t::[RngElt]) -> CrvHyp, MapIsoSch
    {The transformation of C given by the matrix sequence t, the
    scaling factor e, and the polynomial u, returning the codomain
    curve followed by the isomorphism.}

    R := BaseRing(C);
    bool, t := CanChangeUniverse(t,R);
    require bool : "Argument 1 must be coercible to a sequence over " *
                   "the base ring of argument 1.";
    u := PolynomialRing(R)!0;
    C1 := TransformationCodomain(C,t,R!1,u);
    return C1, HyperellipticIsomorphism(C, C1, t, R!1, u);
end intrinsic;

intrinsic Transformation(C::CrvHyp, e::RngElt, u::RngUPolElt)
    -> CrvHyp, MapIsoSch
    {The transformation of C given by the scaling factor e and
    shifting polynomial u, returning the codomain curve followed
    by the isomorphism.}

    R := BaseRing(C);
    bool, e := IsCoercible(R,e);
    require bool :
        "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(e) :
       "Argument 2 must be a unit in the base ring of argument 1.";
    require BaseRing(Parent(u)) cmpeq R :
        "Parent of argument 3 must be defined over " * 
        "the base ring of argument 1.";
    C1 := TransformationCodomain(C,[R|1,0,0,1],e,u);
    return C1, HyperellipticIsomorphism(C, C1, [R|1,0,0,1], e, u);
end intrinsic;

function ShiftedCurve(C,u)
    f, h := HyperellipticPolynomials(C);
    hu := h - 2*u;
    fu := f + h*u - u^2;
    return Ambient(C)!!HyperellipticCurve(fu,hu);
end function;

intrinsic Transformation(C::CrvHyp,u::RngUPolElt) -> CrvHyp, MapIsoSch
    {The transformation on curves of genus g given by the shift
    polynomial u, of the abscissa, returning the codomain curve
    followed by the isomorphism.}

    R := CoefficientRing(Parent(u));
    require R cmpeq BaseRing(C) :
        "The base ring of argument 1 must equal " * 
        "the base ring of the parent of argument 2.";
    C1 := ShiftedCurve(C,u);
    return C1, HyperellipticIsomorphism(C, C1, [R|1,0,0,1], R!1, u);
end intrinsic;

function ScaledCurve(C,e)
    f, h := HyperellipticPolynomials(C);
    he := e*h; 
    fe := e^2*f;
    return Ambient(C)!!HyperellipticCurve(fe,he);
end function;

intrinsic Transformation(C::CrvHyp, e::RngElt) -> CrvHyp, MapIsoSch
    {The transformation of C given by the scaling factor e,
    returning the codomain curve followed by the isomorphism.}

    R := BaseRing(C);
    bool, e := IsCoercible(R,e);
    require bool :
       "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(e) :
       "Argument 2 must be a unit in the base ring of argument 1.";
    C1 := ScaledCurve(C,e);
    u := PolynomialRing(R)!0;
    return C1, HyperellipticIsomorphism(C, C1, [R|1,0,0,1], e, u);
end intrinsic;

///////////////////////////////////////////////////////////////////
// reinstalled (plus bug fix), MS 2004-10-07
// NOTE: Should really work with application ( .(.) ) and '@' ...
//       Some more testing of the arguments should also be incorporated
//       (is codomain really a hyperelliptic curve)

intrinsic Evaluate(f::MapIsoSch,P::JacHypPt) -> JacHypPt
    {The image of P under f.}

    J1 := Jacobian(Domain(f));
    J2 := Jacobian(Codomain(f));
    require J1 eq Parent(P) :  "Argument 2 must be a point of the " *
        "Jacobian of the domain of argument 1.";

    J2odd := IsOdd(#PointsAtInfinity(Codomain(f)));
    d1,d2,d3 := Explode(DefiningPolynomials(f));
    _<x,y,z> := Parent(d1);
    MC := MonomialCoefficient;
    a := MC(d1,x); b := MC(d1,z);
    c := MC(d3,x); d := MC(d3,z);
    e := MC(d2,y);
    R := BaseRing(J1);
    P1 := PolynomialRing(R); 
    u1 := Evaluate(d2, [P1.1,0,1]);
    det := a*d - b*c;

    dP := P[3];
    if not J2odd then dP := 2*Ceiling(dP/2); end if;
    x := P1.1;
    P2 := PolynomialRing(R, 2); x1 := P2.1; z1 := P2.2;
    homogen := func< pol, deg |
        &+[ Coefficient(pol,i)*x1^i*z1^(deg-i) : i in [0..deg] ] >;
    d1 := Dimension(J1)+1;
    uh := homogen(u1, d1);
    pta := Evaluate(homogen(P[1], dP), [d*x-b, -c*x+a]);
    ptb := Evaluate((e*homogen(P[2], d1) + uh)/det^d1, [d*x-b, -c*x+a]);
    deg := J2odd select Degree(pta) else dP;
    return elt< J2 |  pta, ptb, deg >;
end intrinsic;
