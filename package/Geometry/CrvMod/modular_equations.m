freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  DEFINING POLYNOMIALS OF MODULAR CURVES            //
//                       Last modified June 2002                      //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                       ATKIN MODULAR POLYNOMIALS                    //
////////////////////////////////////////////////////////////////////////

/* This version is deprecated and will be removed. */
intrinsic AtkinModularEquation(p::RngIntElt) -> RngMPolElt
    {The Atkin modular polynomial of prime level p.}

    require IsPrime(p : Proof := false) : "Argument must be prime.";
    i := (p div 200) + 1;
    require i le 5 : 
        "Data for argument is not in modular curve database.";
    D := ModularCurveDatabase("Atkin",i);
    require p in D :
        "Data for argument is not in modular curve database.";
    return Polynomial(ModularCurve(D,p));
end intrinsic;

intrinsic AtkinModularPolynomial(p::RngIntElt) -> RngMPolElt
    {The Atkin modular polynomial of prime level p.}

    require IsPrime(p : Proof := false) : "Argument must be prime.";
    i := (p div 200) + 1;
    require i le 5 : 
        "Data for argument is not in modular curve database.";
    D := ModularCurveDatabase("Atkin",i);
    require p in D :
        "Data for argument is not in modular curve database.";
    return Polynomial(ModularCurve(D,p));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                    CANONICAL MODULAR POLYNOMIALS                   //
////////////////////////////////////////////////////////////////////////

/* This version is deprecated and will be removed. */
intrinsic CanonicalModularEquation(p::RngIntElt) -> RngMPolElt
    {The canonical modular polynomial of prime level p.}

    require IsPrime(p : Proof := false) : "Argument must be prime.";
    D := ModularCurveDatabase("Canonical");
    require p in D : "Data for argument is not in modular curve database.";
    return Polynomial(ModularCurve(D,p));
end intrinsic;

intrinsic CanonicalModularPolynomial(p::RngIntElt) -> RngMPolElt
    {The canonical modular polynomial of prime level p.}

    require IsPrime(p : Proof := false) : "Argument must be prime.";
    D := ModularCurveDatabase("Canonical");
    require p in D : "Data for argument is not in modular curve database.";
    return Polynomial(ModularCurve(D,p));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                    CLASSICAL MODULAR POLYNOMIALS                   //
////////////////////////////////////////////////////////////////////////

/* This version is deprecated and will be removed. */
intrinsic ClassicalModularEquation(p::RngIntElt) -> RngMPolElt
    {The classical modular polynomial of level p.}

    D := ModularCurveDatabase("Classical");
    require p in D :
        "Data for argument is not in modular curve database.";
    return Polynomial(ModularCurve(D,p));
end intrinsic;

intrinsic ClassicalModularPolynomial(p::RngIntElt) -> RngMPolElt
    {The classical modular polynomial of level p.}

    D := ModularCurveDatabase("Classical");
    require p in D :
        "Data for argument is not in modular curve database.";
    return Polynomial(ModularCurve(D,p));
end intrinsic;







