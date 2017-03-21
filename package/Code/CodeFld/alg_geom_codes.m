freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//                   Algebraic-Geometric Codes                    //
//                  Created by Lancelot Pecquet                   //
//                    Modified by David Kohel                     //
//                                                                //
////////////////////////////////////////////////////////////////////

declare verbose AGCode, 2;

////////////////////////////////////////////////////////////////////
//                     Attribute Declarations                     //
////////////////////////////////////////////////////////////////////

declare attributes Code:
   IsWeaklyAG, // true if and only if constructed as AGCode.
   IsWeaklyAGDual, //true if and only if constructed as the dual of an AGCode
   Divisor,
   GeometricSupport,
   RiemannRochBasis,
   GoppaDesignedDistance;

////////////////////////////////////////////////////////////////////
//                  Specific Code Constructors                    //
////////////////////////////////////////////////////////////////////

intrinsic HermitianCode(q::RngIntElt,r::RngIntElt) -> Code
    {Given an integer q, builds the Hermitian code with support all 
    places of degree one of the curve x^(q+1) + y^(q+1) + z^(q+1) over
    GF(q^2), except the place over (1:1:0), and divisor divisor r*P.}

    require IsPrimePower(q): "First argument must be a prime power";
    requirege r, 1;

    K := GF(q^2);
    C := HermitianCurve(ProjectiveSpace(K,2));

    PlcSet := Places(C,1);
    S := [];
    for Q in PlcSet do
	if not assigned P and RepresentativePoint(Q)[3] eq 0 then
	    P := Q;
	else
	    Append(~S,Q);
	end if;
    end for;

    C := AlgebraicGeometricCode(S,r*P);
    return C;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                     Algebraic-Geometric Codes                  //
////////////////////////////////////////////////////////////////////

intrinsic AGCode(S::[PlcCrvElt],D::DivCrvElt) -> Code
   {The (weakly) algebraic-geometric code build by evaluating 
   functions of the Riemann-Roch space of D on the support S 
   of places of degree 1 together with this basis.  The degree 
   of D need not be bounded by #S.}

   C := Curve(D);
   require Curve(Universe(S)) eq C:
      "Arguments must be defined with respect to the same curve";
   require &and[ Degree(P) eq 1 : P in S ] : 
      "Argument 1 must consist of places of degree 1.";
   return AlgebraicGeometricCode(S,D);
end intrinsic;


intrinsic AlgebraicGeometricCode(S::[PlcCrvElt],D::DivCrvElt) -> Code
   {The (weakly) algebraic-geometric code build by evaluating 
   functions of the Riemann-Roch space of D at the points of S.
   The degree of D need not be bounded by #S.}

   C := Curve(D);
   require Curve(Universe(S)) eq C:
      "Arguments must be defined with respect to the same curve";

   require &and[ Degree(P) eq 1 : P in S ] : 
      "Argument 1 must consist of places of degree 1.";
   suppD := Support(D);
   require &and [ P notin suppD : P in S ] : 
      "Support of argument 2 must be disjoint from argument 1.";
   total_tyme := Cputime();
   vprintf AGCode : "Algebraic-geometric code:\n";
   IndentPush();

   K := BaseRing(C);

   tyme := Cputime();
   g := GeometricGenus(C);
   vprintf AGCode : "Genus computation time: %o\n", Cputime(tyme);

   tyme := Cputime();
   vprintf AGCode, 2 : "Riemann-Roch divisor, support:\n%o\n", suppD;
   VD, mD := RiemannRochSpace(D);
   LD := [ mD(x) : x in Basis(VD) ];
   vprint AGCode : "Riemann-Roch dimension:", Dimension(VD);
   vprint AGCode : "Riemann-Roch space time: ", Cputime(tyme);

   k := #LD; n := #S;
   A := RMatrixSpace(K,k,n);

   tyme := Cputime();
   G := Matrix([ Vector([ Evaluate(f,P) : P in S ]) : f in LD ]);
   vprintf AGCode : "Evaluation time: %o\n", Cputime(tyme);

   C := LinearCode(G);
   C`IsWeaklyAG := true;
   C`IsWeaklyAGDual := false;
   C`GeometricSupport := S;
   C`Divisor := D;
   C`RiemannRochBasis := LD;
   if IsAlgebraicGeometric(C) then
      C`MinimumWeightLowerBound := GoppaDesignedDistance(C);
   end if;
   IndentPop();
   vprintf AGCode, 1 : 
      "Algebraic-geometric code time: %o\n", Cputime(total_tyme);
   return C;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                     Algebraic-Geometric Codes                  //
////////////////////////////////////////////////////////////////////

intrinsic AGCode(S::[PlcFunElt],D::DivFunElt) -> Code
   {The (weakly) algebraic-geometric code build by evaluating 
   functions of the Riemann-Roch space of D on the support S 
   of places of degree 1 together with this basis.  The degree 
   of D need not be bounded by #S.}

   F := FunctionField(D);
   require FunctionField(Universe(S)) eq F:
      "Arguments must be defined with respect to the same curve";
   require &and[ Degree(P) eq 1 : P in S ] : 
      "Argument 1 must consist of places of degree 1.";
   return AlgebraicGeometricCode(S,D);
end intrinsic;

intrinsic AlgebraicGeometricCode(S::[PlcFunElt],D::DivFunElt) -> Code
   {The (weakly) algebraic-geometric code build by evaluating 
   functions of the Riemann-Roch space of D at the points of S.
   The degree of D need not be bounded by #S.}

   F := FunctionField(D);
   require FunctionField(Universe(S)) eq F:
      "Arguments must be defined with respect to the same curve";

   require &and[ Degree(P) eq 1 : P in S ] : 
      "Argument 1 must consist of places of degree 1.";
   suppD := Support(D);
   require &and [ P notin suppD : P in S ] : 
      "Support of argument 2 must be disjoint from argument 1.";
   total_tyme := Cputime();
   vprintf AGCode : "Algebraic-geometric code:\n";
   IndentPush();

   K := BaseRing(F);

   tyme := Cputime();
   g := Genus(F);
   vprintf AGCode : "Genus computation time: %o\n", Cputime(tyme);

   tyme := Cputime();
   vprintf AGCode, 2 : "Riemann-Roch divisor, support:\n%o\n", suppD;
   VD, mD := RiemannRochSpace(D);
   LD := [ mD(x) : x in Basis(VD) ];
   vprint AGCode : "Riemann-Roch dimension:", Dimension(VD);
   vprint AGCode : "Riemann-Roch space time: ", Cputime(tyme);

   k := #LD; n := #S;
   A := RMatrixSpace(K,k,n);

   tyme := Cputime();
   G := Matrix([ Vector([ Evaluate(f,P) : P in S ]) : f in LD ]);
   vprintf AGCode : "Evaluation time: %o\n", Cputime(tyme);

   C := LinearCode(G);
   C`IsWeaklyAG := true;
   C`GeometricSupport := S;
   C`Divisor := D;
   C`RiemannRochBasis := LD;
// if IsAlgebraicGeometric(C) then
//    C`MinimumWeightLowerBound := GoppaDesignedDistance(C);
// end if;
   IndentPop();
   vprintf AGCode, 1 : 
      "Algebraic-geometric code time: %o\n", Cputime(total_tyme);
   return C;
end intrinsic;

//////////////////////////////////////////////////////////////////////

intrinsic AlgebraicGeometricDualCode(S::[PlcCrvElt],D::DivCrvElt) -> Code
{Return the differential algebraic-geometric code, obtained
by computing residues of differential forms.
These are dual to the codes constructed using AlgebraicGeometricCode.};

   C := AlgebraicGeometricCode(S,D);
   D := Dual(C);
   D`IsWeaklyAG := false;
   D`IsWeaklyAGDual := true;
   D`GeometricSupport := C`GeometricSupport;
   D`Divisor := C`Divisor;
   D`RiemannRochBasis := C`RiemannRochBasis;
   D`GoppaDesignedDistance := Degree(D`Divisor) - 2*Genus(Curve(D`Divisor))+2;

   return D;
end intrinsic;

intrinsic AlgebraicGeometricDualCode(S::[PlcFunElt],D::DivFunElt) -> Code
{Return the differential algebraic-geometric code, obtained
by computing residues of differential forms.
These are dual to the codes constructed using AlgebraicGeometricCode.};

   C := AlgebraicGeometricCode(S,D);
   D := Dual(C);
   D`IsWeaklyAG := false;
   D`IsWeaklyAGDual := true;
   D`GeometricSupport := C`GeometricSupport;
   D`Divisor := C`Divisor;
   D`RiemannRochBasis := D`RiemannRochBasis;
   D`GoppaDesignedDistance := Degree(D`Divisor) - 2*Genus(Curve(D`Divisor))+2;
   return D;
end intrinsic;

intrinsic AGDualCode(S::[PlcCrvElt],D::DivCrvElt) -> Code
{Return the differential algebraic-geometric code, obtained
by computing residues of differential forms.
These are dual to the codes constructed using AlgebraicGeometricCode.};
    return AlgebraicGeometricDualCode(S, D);
end intrinsic;

////////////////////////////////////////////////////////////////////
//                Boolean Functions for AGCodes                   //
////////////////////////////////////////////////////////////////////

intrinsic IsWeaklyAG(C::CodeLinFld) -> BoolElt
   {Return true if and only if C is a weakly algebraic-geometric 
   code, i.e. constructed as an algebraic-geometric code with 
   respect to a divisor of any degree.}
   if not assigned C`IsWeaklyAG then
      C`IsWeaklyAG := false;
   end if;
   return C`IsWeaklyAG;
end intrinsic;

intrinsic IsWeaklyAGDual(C::CodeLinFld) -> BoolElt
   {Return true if and only if C is constructed as the
   dual of a weakly algebraic-geometric 
   code.}
   if not assigned C`IsWeaklyAGDual then
      C`IsWeaklyAGDual := false;
   end if;
   return C`IsWeaklyAGDual;
end intrinsic;

intrinsic IsAlgebraicGeometric(C::CodeLinFld) -> BoolElt
   {Return true if and only if C is of algebraic-geometric
   construction of length n, built from a divisor D with deg(D) < n.}
   require IsWeaklyAG(C): 
      "Code must be of algebraic-geometric construction.";
   return Degree(Divisor(C)) lt Length(C);
end intrinsic;

intrinsic IsStronglyAG(C::CodeLinFld) -> BoolElt
   {Return true iff C is an algebraic-geometric code of length n 
   built from a divisor D with 2g-2 < deg(D) < n.}

   require IsWeaklyAG(C):"Code must be algebraic-geometric.";
   D := Divisor(C);
   X := Curve(D);
   g := GeometricGenus(X);
   return (deg gt 2*g-2) and (deg lt Length(C)) 
      where deg is Degree(Divisor(C));
end intrinsic;

////////////////////////////////////////////////////////////////////
//                      Access Functions                          //
////////////////////////////////////////////////////////////////////

intrinsic Curve(C::CodeLinFld) -> Crv
   {Given an algebraic-geometric code, returns the curve from which 
   is was defined.}
   require IsWeaklyAG(C): 
      "Code must be of algebraic-geometric construction.";
   return Curve(C`Divisor);
end intrinsic;

intrinsic GeometricSupport(C::CodeLinFld) -> DivCrvElt
   {Given an algebraic-geometric code, returns the sequence of 
   places from which forms its support.}
   require IsWeaklyAG(C):"Code must be weakly algebraic-geometric.";
   return C`GeometricSupport;
end intrinsic;

intrinsic Divisor(C::CodeLinFld) -> DivCrvElt
   {Given an algebraic-geometric code, returns the divisor from which 
   C was constructed.}
   require IsWeaklyAG(C): 
      "Code must be of algebraic-geometric construction.";
   return C`Divisor;
end intrinsic;

intrinsic GoppaDesignedDistance(C::CodeLinFld) -> RngIntElt
   {Given an algebraic-geometric code built with a divisor D, returns 
   the Goppa designed distance: n - deg(D).}
   require IsWeaklyAG(C):"Code must be weakly algebraic-geometric.";
   require IsAlgebraicGeometric(C): 
      "Code must be algebraic-geometric.";
   if not assigned C`GoppaDesignedDistance then
      C`GoppaDesignedDistance := Length(C)-Degree(Divisor(C));
   end if;
   return C`GoppaDesignedDistance;
end intrinsic;


////////////////////////////////////////////////////////

intrinsic AGDecode(C::CodeLinFld, rec_vec::ModTupFldElt, Fd::DivCrvElt) -> ModTupFldElt, BoolElt
{Decode a dual Algebraic Geometric code up to the designated distance.
Requires an input divisor Fd whose support is disjoint from the 
divisor defining the curve.}

    require C`IsWeaklyAGDual : "C must be a dual AG code";

    D := C`Divisor;
    Cv := Curve(D);
    g := Genus (Cv);
    F := CoefficientRing(Cv);
    P := C`GeometricSupport;
    t := Floor((C`GoppaDesignedDistance-1)/2);
    n := #P;

    require n eq Length(C) : "Code Length does not match assigned Curve";
    require Curve(Fd) eq Cv : "Divisor is not from the correct curve";
    require Ncols(rec_vec) eq n : "Received vector has incorrect length";
    require CoefficientRing(rec_vec) eq F : "Received vector over incorrect field";

    bad_div := 
	/* Degree(Fd) le a and */
      IsEmpty(Seqset(Support(Fd)) meet Seqset(P)) and
      Dimension(RiemannRochSpace(Fd)) gt t  and
      Degree(D - Fd) gt 2*g - 2 + t and
      Degree(Fd) ge t + g
      /* a - Degree(Fd) gt t + 2*g - 2 */ ;

    require not bad_div : "Divisor does not meet required conditions";
    
        ///////////// basis of the spaces of functions
    LD, mp := RiemannRochSpace(D);
    kD := Dimension(LD);
    LD_basis := [ mp(x) : x in Basis(LD) ];

    LF, mp := RiemannRochSpace(Fd);
    kF := Dimension(LF);
    LF_basis := [ mp(x) : x in Basis(LF) ];

    LDF, mp := RiemannRochSpace(D-Fd);
    kDF := Dimension(LDF);
    LDF_basis := [ mp(x) : x in Basis(LDF) ];

        //////////// now build the matrices needed
    M :=  Matrix(F, kD,  n, [ Evaluate(x, p) : p in P, x in LD_basis ]);
    G :=  Matrix(F, kF,  n, [ Evaluate(x, p) : p in P, x in LF_basis ]);
    H :=  Matrix(F, kDF, n, [ Evaluate(x, p) : p in P, x in LDF_basis]);

    S := G * DiagonalMatrix(F, n, [ rec_vec[i] : i in [1..n] ]) * Transpose(H);

        //////////// get an error locator polynomial
    NS := NullSpace(S);
//"dim:",Dimension(NS);
    if IsZero(Dimension(NS)) then error "no error locator found"; end if;
    err_locator   := Random(NS);
    err_locations := err_locator * G;
    zeroes := { i : i in [1..n] | IsZero(err_locations[i]) };
//"located:",zeroes;

        ///////////  Solve for error values
    syn := Transpose(M*Transpose(Matrix(rec_vec)));
    W := M;
    for i in [Ncols(W)..1 by -1] do
        if i in zeroes then continue; end if;
        RemoveColumn(~W, i);
    end for;

    soln := Solution(Transpose(W), syn);

    Z := Sort(Setseq(zeroes));
    res_e := Zero(Parent(rec_vec));
    for i in [1..#Z] do
        res_e[Z[i]] := soln[1][i];
    end for;

    res := rec_vec - res_e;

    return res, res in C;
end intrinsic;
