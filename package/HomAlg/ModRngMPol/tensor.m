freeze;

/*******************************************************************************
				Tensor Product
*******************************************************************************/

intrinsic TensorProduct(M::ModMPol, N::ModMPol: Minimize := true) -> ModMPol
{The tensor product T of modules M and N and a map f: (M x N) -> T}

    R := BaseRing(M);

    MP := Presentation(M);
    NP := Presentation(N);

    /*
    MX := RelationMatrix(MP);
    NX := RelationMatrix(NP);
    TX := TensorProduct(MX, NX);
    */

    MX := TensorProduct(RelationMatrix(MP), IdentityMatrix(R, Degree(NP)));
    NX := TensorProduct(IdentityMatrix(R, Degree(MP)), RelationMatrix(NP));
    TX := VerticalJoin(MX, NX);

    // "TX:", TX;

    MC := ColumnWeights(MP);
    NC := ColumnWeights(NP);
    C := [i + j: j in NC, i in MC];

    if IsGraded(M) and IsGraded(N) then
	G := GradedModule(R, C);
    else
	G := RModule(R, C);
    end if;

    T := quo<G | Rows(TX): Minimize := Minimize>;

    f := map<
	CartesianProduct(M, N) -> T |
	t :-> T!G!Eltseq(TensorProduct(Vector(MP!t[1]), Vector(NP!t[2])))
    >;

    return T, f, G;
end intrinsic;

/*******************************************************************************
			Tensor Product with complex
*******************************************************************************/

intrinsic TensorProduct(C::ModCpx, N::ModMPol) -> ModCpx
{Return the tensor product of the complex C and the module N}

    N := Presentation(N);

    max, min := Degrees(C);
    dir := -1;
    C_range := [max .. min by dir];

    TB := [**];

    //NB := BasisMatrix(N);
    NB := MatrixRing(BaseRing(N), Degree(N))!1; // To avoid reduction
    TL := 0;
    TGL := 0;

    for i in C_range do
	M := Term(C, i);
	T, f, TG := TensorProduct(M, N: Minimize := false);

	// "\n***********"; i; "M:", M; "TG:", TG; "T:", T;

	if i ne C_range[1] then
	    X := BoundaryMap(C, i - dir);
	    mat := TensorProduct(Matrix(X), NB);
	    GY := Homomorphism(TGL, TG, mat: Check := 1 eq 1);

	    /*
	    "X:", X;
	    "X tens mat:", mat;
	    "GY:", GY;
	    "TGL:", TGL;
	    Relations(TGL);
	    "TG:", TG;
	    Relations(TG);
	    Morphism(TG, T); GY*Morphism(TG, T);
	    "TL:", TL; "TGL:", TGL; "TGL -> TL:", Morphism(TGL, TL);
	    */

	    imat := Matrix([TGL | UnitVector(TL, i): i in [1 .. Degree(TL)]]);

	    if 1 eq 1 then
		// "3 mats:"; imat, mat, Matrix(Morphism(TG, T));
		// "prod:"; imat*mat*Matrix(Morphism(TG, T));
		// "TL:", TL; "T:", T;
		Y := Homomorphism(TL, T, imat*mat*Matrix(Morphism(TG, T)));
	    else
		imat := Homomorphism(TL, TGL, imat);
		Y := imat*GY*Morphism(TG, T);
	    end if;

	    // "final Y:", Y;
	    Append(~TB, Y);
	end if;

	TL := T;
	TGL := TG;
    end for;

    return Complex(TB, min);
end intrinsic;

/*******************************************************************************
				Tor
*******************************************************************************/

intrinsic Tor(i::RngIntElt, M::ModMPol, N::ModMPol) -> ModMPol
{Return Tor^i(M, N)}

    if i eq 0 then
    end if;

    C, cmp := FreeResolution(M: Limit := i + 1);

    R := BaseRing(M);
    m := #DimensionsOfTerms(C) - 2;

    if i ge m then
	return RModule(R, 0);
    end if;

    CT := TensorProduct(C, N);
    if IsZero(Term(CT, i)) then
	return RModule(R, 0);
    end if;

    T := Homology(CT, i);
    return T;
end intrinsic;
