freeze;

/*
Operations on Complexes.
AKS, Oct 08.
*/

////////////////////////////////////////////////////////////////////////////////

AddAttribute(ModMPol, "HomMap");

intrinsic Hom(C::ModCpx, N::ModMPol) -> ModCpx
{Return Hom(C, N)}

    max, min := Degrees(C);
    dir := -1;
    C_range := [max .. min by dir];

    HT := [];
    HB := [**];

    HL := 0;
    HLf := 0;

    for i in C_range do
	M := Term(C, i);
//"\n*** i:", i; Term M:", M;
	H, Hf := Hom(M, N);
	Append(~HT, H);
//"H:", H;

H`HomMap := Hf;

	if i ne C_range[1] then
	    X := BoundaryMap(C, i - dir);

	    /*
	    Compute Y so that Y maps phi to psi, where psi = X.phi,
	    where phi in H, psi in HL.
	    */

	    I := [HL | ];
	    //d := Dimension(H);
	    d := Degree(H);
	    for j := 1 to d do
		phi := Hf(H.j);
// "\nj:", j;
// "X:", X; Parent(X);
// "IsHomogeneous:", IsHomogeneous(X);
// "phi:", phi; Parent(phi);
// "IsHomogeneous:", IsHomogeneous(phi);
		psi := X * phi;
// "psi:", psi; Parent(psi);
// "IsHomogeneous:", IsHomogeneous(psi);
		im := psi @@ HLf;
// "im:", im;
// "IsHomogeneous:", IsHomogeneous(im);
		Append(~I, im);
	    end for;
	    //Y := RMatrixSpace(H, HL) ! Matrix(I);
// "I:", I;
// "H:", H;
// "HL:", HL;
	    //mat := Matrix(BaseRing(M), Degree(HL), &cat[Eltseq(v): v in I]);
	    mat := Matrix(I);
//"H:", H; BaseRing(H);
//"HL:", HL; BaseRing(HL);
//"mat:", Parent(mat); BaseRing(Parent(mat));
	    Y := Homomorphism(H, HL, mat);
// "final Y:", Y;
	    Append(~HB, Y);
	end if;

	HL := H;
	HLf := Hf;
    end for;

    return LeftComplex(HB, min);

    return HB;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////

intrinsic Ext(i::RngIntElt, M::ModMPol, N::ModMPol) -> ModMPol
{Return Ext^i(M, N)}

    C, cmp := FreeResolution(M: Limit := i + 1);

    CH := Hom(C, N);

    R := BaseRing(M);
    m := #DimensionsOfTerms(CH) - 2;

    if i ge m then
        return RModule(R, 0);
    end if;

    f_in := BoundaryMap(CH, i);
    f_out := BoundaryMap(CH, i + 1);

    im := Image(f_in);
    ker := Kernel(f_out);
    q := ker/im;
    return q;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////
