freeze;

/*******************************************************************************
			    Basic defs
*******************************************************************************/

Z := IntegerRing();

Diag := func<X | [X[i][i]: i in [1 .. Min(Nrows(X), Ncols(X))]]>;
DUMP := func<X | Diag(X)>;

//MyHerm := HermiteForm;
//MyHerm := EchRec;
//MyHerm := HMod;
MyHerm := HermiteForm;

/*******************************************************************************
			    Aux functions
*******************************************************************************/

function pivots(X)
    return [Min(Support(X[i])): i in [1 .. Nrows(X)]];
end function;

procedure inv_rows(~X)
    i := 1;
    j := Nrows(X);
    while i lt j do
	SwapRows(~X, i, j);
	i +:= 1;
	j -:= 1;
    end while;
end procedure;

procedure inv_cols(~X)
    i := 1;
    j := Ncols(X);
    while i lt j do
	SwapColumns(~X, i, j);
	i +:= 1;
	j -:= 1;
    end while;
end procedure;

function ppart(w)
    ew := Eltseq(w);
    g := GCD(ew);
    assert g gt 1;
    w := Parent(w)![x div g: x in ew];
    return w;
end function;

/*******************************************************************************
			    Iterative Sat
*******************************************************************************/

ITER_START := 20;

function sat_iter(X)

    nr := Nrows(X);
    nc := Ncols(X);

    vprintf Saturation: "Iterative Saturation: %o by %o\n", nr, nc;

    D := [];
    d := nr;
    while d ge ITER_START do
        Append(~D, d);
        d := (d + 1) div 2;
    end while;
    D := Reverse(D);

    vprint Saturation: "D:", D;
    v := GetVerbose("Saturation");

    for d in D do
        T := <>;
        I := [1 .. nr by d];
        vprintf Saturation: "d: %o, I: %o\n", d, [i: i in I];
        vtime Saturation: for i in I do
            Y := RowSubmatrix(X, i, Min(d, nr - i + 1));
	    SetVerbose("Saturation", 0);
            Y := Saturation(Y);
	    SetVerbose("Saturation", v);
Y := HermiteForm(Y: Al := "Classical");
            Append(~T, Y);
        end for;
        X := VerticalJoin(T);
        delete T;
    end for;

    return X;
end function;


/*******************************************************************************
			    Basic defs
*******************************************************************************/

intrinsic NewSaturation(X::Mtrx) -> Mtrx
{Internal}

    if 0 eq 1 then
	r := Round(1000*Cputime());

	FN := Sprintf("%o/mat%o_%o_%o", GetTempDir(), r, Nrows(X), Ncols(X));
	printf "NewSaturation Dump to %o\n", FN;
	PrintFile(FN, Sprintf("X := %m;\n", X));
    end if;

    if 0 eq 1 then
	vprintf Saturation: "Saturation: %o by %o\n", Nrows(X), Ncols(X);
	vprint Saturation: "Get rational echelon";
	vtime Saturation: E := RemoveZeroRows(EchRat(X));
if Nrows(E) gt ITER_START then
    return sat_iter(E);
end if;
return Saturation(X);

	piv := pivots(E);
	assert #piv eq Nrows(E);

	M := LCM([E[i, piv[i]]: i in [1 .. #piv]]);
	vprint Saturation: "Modulus:", M;
	R := IntegerRing(2*M);
	H := Matrix(R, Transpose(E));
	vprint Saturation: "Get echelon mod M:";
	vtime Saturation: H := EchelonForm(H);
	H := RemoveZeroRows(H);
	H := Matrix(Z, H);
	vprint Saturation: "Get Inverse";
	vtime Saturation: HI, d := PseudoInverse(H);
	delete H;
	vprint Saturation: "Denom:", d;
	vprint Saturation: "Get product";
	vtime Saturation: E := HI * E;
	RemoveRowContents(~E);
	return E;
    end if;

return Saturation(X);

    vprint Saturation: "NewSaturation: get HMod";

/*
"SAT X:";
X: Magma;
";";
*/

    vtime Saturation: H := MyHerm(Transpose(X));

    r := Nrows(X);
    H := RowSubmatrix(H, 1, r);

    while true do
	vprint Saturation: "\n****";
	vprint Saturation: "H:", DUMP(H);

	if not exists(i){i: i in [1 .. r] | H[i, i] ne 1} then
	    break;
	end if;

	M := H[i, i];
//M := LCM(Diag(H));

	vprint Saturation: "M:", M;
	R := IntegerRing(M);

	HR := Matrix(R, H);
	inv_cols(~HR);
	N := BasisMatrix(NullspaceOfTranspose(HR));
	//"First N:", N;
	inv_cols(~N);
	//inv_rows(~H);

	N := Matrix(Z, N);
	vprint Saturation: "Dim N:", Nrows(N);
	assert Nrows(N) gt 0;

//"Swapped H:", H;
	HT := Transpose(H);
//"HT:", HT;
	HH := HT;

	vprint Saturation: "Do N*HT";
	vtime Saturation: NHT := N*HT;
	vprint Saturation: "Do N*X";
	vtime Saturation: NX := N*X;
	for i := 1 to Nrows(N) do
	    v := N[i];
	    j := Max(Support(v));
//"i:", i;
//"j:", j;
//"v*HT:", v*HT;
	    HH[j] := ppart(NHT[i]);
	    X[j] := ppart(NX[i]);
	end for;
	delete NX, NHT;
	//"HH:", DUMP(HH);
	H := Transpose(HH);
	//"H:", H;

    end while;

    return X;
end intrinsic;
