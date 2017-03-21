freeze;

/*
New ANF/order CRT.
AKS, Feb 2013.
*/

Z := IntegerRing();

/******************************************************************************/

function setup_IQ(IQ)
    O := Order(IQ[1]);
    n := Degree(O);

    IP := &*IQ;
    B := LLL(BasisMatrix(IP));

    k := #IQ;
    if k eq 2 then
	IC := [IQ[2], IQ[1]];
    elif true then
	IC := [];
	// "Get IC via inverses"; time
	for i := 1 to k do
	    J := IQ[i]/2*2; // To make it fractional
	    J := J^-1;
	    Append(~IC, O!!(IP * J));
	end for;
	// "CHECK IC"; time assert IC eq [&*[IQ[j]: j in [1 .. k] | j ne i]:i in [1 .. k]];
    else
	IC := [&*[IQ[j]: j in [1 .. k] | j ne i]: i in [1 .. k]];
    end if;

    //"IC:", IC;
    //"Get BM"; time
    BM := [LLL(BasisMatrix(I)): I in IC];

    U := VerticalJoin(BM);
    // "BM:", BM;
    // "U:", U;

    if 1 eq 1 then

	time VY, V, N, Ypp, Y, pp := LatticeBasisMatrix(U);
	// pp is minimal list
	delete VY;

	US := RowSubmatrix(U, pp);
//"Get Herm", Parent(US); time
	USH, UST := HermiteForm(US: Optimize); // split out
	w := UST[1];
//"Got w:", w;
	v := RSpace(Z, Nrows(U)) ! 0;
	for i := 1 to #pp do
	    v[pp[i]] := w[i];
	end for;

    elif 1 eq 0 then
	// "Get Hermite"; Parent(U); time
	UH, UT := HermiteForm(U: Optimize := false);
	v := UT[1];
	//delete UH;

	BlockSize := 200;
	BlockSize := 50;
	BlockSize := 10;
	r := Nrows(UT);
	// "Nicify v"; time
//time
	for b := n + 1 to r by BlockSize do
	    T := RowSubmatrixRange(UT, b, Min(b + BlockSize - 1, r));
	    T := VerticalJoin(T, v);
	    t := Nrows(T);
	    T := GramSchmidtReduce(T, t - 1);
	    v := T[t];
	    // "b:", b; "v:", v;
	end for;
// assert v*U eq UH[1];
	delete UH;
    else
	// "Get Hermite"; Parent(U); U: Magma; time
	UH, UT := HermiteForm(U: Optimize);
	v := UT[1];
	// "UH:", UH; "UT:", UT;
    end if;

    // "v:", v; "Get idem"; time
    idem := [O | Eltseq(ColumnSubmatrix(v, (i - 1)*n + 1, n)*BM[i]):
	i in [1 .. k]];

    // "idem:", idem; "&+idem:", &+idem;
    assert &+idem eq 1;
    // "Do idem check"; time
    // for i := 1 to k do assert idem[i] in IC[i]; end for;

    // "B log norms:", LogNorms(B);

    return B, idem;

end function;

/******************************************************************************/

intrinsic InternalCRTSetup(IQ::[RngOrdIdl]) -> .
{Internal}

    B, idem := setup_IQ(IQ);
    return B, idem, Matrix([Eltseq(x): x in idem]);

end intrinsic;

intrinsic InternalCRTSetup(I::RngOrdIdl, J::RngOrdIdl) -> .
{Internal}

    return InternalCRTSetup([I, J]);

end intrinsic;
