freeze;

Z := IntegerRing();
Q := RationalField();

function RowSum(v)
    return &+[v[i]: i in [1..Ncols(v)]];
end function;

function ReducedLattice(B)
    g := GCD(Eltseq(B * Transpose(B)));
    if g eq 1 then
	return LatticeWithBasis(B);
    else
	MQ := MatrixRing(Q, Nrows(B));
	return LatticeWithBasis(MQ!B, MQ!1/g);
    end if;
end function;

intrinsic Lattice(C::CodeLinRng) -> Lat
{Construct the lattice corresponding to a code over Z/mZ via construction A}
 K:=Alphabet(C); require Type(K) eq RngIntRes: "Code must be over Z/mZ";
 m:=#K; B:=BasisMatrix(C); k:=NumberOfRows(B); n:=Length(C);
 B:=RMatrixSpace(Z,k,n)!B; B:=VerticalJoin(B,MatrixRing(Z,n)!m);
 H:=EchelonForm(B); H:=ChangeRing(Submatrix(H,1,1,n,n),Rationals());
 return LatticeWithBasis(H,MatrixRing(Rationals(),n)!(1/m)); end intrinsic;

intrinsic Lattice(C::CodeLinFld, S::MonStgElt) -> Lat
{The lattice constructed from code C according to method S};

    K := Alphabet(C);

    if S eq "A" then

    require Degree(K) eq 1: "Alphabet of argument 1 must be prime";

	p := #K;
	B := BasisMatrix(C);
	k := Dimension(C);
	n := Length(C);
	B := RMatrixSpace(Z, k, n) ! BasisMatrix(C);
	B := VerticalJoin(B, MatrixRing(Z, n) ! p);
	H := EchelonForm(B);
	H := Submatrix(H, 1, 1, n, n);
	return LatticeWithBasis(H);

    elif S eq "B" then

	require Degree(K) eq 1: "Alphabet of argument 1 must be prime";

	p := #K;
	B := BasisMatrix(C);
	n := Length(C);
	k := Dimension(C);

	require forall{i: i in [1 .. k] | RowSum(B[i]) eq 0}:
	    "Not all codewords of argument 1 have zero coordinate sum";

	B := RMatrixSpace(Z, k, n) ! BasisMatrix(C);
	for i := 1 to k do
	    B[i][1] -:= RowSum(B[i]) mod p^2;
	end for;

	P := RMatrixSpace(Z, n, n) ! 0;
        for i := 1 to n - 1 do
            P[i][i] := p^2 - p;
            P[i][i + 1] := p;
        end for;
	P[n][n] := p^2;

	H := EchelonForm(VerticalJoin(B, P));
	H := Submatrix(H, 1, 1, n, n);

	return ReducedLattice(H);

    else

	require false: "Argument 2 should be \"A\" or \"B\"";

    end if;
end intrinsic;
