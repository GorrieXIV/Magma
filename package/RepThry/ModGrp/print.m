freeze;

// AKS, 2010

is_ext_ring := func<K |
    Type(K) in {FldNum, FldCyc, FldQuad} or
    ISA(Type(K), FldFin) and Degree(K) gt 1
>;

procedure PrintMat(X, ie)
    if not ie then
	printf "%m", Matrix(X);
	return;
    end if;

    K<w> := BaseRing(X); // Needed for wretched print name
    if IsScalar(X) and Ncols(X) gt 0 then
	printf "ScalarMatrix(K, %o, %o)", Ncols(X), X[1, 1];
    elif IsDiagonal(X) then
	printf "DiagonalMatrix(K, %o)", [Sprint(x): x in Diagonal(X)];
    elif true and Density(X) le 0.5 then
	printf "Matrix(%m)", SparseMatrix(X);
    else
	printf "Matrix(K, %o, %o,\n", Nrows(X), Ncols(X);
	IndentPush();
	printf "%o)", [Sprint(Eltseq(x)): x in Eltseq(X)];
	IndentPop();
    end if;
end procedure;

intrinsic PrintModuleMagma(M::ModRng: GName := "G")
{Print module M in Magma mode (better version for extension rings)}

    K<w> := BaseRing(M);
    ie := is_ext_ring(K);

    if Type(M) eq ModGrp then
	if GName cmpne 0 then
	    printf "GModule(%o, ", GName;
	else
	    G := Group(M);
	    printf "GModule(%m, ", G;
	end if;
    else
	printf "RModule(";
    end if;

    "[";
    IndentPush();

    nag := Nagens(M);
    for i := 1 to nag do
	PrintMat(ActionGenerator(M, i), ie);

	if i lt nag then
	    printf ",";
	end if;
	"";
    end for;

    IndentPop();
    printf "]";
    if Type(M) eq ModGrp then
	printf(": Check := false");
    end if;
    printf ") where w := K.1 where K := %m", K;

end intrinsic;

intrinsic PrintMatgMagma(G::GrpMat)
{Print matrix group in Magma mode (better version for extension rings)}

    K<w> := BaseRing(G);
    ie := is_ext_ring(K);

    printf "MatrixGroup<%o, K | [\n", Degree(G);
    IndentPush();

    ng := Ngens(G);
    for i := 1 to ng do
	PrintMat(G.i, ie);
	if i lt ng then
	    printf ",";
	end if;
	"";
    end for;

    IndentPop();
    printf "]> where w := K.1 where K := %m", K;

end intrinsic;
