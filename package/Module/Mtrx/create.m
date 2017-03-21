freeze;

/*******************************************************************************
			    Standard Matrix functions
*******************************************************************************/

intrinsic Matrix(Q::[[]]) -> Mtrx
{The matrix with m rows and n columns, whose rows are given by the
elements of Q, where Q is a sequence of m sequences, each of length n}
    m := #Q;

    require m gt 0: "Argument 1 must not be empty";

    v := Q[1];
    require not IsNull(v): "Inner sequence must not be null ";
    n := #v;
    require ISA(Type(Universe(v)), Rng):
	"Inner sequences do not contain ring elements";

    for i := 2 to m do
	require #(Q[i]) eq n:
	    "Element", i, "of sequence does not have length", n;
    end for;

    Q := &cat Q;
    return Matrix(m, n, Q);
end intrinsic;

intrinsic Matrix(R::Rng, Q::[[]]) -> Mtrx
{The matrix over R with m rows and n columns, whose rows are given by the
elements of Q, where Q is a sequence of m sequences, each of length n}

    m := #Q;

    require m gt 0: "Argument 2 must not be empty";

    v := Q[1];
    //require not IsNull(v): "Inner sequence must not be null";
    n := #v;
    if not IsNull(v) then
	S := Universe(v);
	require ISA(Type(S), Rng):
	    "Inner sequences do not contain ring elements";
    end if;

    for i := 2 to m do
	require #(Q[i]) eq n:
	    "Element", i, "of sequence does not have length", n;
    end for;

    Q := &cat Q;
    l, Q := CanChangeUniverse(Q, R);
    require l: "Element of inner sequence not coercible into argument 1";

    return Matrix(m, n, Q);
end intrinsic;

intrinsic Matrix(m::RngIntElt, n::RngIntElt, Q::[[]]) -> Mtrx
{The matrix with m rows and n columns, whose rows are given by the
elements of Q, where Q is a sequence of m sequences, each of length n}

    require #Q eq m: "Length of argument 3 is not", m;
    require not IsNull(Q): "Argument 3 must not be null";

    for i := 1 to m do
	require #(Q[i]) eq n:
	    "Element", i, "of sequence does not have length", n;
    end for;

    Q := &cat Q;
    return Matrix(m, n, Q);
end intrinsic;

intrinsic Matrix(R::Rng, m::RngIntElt, n::RngIntElt, Q::[[]]) -> Mtrx
{The matrix over R with m rows and n columns, whose rows are given by the
elements of Q, where Q is a sequence of m sequences, each of length n}

    if #Q ne m and #Q eq m*n then
	QQ := [];
	for x in Q do
	    l, y := IsCoercible(R, x);
	    require l: "Element of sequence not coercible into R";
	    Append(~QQ, y);
	end for;
	return Matrix(R, m, n, QQ);
    end if;

    require #Q eq m: "Length of argument 4 is not", m;

    for i := 1 to m do
	require #(Q[i]) eq n:
	    "Element", i, "of sequence does not have length", n;
    end for;

    Q := &cat Q;
    return Matrix(R, m, n, Q);
end intrinsic;

intrinsic ColumnMatrix(Q::[RngElt]) -> Mtrx
{The column matrix given by the entries of Q}
    require not IsNull(Q): "Sequence must not be null ";
    return Matrix(1, Q);
end intrinsic;

intrinsic Matrix(m::RngIntElt, n::RngIntElt, Q::[ModTupRngElt]) -> Mtrx
{The matrix with m rows and n columns, whose rows are given by the
elements of Q, where Q is a sequence of m vectors, each of length n}

    require #Q eq m: "Length of argument 3 is not", m;
    require not IsNull(Q): "Argument 3 must not be null";
    require Degree(Universe(Q)) eq n:
	"Sequence does not contain vectors of length", n;

    return Matrix(Q);
    //Q := &cat [ Eltseq(Q[i]) : i in [1..m] ];
    //return Matrix(m, n, Q);
end intrinsic;

intrinsic Matrix(R::Rng, m::RngIntElt, n::RngIntElt, Q::[ModTupRngElt]) -> Mtrx
{The matrix over R with m rows and n columns, whose rows are given by the
elements of Q, where Q is a sequence of m vectors, each of length n}

    require #Q eq m: "Length of argument 4 is not", m;
    require Degree(Universe(Q)) eq n:
                            "Sequence does not contain vectors of length", n;
    l, Q := CanChangeUniverse(Q, RSpace(R,n));
    require l:
     "Elements of sequence cannot be coerced into tuple space over argument 1";

    Q := &cat [ Eltseq(Q[i]) : i in [1..m] ];

    return Matrix(R, m, n, Q);
end intrinsic;

/*******************************************************************************
			Diagonal matrices
*******************************************************************************/

intrinsic DiagonalMatrix(R::Rng, n::RngIntElt, Q::[RngElt]) -> Mtrx
{The diagonal matrix over R with n rows and n columns whose diagonal entries
correspond to the the entries of Q}

    require #Q eq n: "Length of argument 3 is not", n;
    l, Q := CanChangeUniverse(Q, R);
    require l: "Element of sequence not coercible into argument 1";
    return DiagonalMatrix(MatrixRing(R, n), Q);
end intrinsic;

intrinsic DiagonalMatrix(R::Rng, Q::[RngElt]) -> Mtrx
{The diagonal matrix over R with #Q rows and #Q columns whose diagonal entries
correspond to the the entries of Q}

    l, Q := CanChangeUniverse(Q, R);
    require l: "Element of sequence not coercible into argument 1";
    return DiagonalMatrix(MatrixRing(Universe(Q), #Q), Q);
end intrinsic;

intrinsic DiagonalMatrix(Q::[RngElt]) -> Mtrx
{The diagonal matrix with #Q rows and #Q columns whose diagonal entries
correspond to the the entries of Q}

    require not IsNull(Q): "Argument 1 must not be null";
    return DiagonalMatrix(MatrixRing(Universe(Q), #Q), Q);
end intrinsic;

/*******************************************************************************
				Zero/identity
*******************************************************************************/

intrinsic ZeroMatrix(R::Rng, m::RngIntElt, n::RngIntElt) -> Mtrx
{The zero matrix over R with m rows and n columns}
    return Matrix(R, m, n, []);
end intrinsic;

intrinsic IdentityMatrix(R::Rng,n::RngIntElt) -> AlgMatElt
{The identity (n x n)-matrix over the ring R}
    return MatrixRing(R, n) ! 1;
end intrinsic;

/*******************************************************************************
			    MonomialMatrix
*******************************************************************************/

intrinsic MonomialMatrix(
    m::RngIntElt, n::RngIntElt, Q::[RngElt], P::[]
) -> Mtrx
{The m by n monomial matrix corresponding to the ring elements in Q and the
integers in P}
  require #Q eq #P: "The two sequences must be the same length";
  require Seqset(P) subset { 1 .. n }:
    "The elements of P must be in the range", [ 1 .. n ];

  M := ZeroMatrix(Universe(Q), m, n);
  for i in [1 .. #Q] do
    M[i, P[i]] := Q[i];
  end for;
  return M;
end intrinsic;
  
intrinsic MonomialMatrix(Q::[RngElt], g::GrpPermElt) -> Mtrx
{The monomial matrix corresponding to the ring elements in Q and the
permutation g}

  require #Q eq Degree(Parent(g)): "Incompatible degrees";
  return DiagonalMatrix(Q) * PermutationMatrix(Universe(Q), g);
end intrinsic;
