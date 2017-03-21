freeze;

/*******************************************************************************
			    Block matrices
*******************************************************************************/

/*
Steve Donnelly, June 2006.
*/

intrinsic BlockMatrix(m::RngIntElt, n::RngIntElt, blocks::SeqEnum[Mtrx]) -> Mtrx
{The matrix constructed from the given block matrices, which should all have the
same dimensions, and should be given as a sequence of m*n block matrices (in 
row-major order, in other words listed across rows).}

  return BlockMatrix([[blocks[j+n*(i-1)] : j in [1..n]] : i in [1 .. m]]);
end intrinsic;  

intrinsic BlockMatrix(rows::SeqEnum[SeqEnum]) -> Mtrx
{The matrix constructed from the block matrices given by the sequence
of sequences}

  return BlockMatrix(#rows, #rows[1], rows);
end intrinsic;

intrinsic BlockMatrix(m::RngIntElt, n::RngIntElt, rows::SeqEnum[SeqEnum])
    -> Mtrx
{The matrix constructed from the given block matrices, which should all
have the same dimensions, and should be given as a sequence of m rows,
each containing n block matrices.}

    /*
    AKS, Sep 13 (saves a lot of memory copying):
    */

    assert m eq #rows;
    assert n eq #rows[1];
    Y := rows[1, 1];
    nr := Nrows(Y);
    nc := Ncols(Y);
    X := ZeroMatrix(CoefficientRing(Y), m*nr, n*nc);
    bi := 1;
    for i := 1 to #rows do
	L := rows[i];
	bj := 1;
	for j := 1 to #L do
	    InsertBlock(~X, L[j], bi, bj);
	    bj +:= nc;
	end for;
	bi +:= nr;
    end for;
    return X;

    /*
    ans := Matrix(
	CoefficientRing(U), 0, n*NumberOfColumns(rows[1][1]), []
    );
    for row in rows do
	row_joined := row[1];
	for j := 2 to n do
	    row_joined := HorizontalJoin(row_joined, row[j]);
	end for;
	ans := VerticalJoin(ans, row_joined);
    end for;
    return ans; 
    */

end intrinsic;
