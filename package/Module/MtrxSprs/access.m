freeze;

intrinsic Submatrix(X::MtrxSprs, I::[RngIntElt], J::[RngIntElt]) -> Mtrx
{Return the submatrix of X given by the row indices in I and
the column indices in J.}
    
    require forall{i: i in I | i in [1 .. Nrows(X)]}: "Row index out of range";
    require forall{j: j in J | j in [1 .. Ncols(X)]}:
	"Column index out of range";

    Y := SparseMatrix(BaseRing(X), #I, #J);
    for ci := 1 to #I do
	i := I[ci];
	for cj := 1 to #J do
	    Y[ci, cj] := X[i, J[cj]];
	end for;
    end for;

    return Y;
end intrinsic;
