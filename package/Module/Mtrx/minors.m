freeze;

///////////////////////////////////////////////////////////////////////
// minors.m		matrix minors
///////////////////////////////////////////////////////////////////////

function get_minors(M, r, signed)
    R := BaseRing(Parent(M));
    nr := NumberOfRows(M);
    nc := NumberOfColumns(M);
    minors := [R|];
    cols := Sort([Sort(SetToSequence(s)) : s in Subsets({1..nc}, r)]);
    rows := Sort([Sort(SetToSequence(s)) : s in Subsets({1..nr}, r)]);
    for csp in cols do
	for rsp in rows do
	    // Get submatrix determinant, adjust sign if appropriate
	    det := Determinant(Submatrix(M, rsp, csp));
	    if signed and IsOdd(&+csp + &+rsp) then
		det := -det;
	    end if;
	    Append(~minors, det);
	end for;
    end for;
    Reverse(~minors);
    return minors;
end function;

function get_minors2(M, r, signed)
    R := BaseRing(Parent(M));
    nr := NumberOfRows(M);
    nc := NumberOfColumns(M);
    minors := [R|];
    cols := Sort([Sort(SetToSequence(s)) : s in Subsets({1..nc}, r)]);
    rows := Sort([Sort(SetToSequence(s)) : s in Subsets({1..nr}, r)]);

    A := AssociativeArray();

    for csp in cols do
	for rsp in rows do
	    // Get submatrix determinant, adjust sign if appropriate
	    det := Determinant(Submatrix(M, rsp, csp));
	    if signed and IsOdd(&+csp + &+rsp) then
		det := -det;
	    end if;
	    Append(~minors, det);
	end for;
    end for;
    Reverse(~minors);
    return minors;
end function;

function minor(M, i, j)
    return Determinant(RemoveRowColumn(M, i, j));
end function;


intrinsic Minors(A::Mtrx, r::RngIntElt) -> SeqEnum
{A sequence containing all the r by r minors of A}
    require r ge 0: "Minor dimension must be non-negative";

    if r gt NumberOfRows(A) or r gt NumberOfColumns(A) then
	return [ BaseRing(Parent(A)) | ];
    end if;
    return get_minors(A, r, false);
end intrinsic;

intrinsic Minor(A::Mtrx, I::[RngIntElt], J::[RngIntElt]) -> RngElt
{The determinant of the submatrix of A given by the row indices in
I and the column indices in J}
    require #I eq #J: "Submatrix must be square";
    require forall{i: i in I | 1 le i and i le Nrows(A)}: "Row index out of range";
    require forall{j: j in J | 1 le j and j le Ncols(A)}: "Column index out of range";

    return Determinant(Submatrix(A, I, J));
end intrinsic;

intrinsic Minor(A::Mtrx, i::RngIntElt, j::RngIntElt) -> RngElt
{The determinant of the submatrix of A formed by excluding the i-th row
and the j-th column}
    require Nrows(A) eq Ncols(A): "Matrix must be square";
    requirerange i,1,Nrows(A);
    requirerange j,1,Ncols(A);

    return minor(A, i, j);
end intrinsic;


intrinsic Cofactors(A::Mtrx, r::RngIntElt) -> SeqEnum
{A sequence containing all the r by r cofactors of A}
    require r ge 0: "Minor dimension must be non-negative";

    if r gt NumberOfRows(A) or r gt NumberOfColumns(A) then
	return [ BaseRing(Parent(A)) | ];
    end if;
    return get_minors(A, r, true);
end intrinsic;

intrinsic Cofactors(A::Mtrx) -> SeqEnum
{A sequence containing the cofactors of A}
    require Nrows(A) eq Ncols(A): "Matrix must be square";
    require Nrows(A) gt 0: "Cannot take cofactors of zero-dimensional matrix";

    return get_minors(A, Nrows(A)-1, true);
end intrinsic;

intrinsic Cofactor(A::Mtrx, i::RngIntElt, j::RngIntElt) -> RngElt
{The determinant of the submatrix of A formed by excluding the i-th row
and the j-th column, multiplied by (-1)^(i+j)}
    require Nrows(A) eq Ncols(A): "Matrix must be square";
    requirerange i,1,Nrows(A);
    requirerange j,1,Ncols(A);

    return (-1)^(i+j)*minor(A, i, j);
end intrinsic;

