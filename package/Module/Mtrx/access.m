freeze;

intrinsic CanWriteOver(M::Mtrx,A::AlgAssV : Check:=true) -> BoolElt,AlgAssVElt
{Given a dxd matrix and a d-dimensional algebra, return whether it represents
 an element of the algebra via RepresentationMatrix}
 d:=Dimension(A);
 require NumberOfRows(M) eq d and NumberOfColumns(M) eq d: "Matrix is not dxd";
 require BaseRing(M) subset BaseRing(Center(A)):
  "M must have entries in Center(A)"; // better check? -- M/K subset FldRat
 B:=Basis(A); r:=M[1]; e:=&+[r[i]*B[i] : i in [1..d]];
 // assumes top row of RepresentationMatrix is 1 at every place but one
 if Check then b:=(RepresentationMatrix(e) eq M); else b:=true; end if;
 if b eq false then return b,_; else return b,e; end if; end intrinsic;

intrinsic WriteOverElement(M::Mtrx,A::AlgAssV : Check:=true) -> AlgAssVElt
{Given a dxd matrix and a d-dimensional algebra that represents an element
 via RepresentationMatrix, return the element}
 b,e:=CanWriteOver(M,A : Check:=Check);
 if Check then require b: "Cannot write the matrix over the algebra"; end if;
 return e; end intrinsic;

intrinsic WriteOverMatrix(M::Mtrx,A::AlgAssV : Check:=true) -> Mtrx
{Given a md-by-nd matrix and a d-dimensional algebra that represents an
 element via RepresentationMatrix, return the element}
 d:=Dimension(A); r:=NumberOfRows(M); c:=NumberOfColumns(M);
 require r mod d eq 0 and c mod d eq 0: "Matrix is not the right dimension";
 R:=[[WriteOverElement(Submatrix(M,1+d*(i-1),1+d*(j-1),d,d),A : Check:=Check) :
		       j in [1..c div d]] : i in [1..r div d]];
 return Matrix(R); end intrinsic;

intrinsic WriteOver(M::Mtrx,A::AlgAssV : Check:=true) -> .
{Given a md-by-nd matrix and a d-dimensional algebra that represents an
 element via RepresentationMatrix, return the element, as an A-element
 in the dxd case, and else as a matrix}
 d:=Dimension(A); r:=NumberOfRows(M); c:=NumberOfColumns(M);
 require r mod d eq 0 and c mod d eq 0: "Matrix is not the right dimension";
 if d eq r and d eq c then return WriteOverElement(M,A : Check:=Check); end if;
 return WriteOverMatrix(M,A : Check:=Check); end intrinsic;

intrinsic RepresentationMatrixOfMatrix(M::Mtrx[AlgAssV] : Side:="Right") -> Mtrx
{Given a m-by-n matrix, return one over the base of size dm-by-dn}
 c:=NumberOfColumns(M); r:=NumberOfRows(M); d:=Degree(BaseRing(M));
 return BlockMatrix(r,c,[RepresentationMatrix(x: Side:=Side) :
					      x in Eltseq(M)]); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic CanWriteOver(M::Mtrx,K::FldNum : Check:=true) -> BoolElt,FldNumElt
{Given a dxd matrix and a d-dimensional algebra, return whether it represents
 an element of the algebra via RepresentationMatrix}
 d:=Degree(K);
 require NumberOfRows(M) eq d and NumberOfColumns(M) eq d: "Matrix is not dxd";
 B:=Basis(K); r:=M[1]; e:=&+[r[i]*B[i] : i in [1..d]];
 // assumes top row of RepresentationMatrix is 1 at every place but one
 if Check then b:=(RepresentationMatrix(e) eq M); else b:=true; end if;
 if b eq false then return b,_; else return b,e; end if; end intrinsic;

intrinsic WriteOverElement(M::Mtrx,K::FldNum : Check:=true) -> FldNumElt
{Given a dxd matrix and a d-dimensional algebra that represents an element
 via RepresentationMatrix, return the element}
 b,e:=CanWriteOver(M,K : Check:=Check);
 if Check then require b: "Cannot write the matrix over the field"; end if;
 return e; end intrinsic;

intrinsic WriteOverMatrix(M::Mtrx,K::FldNum : Check:=true) -> Mtrx
{Given a number field of degree d and a md-by-nd matrix and that represents an
 element via RepresentationMatrix, return the element}
 d:=Degree(K); r:=NumberOfRows(M); c:=NumberOfColumns(M);
 require r mod d eq 0 and c mod d eq 0: "Matrix is not the right dimension";
 R:=[[WriteOverElement(Submatrix(M,1+d*(i-1),1+d*(j-1),d,d),K : Check:=Check) :
		       j in [1..c div d]] : i in [1..r div d]];
 return Matrix(R); end intrinsic;

intrinsic WriteOver(M::Mtrx,K::FldNum : Check:=true) -> .
{Given a md-by-nd matrix and a d-dimensional number field that represents an
 element via RepresentationMatrix, return the element, as an K-element
 in the dxd case, and else as a matrix}
 d:=Degree(K); r:=NumberOfRows(M); c:=NumberOfColumns(M);
 require r mod d eq 0 and c mod d eq 0: "Matrix is not the right dimension";
 if d eq r and d eq c then return WriteOverElement(M,K : Check:=Check); end if;
 return WriteOverMatrix(M,K : Check:=Check); end intrinsic;

intrinsic RepresentationMatrixOfMatrix(M::Mtrx[FldNum]) -> Mtrx
{Given a m-by-n matrix over a number field,
 return one over the rationals of size dm-by-dn}
 c:=NumberOfColumns(M); r:=NumberOfRows(M); d:=Degree(BaseRing(M));
 return BlockMatrix(r,c,[RepresentationMatrix(x) : x in Eltseq(M)]);
 end intrinsic; /* MW 27 Aug 2010 */

////////////////////////////////////////////////////////////////////////

function density(X)
    l := Nrows(X) * Ncols(X);
    if l eq 0 then
	d := 0;
    else
	d := NumberOfNonZeroEntries(X) / l;
    end if;
    return d + 0.0;
end function;

intrinsic Density(X::Mtrx) -> RngElt
{The density of X, as an element of the default real field}
    return density(X);
end intrinsic;

intrinsic Density(X::MtrxSprs) -> RngElt
{The density of X, as an element of the default real field}
    return density(X);
end intrinsic;

intrinsic Submatrix(X::Mtrx, I::[RngIntElt], J::[RngIntElt]) -> Mtrx
{Return the submatrix of X given by the row indices in I and
the column indices in J.}
    
    require forall{i: i in I | i in [1 .. Nrows(X)]}: "Row index out of range";
    require forall{j: j in J | j in [1 .. Ncols(X)]}:
	"Column index out of range";

    return Matrix(BaseRing(X), #I, #J, [X[i, j]: j in J, i in I]);
end intrinsic;

intrinsic ExtractDiagonalBlocks(M::Mtrx) -> List
{Decomposition of the square matrix M as a block-diagonal matrix.
 Returns list of square matrices (possibly of different sizes)}
    r := Nrows(M); 
    require r eq Ncols(M) : "The argument must be a square matrix";
    blocks := [* *];
    b := 1; e := b; // will mark the beginning and end of a block
    repeat
        i := b;
        repeat
            e := Max([e] cat [j : j in [b..r] | M[i,j] ne 0]);
            i +:= 1;
        until i gt e; // now e = end of block
        Append(~blocks, ExtractBlock(M, [b..e], [b..e]) );
        b := e+1; e := b;
    until b gt r;
    return blocks;
end intrinsic;

intrinsic DiagonalBlocks(X::Mtrx, L::[RngIntElt]) -> []
{Return the diagonal blocks of given lengths in L}

    require forall{x ge 0: x in L}: "Lengths are not all non-negative";
    require &+L le Min(Nrows(X), Ncols(X)): "Lengths out of range";

    B := [**];
    b := 1;
    for e in L do
	Y := Submatrix(X, b,b, e,e);
	Append(~B, Y);
	b +:= e;
    end for;

    return B;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////

intrinsic DiagonalBlocksStructure(X::Mtrx) -> []
{Return the diagonal block structure of X (as a sequence of lengths)}

    require Nrows(X) eq Ncols(X): "Matrix must be square";

    n := Nrows(X);
    D := [];

    b := 1;
    p := 1;
    l := 0;
    while p le n do
	m := n;
	while m gt p and m ge l do
	    if X[p, m] ne 0 or X[m, p] ne 0 then
		break;
	    end if;
	    m -:= 1;
	end while;
	if m gt l then
	    l := m;
	end if;
//"p:", p, "m:", m, "l:", l;
	if l eq p then
	    Append(~D, p - b + 1);
	    b := p + 1;
	    l := 0;
	end if;
	p +:= 1;
    end while;

    return D;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////
