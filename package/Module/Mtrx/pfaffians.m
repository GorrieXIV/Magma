freeze;

//////////////////////////////////////////////////////////////////////////
//           Pfaffians - mch 08/06                                      //
//                                                                      //
//      Basic implementation of pfaffians functions.                    //
//////////////////////////////////////////////////////////////////////////

function pfaffian_gen(M)
    n := Nrows(M);

    // do special cases first
    if n eq 2 then return M[1,2]; end if;
    if n eq 4 then 
	return M[1,2]*M[3,4]-M[1,3]*M[2,4]+M[1,4]*M[2,3];
    end if;

    // do inductive row expansion along first row
    M1 := ExtractBlock(M,2,2,n-1,n-1);
    pf := &+[BaseRing(M)|((-1)^i)*M[1,i]*pfaffian_gen(
	RemoveRowColumn(M1,i-1,i-1)) : i in [2..n]|M[1,i] ne 0];
    return pf; 
end function;

intrinsic Pfaffian(M::Mtrx) -> RngElt
{Return the Pfaffian of anti-symmetric matrix M.} 

    n := Nrows(M);
    require (Ncols(M) eq n) and IsZero(M+Transpose(M)):
	"Argument must be an anti-symmetric matrix";

    if (n eq 0) or IsOdd(n) then
	return BaseRing(M)!0;
    else
	return pfaffian_gen(M);
    end if;

end intrinsic;

intrinsic Pfaffian(M::Mtrx, I::[RngIntElt]) -> RngElt
{Return the Pfaffian of anti-symmetric matrix M.} 

    require (Nrows(M) eq Ncols(M)) and IsZero(M + Transpose(M)):
        "Argument must be an anti-symmetric matrix";

    I := Sort(I);
    N := -AntisymmetricMatrix([M[i,j]: i in I, j in I | i lt j ]);
    return Pfaffian(N);
end intrinsic;

intrinsic Pfaffians(M::Mtrx, k::RngIntElt) -> SeqEnum
{Return the sequence of Pfaffians of all principal k-by-k minors of
anti-symmetric matrix M.} 

    n := Nrows(M);
    require (Ncols(M) eq n) and IsZero(M+Transpose(M)):
	"Argument must be an anti-symmetric matrix";
    require (k gt 0) and (k le n):
	"Second argument must be positive integer less than or",
	"equal to the number of rows of the first";

    if IsOdd(k) then
	r := BaseRing(M)!0;
	return [r : i in [1..Binomial(n,k)]];
    elif k eq n then
	return [pfaffian_gen(M)];
    else
	indset := Subsets({1..n},k);
	return [pfaffian_gen(Matrix([[(M[i])[j]:j in inds] : i in inds]))
		: inds in indset];

    end if;

end intrinsic;
