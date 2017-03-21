freeze;

///////////////////////////////////////////////////////////////////////
// blowup.m
///////////////////////////////////////////////////////////////////////

function IsCoercibleMatrix(S,M) // -> BoolElt, Mtrx
    // True if and only if all entries of M are coercible
    // into S; in that case, also return 'S!M'
    bool := true;
    nc := NumberOfColumns(M);
    nr := NumberOfRows(M);
    newentries := [ S | ];
    for i in [1..nr] do
        for j in [1..nc] do
            iscoer,x := IsCoercible(S,M[i,j]);
            if not iscoer then
                bool := false;
                break i;
            end if;
            Append(~newentries,x);
        end for;
    end for;
    if bool then
        Mnew := Matrix(nc,newentries);
        return bool,Mnew;
    else
        return bool,_;
    end if;
end function;

intrinsic ToroidalAutomorphism(P::Prj,M::Mtrx) -> Map
{The birational automorphism of P determined by the matrix of natural
numbers M: the rows are the powers appearing in the images of the
coordinates}
    np := Length(P);
    R := CoordinateRing(P);
    // error checks
    coerced,M1 := IsCoercibleMatrix(Integers(),M);
    require coerced:
        "the entries of M must be coercible into the base ring of P.";
    for i in [1..np] do
	for j in [1..np] do
	    require M[i,j] ge 0:
		"M must contain only nonnegative integers.";
	end for;
    end for;
    require NumberOfColumns(M1) eq np:
	"M has the wrong number of columns.";
    require NumberOfRows(M1) eq np:
	"M has the wrong number of rows.";
    require Rank(M1) eq np:
	"M must have full rank.";
    // make the automorphism
    funs := [ R | ];
    for i in [1..np] do
	h := &*[ R.j^M[i,j] : j in [1..np] ];
	Append(~funs,h);
    end for;
    return map< P -> P | funs >;
end intrinsic;

