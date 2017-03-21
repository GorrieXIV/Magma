freeze;

///////////////////////////////////////////////////////////////////////
// pt.m
// Code for creating special points
// GDB 13/11/00
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
//		Simple functions of points
///////////////////////////////////////////////////////////////////////

intrinsic Origin(A::Aff) -> Pt
{The origin of the affine space A}
    if Dimension(A) ge 1 then
	return A ! [ 0 : i in [1..Dimension(A)] ];
    else
	return A;
    end if;
end intrinsic;

intrinsic Simplex(P::Prj) -> SeqEnum
{The sequence of projective coordinate points (0,..,1,..0) and (1,..1)}
    require #Gradings(P) eq 1:
	"Argument must be a projective spaces with one grading";
    n := Dimension(P);
    zero := [ 0 : i in [1..n] ];
    one := [ 1 : i in [1..n+1] ];
    return [P!Insert(zero,i,1) : i in [1..n+1]] cat [P![1:i in [1..n+1]]];
end intrinsic;

intrinsic Minus(p::Pt) -> Pt
{The point whose coordinates are the negative of those of p}
    return Ambient(Scheme(p)) ! [ Universe(cp) | -a : a in cp ]
    			where cp is Coordinates(p);
end intrinsic;

intrinsic NonZeroCoordinates(p::Pt) -> SeqEnum,SeqEnum
{The nonzero coordinates of p as a sequence together with a sequence of the
indices of these coordinates}
    cp := Coordinates(p);
    np := #cp;
    coords := [ Universe(cp) | ];
    indices := [];
    number := 0;
    for i in [1..np] do
	if cp[i] ne 0 then
	    number +:= 1;
	    indices[number] := i;
	    coords[number] := cp[i];
	end if;
    end for;
    return coords,indices;
end intrinsic;

intrinsic ZeroCoordinates(p::Pt) -> SeqEnum
{The indices of the zero coordinates of p as a sequence}
    cp := Coordinates(p);
    np := #cp;
    indices := [];
    number := 0;
    for i in [1..np] do
	if cp[i] eq 0 then
	    number +:= 1;
	    indices[number] := i;
	end if;
    end for;
    return indices;
end intrinsic;

intrinsic AreCollinear(S::{Pt}) -> BoolElt
{True iff the points of S line on a line}
    require #S ge 1:
        "The set is empty";
    if #S eq 1 then
        return true;
    end if;
    S := SetToSequence(S);
    L := Line(Ambient(Scheme(S[1])),{S[1],S[2]});
    for p in S[3..#S] do
        if not p in L then
            return false;
        end if;
    end for;
    return true;
end intrinsic;

