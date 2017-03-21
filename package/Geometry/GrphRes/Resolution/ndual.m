freeze;

///////////////////////////////////////////////////////////////////////
// ndual.m
//	Contents:
//		duality calculations
//		calculation of the resolved dual fan of a newton polygon
//		calculation of the mults of a polygon on a given fan
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
//		Duality
///////////////////////////////////////////////////////////////////////

/*
intrinsic IsOnDualRay(N::NwtnPgon,a::RngElt,b::RngElt) -> BoolElt
{True if and only if (a,b) lies on one of the dual rays of N}
    ison := false;
    F := Faces(N);
    for i in [2..#F-1] do
	if F[i][1] eq 0 then
	    if a eq 0 then
		return true;
	    else
		continue;
	    end if;
	end if;
        ratio := a/F[i][1];
        if F[i][2]*ratio eq b then
            ison := true;
            break;
        end if;
    end for;
    return ison;
end intrinsic;
*/ 

intrinsic DualFan(N::NwtnPgon) -> SeqEnum
{A sequence of primitive points on the rays of the dual fan to N}
    dualfan := [];
    //	THINK DEFUNCT	F := Faces(N);
    F := InnerFaces(N);
    nf := #F;
    dualfan[1] := <1,0>;
    for i in [1..nf] do
        //	THINK DEFUNCT	dualfan[i+1] := <F[i][1],F[i][2]>;
        dualfan[i+1] := GradientVector(F[i]);
    end for;
    dualfan[nf+2] := <0,1>;
    return dualfan;
end intrinsic;
 
det := function(v,w);
// calculate the determinant of the 2x2 matrix with first column v, second w
    return v[1]*w[2] - v[2]*w[1];
end function;
 
leftneighbour := function(v,F);
/* assuming that F is a sequence of vectors ordered anticlockwise, this
 * function returns the index of the element of F at or anticlockwise of v.
 * the default is 1.
 */
    nf := #F;
    for i in [1..nf] do
        w := F[i];
        if det(v,w) ge 0 then
            return i;
        end if;
    end for;
    return 1;
end function;
 
intrinsic Multiplicity(N::NwtnPgon,v::Tup) -> RngIntElt
{The minimum value among the dot products v.w where w is a vertex of N}
    return Minimum([ v[1]*w[1] + v[2]*w[2] : w in Vertices(N) ]);
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Resolved dual fans
///////////////////////////////////////////////////////////////////////

intrinsic ResolvedDualFan(N::NwtnPgon) -> SeqEnum
{The minimal resolution of the dual fan labelled by selfintersection
and multiplicity}
    F := DualFan(N);
    nr := #F - 1;
    RF := [];
    m1 := Multiplicity(N,< 1,0 >);
    m2 := Multiplicity(N,< 0,1 >);
    RF[1] := <1,0,0,m1>;	// RF will be the resolved fan; it is
    RF[2] := <0,1,0,m2>;	// built inductively from this initial version.
    nbl := 0;
    for i in [2..nr] do
        curay := F[i];
        done := false;
        while not done do
            /* find the rays currently adjacent to curay */
            cul := leftneighbour(curay,RF);
            if RF[cul][1] eq curay[1] and RF[cul][2] eq curay [2] then
                break;
            end if;
            cur := cul - 1;
            /* make the blowup */
            nbl +:= 1;
            RF[cul][3] -:= 1;
            RF[cur][3] -:= 1;
            newx := RF[cul][1] + RF[cur][1]; /* NB newx&y coprime by constr. */
            newy := RF[cul][2] + RF[cur][2];
            news := -1;
            newm := Multiplicity(N,< newx,newy >);
            newray := <newx,newy,news,newm>;
            Insert(~RF,cul,newray);
            if curay[1] eq newx and curay[2] eq newy then
                done := true;
            end if;
        end while;
    end for;
    return RF;
end intrinsic;

intrinsic Multiplicities(N::NwtnPgon,S::SeqEnum) -> SeqEnum
{If S represents a dual fan of some Newton polygon, return S with its
multiplicities adjusted to be those calculated with respect to N}
    Snew := [ Universe(S) | ];
    for i in [1..#S] do
	s := S[i];
	ray := < s[1],s[2] >;
	s[4] := Multiplicity(N,ray);
	Append(~Snew,s);
    end for;
    return Snew;
end intrinsic;

