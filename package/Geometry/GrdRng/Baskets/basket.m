freeze;
 
///////////////////////////////////////////////////////////////////////
//              Baskets of 3-fold singularities
// Gavin Brown
// September 2003, Sydney.
///////////////////////////////////////////////////////////////////////

/*
A BASKET is a collection of singularity types that lie on
a polarised variety X,A.
The datatype name is
	GRBskt.

THINK: add compatability check between nonisolated point sings and curves?
*/

declare attributes GRBskt: points, curves;


//////////////////////////////////////////////////////////////////////////////
//			Creation of baskets
//////////////////////////////////////////////////////////////////////////////

function BasketCreate(P,C)
    B := HackobjCreateRaw(GRBskt);
    B`points := P;
    B`curves := C;
    return B;
end function;

intrinsic EmptyBasket() -> GRBskt
{}
    points := [PowerStructure(GRPtS)|];
    curves := [PowerStructure(GRCrvS)|];
    return Basket(points,curves);
end intrinsic;

intrinsic Basket(Q::SeqEnum) -> GRBskt
{}
    if #Q eq 0 then
	points := [PowerStructure(GRPtS)|];
	curves := [PowerStructure(GRCrvS)|];
    elif Universe(Q) cmpeq PowerStructure(GRPtS) then
	points := Q;
	curves := [PowerStructure(GRCrvS)|];
    elif Universe(Q) cmpeq PowerStructure(GRCrvS) then
	points := [PowerStructure(GRPtS)|];
	curves := Q;
    else
	require false: "Argument must contain singularities";
    end if;
    return Basket(points,curves);
end intrinsic;

intrinsic Basket(P::SeqEnum,Q::SeqEnum) -> GRBskt
{The basket of point and curve singularities, each listed in a sequence
(points first) or omitted altogether}
    if IsEmpty(P) then
	P := [PowerStructure(GRPtS)|];
    end if;
    if IsEmpty(Q) then
	Q := [PowerStructure(GRCrvS)|];
    end if;
    require Universe(P) cmpeq PowerStructure(GRPtS)
	and Universe(Q) cmpeq PowerStructure(GRCrvS):
	"First argument sequence must contain point singularities," *
	    "the second must contain curve singularities";
    if not IsEmpty(P) then
	d := Dimension(P[1]);
	require &and [ Dimension(q) eq d : q in P ] and
		&and [ Dimension(C) eq d : C in Q ]:
	    "Singularities must lie on varieties with a common dimension";
    elif not IsEmpty(Q) then
	d := Dimension(Q[1]);
	require &and [ Dimension(C) eq d : C in Q ]:
	    "Singularities must lie on varieties with a common dimension";
    end if;
    return BasketCreate(P,Q);
end intrinsic;

intrinsic MakeBasket(Q::SeqEnum) -> GRBskt
{Make a basket of point singularities from a sequence Q of sequences
in the form:  [r,a] for points 1/r(a,r-a) on surfaces; [r,a,b,c]
or similar in higher dimensions}
    Sort(~Q);
    newpts := [];
    if #Q eq 0 then
	return EmptyBasket();
    end if;
    N := #Q[1];
    require &and[ #q eq N : q in Q ]:
	"The sequences in the argument sequence must have a common length";
    if N eq 2 then
	for q in Q do
	    require GCD(q[1],q[2]) eq 1:
		"Argument must be a sequence of the form " *
			"[[r1,a1],[r2,a2],...] with ri,ai coprime integers";
	    r := q[1];
	    a := q[2] mod r;
	    if a gt (r/2) then
		Append(~newpts,Point(r,[r-a,a]));
	    else
		Append(~newpts,Point(r,[a,r-a]));
	    end if;
	end for;
    else
	for q in Q do
	    r := q[1];
	    Append(~newpts,Point(r,[q[i] mod r : i in [2..#q]]));
	end for;
    end if;
    return Basket(newpts);
end intrinsic;

intrinsic RawBasket(B::GRBskt) -> SeqEnum
{Return a sequence of raw data representing the point basket B}
    require #Curves(B) eq 0:
	"Argument must be a basket of points with no curves";
    if IsGorensteinSurface(B) then
	return [ [r, Minimum(a,r-a)]
			where r is Index(p)
			where a is Polarisation(p)[1] : p in Points(B) ];
    else
	return Sort([ [Index(p)] cat Polarisation(p) : p in Points(B) ]);
    end if;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//                      Printing
///////////////////////////////////////////////////////////////////////

forward print_pts;
intrinsic HackobjPrintGRBskt(B::GRBskt,l::MonStgElt)
{Print the singularity basket B}
    Bp := Points(B);
    Bc := Curves(B);
    if #Bp + #Bc eq 0 then
	printf "no singularities";
    elif #Bc eq 0 then
	print_pts(~Bp);
    elif #Bp eq 0 then
	for C in Bc do
	    // curves always get printed on a new line
	    printf "\n%o",C;
	end for;
    else
	print_pts(~Bp);
	for C in Bc do
	    printf "\n%o",C;
	end for;
    end if;
end intrinsic;

procedure print_pts(~Bp)
    Bdone := [];
    first := true;
    for i in [1..#Bp] do
	p := Bp[i];
	if &or[ p eq Bdone[j] : j in [1..#Bdone] ] then
	    continue i;
	end if;
	Append(~Bdone,p);
	if not first then
		printf ", ";
	end if;
	first := false;
	np := #[ q : q in Bp | p eq q ];
	if np ge 2 then
	    printf "%o x ",np;
	end if;
	printf "%o",p;
    end for;
end procedure;


//////////////////////////////////////////////////////////////////////////////
//                      Access and comparison
//////////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(B1::GRBskt,B2::GRBskt) -> BoolElt
{True iff the singularity baskets B1,B2 are equal}
    ptstemp := Points(B1);
    for p in Points(B2) do
	i := Index(ptstemp,p);
	if i eq 0 then
	    return false;
	end if;
	Remove(~ptstemp,i);
    end for;
    if #ptstemp ne 0 then
	return false;
    end if;
    cvstemp := Curves(B1);
    for C in Curves(B2) do
	i := Index(cvstemp,C);
	if i eq 0 then
	    return false;
	end if;
	Remove(~cvstemp,i);
    end for;
    if #cvstemp ne 0 then
	return false;
    end if;
    return true;
end intrinsic;

intrinsic Points(B::GRBskt) -> SeqEnum
{The point singularities of the basket B}
    return B`points;
end intrinsic;

intrinsic Curves(B::GRBskt) -> SeqEnum
{The curve singularities of the basket B}
    return B`curves;
end intrinsic;

intrinsic IsIsolated(B::GRBskt) -> BoolElt
{True iff all singularities of the basket B are isolated}
    return &and [ IsIsolated(p) : p in Points(B) ] and #Curves(B) eq 0;
end intrinsic;

intrinsic IsTerminalThreefold(B::GRBskt) -> BoolElt
{True iff all singularities of the basket B are terminal 3-fold points}
    return &and [ IsTerminalThreefold(p) : p in Points(B) ] and #Curves(B) eq 0;
end intrinsic;

intrinsic IsGorensteinSurface(B::GRBskt) -> BoolElt
{True iff all singularities of the basket B are Gorenstein surface points}
    return &and [ IsGorensteinSurface(p) : p in Points(B) ] and #Curves(B) eq 0;
end intrinsic;

intrinsic IsCanonical(B::GRBskt) -> BoolElt
{True iff all singularities of the basket B are canonical}
    return &and [ IsCanonical(p) : p in Points(B) ] and
		&and [ IsCanonical(C) : C in Curves(B) ];
end intrinsic;

intrinsic Dimension(B::GRBskt) -> BoolElt
{True iff all singularities of the basket B are canonical}
    return &and [ IsCanonical(p) : p in Points(B) ] and
		&and [ IsCanonical(C) : C in Curves(B) ];
end intrinsic;

intrinsic PointIndexes(B::GRBskt) -> SeqEnum
{The (ordered) sequence of indexes of point singularities of B}
    return Sort([Index(p):p in Points(B)]); 
end intrinsic;

