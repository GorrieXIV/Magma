freeze;
 
///////////////////////////////////////////////////////////////////////
//              Polarised point singularities
// Gavin Brown
// September 2003, Sydney.
///////////////////////////////////////////////////////////////////////

/*
X,D is a polarised variety with D an ample (so QQ-Cartier) divisor:
    p in X denotes a point singularity polarised by D.
The datatype name for point singularities is
	GRPtS.
Point singularities are always cyclic quotient singularities.
Point singularities do not need to be isolated:  they may be
special (dissident) points on a curve of singularities.

Each p in X has some of the following properties (* marks compulsory fields)
	r	*- index
	n	*- local polarisation, i.e. eigenspace of D
	P	*- polarisation [a,b,...] (d terms)
	P1	-- principle polarisation:  characters relative to n = -1.
	C	-- contributions, a sequence of r rational numbers
	tP	-- P in order [f,a,r-a] when p is terminal 3-fold singularity

Typical cases
-------------
(1)  Isolated point: r,a,b,... coprime.
Often also have one of the following:
	-- d=2, a+b=r for DuVal surface singularity of type A_(r-1)
        -- a+b+c = r for 3-fold with crepant resolution
        -- a+b+c not= r but a+b = r (or other combination) for 3-fold terminal

(2)  Dissident point on a singular curve: s,a have common factor h.
In this case, the point must lie on a singular curve of Type h, i.e.
        Curve([h,b or c],d,t,N) where t is LCM(dissident indexes)/h.
*/

declare attributes GRPtS:
	r, n, P, P1, C, tP;


//////////////////////////////////////////////////////////////////////////////
//		Creation of point singularities
//////////////////////////////////////////////////////////////////////////////

function PointSingCreate(r,n,P,factor)
    p := HackobjCreateRaw(GRPtS);
    p`r := r;
    p`n := n;
    Pbar := [ Integers() | a mod r : a in P ];
    p`P := Pbar;
    if n eq -1 then
	p`P1 := Pbar;
    else
	p`P1 := [ Integers() | Integers(r) ! (a * factor) : a in Pbar ];
    end if;
    return p;
end function;

forward qs;
intrinsic Point(r::RngIntElt,n::RngIntElt,Q::SeqEnum) -> GRPtS
{}
    bool,factor := IsInvertible(Integers(r)!n);
    require bool: "Local polarisation n must be a unit modulo the index r";
    require IsComplete(Q) and #Q ne 0:
	"Q must be a complete sequence of positive length";
    ChangeUniverse(~Q,Integers());
    require qs([r] cat Q):
	"No integer k > 1 should divide all but one of the integer arguments";
    return PointSingCreate(r,n,Q,-factor);
end intrinsic;

intrinsic Point(r::RngIntElt,Q::SeqEnum) -> GRPtS
{The point (quotient) singularity (1/r(a,b,...))_n where Q is [a,b,...]
(and n = -1 if omitted)}
    require IsComplete(Q) and #Q ne 0:
	"Q must be a complete sequence of positive length";
    ChangeUniverse(~Q,Integers());
    require qs([r] cat Q):
	"No integer k > 1 should divide all but one of the integer arguments";
    return PointSingCreate(r,-1,Q,1);
end intrinsic;

function qs(Q)
    return &and [ GCD(Remove(Q,i)) eq 1 : i in [2..#Q] ];
end function;

///////////////////////////////////////////////////////////////////////
//                      Printing
///////////////////////////////////////////////////////////////////////

intrinsic HackobjPrintGRPtS(p::GRPtS,l::MonStgElt)
{Print the point singularity p}
	printf "1/%o(",Index(p);
	first := true;
	for a in Polarisation(p) do
	    case first:
		when true: first := false;
		when false: printf ",";
	    end case;
	    printf "%o",a;
	end for;
	n := Eigenspace(p);
	if n eq -1 then
	    printf ")";
	else
	    printf ")_[%o]",n;
	end if;
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//                      Access and comparison
//////////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(p::GRPtS,q::GRPtS) -> BoolElt
{True iff the point singularities p,q are equal}
    return Dimension(p) eq Dimension(q) and
		Index(p) eq Index(q) and
		Sort(Polarisation(p)) eq Sort(Polarisation(q)) and
		Eigenspace(p) eq Eigenspace(q);
end intrinsic;

intrinsic Dimension(p::GRPtS) -> RngIntElt
{Dimension of the variety on which the singularity p lies}
    return #Polarisation(p);
end intrinsic;

intrinsic Index(p::GRPtS) -> RngIntElt
{Index of the singularity p}
    return p`r;
end intrinsic;

intrinsic Polarisation(p::GRPtS) -> SeqEnum
{Polarisation sequence of the singularity p}
    return p`P;
end intrinsic;

intrinsic TerminalPolarisation(p::GRPtS) -> SeqEnum
{Polarisation sequence of the singularity p in the order [f,a,-a]}
    if not assigned p`tP then
	// IsTerminalThreefold assigns p`tP if true.
	require IsTerminalThreefold(p):
	    "Point must be a terminal 3-fold quotient singularity";
    end if;
    return p`tP;
end intrinsic;

intrinsic PrincipalPolarisation(p::GRPtS) -> SeqEnum
{Polarisation sequence of the singularity p when polarised in degree -1}
    return p`P1;
end intrinsic;

intrinsic Eigenspace(p::GRPtS) -> SeqEnum
{Eigenspace of polarising divisor of point singularity p}
    if not assigned p`n then
	p`n := -1;
    end if;
    return p`n;
end intrinsic;

intrinsic IsIsolated(p::GRPtS) -> BoolElt
{True iff the point singularity p is an isolated singularity}
    return &and[ GCD(Index(p),a) eq 1 : a in Polarisation(p) ];
end intrinsic;

intrinsic IsGorensteinSurface(p::GRPtS) -> BoolElt,RngIntElt
{True iff the point singularity p is a Gorenstein surface point}
    if Dimension(p) ne 2 or not IsIsolated(p) then
	return false;
    end if;
    P := Polarisation(p);
    return P[1] + P[2] eq Index(p);
end intrinsic;

intrinsic IsTerminalThreefold(p::GRPtS) -> BoolElt
{True iff the point singularity p is a terminal 3-fold point}
    if Dimension(p) ne 3 or not IsIsolated(p) then
	return false;
    end if;
    r := Index(p);
    P := Polarisation(p);
    if P[1] + P[2] eq r then
	if P[1] le P[2] then
	    p`tP := [P[3],P[1],P[2]];
	else
	    p`tP := [P[3],P[2],P[1]];
	end if;
	return true;
    elif P[1] + P[3] eq r then
	if P[1] le P[3] then
	    p`tP := [P[2],P[1],P[3]];
	else
	    p`tP := [P[2],P[3],P[1]];
	end if;
	return true;
    elif P[2] + P[3] eq r then
	if P[2] le P[3] then
	    p`tP := [P[1],P[2],P[3]];
	else
	    p`tP := [P[1],P[3],P[2]];
	end if;
	return true;
    end if;
    return false;
end intrinsic;

intrinsic IsCanonical(p::GRPtS) -> BoolElt
{True iff the point singularity p is canonical}
    return &+Polarisation(p) mod Index(p) eq 0;
end intrinsic;

intrinsic TerminalIndex(p::GRPtS) -> RngIntElt
{The index of the canonical class at p relative to the polarisation,
assuming p is terminal}
    bool := IsTerminalThreefold(p);
    require bool: "Argument must be a terminal 3-fold singularity";
    return TerminalPolarisation(p)[1];
end intrinsic;

