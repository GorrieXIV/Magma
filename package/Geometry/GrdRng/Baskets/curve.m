freeze;
 
///////////////////////////////////////////////////////////////////////
//              Polarised curve singularities
// Gavin Brown
// September 2003, Sydney.
///////////////////////////////////////////////////////////////////////

/*
X,D is a polarised variety with D an ample (so QQ-Cartier) divisor:
    C in X denotes a curve singularity polarised by D.
The datatype name is
	GRCrvS.
In this package, curve singularities have a fixed cyclic quotient
surface singularity as generic transverse section.
They may also have special (dissident) points on them that do not
have the same transverse type.

Each C in X has some of the following properties (* marks compulsory fields)
	d	*- degree
	p	*- transverse type (a point singularity)
	N	*- 'normal number' --- something to do with splitting of N_C
	t	*- the tau invariant = GCD([i/trans-index:pt of index i on C])
	magic	-- N/t, the thing that appears linearly in RR
	rrb	-- rr data
	rrc	-- rr data
	raw	-- if true then the curve does not have all necessary data
NOTE: for some purposes one only needs 'magic', so it might be worth
thinking about a version of this code that does not use N,t but rather magic.
Anyway, that's the reason that magic is kept on as a separate attribute.
Attributes x1,e are to do with N, but the formulas are not encoded here.
*/

declare attributes GRCrvS:
	d, p, x1, e, N, t, magic, raw, rrb, rrc;


//////////////////////////////////////////////////////////////////////////////
//		Creation of curve singularities
//////////////////////////////////////////////////////////////////////////////

function CurveSingCreate1(d,p,N,t)
    C := HackobjCreateRaw(GRCrvS);
    C`d := d;
    C`p := p;
    C`N := N;
    C`t := t;
    C`magic := N/t;
    return C;
end function;

function CurveSingCreate2(d,p,magic)
    C := HackobjCreateRaw(GRCrvS);
    C`d := d;
    C`p := p;
    C`magic := magic;
    return C;
end function;

function CurveSingCreate3(p)
    C := HackobjCreateRaw(GRCrvS);
    C`p := p;
    C`raw := true;
    return C;
end function;

intrinsic RawCurve(p::GRPtS) -> GRCrvS
{}
    require Dimension(p) eq 2:
	"Transverse generic singularity p must be a surface singularity";
    return CurveSingCreate3(p);
end intrinsic;

intrinsic Curve(d::FldRatElt,p::GRPtS,magic::FldRatElt) -> GRCrvS
{}
    require d gt 0: "Degree d must be > 0";
    require Dimension(p) eq 2:
	"Transverse generic singularity p must be a surface singularity";
    return CurveSingCreate2(d,p,magic);
end intrinsic;

intrinsic Curve(d::FldRatElt,p::GRPtS,N::RngIntElt) -> GRCrvS
{}
    require d gt 0: "Degree d must be > 0";
    require Dimension(p) eq 2:
	"Transverse generic singularity p must be a surface singularity";
    return CurveSingCreate1(d,p,N,1);
end intrinsic;

intrinsic Curve(d::FldRatElt,p::GRPtS,N::RngIntElt,t::RngIntElt) -> GRCrvS
{The 3-fold curve singularity C of degree d with transverse type
a point singularity p and invariants N_C = N, tau = t (magic = N/t;
t = 1 if omitted)}
    require d gt 0: "Degree d must be > 0";
    require Dimension(p) eq 2:
	"Transverse generic singularity p must be a surface singularity";
    C := CurveSingCreate1(d,p,N,t);
    return C;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//                      Printing
///////////////////////////////////////////////////////////////////////

intrinsic HackobjPrintGRCrvS(C::GRCrvS,l::MonStgElt)
{Print the curve singularity C}
    if IsRawCurve(C) then
	if assigned C`t then
	    printf "Raw curve with t = %o, transverse type %o",
			Index(C),TransverseType(C);
	else
	    printf "Raw curve with transverse type %o",TransverseType(C);
	end if;
    else
	if l eq "Minimal" then
	    printf "Curve of degree %o with transverse type %o",
		Degree(C),TransverseType(C);
	else
	    if assigned C`N and assigned C`t then
		printf
	    "Curve of degree %o, N = %o, t = %o with transverse type %o",
		    Degree(C),NormalNumber(C),Index(C),TransverseType(C);
	    elif assigned C`magic then
		printf "Curve of degree %o, N/t = %o with transverse type %o",
		    Degree(C),MagicNumber(C),TransverseType(C);
	    else
		printf "Curve of degree %o with transverse type %o",
		    Degree(C),TransverseType(C);
	    end if;
	end if;
    end if;
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//                      Access and comparison
//////////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(C::GRCrvS,D::GRCrvS) -> BoolElt
{True iff the curve singularities C,D are equal (as far as RR is concerned)}
    return Dimension(C) eq Dimension(D) and
		Degree(C) eq Degree(D) and
		TransverseType(C) eq TransverseType(D) and
		MagicNumber(C) eq MagicNumber(D);
end intrinsic;

intrinsic IsRawCurve(C::GRCrvS) -> BoolElt
{True iff C has essential data missing}
    if not assigned C`raw then
	return false;
    else
	return C`raw;
    end if;
end intrinsic;

intrinsic Degree(C::GRCrvS) -> RngIntElt
{Degree of the curve singularity C}
    return C`d;
end intrinsic;

intrinsic TransverseIndex(C::GRCrvS) -> RngIntElt
{Index of the generic tranverse section of the curve singularity C}
    return Index(C`p);
end intrinsic;

intrinsic TransverseType(C::GRCrvS) -> GRPtS
{Singularity that is the generic tranverse section of the curve singularity C}
    return C`p;
end intrinsic;

intrinsic NormalNumber(C::GRCrvS) -> RngIntElt
{Normal number N_C of the curve singularity C}
    return C`N;
end intrinsic;

intrinsic Index(C::GRCrvS) -> RngIntElt
{The index of the curve singularity C, that is, the invariant tau}
    return C`t;
end intrinsic;

intrinsic MagicNumber(C::GRCrvS) -> RngIntElt
{The rational number N/t of the curve singularity C, where N is the
normal number and t is the index of C}
    if not assigned C`magic then
	require assigned C`t: "Index of the curve is not assigned";
	require assigned C`N: "Normal number of the curve is not assigned";
	C`magic := C`N/C`t;
    end if;
    return C`magic;
end intrinsic;

intrinsic Dimension(C::GRCrvS) -> RngIntElt
{Dimension of the variety on which the singularity C lies}
    return Dimension(TransverseType(C)) + 1;
end intrinsic;

intrinsic IsIsolated(C::GRCrvS) -> BoolElt
{False for a curve singularity C}
    return false;
end intrinsic;

intrinsic IsTerminalThreefold(C::GRCrvS) -> BoolElt
{False for a curve singularity C}
    return false;
end intrinsic;

intrinsic IsCanonical(C::GRCrvS) -> BoolElt
{True iff the curve singularity C is canonical}
    return IsCanonical(TransverseType(C));
end intrinsic;

intrinsic FindIndexes(B::GRBskt) -> SeqEnum
{A sequence containing the possible values of the index tau for each curve of B}
    Bp := Points(B);
    Bc := Curves(B);
    inds := [ Parent([1,2]) | ];
    for C in Bc do
        indsC := [ Integers() | ];
        for p in Bp do
            r := TransverseIndex(C);
            a,b := IsDivisibleBy(Index(p),r);
            if a and r in Polarisation(p) then
                Append(~indsC,b);
            end if;
        end for;
        Append(~inds,indsC);
    end for;
    return inds;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Modifying a curve singularity
///////////////////////////////////////////////////////////////////////

intrinsic ChangeN(C::GRCrvS,N::RngIntElt) -> GRCrvS
{}
    Cnew := RawCurve(TransverseType(C));
    if assigned C`t then
	Cnew`t := C`t;
    end if;
    if assigned C`magic then
	Cnew`magic := C`magic * (N/C`N);
    end if;
    if assigned C`d then
	Cnew`d := C`d;
    end if;
    if assigned C`e then
	Cnew`e := C`e;
    end if;
    if assigned C`x1 then
	Cnew`x1 := C`x1;
    end if;
    if assigned C`raw then
	Cnew`raw := C`raw;
    else
	Cnew`raw := false;
    end if;
    Cnew`N := N;
    return Cnew;
end intrinsic;

intrinsic ChangeN(~C::GRCrvS,N::RngIntElt)
{Return (or modify C to be) a curve singularity that has the same data
as C except that its normal number is set to be N}
    if assigned C`magic then
	magic := C`magic;
	newmagic := magic * (N/C`N);
	C`magic := newmagic;
    end if;
    C`N := N;
end intrinsic;

intrinsic ChangeN(B::GRBskt,N::RngIntElt,i::RngIntElt) -> GRBskt
{}
    Bc := Curves(B);
    require i ge 1 and IsDefined(Bc,i): "Argument i must be the index " *
		"of a curve in the sequence of curves of the basket B";
    C := Bc[i];
    C1 := ChangeN(C,N);
    Bc[i] := C1;
    return Basket(Points(B),Bc);
end intrinsic;

intrinsic ChangeN(~B::GRBskt,N::RngIntElt,i::RngIntElt)
{Return (or modify B to be) a basket in which the i-th curve singularity 
has its normal number set to be N}
    Bc := Curves(B);
    require i ge 1 and IsDefined(Bc,i): "Argument i must be the index " *
		"of a curve in the sequence of curves of the basket B";
    C := Bc[i];
    C1 := ChangeN(C,N);
    Bc[i] := C1;
    B := Basket(Points(B),Bc);
end intrinsic;

