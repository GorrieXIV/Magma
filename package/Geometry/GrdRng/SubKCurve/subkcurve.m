freeze;
 
///////////////////////////////////////////////////////////////////////
//		Package for subcanonical curves
// Gavin Brown
// September 2003, Sydney.
///////////////////////////////////////////////////////////////////////

import "../HilbertSeries/first_gens.m": number_of_monos;
import "../HilbertSeries/hilb.m": nonzerocoeffs;

/*
A SUBCANONICAL CURVE is a pair C,D where C is a nonsingular curve
and D is an ample (integral) divisor on C, that is, D is a divisor
with deg(D) > 0.
The datatype name is
	GRCrvK
and it is a derived type of GRSch.  As such, it inherits the
following attributes:
	genus	-- genus of C
	degree	-- degree of D
	hilbert	-- Hilbert series of R
	coeffs	-- first 2g - 2 coefficients of h
	weights	-- weights of a possible ambient PP for C,D
	num	-- numerator of h w.r.t. W
	ring	-- the graded ring R(C,D) (if it is ever calculated).
We use RR to determine the Hilbert series h. Since vanishing of H^1(nD)
only takes effect once nd > 2g - 2 we also need to feed in a sequence of
the early coefficients 'coeffs' (often denoted 'V') of h.

There are no other attributes of this subtype.
*/


///////////////////////////////////////////////////////////////////////
//		Creation of a curve
// 3 functions:
//	-- basic creation function which makes no checks on the input data;
//	-- SubcanonicalCurve(g,d,V); fails with an error if data is bad;
//	-- IsSubcanonicalCurve(g,d,V); returns a boolean, with the
//	   subcanonical curve as a second value if the boolean is true.
///////////////////////////////////////////////////////////////////////

function SubKCrvCreate(g,d,V)
    C := HackobjCreateRaw(GRCrvK);
    C`dim := 1;
    C`genus := g;
    C`degree := d;
    C`coeffs := V;
    return C;
end function;

forward usedvars, serredual;
intrinsic SubcanonicalCurve(g::RngIntElt,d::RngIntElt,V::SeqEnum) -> GRCrvK
{The subcanonical curve C,D of genus g, degree d and initial Hilbert
series coefficients V.}

    bool,top := IsDivisibleBy(2*g - 2,d);
    require bool: "2*g - 2 must be divisible by d";
    case IsEven(top):
	when true:	half := Integers()! (top/2) + 1;
	when false:	half := Integers()! ((top+1)/2);
    end case;
    require #V ge half: "V must have length at least",half;

    // The next function takes the first first 'half' entries of V, replaces
    // the next 'half' with the required dual and destroys any others.
    V := serredual(V,g,d);

    // Make a raw curve
    C := SubKCrvCreate(g,d,V);
    
    // Compute other things
    p := HilbertPolynomialOfCurve(g,d);
    h := HilbertSeries(p,V);
    W := FindFirstGenerators(h);
    num := HilbertNumerator(h,W);
    betti := nonzerocoeffs(num);

    // rule out a known bad case: Adam Keenan's Lemma.
    // 1. can't have an irreducible poly in <= 2 vars
    // 2. if D = pt then the first equation must involve at least two
    // rational functions having exactly the expected pole
    // 3. it is no good if there is a common factor of every monomial of
    // appearing in some equation: we rule this out for the first equation
    Cworks := true;
    eqdeg1 := betti[2][1][1];
    if #[ w : w in W | w lt eqdeg1 ] le 2 then
        Cworks := false;
    elif d eq 1 and V[2] eq 1 then
        Cworks := number_of_monos(W[2..#W],eqdeg1) gt 1;
    end if;

    if Cworks then
	usedno,monono,hasfactor := usedvars(W,eqdeg1);
	Cworks and:= usedno ge 3 and monono ge 2 and not hasfactor;
    end if;
    require Cworks: "The data fails some necessary numerical tests";
    // THINK:  could have better error message here?

    // Assign everything we have computed
    C`hilbert := h;
    C`weights := W;
    C`num := num;
    return C;
end intrinsic;

intrinsic IsSubcanonicalCurve(g::RngIntElt,d::RngIntElt,V::SeqEnum)
	-> BoolElt,GRCrvK
{Return true if and only if the data g,d,V passes some basic checks that
there is a subcanonical curve C,D of genus g, degree d and initial Hilbert
series coefficients V. In that case, the second return value is such a curve.}
// Virtually the same as the SubcanonicalCurve(g,d,V) intrinsic.
    bool,top := IsDivisibleBy(2*g - 2,d);
    if not bool then
	return false,_;
    end if;
    case IsEven(top):
	when true:	half := Integers()! (top/2) + 1;
	when false:	half := Integers()! ((top+1)/2);
    end case;
    if #V lt half then
	return false,_;
    end if;
    V := serredual(V,g,d);
    C := SubKCrvCreate(g,d,V);
    p := HilbertPolynomialOfCurve(g,d);
    h := HilbertSeries(p,V);
    W := FindFirstGenerators(h);
    num := HilbertNumerator(h,W);
    betti := nonzerocoeffs(num);
    Cworks := true;
    eqdeg1 := betti[2][1][1];
    if #[ w : w in W | w lt eqdeg1 ] le 2 then
        Cworks := false;
    elif d eq 1 and V[2] eq 1 then
        Cworks := number_of_monos(W[2..#W],eqdeg1) gt 1;
    end if;
    if Cworks then
	usedno,monono,hasfactor := usedvars(W,eqdeg1);
	Cworks and:= usedno ge 3 and monono ge 2 and not hasfactor;
    end if;
    if not Cworks then
	return false,_;
    end if;
    C`hilbert := h;
    C`weights := W;
    C`num := num;
    return true,C;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Printing curves
///////////////////////////////////////////////////////////////////////

intrinsic HackobjPrintGRCrvK(C::GRCrvK,l::MonStgElt)
{Print the subcanonical curve C}
    g := Genus(C);
    d := Degree(C);
    fac := Integers() ! ((2*g-2)/d);
    W := Weights(C);
    codim := #W - 2;
    betti := BettiNumbers(C);
    eqdegs := ApparentEquationDegrees(C);
    syzdegs := ApparentSyzygyDegrees(C);
    printf "Subcanonical curve C,D of genus %o, K_C = %o*D," * 
    		" deg(D) = %o, codim = %o with\n",
    		g,fac,d,codim;
    printf "  Weights: %o\n",W;
    if codim le 4 and Codimension(C) eq ApparentCodimension(C) then
	printf "  Numerator: %o",HilbertNumerator(C);
    elif codim le 7 then
	printf "  Apparent format: %o x %o\t\timplied codim: %o\n",
    	    #eqdegs,#syzdegs,ApparentCodimension(C);
	printf "  Equations: %o\n",eqdegs;
	printf "  Syzygies: %o",syzdegs;
    end if;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Access functions
// These are mostly inherited from GRSch.
///////////////////////////////////////////////////////////////////////

intrinsic IsEffective(C::GRCrvK) -> BoolElt
{True iff the polarising divisor of the subcanonical curve C is effective}
    return InitialCoefficients(C)[2] ne 0;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Hilbert stuff
///////////////////////////////////////////////////////////////////////

intrinsic HilbertPolynomialOfCurve(g::RngIntElt,m::RngIntElt) -> RngUPolElt
{The Hilbert polynomial m*t + 1 - g of a divisor of degree m on a curve of
genus g}
    R := PolynomialRing(Rationals());
    AssignNames(~R,["t"]);
    return m*R.1 + 1 - g;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Auxilliary functions
///////////////////////////////////////////////////////////////////////

function usedvars(W,d)
    // the number of variables of W used to make monos of wt d, together
    // with the number of such monos.
    early_vars := [ w : w in W | w lt d ];
    RR := PolynomialRing(FiniteField(2),early_vars);
    monos := MonomialsOfWeightedDegree(RR,d);
    divis := [ [IsDivisibleBy(m,RR.i): m in monos] : i in [1..Rank(RR)] ];
    used := [ i : i in [1..Rank(RR)] | &or(divis[i]) ];
    return #used,#monos, &or[ &and(D) : D in divis ];
end function;

function serredual(Q,g,d)
// This takes the first first 'half' entries of Q, replaces the next
// 'half' with the required serre dual terms and destroys any others.
    bool,top := IsDivisibleBy(2*g - 2,d);
    if IsEven(top) then
	half := top div 2;
	for i in [half..top] do
	    Q[i+1] := (d*i + 1 - g) + Q[top-i+1];
	end for;
    else
	half := (top-1) div 2;
	for i in [half+1..top] do
	    Q[i+1] := (d*i + 1 - g) + Q[top-i+1];
	end for;
    end if;
    return Q[1..top+1];
end function;

