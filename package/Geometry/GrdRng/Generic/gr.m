freeze;
 
///////////////////////////////////////////////////////////////////////
//		Polarised varieties --- the generic overtype
// GB Sept 2003 Sydney
///////////////////////////////////////////////////////////////////////

/*
A generic POLARISED VARIETY represents a pair X,A where X is some
variety is an ample divisor on X.  Such a pair X,A has an
associated graded ring R(X,A) = R/I, where R is a (positively)
graded polynomial ring and I is a homogeneous ideal.  This ring
R(X,A) is rarely created explicitly.  The usual Proj construction
then exhibits X embedded in a weighted projective space (wps)
		X = Proj R(X,A)  \subset  Proj R.
The datatype name is
	GRSch.
There are subtypes (types that are ISA GRSch) which carry more
detailed information about what kind of variety X is.

Data stored with X as attributes:
    dim		-- an integer
    genus	-- an integer (usually related to h^0(X,kA) for some k)
    twogenus	-- another integer (probably related to h^0(X,2kA))
    degree	-- a rational number A^n where n = dimension
    Ac		-- the rational number (1/12) * A * c_2(X) in RR
    basket	-- a basket of singularities of X
    rawbasket	-- the basket as a seq:  [ [5,1,2,3], [11,1,2,9] ], or similar.
    hilbert	-- the Hilbert series of X
    coeffs	-- a seq of the first few coeffs of the Hilbert series
    weights	-- weights of the ambient wps Proj R
    num		-- the Hilbert numerator of X w.r.t weights
    numseq	-- the coefficient sequence of the Hilbert numerator
    numinfo	-- numerical information about the numerator: eqn degs, etc.
    betti	-- betti numbers of the numerator (regarded as free resolution)
    firstw	-- a seq of weights assigned to X during its construction
    noetherw	-- a seq of noether weights
    noethern	-- the Hilbert numerator of X w.r.t noetherw
    noethernseq	-- the sequence of coefficients of the noether numerator
    ring	-- a graded ring representing X,A if one has been made.
    indexes	-- a sequence of <= 5 integers to be used in databases

Generic intrinsics that work on this type
    -- unload these attributes
    -- test for equality
    -- do default creation and printing (which might be never used)
    -- trivial coercion and 'in', as required for hackobj types
    -- add or remove of weights (changing only weights and numerator).

The point of numinfo, betti, noetherw, noethern is that large databases
work best if they store small pieces of information.  These three are enough
to give the hilbert series and the equation/syzygy degree information
that is usually required, preventing the need to store (or read, or 
calculate) thousands of very large numerators.
    betti = [ [(+)betti numbers], [equation degrees],
		    [syzygy degrees], [degree,#[betti numbers]] ]
where 'betti numbers' does not include the end (+/-)1s: thus
    num = -t^20 + t^14 + t^13 + t^12 + t^11 - t^9 - t^8 - t^7 - t^6 + 1
becomes
    betti = [ [4,4], [6,7,8,9], [11,12,13,14], [20,2] ].
Note that all integers are strictly positive.
*/

declare attributes GRSch:
    dim, genus, degree, Ac, basket, rawbasket, weights, hilbert,
    coeffs, num, numseq, ring, numinfo, betti, indexes,
    firstw, noetherw, noethern, noethernseq;


///////////////////////////////////////////////////////////////////////
//			Creation
///////////////////////////////////////////////////////////////////////

intrinsic PolarisedVariety(d::RngIntElt,W::SeqEnum,n::RngUPolElt) -> GRSch
{A generic polarised variety with dimension d, weights W, numerator n}
    require d ge 0: "First argument (dimension d) must be >= 0";
    require Type(Universe(W)) eq RngInt:
	"Second argument (weights W) must be a sequence of integers";
    require Type(CoefficientRing(Parent(n))) eq FldRat:
	"Third argument (numerator n) must have rational coefficients";
    X := HackobjCreateRaw(GRSch);
    X`dim := d;
    X`weights := Sort(W);
    X`num:= n;
    return X;
end intrinsic;

intrinsic PrintoutData(X::GRSch)
{Print all data assigned to polarised variety X}
    for att in GetAttributes(Type(X)) do
        if assigned X``att then
            printf "%o:\t%o\n",att,X``att;
	else
            printf "%o:\tunassigned\n",att;
        end if;
    end for;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//			Printing
///////////////////////////////////////////////////////////////////////

forward num_print;
intrinsic HackobjPrintGRSch(X::GRSch,l::MonStgElt)
{Print the generic polarised variety X}
    printf "Graded ring object of dimension %o with data\n",Dimension(X);
    printf "  Weights: %o\n",Weights(X);
    printf "  Numerator: "; num_print(X);
end intrinsic;

// Printing of numerator given only the numinfo data, b.
// This is used for derived types too.
procedure num_print(X)
    b := NumeratorData(X);
    // printing of degenerate (small) cases
    eqns := Reversion(Sort(ApparentEquationDegrees(X)));
    ChangeUniverse(~eqns,Integers());
	// e.g. eqns = [3,3,3,4,4,6] prints as - t^6 - 2*t^4 - 3*t^3 + 1
    if #eqns eq 0 then
	printf "1";
    elif #eqns eq 1 then
	printf "-t^%o + 1",b[3][1];
    elif #eqns eq 2 then
	if eqns[1] eq eqns[2] then
	    printf "t^%o - 2*t^%o + 1",b[3][1],eqns[1];
	else
	    printf "t^%o - t^%o - t^%o + 1",b[3][1],eqns[1],eqns[2];
	end if;
    else
	// organisation of big cases
	sorted := [ Integers() | 0 : i in [1..Maximum(eqns)] ];
	for d in eqns do
	    sorted[d] +:= 1;
	end for;
	// printing
	if IsOdd(Codimension(X)) then
	    printf "-t^%o + ... ",b[3][1];
	else
	    printf "t^%o - ... ",b[3][1];
	end if;
	// put in the last syzygy
	syzdegs := X`numinfo[2];
	syze := syzdegs[1];
	syzc := syzdegs[2];
	if syzc eq 1 then
	    printf "+ t^%o ",syze;
	else
	    printf "+ %o*t^%o ",syzc,syze;
	end if;
	for d in [#sorted..1 by -1] do
	    if sorted[d] ne 0 then
		if sorted[d] eq 1 then
		    printf "- t^%o ",d;
		else
		    printf "- %o*t^%o ",sorted[d],d;
		end if;
	    end if;
	end for;
	printf "+ 1";
    end if;
end procedure;


///////////////////////////////////////////////////////////////////////
//	Equality testing, hackobj formilites and other tests
///////////////////////////////////////////////////////////////////////

intrinsic 'eq'(X::GRSch,Y::GRSch) -> BoolElt
{True iff the polarised varieties X and Y have the same dimension,
weights, basket and numerator}
    return Dimension(X) eq Dimension(Y) and
	Weights(X) eq Weights(Y) and
	NumeratorSequence(X) eq NumeratorSequence(Y) and
	RawBasket(X) eq RawBasket(Y);
end intrinsic;

intrinsic CheckCodimension(X::GRSch) -> BoolElt
{True iff the codimension of X in PP(weights) is equal to the
apparent codimension of X determined by its Hilbert numerator}
    return Codimension(X) eq ApparentCodimension(X);
end intrinsic;

intrinsic HackobjCoerceGRSch(x::GRSch, y::.) -> BoolElt, .
{}
    return false;
end intrinsic

intrinsic HackobjInGRSch(x::., y::GRSch) -> BoolElt
{}
    return false;
end intrinsic


///////////////////////////////////////////////////////////////////////
//			Access functions
///////////////////////////////////////////////////////////////////////

intrinsic Degree(X::GRSch) -> FldRatElt
{Degree of the polarised variety (or derived type) X}
    require assigned X`degree: "degree data missing";
    // specific types can deduce degree from the genus and the basket
    return X`degree;
end intrinsic;

intrinsic Genus(X::GRSch) -> RngInt
{Genus of the polarised variety X}
    require assigned X`genus: "genus data missing";
    // specific types can deduce genus from the weights
    return X`genus;
end intrinsic;

intrinsic TwoGenus(X::GRSch) -> RngInt
{Second genus of the polarised variety X}
    require assigned X`twogenus: "2-genus data missing";
    // specific types can deduce genus from the weights
    return X`twogenus;
end intrinsic;

intrinsic Basket(X::GRSch) -> GRBskt
{Basket of the polarised variety (or derived type) X}
    if not assigned X`basket then
	require assigned X`rawbasket: "basket data missing";
	X`basket := MakeBasket(X`rawbasket);
    end if;
    return X`basket;
end intrinsic;

intrinsic RawBasket(X::GRSch) -> GRBskt
{Basket of the polarised variety (or derived type) X in raw 'sequence' format}
    if not assigned X`rawbasket then
	require assigned X`basket: "basket data missing";
	X`rawbasket := RawBasket(X`basket);
    end if;
    return X`rawbasket;
end intrinsic;

intrinsic SingularRank(X::GRSch) -> RngInt
{Singular rank of the polarised variety X}
    require assigned X`dim and X`dim eq 2:
	"The argument X must be 2 dimensional";
    return &+[ Index(p) - 1 : p in Points(Basket(X)) ];
end intrinsic;

intrinsic Weights(X::GRSch) -> SeqEnum
{Weights of the polarised variety (or derived type) X}
    if not assigned X`weights then
	// do not do 'CheckBasket' in this generic version.
	X`weights := FindFirstGenerators(HilbertSeries(X));
    end if;
    return X`weights;
end intrinsic;

intrinsic InitialCoefficients(X::GRSch) -> SeqEnum
{Initial coefficients of the Hilbert series of the polarised variety X}
    if not assigned X`coeffs then
	S := PowerSeriesRing(Rationals());
	coeffs := Coefficients( S ! HilbertSeries(X) );
	ChangeUniverse(~coeffs,Integers());
	X`coeffs := coeffs;
    end if;
    return X`coeffs;
end intrinsic;

intrinsic HilbertCoefficients(X::GRSch,n::RngIntElt) -> SeqEnum
{The first n coefficients of the Hilbert series (not including the
constant term) of the polarised variety X}
    if not assigned X`coeffs or #X`coeffs lt n then
	S := PowerSeriesRing(Rationals(),n+2);
	coeffs := Coefficients( S ! HilbertSeries(X) );
	ChangeUniverse(~coeffs,Integers());
	X`coeffs := coeffs;
    end if;
    return (X`coeffs)[2..n+1];
end intrinsic;

intrinsic P1(X::GRSch) -> RngIntElt
{The dimension of H^0(X,A) for a polarised variety X,A}
    return X`coeffs[2];
end intrinsic;

intrinsic P2(X::GRSch) -> RngIntElt
{The dimension of H^0(X,2A) for a polarised variety X,A}
    return X`coeffs[3];
end intrinsic;

intrinsic HilbertSeries(X::GRSch) -> FldFunRat
{Hilbert series of the polarised variety (or derived type) X}
    if not assigned X`hilbert then
        if assigned X`noetherw and assigned X`noethern then
            W := X`noetherw;
            n := X`noethern;
            t := Parent(n).1;
            X`hilbert := n / ( &*[ 1-t^a : a in W] );
	elif assigned X`weights and assigned X`num then
	    num := HilbertNumerator(X);
	    t := Parent(num).1;
	    X`hilbert := num / &*[ 1 - t^w : w in Weights(X) ];
	else
	    require false: "Not enough data to compute the Hilbert series";
	end if;
    end if;
    return X`hilbert;
end intrinsic;

intrinsic HilbertNumerator(X::GRSch) -> RngUPolElt
{Hilbert numerator of the polarised variety X}
    if not assigned X`num then
	if assigned X`numseq then
	    R := PolynomialRing(Rationals());
	    X`num := R ! X`numseq;
	else
	    h := HilbertSeries(X);
	    R := RingOfIntegers(Parent(h));
	    t := R.1;
	    num0 := h * &*[ 1 - t^w : w in Weights(X) ];
	    bool,num := IsCoercible(R,num0);
	    require bool:
		"Weights of X are inconsistent with its Hilbert series";
	    X`num := num;
	end if;
    end if;
    return X`num;
end intrinsic;

intrinsic Numerator(X::GRSch) -> RngUPolElt
{Hilbert numerator of the polarised variety X}
    if not assigned X`num then
	if assigned X`numseq then
	    R := PolynomialRing(Rationals());
	    X`num := R ! X`numseq;
	else
	    h := HilbertSeries(X);
	    R := RingOfIntegers(Parent(h));
	    t := R.1;
	    num0 := h * &*[ 1 - t^w : w in Weights(X) ];
	    bool,num := IsCoercible(R,num0);
	    require bool:
		"Weights of X are inconsistent with its Hilbert series";
	    X`num := num;
	    X`numseq := Eltseq(num);
	end if;
    end if;
    return X`num;
end intrinsic;

intrinsic NumeratorSequence(X::GRSch) -> SeqEnum
{Coefficient sequence of the Hilbert numerator of the polarised variety X}
    if not assigned X`numseq then
	if assigned X`num then
	    X`numseq := Eltseq(X`num);
	else
	    num := Numerator(X);
	    // this will set X`numseq
	end if;
    end if;
    return X`numseq;
end intrinsic;

forward find_noether_weights;
intrinsic NoetherWeights(X::GRSch) -> SeqEnum
{Noether weights for the polarised variety X (that is, weights of variables
of a Noether normalisation of X); if these are not assigned, an attempt to
calculate them will be made, but this will not necessarily succeed and
will end in an error if it fails}
    if not assigned X`noetherw then
	X`noetherw := find_noether_weights(X);
    end if;
    return X`noetherw;
end intrinsic;

intrinsic NoetherNumerator(X::GRSch) -> RngUPolElt
{Numerator of the polarised variety X w.r.t. its Noether weights}
    if not assigned X`noethern then
	if assigned X`noethernseq then
	    R := PolynomialRing(Rationals());
	    X`noethern := R ! X`noethernseq;
	else
	    X`noethern := HilbertNumerator(HilbertSeries(X),NoetherWeights(X));
	end if;
    end if;
    return X`noethern;
end intrinsic;

intrinsic NoetherNormalisation(X::GRSch) -> Tup
{Noether weights and numerator of the polarised variety X as elements
of a tuple}
    return <NoetherWeights(X),NoetherNumerator(X)>;
end intrinsic;

intrinsic FirstWeights(X::GRSch) -> SeqEnum
{These may be weights assigned to the polarised variety X during its
construction that carry some relevance; if no such weights were assigned,
the usual weights of X will be returned}
    if not assigned X`firstw then
	return X`weights;
    end if;
    return X`firstw;
end intrinsic;

intrinsic Dimension(X::GRSch) -> RngIntElt
{The codimension of the polarised variety X}
    require assigned X`dim: "dimension data missing";
    // specific subtypes simply assign this value with no calculation
    return X`dim;
end intrinsic;

intrinsic Codimension(X::GRSch) -> RngIntElt
{The codimension of the polarised variety X}
    return #Weights(X) - Dimension(X) - 1;
end intrinsic;

forward bettidata;
intrinsic BettiNumbers(X::GRSch) -> SetEnum
{The betti numbers of a free resolution of R(X,A), interpreted from
the Hilbert numerator of the polarised variety X,A}
    if not assigned X`betti then
	data := bettidata(HilbertNumerator(X));
	X`betti := data[1];
	X`numinfo := data[2..4];
    end if;
    return X`betti;
end intrinsic;

intrinsic NumeratorData(X::GRSch) -> SetEnum
{Numerical data regarding the Hilbert numerator of the polarised variety X,A}
    if not assigned X`numinfo then
	data := bettidata(HilbertNumerator(X));
	X`betti := data[1];
	X`numinfo := data[2..4];
    end if;
    return X`numinfo;
end intrinsic;

intrinsic ApparentCodimension(X::GRSch) -> RngIntElt
{The apparent number of terms in a free resolution of R(X,A), interpreted
from the Hilbert numerator of the polarised variety X,A}
    if assigned X`numinfo then
	return (X`numinfo)[3][2] + 1;
    elif assigned X`betti then
	return #(X`betti) + 1;
    else
	// have to force the calculation using the numerator.
	return #BettiNumbers(X) + 1;
    end if;
end intrinsic;

intrinsic ApparentEquationDegrees(X::GRSch) -> SeqEnum
{The apparent degrees of the equations of R(X,A), interpreted
from the Hilbert numerator of the polarised variety X,A}
    data := NumeratorData(X)[1];
    // report [ 3,2,4,3 ] as [ 3,3,4,4,4 ]
    N := Integers() ! (#data/2);
    return &cat [ [ data[2*i-1] : j in [1..data[2*i]]] : i in [1..N] ];
end intrinsic;

intrinsic ApparentSyzygyDegrees(X::GRSch) -> SeqEnum
{The apparent degrees of the syzygies of R(X,A), interpreted
from the Hilbert numerator of the polarised variety X,A}
    data := NumeratorData(X)[2];
    // report [ 3,2,4,3 ] as [ 3,3,4,4,4 ]
    N := Integers() ! (#data/2);
    return &cat [ [ data[2*i-1] : j in [1..data[2*i]]] : i in [1..N] ];
end intrinsic;

function bettidata(f)
    hnbn := HilbertNumeratorBettiNumbers(f);
    betti1 := [ AbsoluteValue(&+[a[2]:a in b]) : b in hnbn[2..#hnbn-1] ];
    // record [ 5,6,6,6,7,7 ] as [5,1,6,3,7,2]
    aed := [ Integers() | ];
    for a in Sort(ApparentEquationDegrees(f)) do
	N := #aed;
	if IsEven(N) then
	    // this is the first occurance of a
	    Append(~aed,a);
	    count := 1;
	else
	    if a eq aed[N] then
		count +:= 1;
	    else
		Append(~aed,count);
		Append(~aed,a);
		count := 1;
	    end if;
	end if;
    end for;
    if IsOdd(#aed) then
	Append(~aed,count);
    end if;
    asd := [ Integers() | ];
    for a in Sort(ApparentSyzygyDegrees(f)) do
	N := #asd;
	if IsEven(N) then
	    // this is the first occurance of a
	    Append(~asd,a);
	    count := 1;
	else
	    if a eq asd[N] then
		count +:= 1;
	    else
		Append(~asd,count);
		Append(~asd,a);
		count := 1;
	    end if;
	end if;
    end for;
    if IsOdd(#asd) then
	Append(~asd,count);
    end if;
    return [ betti1, aed, asd, [Degree(f), #betti1] ];
end function;


/////////////////////////////////////////////////////////////////////
//			Generic modification
// Derived types need their own functional versions to get the
// type of the copy right.
/////////////////////////////////////////////////////////////////////

intrinsic IncludeWeight(~X::GRSch,w::RngIntElt)
{Include the weight w > 0 to the weights of polarised variety X}
    require w gt 0: "Argument w must be > 0";
    X`weights := Sort(Weights(X) cat [w]);
    num := Numerator(X);
    t := Parent(num).1;
    X`num := num * (1-t^w);
    delete X`numinfo;
    delete X`numseq;
    delete X`betti;
end intrinsic;

intrinsic RemoveWeight(~X::GRSch,w::RngIntElt)
{Remove the weight w from the weights of polarised variety X if possible}
    // first check that it is sensible to remove w:
    //	 1. is it a weight;  2. does the numerator remain polynomial.
    W := Weights(X);
    i := Index(W,w);
    require i gt 0: "Second argument is not a weight";
    Wnew := Remove(W,i);
    num := Numerator(X);
    R := Parent(num);
    bool,numnew := IsCoercible(R, num / (1 - (R.1)^w) );
    require bool: "The proposed weight cannot be removed";
    X`weights := Wnew;
    X`num := numnew;
    delete X`numinfo;
    delete X`numseq;
    delete X`betti;
end intrinsic;

forward reduce;
intrinsic MinimiseWeights(~X::GRSch)
{Remove weights from X so that the degree equation of smallest degree is
not that of a weight:  beware that this does not consider the basket
so may well make a ring that is too small}
    W := Weights(X);
    Wnew,removed := reduce(W,HilbertSeries(X));
    numnew := num div &*[ 1 - (R.1)^w : w in removed ]	// i know this divides
	where R is Parent(num)
	where num is Numerator(X);
    X`weights := Wnew;
    X`num := numnew;
end intrinsic;

forward leading_eqn;
function reduce(D,h)
    R := RingOfIntegers(Parent(h));
    t := R.1;
    done := false;
    removed := [ Integers() | ];
    repeat
        num := HilbertNumerator(h,D);
        d := leading_eqn(num);
        if d notin D then
            done := true;
        else
            bool,num1 := IsDivisibleBy(num,1-t^d);
            if bool then
		Append(~removed,d);
                Remove(~D,Index(D,d));
            else
                done := true;
            end if;
        end if;
    until done;
    return D,removed;
end function;

function leading_eqn(f)
    d := 1;
    while Coefficient(f,d) eq 0 do
        d +:= 1;
    end while;
    return d;
end function;


/////////////////////////////////////////////////////////////////////
//	Auxilliary functions (including noether weights)
/////////////////////////////////////////////////////////////////////

/*
two examples.  there are choices to be made, but I see no need
to try to make a brilliantly optimal choice.

=====================================================================
example 1: X is 
Codimension 4 K3 surface, number 250, Altinok4(79), with data
  Weights: [ 2, 3, 5, 5, 7, 12, 17 ]
  Numerator: t^51 - t^41 - t^39 - t^37 - t^36 + t^29 + t^27 + t^26 + t^25
     + t^24 + t^22 - t^15 - t^14 - t^12 - t^10 + 1
  Basket: [ 17, 5 ]

> h := HilbertSeries(X);

> h*&*[1-t^a:a in [2,6,17]];
t^25 + t^22 + 2*t^20 + t^18 + 2*t^17 + 3*t^15 + 2*t^13 + 2*t^12 + 3*t^10
+ 2*t^8 + t^7 + 2*t^5 + t^3 + 1

> h*&*[1-t^a:a in [2,3,17]];
t^22 + 2*t^17 + t^15 + 2*t^12 + 2*t^10 + t^7 + 2*t^5 + 1

=====================================================================
example 2: X is 
Codimension 1 K3 surface, number 41, Reid1(33), with data
  Weights: [ 2, 3, 5, 7 ]
  Numerator: -t^17 + 1
  Basket: [ 2, 1 ], [ 3, 1 ], [ 5, 2 ], [ 7, 2 ]

> h:=HilbertSeries(X);

> h*&*[1-t^a:a in [5,6,7]];
t^18 + t^16 + t^15 + t^14 + t^13 + t^12 + t^11 + t^10 + t^9 + t^8 + t^7
+ t^6 + t^5 + t^4 + t^3 + t^2 + 1
*/

forward primary_factors, is_noether, can_find_3weights, can_find_3weights1,
can_find_4weights, can_find_4weights1;
function find_noether_weights(X)
    case Dimension(X):
    when 2:
	// First attempt:  use 3 small weights s.t. all primary factors
	// are visible.  Rather than using all the weights, just try the
	// 'first' weights.
	W := FirstWeights(X);
	h := HilbertSeries(X);
	bool,result := can_find_3weights(h,W);
	if bool then
	    return result;
	end if;
	// ok, that failed.  we are probably in a case like
	//   Weights: [ 2, 3, 5, 7 ]
	//   Basket: 1/2(1,1), 1/3(1,2), 1/5(2,3), 1/7(2,5)
	// which really wants [5,6,7] rather than a trio from the weights.
	// repeat the previous brainless game, but add some product of
	// the indices of the singularities at the beginning of the weights.
	B := Points(Basket(X));
	indices := [ Integers() | i : i in { Integers() | Index(p) : p in B } ];
	pf := primary_factors(indices);
	if #pf ge 2 then
	    W1 := [ pf[1]*pf[2] ] cat W;
	    bool,result := can_find_3weights1(h,W1);
	    if bool then
		return result;
	    end if;
	end if;
	// ok, i will try a ridiculous thing:  use all products of
	// primary factors and all weights.
	prods := SetToSequence({ pf[i]*pf[j] : j in [i+1..#pf], i in [1..#pf]});
	W2 := Sort(prods cat W);
	bool,result := can_find_3weights(h,W2);
	if bool then
	    return result;
	end if;
	error if true, "All my tricks to find the Noether weights failed; "*
	    "best to figure this one out yourself and assign the result " *
	    "to X`noetherw";

    when 3:
	// First attempt:  use 4 small weights s.t. all primary factors
	// are visible.  Rather than using all the weights, just try the
	// 'first' weights.
	W := FirstWeights(X);
	h := HilbertSeries(X);
	bool,result := can_find_4weights(h,W);
	if bool then
	    return result;
	end if;
	// try again, including all singularity indexes.
	bool,result := can_find_4weights(h,
		W cat [ Index(p) : p in Points(Basket(X))]);
	if bool then
	    return result;
	end if;
	// ok, that failed.
	// repeat the previous brainless game, but add some product of
	// the indices of the singularities at the beginning of the weights.
	B := Points(Basket(X));
	indices := [ Integers() | i : i in { Integers() | Index(p) : p in B } ];
	pf := primary_factors(indices);
	if #pf ge 2 then
	    W1 := [ pf[1]*pf[2] ] cat W;
	    bool,result := can_find_4weights1(h,W1);
	    if bool then
		return result;
	    end if;
	end if;
	// ok, i will try a ridiculous thing:  use all products of
	// primary factors and all weights.
	prods := SetToSequence({ pf[i]*pf[j] : j in [i+1..#pf], i in [1..#pf]});
	W2 := Sort(prods cat W);
	bool,result := can_find_4weights(h,W2);
	if bool then
	    return result;
	end if;
	error if true, "All my tricks to find the Noether weights failed; "*
	    "best to figure this one out yourself and assign the result " *
	    "to X`noetherw";
    end case;
end function;

function can_find_3weights(h,W)
    for i in [1..#W] do
        for j in [i+1..#W] do
            for k in [j+1..#W] do
                attempt := [W[i],W[j],W[k]];
                if is_noether(h,attempt) then
                    return true,attempt;
                end if;
            end for;
        end for;
    end for;
    return false,_;
end function;

function can_find_3weights1(h,W)
// same as above, but fixing i = 1
    for j in [1..#W] do
	for k in [j+1..#W] do
	    attempt := [W[1],W[j],W[k]];
	    if is_noether(h,attempt) then
		return true,attempt;
	    end if;
	end for;
    end for;
    return false,_;
end function;

function can_find_4weights(h,W)
    for i in [1..#W] do
        for j in [i+1..#W] do
            for k in [j+1..#W] do
		for l in [k+1..#W] do
		    attempt := [W[i],W[j],W[k],W[l]];
		    if is_noether(h,attempt) then
			return true,attempt;
		    end if;
		end for;
            end for;
        end for;
    end for;
    return false,_;
end function;

function can_find_4weights1(h,W)
// same as above, but fixing i = 1
    for j in [1..#W] do
	for k in [j+1..#W] do
	    for l in [k+1..#W] do
		attempt := [W[1],W[j],W[k],W[l]];
		if is_noether(h,attempt) then
		    return true,attempt;
		end if;
	    end for;
	end for;
    end for;
    return false,_;
end function;

// h a rational function, W some weights.
// return true iff numerator of h w.r.t. W is poly with positive coefficients.
function is_noether(h,W)
    bool,num := IsHilbertNumerator(h,W);
    if bool then
        // check whether num has only positive coefficients
        pos := &and [ x ge 0 : x in Coefficients(num) ];
        if pos then
            return true;
        end if;
    end if;
    return false;
end function;

// Q is a sequence of integers.
// return a seq ctg the biggest factor p^n that appears (as a factor) anywhere
// in Q, for each prime p that occurs anywhere in Q (as a factor).
function primary_factors(Q)
    primaries := Sort( &cat [
        [ Integers() | x[1]^x[2] : x in Factorization(a) ] : a in Q ] );
    result := [ Integers() | ];
    N := #primaries;
    for i in [1..N] do
        f := primaries[i];
        if not &or [ IsDivisibleBy(g,f) : g in primaries[i+1..N] ] then
            Append(~result,f);
        end if;;
    end for;
    return result;
end function;

