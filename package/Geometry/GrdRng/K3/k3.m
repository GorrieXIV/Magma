freeze;
 
///////////////////////////////////////////////////////////////////////
//			K3 surfaces
// GB Sept 2003
///////////////////////////////////////////////////////////////////////

import "../Generic/gr.m": num_print;
import "AFR.m": get_AFR;

/*
A K3 surface is a pair X,A where X is a K3 surface with cyclic quotient
Du Val singularities and A is an ample divisor on X.
The datatype name is
	GRK3
with is a derived type of GRSch.

Data stored with X:
	// inherited from GRSch
    dim		-- 2
    genus	-- h^0(A) - 1 (an integer at least -1, the genus of curve (x=0))
    twogenus	-- h^0(2A) - 1 (same, genus of curve (y=0), where weight(y)=2)
    basket	-- a sequence of singularities
    rawbasket	-- the basket in abbreviated form [ [r,a], ... ]
    weights	-- weights of the ambient wps
    coeffs	-- a seq of the first few coeffs of the Hilbert series
    degree	-- A^2
    hilbert	-- the Hilbert series of X
    num		-- the Hilbert numerator of X
    numinfo	-- [ [eqn degs], [syz degs], [deg(num), #betti numbers] ]
    betti	-- the betti numbers of num (ignoring first and last +/- 1
	// additional (used mainly when X appears in a database)
    afr		-- the number of X in the Altinok--Fletcher--Reid lists
    base	-- weights of the base of h'ell or ell structure (not used)
    number	-- the index of X in the db
    proj	-- seq of data about proj's of X in the db
    unproj	-- seq of data about unproj's of X in the db

A projection p (X -> Y) is a tuple
	< number of Y, codim of Y, centre on X, type of p, subtype of p >
An unprojection q (X <- Y) is a tuple
	< number of Y, codim of Y, centre on Y, type of q, subtype of q >
*/

declare attributes GRK3:
	afr, base, number, proj, unproj;


/////////////////////////////////////////////////////////////////////
//			Basic RR formulas
/////////////////////////////////////////////////////////////////////

function k3_degree(g,B)
    Bnew := [];
    for b in B do
        r := b[1];
        a := b[2];
        Append(~Bnew,[r, Integers() ! (Integers(r) ! (1/a))] );
    end for;
    B := Bnew;
    if #B eq 0 then
        return 2*g - 2;
    else
        return 2*g - 2 + &+[ a*(r-a)/r where r is b[1] where a is b[2] :b in B];
    end if;
end function;

function k3_hilbert_series(g,B)
    K := RationalFunctionField(Rationals());
    t := K.1;
    d := k3_degree(g,B);
    Bnew := [];
    for b in B do
        r := b[1];
        a := b[2];
        Append(~Bnew,[r, Integers() ! (Integers(r) ! (1/a))] );
    end for;
    B := Bnew;
    // The expression below is RR for a K3: the plurigenus formula in fact.
    h0 := (1+t)/(1-t) + (t+t^2)/(1-t)^3*d/2;
    if #B eq 0 then
        return h0;
    else
        return h0 -&+extra where extra is
            [ K | 1/(1-t^r)*1/(2*r)*
                &+[ (a*k mod r)*(r - (a*k mod r))*t^k : k in [1..r-1] ]
                    where a is b[2]
                    where r is b[1] : b in B ];
    end if;
end function;


/////////////////////////////////////////////////////////////////////
//                      Creation
/////////////////////////////////////////////////////////////////////

function K3Create(genus,basket);
    X := HackobjCreateRaw(GRK3);
    X`genus := Integers() ! genus;
    if Type(basket) eq GRBskt then
	X`basket := basket;
    else
	X`rawbasket := basket;
    end if;
    X`dim := 2;
    return X;
end function;

intrinsic K3Surface(g::RngIntElt,B::GRBskt) -> GRK3
{}
    require g ge -1: "First argument g must be >= -1";
    require IsGorensteinSurface(B):
	"Basket B must contain only Gorenstein surface singularities";
    X := K3Create(g,B);
    d := Degree(X);
    require d gt 0: "Given <genus,basket> data has negative degree";
    h := HilbertSeries(X);
    X`hilbert := h;
    W := FindFirstGenerators(h : Precision:=200);
    _,W := CheckBasket(B,W);
    Sort(~W);
    X`weights := W;
    X`firstw := W;
    return X;
end intrinsic;

intrinsic K3Surface(g::RngIntElt,B::SeqEnum) -> GRK3
{A K3 surface with genus g and basket of singularities B (as a basket
type or in raw sequence format)}
    require g ge -1: "First argument g must be >= -1";
    d := k3_degree(g,B);
    require d gt 0: "Given <genus,basket> data has negative degree";
    X := K3Create(g,B);
    h := HilbertSeries(X);
    W := FindFirstGenerators(h : Precision:=200);
    _,W := CheckBasket(Basket(X),W);
    Sort(~W);
    X`weights := W;
    X`firstw := W;  // the weights may be altered later, but these remain fixed.
    return X;
end intrinsic;

intrinsic K3Copy(X::GRK3) -> GRK3
{A new K3 surface that is identical to X}
    Y := HackobjCreateRaw(GRK3);
    for att in GetAttributes(Type(X)) do
	if assigned X``att then
	    Y``att := X``att;
	end if;
    end for;
    return Y;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//                      Printing
///////////////////////////////////////////////////////////////////////

intrinsic HackobjPrintGRK3(X::GRK3,l::MonStgElt)
{Print the K3 surface X}
if l eq "Minimal" then
    W := Weights(X);
    if assigned X`number then
	printf "K3 surface (g=%o, no.%o) in P^%o(%o",
			Genus(X),Number(X),#W-1,W[1];
    else
	printf "K3 surface (g=%o) in P^%o(%o",Genus(X),#W-1,W[1];
    end if;
    for w in W[2..#W] do
	printf ",%o",w;
    end for;
    printf ")\n";
    printf "  Basket: %o\n",Basket(X);
    printf "  Numerator: ";
    num_print(X);
else
    if assigned X`number then
        printf "K3 surface no.%o, genus %o, in codimension %o with data\n",
                Number(X),Genus(X),Codimension(X);
    else
        printf "K3 surface in codimension %o with data\n",
                Codimension(X);
    end if;
    printf "  Weights: %o\n",Weights(X);
    printf "  Basket: %o\n",Basket(X);
    printf "  Degree: %o\t\tSingular rank: %o\n",Degree(X),SingularRank(X);
    printf "  Numerator: ";
    num_print(X);

    // print the projection/unprojection information if X is part of the k3db
    if assigned X`number then	// I presume that proj/unprojection data is set
	proj := ProjectionIndices(X);
	PT := [ "[?]", "I", "II", "III", "IV" ];	// names of proj types
	if #proj gt 0 then
	    cents := ProjectionCentres(X);
	    cods := ProjectionCodimensions(X);
	    types := ProjectionTypes(X);
	    subtypes := ProjectionSubtypes(X);
	    for i in [1..#proj] do
		if subtypes[i] ne 0 then
		    // get spacing right
  printf "\n  Projection to codim %o K3 no.%o -- type %o_%o from %o",
			    cods[i],proj[i],PT[1+types[i]],subtypes[i],cents[i];
		else
	    printf "\n  Projection to codim %o K3 no.%o -- type %o from %o",
			    cods[i],proj[i],PT[1+types[i]],cents[i];
		end if;
	    end for;
	end if;
	unproj := UnprojectionIndices(X);
	if #unproj gt 0 then
	    cents := UnprojectionCentres(X);
	    cods := UnprojectionCodimensions(X);
	    types := UnprojectionTypes(X);
	    subtypes := UnprojectionSubtypes(X);
	    for i in [1..#unproj] do
		if subtypes[i] ne 0 then
    printf "\n  Unproj'n from codim %o K3 no.%o -- type %o_%o from %o",
			cods[i],unproj[i],PT[1+types[i]],subtypes[i],cents[i];
		else
	printf "\n  Unproj'n from codim %o K3 no.%o -- type %o from %o",
			    cods[i],unproj[i],PT[1+types[i]],cents[i];
		end if;
	    end for;
	end if;
    end if;
end if;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//                      Access functions
// These are mostly inherited from GRSch.
// Versions are included here in cases where the value may not be
// set for a K3 surface, but could be calculated from other attributes.
///////////////////////////////////////////////////////////////////////

intrinsic Degree(X::GRK3) -> FldRatElt
{}
    if not assigned X`degree then
	X`degree := k3_degree(Genus(X),RawBasket(X));
    end if;
    return X`degree;
end intrinsic;

intrinsic HilbertSeries(X::GRK3) -> FldFunRatUElt
{}
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
	    X`hilbert := k3_hilbert_series(Genus(X),RawBasket(X));
	end if;
    end if;
    return X`hilbert;
end intrinsic;

intrinsic Genus(X::GRK3) -> FldRatElt
{Genus of the K3 surface X, the genus of a generic degree 1 section of X}
    if not assigned X`genus then
	X`genus := #[w:w in Weights(X)|w eq 1] - 1;
    end if;
    return X`genus;
end intrinsic;

intrinsic TwoGenus(X::GRK3) -> FldRatElt
{Two genus of the K3 surface X, the genus of a generic degree 2 section of X}
    if not assigned X`twogenus then
	n1 := #[w:w in Weights(X)|w eq 1];
	n2 := #[w:w in Weights(X)|w eq 2];
	X`twogenus := Binomial(n1,2) + n2 - 1;
    end if;
    return X`twogenus;
end intrinsic;

intrinsic SingularRank(X::GRK3) -> RngInt
{Singular rank of the K3 surface X, that is the sum of r - 1 for 1/r(a,b)
in the basket of X}
    return &+[ Integers() | p[1] - 1 : p in RawBasket(X) ];
end intrinsic;

intrinsic AFRNumber(X::GRK3) -> RngInt
{The number of the K3 surface X in the Altinok--Fletcher--Reid lists;
0 is returned if X is not on those lists}
    if not assigned X`afr then
	X`afr := get_AFR(Weights(X),RawBasket(X));
    end if;
    return X`afr;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Access intrinsics for X in a database
//
// A projection p (X -> Y) is a tuple
//	< number of Y, codim of Y, centre on X, type of p >
// An unprojection q (X <- Y) is a tuple
//	< number of Y, codim of Y, centre on Y, type of q >
///////////////////////////////////////////////////////////////////////

intrinsic Number(X::GRK3) -> RngInt
{The index of the K3 surface X if it comes from a K3 database}
    require assigned X`number: "Argument is not part of a database";
    return X`number;
end intrinsic;

intrinsic Projections(X::GRK3) -> SeqEnum
{}
    require assigned X`proj: "Argument is not part of a database";
    return X`proj;
end intrinsic;

intrinsic ProjectionIndices(X::GRK3) -> SeqEnum
{}
    require assigned X`proj: "Argument is not part of a database";
    return [ p[1] : p in X`proj ];
end intrinsic;

intrinsic ProjectionCodimensions(X::GRK3) -> SeqEnum
{}
    require assigned X`proj: "Argument is not part of a database";
    return [ p[2] : p in X`proj ];
end intrinsic;

intrinsic ProjectionCentres(X::GRK3) -> SeqEnum
{}
    require assigned X`proj: "Argument is not part of a database";
    return [ p[3] : p in X`proj ];
end intrinsic;

intrinsic ProjectionTypes(X::GRK3) -> SeqEnum
{}
    require assigned X`proj: "Argument is not part of a database";
    return [ p[4] : p in X`proj ];
end intrinsic;

intrinsic ProjectionSubtypes(X::GRK3) -> SeqEnum
{}
    require assigned X`proj: "Argument is not part of a database";
    st := [ Integers() | ];
    for p in X`proj do
	if #p eq 5 then
	    Append(~st,p[5]);
	else
	    Append(~st,0);
	end if;
    end for;
    return st;
end intrinsic;

intrinsic Unprojections(X::GRK3) -> SeqEnum
{}
    require assigned X`unproj: "Argument is not part of a database";
    return X`unproj;
end intrinsic;

intrinsic UnprojectionIndices(X::GRK3) -> SeqEnum
{}
    require assigned X`unproj: "Argument is not part of a database";
    return [ p[1] : p in X`unproj ];
end intrinsic;

intrinsic UnprojectionCodimensions(X::GRK3) -> SeqEnum
{}
    require assigned X`unproj: "Argument is not part of a database";
    return [ p[2] : p in X`unproj ];
end intrinsic;

intrinsic UnprojectionCentres(X::GRK3) -> SeqEnum
{}
    require assigned X`unproj: "Argument is not part of a database";
    return [ p[3] : p in X`unproj ];
end intrinsic;

intrinsic UnprojectionTypes(X::GRK3) -> SeqEnum
{}
    require assigned X`unproj: "Argument is not part of a database";
    return [ p[4] : p in X`unproj ];
end intrinsic;

intrinsic UnprojectionSubtypes(X::GRK3) -> SeqEnum
{}
    require assigned X`unproj: "Argument is not part of a database";
    st := [ Integers() | ];
    for p in X`unproj do
	if #p eq 5 then
	    Append(~st,p[5]);
	else
	    Append(~st,0);
	end if;
    end for;
    return st;
end intrinsic;


/////////////////////////////////////////////////////////////////////
//                      Modifying K3 surfaces
// Procedural versions are done generically --- functional version
// is here to make it easy to preserve the GRK3 type.
/////////////////////////////////////////////////////////////////////

intrinsic IncludeWeight(X::GRK3,w::RngIntElt) -> GRK3
{A new K3 surface with the same data as the K3 surface X but with the
weight w > 0 included among the weights}
    require w gt 0: "Argument w must be > 0";
    Y := K3Copy(X);
    Y`weights := Sort(Weights(Y) cat [w]);
    num := Numerator(Y);
    t := Parent(num).1;
    Y`num := num * (1-t^w);
    delete Y`numinfo;
    delete Y`numseq;
    delete Y`betti;
    return Y;
end intrinsic;

intrinsic RemoveWeight(X::GRK3,w::RngIntElt) -> GRK3
{A new K3 surface with the same data as the K3 surface X but with the
weight w > 0 removed from the weights if that is possible}
    // first check that it is sensible to remove w:
    //   1. is it a weight;  2. does the numerator remain polynomial.
    Y := K3Copy(X);
    W := Weights(Y);
    i := Index(W,w);
    require i gt 0: "Second argument is not a weight";
    Wnew := Remove(W,i);
    num := Numerator(Y);
    R := Parent(num);
    bool,numnew := IsCoercible(R, num / (1 - (R.1)^w) );
    require bool: "The proposed weight cannot be removed";
    Y`weights := Wnew;
    Y`num := numnew;
    delete Y`numinfo;
    delete Y`numseq;
    delete Y`betti;
    return Y;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//                      Auxilliary functions
// Example:  X in PP(4,5,6,6,7,8,9) -> Y_30 in PP(4,5,6,15)
// from the 1/6 singularity.  To confirm those weights inductively
// you must ignore the 15.  That 15 is an integral closure variable
// coming from the hyperelliptic structure on Y.
// In this case, we say that the base weights of Y are [4,5,6].
///////////////////////////////////////////////////////////////////////

/*
// this is NOT yet checked properly --- the lists of cases below
// are only thrown together at quick glance.  But it could be a
// useful idea in a later version.
forward find_base;
intrinsic BaseWeights(X::GRK3) -> SeqEnum
{The base weights of the K3 surface X}
    if not assigned X`base then
	X`base := find_base(Weights(X));
    end if;
    return X`base;
end intrinsic;

function find_base(W)
    if #W eq 4 then
	Sort(~W);
	bad3 := [
[ 7, 8, 9, 12 ], [ 4, 5, 7, 16 ], [ 5, 7, 8, 20 ], [ 2, 3, 8, 13 ],
[ 2, 3, 7, 12 ], [ 2, 3, 5, 10 ], [ 4, 6, 7, 17 ], [ 3, 4, 5, 12 ],
[ 2, 5, 6, 13 ], [ 4, 5, 6, 15 ], [ 2, 6, 7, 15 ], [ 2, 4, 5, 11 ],
[ 2, 3, 4, 9 ],  [ 1, 2, 4, 7 ],  [ 1, 3, 4, 8 ] ];
	bad2 := [
[ 3, 5, 11, 14 ], [ 3, 4, 10, 13 ], [ 2, 5, 9, 11 ],  [ 4, 5, 13, 22 ],
[ 2, 5, 14, 21 ], [ 3, 4, 14, 21 ], [ 2, 3, 10, 15 ], [ 1, 5, 12, 18 ],
[ 1, 6, 14, 21 ], [ 1, 4, 10, 15 ], [ 1, 3, 8, 12 ] ];
	if W in bad3 then
	    return W[1..3];
	elif W in bad2 then
	    return W[1..2];
	end if;
    else
	return W;
    end if;
end function;
*/

