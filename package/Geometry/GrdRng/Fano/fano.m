freeze;
 
///////////////////////////////////////////////////////////////////////
//			Fano 3-folds
// GB May 2002, Sept 2003
// Main formula due to Kaori Suzuki.
///////////////////////////////////////////////////////////////////////

import "../Generic/gr.m": num_print;
import "fanohilb.m": fano_Ac, fano_degree, fano_degree_g,
	fano_hilbert_series, fano_hilbert_series_g;

/*
A FANO THREEFOLD is a pair X,A where X is a Fano 3-fold with terminal
singularities and A is an ample divisor on X.
The datatype name is
	GRFano
which is a derived type of GRSch.

Data stored with X includes:
	// attributes inherited from GRSch
    genus	-- h^0(A) - 2 (an integer at least -2)
    basket	-- a sequence of singularities
    weights	-- weights of the ambient wps
    coeffs	-- a seq of the first few coeffs of the Hilbert series
    degree	-- A^3
    Ac		-- A*c_2(X)
    hilbert	-- the Hilbert series of X
    num		-- the Hilbert numerator of X
    dim		-- 3
	// attributes particular to GRFano
    fanoindex	-- the least f >= 1 st nK_X is Cartier
    fanogenus	-- some integer g (only in cases when f = 1,2)
*/

declare attributes GRFano: fanoindex, fanogenus, fanobasegenus;


///////////////////////////////////////////////////////////////////////
//                      Creation
///////////////////////////////////////////////////////////////////////

function FanoCreate(f,B)
    X := HackobjCreateRaw(GRFano);
    X`fanoindex := f;
    X`basket := B;
    X`dim := 3;
    return X;
end function;

function FanoCreateG(f,B,g,g_min)
    X := HackobjCreateRaw(GRFano);
    X`fanoindex := f;
    X`fanogenus := g;
    X`fanobasegenus := g_min;
    X`basket := B;
    X`dim := 3;
    return X;
end function;

intrinsic Fano(f::RngIntElt,B::GRBskt) -> GRFano
{}
    if f in {1,2} then
	require false:
	    "When f = 1 or 2 a third integer argument must also be given";
    else
	require f ge 3: "The first argument f must be >= 1";
    end if;
    require IsTerminalThreefold(B):
	"Basket must contain only terminal 3-fold singularities";
    require &and[ (f mod Index(p)) eq TerminalPolarisation(p)[1] :
	p in Points(B) ]: "Singularities are not properly polarised "
			* "for the given Fano index f =",f;
    X := FanoCreate(f,B);
    // compute the things that will go into it
    h,d,a := fano_hilbert_series(f,B);
    require d gt 0 : "Data determines a degree <= 0";
    X`hilbert := h;
    X`degree := d;
    X`Ac := a;
    return X;
end intrinsic;

forward base_genus;
intrinsic Fano(f::RngIntElt,B::GRBskt,g::RngIntElt) -> GRFano
{A Fano 3-fold of Fano index f >= 1 and with basket of singularities B
(and genus g >= 0 as additional argument when f is 1 or 2)}
    require f ge 1: "The first argument f must be >= 1";
    require IsTerminalThreefold(B):
	"Basket must contain only terminal 3-fold singularities";
    require &and[ (f mod Index(p)) eq TerminalPolarisation(p)[1] :
	p in Points(B) ]: "Singularities are not properly polarised "
			* "for the given Fano index f =",f;
    g_min := base_genus(f,B);
    require g ge g_min: "Third argument g must be >=",g_min;
    X := FanoCreateG(f,B,g,g_min);
    // h,d,a := fano_hilbert_series_g(g_min + g,f,B);
    h,d,a := fano_hilbert_series_g(g,f,B);
    require d gt 0 : "Data determines a degree <= 0";
    X`hilbert := h;
    X`degree := d;
    X`Ac := a;
    return X;
end intrinsic;

// The minimum value of the Fano genus g for which the triple (f,B,g)
// determine a positive Fano degree.
function base_genus(f,B)
    if not f in {1,2} then
	return 0;	// this value is irrelevant
    end if;
    // I could be smarter about this since the degree is linear in g.
    g := 0;
    if fano_degree_g(g,f,B) le 0 then
	repeat
	    g +:= 1;
	until fano_degree_g(g,f,B) gt 0;
    else
	repeat
	    glast := g;
	    g -:= 1;
	until fano_degree_g(g,f,B) le 0;
	g := glast;
    end if;
    return g;
end function;


///////////////////////////////////////////////////////////////////////
//              Printing for Fano 3-folds
///////////////////////////////////////////////////////////////////////

intrinsic HackobjPrintGRFano(X::GRFano,l::MonStgElt)
{Print the Fano 3-fold or singularity X}
// default printing
    f := FanoIndex(X);
    if f in {1,2} then
	printf "Fano 3-fold X,A of Fano index %o, Fano genus %o, " 
	    * "in codimension %o with data\n",f,FanoGenus(X),Codimension(X);
    else
	printf "Fano 3-fold X,A of Fano index %o in codimension %o with data\n",
				f,Codimension(X);
    end if;
    printf "  Weights: %o\n",Weights(X);
    printf "  Basket: %o\n",Basket(X);
    if IsBogomolovUnstable(X) then
    printf "  Degrees: A^3 = %o,\t(1/12)Ac_2(X) = %o\t(Bogomolov unstable)\n",
		Degree(X),Ac(X);
    else
	printf "  Degrees: A^3 = %o,\t(1/12)Ac_2(X) = %o\n",Degree(X),Ac(X);
    end if;
    printf "  Numerator: ";
    num_print(X);
end intrinsic;


///////////////////////////////////////////////////////////////////////
//                      Stability testing
//
// The Bogomolov inequality for a surface S is
//		c_1(S)^2 <= 3c_2(S).
//
// We apply this to the surface section A of X.
// This is trivial from the data we already hold:
//	c_1(X) = f*A so		A*c_1(X)^2 = f^2 * A^3
// and we already have (1/12)*A*c_2(X).
// So we compute A times the Bogomolov inequality on X.
//
///////////////////////////////////////////////////////////////////////

intrinsic IsBogomolovUnstable(X::GRFano) -> BoolElt
{True iff A * (c_1(X)^2 - 3*c_2(X)) > 0 for the Fano X}
    return BogomolovNumber(X) gt 0;
end intrinsic;

intrinsic BogomolovNumber(X::GRFano) -> RngInt
{The number A * (c_1(X)^2 - 3*c_2(X)) for the Fano X}
    return FanoIndex(X)^2*Degree(X) - 3*12*Ac(X);
end intrinsic;


///////////////////////////////////////////////////////////////////////
//                      Access functions
// These are mostly inherited from GRSch, but some are new and some
// I want to catch with a dedicated version here.
///////////////////////////////////////////////////////////////////////

intrinsic Degree(X::GRFano) -> FldRatElt
{}
    if not assigned X`degree then
	if FanoIndex(X) ge 3 then
	    X`degree := fano_degree(FanoIndex(X),Basket(X));
	else
	    X`degree := fano_degree_g(Genus(X),FanoIndex(X),Basket(X));
	end if;
    end if;
    return X`degree;
end intrinsic;

intrinsic Ac(X::GRFano) -> FldRatElt
{}
    if not assigned X`Ac then
	X`Ac := fano_Ac(FanoIndex(X),Basket(X));
    end if;
    return X`Ac;
end intrinsic;

intrinsic HilbertSeries(X::GRFano) -> FldFunRat
{}
    if not assigned X`hilbert then
	if FanoIndex(X) ge 3 then
	    h,deg,Ac := fano_hilbert_series(FanoIndex(X),Basket(X));
	    X`hilbert := h;
	    X`degree := deg;
	    X`Ac := Ac;
	else
	    h,deg,Ac := fano_hilbert_series_g(Genus(X),FanoIndex(X),Basket(X));
	    X`hilbert := h;
	    X`degree := deg;
	    X`Ac := Ac;
	end if;
    end if;
    return X`hilbert;
end intrinsic;

intrinsic Weights(X::GRFano) -> FldRatElt
{}
    if not assigned X`weights then
	h := HilbertSeries(X);
	W := FindFirstGenerators(h : Precision:=200);
	X`firstw := W;
	_,W := CheckBasket(Basket(X),W);
	Sort(~W);
	X`weights := W;
    end if;
    return X`weights;
end intrinsic;

intrinsic FanoIndex(X::GRFano) -> RngInt
{Fano index of the Fano 3-fold or point X, the least f such that fA is
Cartier, where A is the polarising divisor}
    return X`fanoindex;
end intrinsic;

intrinsic FanoGenus(X::GRFano) -> RngInt
{Fano genus of the Fano 3-fold or point X}
    if not assigned X`fanogenus then
	if FanoIndex(X) in {1,2} then
	    require false: "Fano genus data has not been set";
	else
	    X`fanogenus := 0;	// this value is completely unused.
	end if;
    end if;
    return X`fanogenus;
end intrinsic;

intrinsic FanoBaseGenus(X::GRFano) -> RngInt
{Fano base genus of the Fano 3-fold or point X}
    if not assigned X`fanobasegenus then
	if FanoIndex(X) in {1,2} then
	    X`fanobasegenus := base_genus(FanoIndex(X),Basket(X));
	else
	    X`fanobasegenus := 0;	// this value is completely unused.
	end if;
    end if;
    return X`fanobasegenus;
end intrinsic;

