freeze;
 
///////////////////////////////////////////////////////////////////////
//			Calabi-Yaus
// GB Sept 2003
// Main formula due to Anita Buckley.
///////////////////////////////////////////////////////////////////////

import "cyhilb.m": buckley;

/*
A CALABI-YAU is a pair X,A where X is a Calabi-Yau 3-fold with isolated
canonical Gorenstein quotient singularities and equisingular curve
singularities and A is an ample divisor on X.
The datatype name is
	GRCY
which is a derived type of GRSch.

Standard notation:
	// attributes inherited from GRSch
    dim		-- 3
    coeffs	-- [1,p1,p2,...], where p1,p2 are H^0(X,A), H^0(X,2*A)
    basket	-- basket of singularities of X
    degree	-- A^3
    Ac		-- (1/12)*A*c_2
    hilbert	-- Hilbert series of R
    weights	-- weights of a possible ambient PP for X,A
    num		-- numerator of h w.r.t. W
    ring	-- the graded ring R(X,A) (if it is calculated, which is never)
*/

// Special intrinsic

intrinsic IsCalabiYauNumericalSeries(p1::RngIntElt,p2::RngIntElt,B::GRBskt)
		-> BoolElt
{True iff the Hilbert series formula of Buckley computes a series
with integral coefficients;  if so, the series is returned as a
second value}
    bool,h := buckley(p1,p2,B);
    if bool then
	return true,h;
    else
	return false,_;
    end if;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//			Creation
///////////////////////////////////////////////////////////////////////

function CYCreate0(B,V)
    X := HackobjCreateRaw(GRCY);
    X`dim := 3;
    ChangeUniverse(~V,Integers());
    X`coeffs := V;
    X`basket := B;
    error if #V le 1, "Must give at least the first 2 coefficients of "
		* "the proposed Hilbert series";
    bool,h := buckley(V[1],V[2],B);
    error if not bool, "This data does not produce an integral Hilbert series";
    X`hilbert := h;
    return X;
end function;

function CYCreate1(B,V)
    X := HackobjCreateRaw(GRCY);
    X`dim := 3;
    ChangeUniverse(~V,Integers());
    X`coeffs := V;
    X`basket := B;
    return X;
end function;

function CYCreate2(B,V,h,W)
// no check is made that the weights W are appropriate for the series h.
    X := HackobjCreateRaw(GRCY);
    X`dim := 3;
    ChangeUniverse(~V,Integers());
    X`coeffs := V;
    X`basket := B;
    X`hilbert := h;
    X`weights := W;
    return X;
end function;

intrinsic CalabiYau(p1::RngIntElt,p2::RngIntElt,B::GRBskt) -> GRCY
{A Calabi-Yau X,A with h^0(A) = p1, h^0(2A) = p2, basket of singularities B}
    require IsCanonical(B): "Singularities of the basket must be canonical";
    X := CYCreate1(B,[1,p1,p2]);
    bool,h := buckley(p1,p2,B);
    require bool: "This data does not produce an integral Hilbert series";
    X`hilbert := h;
    return X;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Printing
///////////////////////////////////////////////////////////////////////

intrinsic HackobjPrintGRCY(X::GRCY,l::MonStgElt)
{Print the Calabi--Yau 3-fold X}
    W := Weights(X);
    codim := #W - 4;
    betti := BettiNumbers(X);
    eqdegs := ApparentEquationDegrees(X);
    syzdegs := ApparentSyzygyDegrees(X);
    printf "Calabi-Yau 3-fold X,A in codimension %o with\n",codim;
    printf "  Weights: %o\n",W;
    printf "  Degrees: A^3 = %o,\t\tAc_2 = %o\n",Degree(X),Ac(X);

    // print the basket nicely
    Bp := Points(Basket(X));
    Bc := Curves(Basket(X));
    printf "  Basket: ";
    if #Bp + #Bc eq 0 then
	printf "no singularities\n";
    else
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
	if #Bc ne 0 then
	    printf "\n";
	end if;
	first := true;
	for C in Bc do
	    if not first then
		printf ",\n";
	    end if;
	    first := false;
	    printf "    ";
	    printf "%o",C;
	end for;
	printf "\n";
    end if;
    num := Numerator(X);
    printf "  Numerator: %o",num;
    if #Terms(num) ge 12 then
	    printf "\n  Apparent format: %o x %o",
			#eqdegs,#syzdegs;
    end if;
    if Codimension(X) ne ApparentCodimension(X) then
	    printf "\n  Apparent codimension: %o",ApparentCodimension(X);
    end if;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Access functions
// These are mostly inherited from GRSch.
///////////////////////////////////////////////////////////////////////

forward find_weights;
intrinsic Weights(X::GRCY) -> FldRatElt
{}
    if not assigned X`weights then
        X`weights := find_weights(HilbertSeries(X),Basket(X));
    end if;
    return X`weights;
end intrinsic;

intrinsic Degree(X::GRCY) -> FldRatElt
{}
    if not assigned X`degree then
	X`degree := P1P2toA3Ac2over12(P1(X),P2(X),Basket(X));
    end if;
    return X`degree;
end intrinsic;

intrinsic Ac(X::GRCY) -> FldRatElt
{}
    if not assigned X`Ac then
        _,Ac := P1P2toA3Ac2over12(P1(X),P2(X),Basket(X));
        X`Ac := Ac;
    end if;
    return X`Ac;
end intrinsic;

intrinsic HilbertSeries(X::GRCY) -> FldFunRatUElt
{}
    return X`hilbert;
end intrinsic;



//////////////////////////////////////////////////////////////////////////////
//                      Auxiliary functions
//////////////////////////////////////////////////////////////////////////////

forward curve_ind_ok, reduce;
function find_weights(h,B)
// A first guess at the weights of an ambient wps containing X,A corresponding
// to h. The multiplied up Hilbert series is also returned
// sig:		(h::FldFunRatElt,B::GRBskt) -> SeqEnum,FldFunRatElt
    D := FindFirstGenerators(h);
    _,D := CheckBasket(B,D);
    // SORT OUT CURVES : recall, D is seq of weights so far.
    cB := Curves(B);
    for C in cB do
        ind := TransverseIndex(C);
        // The choice here could be tricky, so for the time being we only
        // make first guesses: if there are >= 3 vars with hcf 'ind' then
        // we're happy; if there are >= 2 vars which equal 'ind' then we're
        // happy, otherwise we add vars of weight 'ind' and risk suffering
        // the appalling consequences.
        while not curve_ind_ok(D,ind) do
            // NB. no test yet whether ind is at all a sensible weight to add.
            D := Sort(D cat [ind]);
        end while;
    end for;
    // THINK:  this doesn't work yet
    // D := reduce(D,h,Points(B),cB);
    return Sort(D),HilbertNumerator(h,D);
end function;

forward leading_eqn;
function reduce(D,h,pB,cB)
    done := false;
    repeat
        num := HilbertNumerator(h,D);
        d := leading_eqn(num);
        if d notin D then
            done := true;
        else
            // THINK:  I DO NOT check that it is OK to remove this weight
            R := Parent(num);
            t := R.1;
            bool,num1 := IsDivisibleBy(num,1-t^d);
            if bool then
                Remove(~D,Index(D,d));
            else
                done := true;
            end if;
        end if;
    until done;
    return D;
end function;

function leading_eqn(f)
    d := 1;
    while Coefficient(f,d) eq 0 do
        d +:= 1;
    end while;
    return d;
end function;

function curve_ind_ok(D,ind)
    // see comments in function for what this does.
    // D = weights so far; ind = transverse singularity index of curve C
    // return true iff conds satisfied.
    if #[ d : d in D | d eq ind ] ge 2 then
        return true;
    end if;
    niceD := [ d : d in D | d mod ind eq 0 ];
    if #niceD ge 3 or (#niceD eq 2 and ind in niceD) then
        return true;
    end if;
    return false;
end function;

