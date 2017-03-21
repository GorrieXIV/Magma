freeze;
 
///////////////////////////////////////////////////////////////////////
// Basic construction of Hilbert series a la Zariski--Samuel.
///////////////////////////////////////////////////////////////////////

intrinsic HilbertSeries(p::RngUPolElt,V::SeqEnum) -> FldFunRatUElt
{}
    return HilbertSeries([p],V);
end intrinsic;

intrinsic HilbertSeries(F::SeqEnum,V::SeqEnum) -> FldFunRatUElt
{The Hilbert series corresponding to a polynomial p or sequence of
polynomials F and a sequence of starting values V}
    n,D := HilbertSeriesMultipliedByMinimalDenominator(F,V);
    return n/&*(D);
end intrinsic;

forward periodicity,poly_diff,fun_diff;
intrinsic HilbertSeriesMultipliedByMinimalDenominator(p::RngUPolElt,V::SeqEnum) -> RngUPolElt,SeqEnum
{}
    return HilbertSeriesMultipliedByMinimalDenominator([p],V);
end intrinsic;

intrinsic HilbertSeriesMultipliedByMinimalDenominator(F::SeqEnum,V::SeqEnum)
		-> RngUPolElt,SeqEnum
{Given a sequence of polynomials determining a Hilbert polynomial with
periodic corrections, together with a sequence of alternative early values,
return the Hilbert series' numerator, together with a sequence containing
the factors of the minimal denominator}
    // First determine the periods appearing in the minimal denominator.
    T := Universe(F);
    t := T.1;
    k := CoefficientRing(T);
    require Type(T) eq RngUPol and Type(k) eq FldRat and IsComplete(F):
	"First argument must be a complete sequence of univariate polynomials"
		* " defined over the rationals";
    if #V gt 0 then
	require Universe(V) eq Integers() and IsComplete(V):
	    "Second argument must be a complete sequence of integers";
    end if;
    A := [Integers()| ];
    G := F;
    while not &and([f eq 0: f in G]) do
	a := periodicity(G);
	Append(~A,a);
	G := [ poly_diff(f,a) : f in G ];
    end while;
    // Compute enough of the Hilbert function so that repeated differencing
    // finds its numerator.
    f := HilbertFunction(F,V);
    cl := #V + &+A - 1;
    for a in A do
	f := fun_diff(f,a);
    end for;
    B := [f(n) : n in [0..cl] ];
    return &+[ B[i]*t^(i-1) : i in [1..#B] ], [ (1-t^a) : a in A ];
end intrinsic;

intrinsic HilbertFunction(p::RngUPolElt,V::SeqEnum) -> UserProgram
{}
    return HilbertFunction([p],V);
end intrinsic;

intrinsic HilbertFunction(F::SeqEnum,V::SeqEnum) -> UserProgram
{The Hilbert function corresponding to a sequence of univariate polynomials
and a sequence of starting values}
    T := Universe(F);
    k := CoefficientRing(T);
    require Type(T) eq RngUPol and Type(k) eq FldRat and IsComplete(F):
	"First argument must be a complete sequence of univariate polynomials"
		* " defined over the rationals";
    if #V gt 0 then
	require Universe(V) eq Integers() and IsComplete(V):
	    "Second argument must be a complete sequence of integers";
    end if;
    function f(n)
	if n lt 0 then
	    return 0;
	end if;
	if n in [0..#V-1] then
	    return V[n+1];
	end if;
	return Evaluate(F[(n mod #F)+1],n);
    end function;
    return f;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Read off Betti-like numbers from a poly
///////////////////////////////////////////////////////////////////////

forward nonzerocoeffs;
intrinsic HilbertNumeratorBettiNumbers(f::RngUPolElt) -> RngIntElt
{}
    R := PolynomialRing(Integers());
    bool,ff := IsCoercible(R,f);
    require bool: "Argument f must be a polynomial with integer coefficients";
    return nonzerocoeffs(ff);
end intrinsic;

intrinsic ApparentCodimension(f::RngUPolElt) -> RngIntElt
{}
    return #HilbertNumeratorBettiNumbers(f) - 1;
end intrinsic;

intrinsic ApparentEquationDegrees(f::RngUPolElt) -> SeqEnum
{}
    betti := HilbertNumeratorBettiNumbers(f);
    if #betti ge 2 then
        eqdegs := &cat[ [ Integers() |
			c[1] : i in [1..AbsoluteValue(Integers()!c[2]) ] ]
                                                        : c in betti[2] ];
    else
        eqdegs := [ Integers() | ];
    end if;
    return eqdegs;
end intrinsic;

intrinsic ApparentSyzygyDegrees(f::RngUPolElt) -> SeqEnum
{}
    betti := HilbertNumeratorBettiNumbers(f);
    if #betti ge 3 then
        syzdegs := &cat[ [ Integers() |
			c[1] : i in [1..AbsoluteValue(Integers()!c[2]) ] ]
                                                        : c in betti[3] ];
    else
        syzdegs := [ Integers() | ];
    end if;
    return syzdegs;
end intrinsic;

function nonzerocoeffs(f)
    current := [ Parent(<0,1>) | ];
    result := [ Parent(current) | ];
    currentsign := 1;
    C := Coefficients(f);
    for i in [1..#C] do
        coef := C[i];
        case Sign(coef):
            when 0:
                continue i;
            when currentsign:
                Append(~current,<i-1,coef>);
            else
                currentsign *:= -1;
                Append(~result,current);
                current := [ <i-1,coef> ];
        end case;
    end for;
    Append(~result,current);
    return result;
end function;


///////////////////////////////////////////////////////////////////////
//		Auxilliary functions
///////////////////////////////////////////////////////////////////////

function periodicity(F)
    R := #F;
    D := Divisors(#F);
    done := false;
    j := 1;
    while not done do
	r := D[j];
	done := &and [ F[i] eq F[i+r] : i in [1..R-r] ] or j eq #D;
	j +:= 1;
    end while;
    return r;
end function;

function poly_diff(f,d)
    R := Parent(f);
    h := hom< R -> R | R.1 - d >;
    return f - h(f);
end function;

function fun_diff(f,d)
    return func< m | f(m) - f(m-d) >;
end function;

