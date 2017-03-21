freeze;

///////////////////////////////////////////////////////////////////////
// scheme.m
// April 2001 GDB
///////////////////////////////////////////////////////////////////////

import "../../Commut/RngMPol/multi_hilb.m" : MultiGradArithGenus;

intrinsic EmptySubscheme(X::Sch) -> Sch, MapSch
    {The empty subscheme of X}
    // THINK: there is a C level function EmptyScheme, 
    // which supposed to be doing the same thing...
    A := Ambient(X);
    R := CoordinateRing(A);
    coords := [ R | R.i : i in [1..Length(A)] ];
/*
    if IsAffine(A) then
        Z := Scheme(X,[R!1]);
        return Z, map< Z -> X | coords >;
    end if;
    if ISA(Type(A), TorVar) then
        I := IrrelevantIdeal(A);
        Z := Scheme(X,I : Saturated := true);
        return Z, map< Z -> X | coords >;
    end if;
    // This is silly, but what can we do...
    I:=Ideal([CoordinateRing(A)| A.i : i in [1..Length(A)]]);
    Z := Scheme(X,I : Saturated := true);
*/
    Z:=EmptyScheme(X);
    return Z, map< Z -> X | coords >;
end intrinsic;

intrinsic IsAffine(X::Sch) -> BoolElt
{True iff the ambient space of X is an affine}
    A:=Ambient(X);
    if ISA(Type(A),Aff) then 
        return true;
    end if;
    if ISA(Type(A),Prj) then 
        return false;
    end if;
    if ISA(Type(A), TorVar) then 
        return ToricIsAffine(A);
    end if;
    return false;
end intrinsic;

intrinsic IsProjective(X::Sch) -> BoolElt
{True iff the ambient space of X is projective}
    A:=Ambient(X);
    if ISA(Type(A),Aff) then 
       return false;
    end if;
    if ISA(Type(A), Prj) then 
       degs:=RowSequence(Transpose(Matrix(Gradings(A))));
       degs:=[PowerSet(Integers()) | Seqset(d) : d in degs];
       return not {0} in degs;
    end if;
    if ISA(Type(A), TorVar) then 
        return ToricIsProjective(A);
    end if;
    return false;
end intrinsic;

intrinsic IsOrdinaryProjective(X::Sch) -> BoolElt
{True iff the ambient space of X is some ordinary (unweighted) projective space}
    Y := Ambient(X);
    gr := Gradings(Y);
    // For toric varieties there is more work to do:
    if Type(Y) eq TorVar then 
        if #QuotientGradings(Y) gt 0 then 
           return false;
        end if;
        if #gr ne 1 or Seqset(gr[1]) ne {1} then 
            return false;
        end if;
        if #IrrelevantComponents(Y) ne 1 then 
            return false;
        end if;
        if #IrrelevantGenerators(Y)[1] ne Dimension(Y) + 1 then 
            return false;
        end if;
    end if;
    return #gr eq 1 and Seqset(gr[1]) eq {1};
end intrinsic;

intrinsic IdenticalAmbientSpace(X::Sch,Y::Sch) -> BoolElt
{True iff X and Y lie in the same ambient space}
    return Ambient(X) cmpeq Ambient(Y);
end intrinsic;

intrinsic GroebnerBasis(X::Sch) -> SeqEnum
{A Groebner basis for the ideal of X}
    Saturate(~X);
    return GroebnerBasis(DefiningIdeal(X));
end intrinsic;

intrinsic MinimalBasis(X::Sch) -> SeqEnum
{A minimal basis for the ideal of X}
    Saturate(~X);
    return MinimalBasis(DefiningIdeal(X));
end intrinsic;

intrinsic IsLinear(X::Sch) -> BoolElt
{True iff X is defined by linear equations, possibly after taking a
Groebner basis}
    if &*[ TotalDegree(f) : f in DefiningPolynomials(X) ] eq 1 then
        return true;
    elif not HasGroebnerBasis(X) then
        return false;
    else
	Saturate(~X);
        Groebner(DefiningIdeal(X));
        return &*[ TotalDegree(f) : f in Basis(DefiningIdeal(X)) ] eq 1;
    end if;
    return false;
end intrinsic;

intrinsic IsLinearScheme(X::Sch) -> BoolElt
{Deprecated name for IsLinear, remove after 2.14}
    return IsLinear(X);
end intrinsic;

intrinsic IsPlanar(X::Sch) -> BoolElt
{True iff the ambient space of X is two dimensional}
    return Dimension(Ambient(X)) eq 2;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Basic basering algorithm tests
///////////////////////////////////////////////////////////////////////

intrinsic HasGroebnerBasis(X::Sch) -> BoolElt
{True iff Groebner basis methods are available for the equations of X}
    // THINK: GB works already for other Euclidean rings,
    // but it seems to refer to PrimeDecomposition etc!
    return IsField(BaseRing(X));
end intrinsic;

intrinsic HasFactorisation(X::Sch) -> BoolElt
{}
    return HasPolynomialFactorization(BaseRing(X));
end intrinsic;
 
intrinsic HasFactorization(X::Sch) -> BoolElt
{True iff factorisation and irreducibility calculations can be carried out in X}
    return HasPolynomialFactorization(BaseRing(X));
end intrinsic;
 
intrinsic HasResultant(X::Sch) -> BoolElt
{True iff resultant calculations can be carried out in X}
    return HasPolynomialResultant(BaseRing(X));
end intrinsic;
 
intrinsic HasGCD(X::Sch) -> BoolElt
{True iff GCD calculations can be carried out in X}
    return HasGCD(BaseRing(X));
end intrinsic;

///// Arithmetic genus added by Mike Harrison (05/2004) ///////
//          Is there a better place for this?                //		

/* First add some functions to compute Hilbert series of
    "multiples" of graded rings ( if R = sum R_n then
    the dth "multiple" graded ring R^(d) = sum R_nd)
    from the Hilbert Series of the original              */
    
/* pol is a univariate polynomial over Q whose
   roots (in the alg closure) are all roots of unity
   of order dividing divides.
   Returns the LCM of the order of these roots.
   VERY BASIC IMPLEMENTATION!!
*/

function RootPower(pol : divides := 0)

    sqfree := pol div Normalise(GCD(pol,Derivative(pol)));
    if not IsMonic(sqfree) then
	sqfree := sqfree/LeadingCoefficient(sqfree);
    end if;
    R := quo<Parent(sqfree) | sqfree>;
    x := R.1;
    if divides eq 0 then
        y := x;
	for m in [1..1000000] do
	    if y eq R!1 then return m; end if;
            y*:=x;
	end for;
	error "Order of roots too large";
    else
	ds := Divisors(divides);
	Sort(~ds);
	for d in ds do
	    if x^d eq R!1 then return d; end if;
	end for;
	error "Order of roots didn't divide the parameter";
    end if;

end function;


/* pol is a monic univariate polynomial over a field whose
   roots (in the alg closure) are {r_1,..r_m}.
   Returns the poly whose roots are {r_1^n,..r_m^n}
*/
function nthPowerPoly(pol,n)

    P2 := PolynomialRing(BaseRing(Parent(pol)),2);
    res := Resultant((P2.2)^n-(P2.1),
	    &+[ Coefficient(pol,i)*(P2.2)^i : i in [0..Degree(pol)]],
	    2);
    return Parent(pol)![MonomialCoefficient(res,(P2.1)^i) : 
		i in [0..Degree(pol)] ];

end function;

function Get_Series_nth_Coeffs(num,den,n,d)

    P := PowerSeriesRing(BaseRing(Parent(num))); T := P.1;
    f := (P!num)/((P!den)+O(T^(n*d+1)));
    return Parent(num)![Coefficient(f,n*i) : i in [0..d]];
  
end function;

function HilbertSeriesMult(H,n)

    if n eq 1 then return H; end if;
    P := PolynomialRing(RationalField());
    num := P!Numerator(H);
    den := P!Denominator(H);
    if not IsMonic(den) then
	lc := LeadingCoefficient(den);
	num /:= lc; den /:= lc;
    end if;
    //assert Degree(GCD(num,den)) eq 0;
    p_1,rnum := Quotrem(num,den);
    
    new_den := nthPowerPoly(den,n);

    /* first transform the integral part */
    if p_1 ne P!0 then
	p_1 := P![Coefficient(p_1,n*i) : i in [0..Degree(p_1) div n]];    
    end if;
    
    /* now do the other bit */
    pow := (Degree(den) eq 0) select P!0 else
		Get_Series_nth_Coeffs(rnum,den,n,Degree(den)-1);
    new_num := p_1*new_den + ((pow*new_den) mod (P.1)^Degree(den));
    return (Parent(H)!new_num)/(Parent(H)!new_den);
   
end function;

function EulerPoincareChar(I)

    /* 
       returns the EulerPoincare charateristic of the projective
       scheme defined by I
    */
    P := PolynomialRing(RationalField());
    H := HilbertSeries(I);
    n := RootPower(P!Denominator(H) : divides := LCM(VariableWeights(I)));
    /* In fact n := LCM(VariableWeights(I)) will do!! */
    H := HilbertSeriesMult(H,n);
    num := P!Numerator(H);
    den := P!Denominator(H);
    if not IsMonic(den) then
	lc := LeadingCoefficient(den);
	num /:= lc; den /:= lc;
    end if;
    //assert Degree(GCD(num,den)) eq 0;
    num mod:= den;
    return (IntegerRing()!Coefficient(num,0)) * (-1)^Degree(den);

end function;

intrinsic InternalEqualityOf_dthTruncations(I1::RngMPol,I2::RngMPol,d::RngIntElt)
				-> BoolElt
{}
/*
   I1 >= I2 are ideals in a (weighted) polynomial ring (over a field). Fn checks
   whether I1(d) eq I2(d), the dth truncations [ie Ii(d) = Ii meet R(d) are the
   direct sums of the wth graded pieces for all w with d|w : ideals of R(d)]
*/
    H1 := HilbertSeries(I1);
    H1 := HilbertSeriesMult(H1,d);
    H2 := HilbertSeries(I2);
    H2 := HilbertSeriesMult(H2,d);
    return (H1 eq H2);

end intrinsic;


intrinsic ArithmeticGenus(X::Sch) -> RngIntElt
{Returns the arithmetic genus of (the projective closure of) scheme X}
   if IsAffine(X) then X := ProjectiveClosure(X); end if;
   require IsProjective(X) and 
    ( ((NumberOfGradings(X) eq 1) and &and[gr ne 0 : gr in Gradings(X)[1]])
      or 
      (Type(Ambient(X)) eq PrjProd)
     ): 
        "X must be a purely projective non-scroll";
   /* 
      Should be able to extend to multiple gradings with more general
      weights than product projective space. this suffices for now.
   */
   if NumberOfGradings(X) eq 1 then // ordinary or weighted projective case
     g := EulerPoincareChar(DefiningIdeal(X));
     return (g - 1) * ((-1)^Dimension(X));
   else                             // product projective case
     return MultiGradArithGenus(X);
   end if;
end intrinsic;
