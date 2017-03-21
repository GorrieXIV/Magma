freeze;
 
///////////////////////////////////////////////////////////////////////
//		Kill leading positive terms
///////////////////////////////////////////////////////////////////////


intrinsic IsHilbertNumerator(g::FldFunRatUElt,D::SeqEnum) -> BoolElt,RngUPolElt
{True iff the product g * &*(1-t^d) taken over all integers d in D is
a polynomial, in which case, that polynomial is returned as a second value}
    K := Parent(g);
    R := RingOfIntegers(K);
    num := g * &*[K| 1 - K.1^d : d in D ];
    bool,num1 := IsCoercible(R,num);
    if bool then
	return true,num1;
    else
	return false,_;
    end if;
end intrinsic;

intrinsic HilbertNumerator(g::FldFunRatUElt,D::SeqEnum) -> RngUPolElt
{The product g * &*(1-t^d) taken over all integers d in D if it is a polynomial}
    K := Parent(g);
    R := RingOfIntegers(K);
    num := g * &*[K| 1 - K.1^d : d in D ];
    bool,num1 := IsCoercible(R,num);
    require bool: "Product is not a polynomial";
    return num1;
end intrinsic;

/*
Input:
	g	- a hilbert series in k(t)
	[ N	- an integer]
    or
	h	- a hilbert series in k[[t]]
	[ N	- an integer]
Output:
	gens	- degree of generators
	i	- degree of first forced relation
Method:
    The idea is to compute the maximum span of the current generators in
    increasing degrees. If that is less that the corresponding coeff then add
    more generators in that degree and continue. If we find that the maximum
    span is strictly bigger than the corr coeff we have found the first
    necessary equation and we stop.
    Variables:
	gens	- the (correct) degrees of generators we know (so far)
	i	- the current element of coeffs we search
		- note the shift in degree: coeff[i] == coeff of t^(i-1)
	next	- the span of current gens in deg i-1
*/

forward which_cyclotomic;
intrinsic FindFirstGenerators(g::FldFunRatUElt:Precision:=200) -> SeqEnum
{} 
    if Degree(Numerator(g)) eq 0 then
	// presumably this comes from some wps
	// so find a product of cyclotomic polynomials that the denom divides.
	factors := [ Integers() | ];
	d := Denominator(g);
	R := Parent(d);
	t := R.1;
	repeat;
	    fact := Factorisation(d);
	    Reversion(~fact);
	    f := fact[1][1];
	    m := fact[1][2];
	    bool,n := which_cyclotomic(f);
	    require bool: "The denominator of the argument must comprise only "
				* "small cyclotomic factors";
	    factors cat:= [ n : j in [1..m] ];
	    bool,dnew := IsDivisibleBy(d,(1-t^n)^m);
	    require bool: "The denominator of the argument must comprise only "
				* "small factors of the form 1-t^n";
	    d := dnew;
	until Degree(d) eq 0;
	return Reverse(factors);
    end if;
    Q := FindFirstGenerators(g,[Integers()|]:Precision:=Precision);
    return Q;
end intrinsic;

function which_cyclotomic(f)
    n := 1;
    repeat
	p := CyclotomicPolynomial(n);
	if f eq p then
	    return true,n;
	end if;
	n +:= 1;
    until n ge 20;
    return false,_;
end function;

forward number_of_monos;
intrinsic FindFirstGenerators(g::FldFunRatUElt,gens::SeqEnum:Precision:=200)
		 -> SeqEnum
{} 
// No check that gens, if given, are sensible.
// Should really be using lazy power series, but they don't exist yet.

    N := Precision;
    S := PowerSeriesRing(Rationals(),N);  // precision can be increased if nec
    coeffs := Coefficients( S ! g );	  // stupid! have to compute in advance

    if #gens eq 0 then
	i := 2;		// = 1 + 1 to correct the shift
    	next := 0;
    else
	gens := Sort(gens);
	i := gens[#gens] + 1;	// + 1 to correct the shift
	next := number_of_monos(gens,i+1);
    end if;
    repeat
	dif := coeffs[i] - next;
	if dif eq 0 then
	    if #gens gt 0 then
		next := number_of_monos(gens,i);
	    else
		next := 0;
	    end if;
	    i +:=1;
	    require i lt N: "Insufficient precision";
	    continue;
	end if;
	d :=Integers() ! dif;
	gens cat:=[i-1 :j in [1..d]];
	next := number_of_monos(gens,i);
	i +:= 1;
	dif := coeffs[i] - next;
	require i lt N: "Insufficient precision";
    until dif lt 0;
    return gens;
end intrinsic;

intrinsic FindFirstGenerators(g::RngSerPowElt,N::RngIntElt) -> SeqEnum
{Return plausible weights of generators for the variety with Hilbert series g}
// no test that g = 1 + h.o.t.
    gens := [ Integers() | ];
    coeffs0 := Coefficients(g);
    if #coeffs0 ge N+1 then
	coeffs := coeffs0[1..N+1];
    else
	coeffs := coeffs0 cat [ Rationals() | 0 : i in [1..N+1-#coeffs0] ];
    end if;
    new := [ Rationals() | 0 : i in [1..N] ];
    dif := [ coeffs[j] - new[j] : j in [1..N] ];
    i := 2;
    while dif[i] ge 0 do
	if dif[i] eq 0 then
	    i +:=1;
	    continue;
	elif i eq N then
	    break;
	end if;
	d :=Integers() ! dif[i];
	gens cat:=[i-1 :j in [1..d]];
	new := [ number_of_monos(gens,j) :  j in [0..N-1]];
	dif := [ coeffs[j] - new[j] : j in [1..N] ];
	i +:= 1;
    end while;
    return gens;
end intrinsic;


/////////////////////////////////////////////////////////////////////
//			Auxilliary functions
/////////////////////////////////////////////////////////////////////

procedure add_q(~Q,q,n)
// include q in every elt of Q for which sum+q le n
    Qnew := [ Universe(Q) | ];
    for S in Q do
        S1 := S;
        done := false;
        repeat
            if &+S1 le n then
                Append(~Qnew,S1);
            else
                done := true;
            end if;
            Append(~S1,q);
        until done;
    end for;
    Q := Qnew;
end procedure;

function number_of_monos(Q,n)
// Q seq of integers, n an integer.
// return the number of combinations of elts of Q (with repeats) that sum to n
    Qout := [Parent([1,2]) |[] ];
    for q in Q do
        add_q(~Qout,q,n);
    end for;
    return #[ S : S in Qout | &+S eq n ];
end function;


///////////////////////////////////////////////////////////////////////
//			Test code
///////////////////////////////////////////////////////////////////////

/*
Attach("~gavinb/HilbertSeries/Ahilb.m");
Q := Rationals();
R<t> := PolynomialRing(Q);
K := FieldOfFractions(R);
S<s> := PowerSeriesRing(Q);
g := (1 - t^4 - t^5 + t^9) / ( (1-t^2)^2*(1-t^3) );
FindFirstGenerators(g);		// [ 2, 2, 3 ] 4

// R(C,P) for a g = 2 curve.
p := n - 1;
V := [1,1,2];
h := HilbertSeries(p,V);        // (t^4 - t^3 + t^2 - t + 1)/(t^2 - 2*t + 1)
FindFirstGenerators(h); // [ 1, 2, 5 ] 10
HilbertNumerator(h,[1,2,5]);    // -t^10 + 1

g := (t^20 - 6*t^16 - 8*t^15 + 2*t^14 + 24*t^13 + 21*t^12 - 16*t^11
- 36*t^10 - 16*t^9 + 21*t^8 + 24*t^7 + 2*t^6 - 8*t^5 - 6*t^4 + 1) /
&*[ 1 - t^d : d in [ 1, 2, 2, 2, 2, 3, 3, 3 ] ];
time FindFirstGenerators(g);		// 0.010
time FindFirstGenerators(g,[1,2,2,2,2]);	// 0.000

g := 1 + s + 2*s^2 + 3*s^3 + 5*s^4;
FindFirstGenerators(g,20);
*/

