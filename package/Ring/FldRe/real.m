freeze;

intrinsic NumericalDerivative
(f::UserProgram,n::RngIntElt,z::FldComElt) -> FldComElt
{Given a suitably nice function f from C to C, compute a numerical
 approximation to the nth derivative at the point z}
 require n ge 0: "Derivative must be at least 0";
 if n eq 0 then return Parent(z)!f(z); end if;
 prec:=Precision(z); b:=Ilog(10,1+Ceiling(Abs(z)));
 wp:=Ceiling(prec*(1+n/2)+n*(b+2)); C:=ComplexField(wp);
 eps:=10^(C!b-prec/2);
 E:=&+[f(C!z-eps+(2*eps)*k/n)*(-1)^k*Binomial(n,k) : k in [0..n]]/eps^n;
 E*:=(-n/2)^n; return Parent(z)!E; end intrinsic;

intrinsic NumericalDerivative
(f::UserProgram,n::RngIntElt,z::FldReElt) -> FldReElt
{Given a suitably nice function f from R to R, compute a numerical
 approximation to the nth derivative at the point z}
 require n ge 0: "Derivative must be at least 0";
 if n eq 0 then return Parent(z)!f(z); end if;
 prec:=Precision(z); b:=Ilog(10,1+Ceiling(Abs(z)));
 wp:=Ceiling(prec*(1+n/2)+n*(b+2)); R:=RealField(wp);
 eps:=10^(R!b-prec/2);
 E:=&+[f(R!z-eps+(2*eps)*k/n)*(-1)^k*Binomial(n,k) : k in [0..n]]/eps^n;
 E*:=(-n/2)^n; return Parent(z)!E; end intrinsic;

intrinsic Interpolation(xa::[FldReElt], ya::[FldReElt], x::FldReElt) -> FldReElt, FldReElt
{A value y and an error estimate dy, such that p(x) = y where p(xa[i]) = ya[i]
for all i}

    /* 
    Polynomial interpolation via Neville's algorithm at real number x.  
    Returns a value y and an error estimate dy,
    such that p(x)=y where p(xa[i])=ya[i] for all i.  
    xa and ya are length-n sequences of reals.
    */

    n := #xa;
    require n eq #ya: "Arguments 1 and 2 should have the same length";
    require forall{1: i in [j + 1 .. n], j in [1 .. n] | xa[i] ne xa[j]}:
	"Two of the x input values are identical (within precision)";

    // initialize tableau
    c := ya;
    d := ya;

    // find index of table entry closest to x
    _, ns:=Minimum([Abs(x - xa[i]): i in [1 .. n]]); 

    //initial aproximation to y
    y := ya[ns];
    ns -:= 1;
    //for each column of tableau,
    for m in [1 .. n - 1] do
	//loop over current c's and d's and update them
	for i in [1 .. n - m] do
	    ho := xa[i] - x;
	    hp := xa[i + m] - x;
	    t := (c[i + 1] - d[i]) / (xa[i] - xa[i + m]);
	    //update c's and d's
	    d[i] := hp * t;
	    c[i] := ho * t;
	end for;
	//decide whether to fork up or down through tableau
	if 2 * ns lt n - m then
	    dy := c[ns + 1]; 
	else 
	    dy := d[ns];
	    ns -:= 1;
	end if;
	y +:= dy;
    end for;
    return y, dy;
end intrinsic;

function TrapezoidalRefinement(f, a, b, n, s, it)
    if n eq 1 then
	return (b - a) / 2 * (f(a) + f(b)), 1;
    end if;

    // spacing of points to be added
    del := (b - a) / it;
    x := a + del / 2;
    sum := &+ [f(x + j * del): j in [0 .. it - 1]];
    return (s + (b - a) * sum / it) / 2, it * 2;
end function;

intrinsic RombergQuadrature(f::Program, a::FldReElt, b::FldReElt: Precision := 1.0e-6, MaxSteps := 20, K := 5) -> FldReElt
{Approximation to integral of real function f from a to b, using Romberg's
method of order 2k}

    //desired fractional accuracy, as determined by the extrapolation error estimate
    R := RealField();
    EPS := Abs(Precision);

    //limits the total number of steps
    JMAX := MaxSteps;
    JMAXP := JMAX + 1;
    //number of points used in the extrapolation
    if K lt 2 then K eq 2; end if;
    K := 5;

    h:=[R | 1.0];
    s:=[R | ];  

    //Magma equivalent of &h[j-K] with K entries is, roughly, h[(j-K+1)..j]
    s[1] := 0;
    it := 0;
    for j in [1 .. JMAX] do
	s[j], it := TrapezoidalRefinement(f, a, b, j, s[j], it);
	if j gt K then 
	    ss, dss := Interpolation(
		h[j - K + 1 .. j], s[j - K + 1 .. j], R!0
	    );
	    if Abs(dss) lt EPS * Abs(ss) then
		return ss;
	    end if; 
	end if;
	s[j + 1] := s[j];
	h[j + 1] := 0.25 * h[j];
    end for;
    //for-loop ended (instead of executing  return ss)
    error "Exceeded maximum number of steps";
end intrinsic;

intrinsic SimpsonQuadrature(f::Program, a::FldReElt, b::FldReElt, n::RngIntElt) -> FldReElt
{Approximation to integral of real function f from a to b using Simpson's
rule with n sub-intervals}
    requirege n, 2;
    require IsEven(n): "Argument 4 must be even";
    h := (b - a) / n;
    return
	h / 3 * (
	    f(a) + f(b) +
	    4 * &+ [R | f(a + k * h): k in [1 .. n - 1 by 2]] +
	    2 * &+ [R | f(a + k * h): k in [2 .. n - 2 by 2]]
	) where R is RealField();
end intrinsic;

intrinsic TrapezoidalQuadrature(f::Program, a::FldReElt, b::FldReElt, n::RngIntElt) -> FldReElt
{Approximation to integral of f from a to b using trapezoidal rule with
n sub-intervals}
    requirege n, 1;
    h := (b - a) / n;
    return
	h/2 * (
	    f(a) + f(b) + 2 * &+ [R | f(a + k * h): k in [1 .. n - 1]]
	) where R is RealField();
end intrinsic;

intrinsic BetaFunction(z::FldReElt, w::FldReElt) -> FldReElt
{The Beta function B(z, w)}
    return Exp(LogGamma(z) + LogGamma(w) - LogGamma(z+w));
end intrinsic;


