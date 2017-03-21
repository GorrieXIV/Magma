freeze;

function curve(p, sigma)
    K := GF(p);
    v := K ! (4*sigma);
    u := K ! (sigma^2-5);
    x := u^3;
    b := 4*x*v;
    a := (v-u)^3*(3*u+v);
    A := a/b-2;
    x := x/v^3;
    b := x^3 + A*x^2 + x;
    E := EllipticCurve([0,b*A,0,b^2,0]);
    return E;
end function;

intrinsic ECMOrder(p::RngIntElt, s::RngIntElt) -> RngQuad
{Given a prime p and integer s, such that p is a factor found by ECM and
s is the sigma parameter defining the curve used, return the order of
the curve over GF(p).};
    require IsPrime(p) and p ge 2: "First argument must be a positive prime";

    E := curve(p, s);
    return #E;
end intrinsic;

intrinsic ECMFactoredOrder(p::RngIntElt, s::RngIntElt) -> RngQuad
{Given a prime p and integer s, such that p is a factor found by ECM and
s is the sigma parameter defining the curve used, return the factorization
of the order of the curve over GF(p).};
    require IsPrime(p) and p ge 2: "First argument must be a positive prime";

    E := curve(p, s);
    return FactoredOrder(E);
end intrinsic;

SIGMA_MAX := 2^32 - 1;

intrinsic ECMSteps(n::RngIntElt, L::RngIntElt, U::RngIntElt) -> RngIntElt
{Apply ECM to n with B1 ranging from L to U using the square root stepping
method; return factor f and corresponding Sigma if factor found; otherwise
return 0.};

    B1 := L;
    while B1 le U do
	sigma := Random(1, SIGMA_MAX);
	f := ECM(n, B1: Sigma := sigma);
	if f ne 0 then
	    return f, sigma;
	end if;
	B1 +:= Isqrt(B1);
    end while;
    return 0, 0;
end intrinsic;
