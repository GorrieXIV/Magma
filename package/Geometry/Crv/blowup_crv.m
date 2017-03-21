freeze;

///////////////////////////////////////////////////////////////////////
// blowup_crv.m
//	Ordinary and weighted blowup of affine plane curves
///////////////////////////////////////////////////////////////////////

intrinsic Blowup(C::Crv) -> Crv, Crv
{The two natural patches of the blowup of C at the origin}
    A := Ambient(C);
    require IsAffine(C):
	"Curve must be affine";
    RA := CoordinateRing(A);
    bxxy := hom< RA -> RA | RA.1, RA.1*RA.2 >;
    bxyy := hom< RA -> RA | RA.1*RA.2, RA.2 >;
    return Curve(A,RA!(bxxy(f)/RA.1^m)),Curve(A,RA!(bxyy(f)/RA.2^m))
	where m is Minimum([ TotalDegree(m) : m in Monomials(f) ])
	where f is Polynomial(C);
end intrinsic;

forward min_degs;
intrinsic Blowup(C::Crv,M::Mtrx) -> Crv,RngIntElt,RngIntElt
{The birational transform of C under the toric blowup given by M}
    // In coordinates, the blowup given by Matrix(2,[a,b,c,d]) is
    //		x -> x^ay^b, y -> x^cy^d.
    require Type(Ambient(C)) eq Aff:
	"Curve must be affine";
    f := Polynomial(C);
    m,n := min_degs(f,M);
    R := Parent(f);
    a := M[1,1];
    b := M[1,2];
    c := M[2,1];
    d := M[2,2];
    blowup := hom< R -> R | R.1^a*R.2^b, R.1^c*R.2^d >;
    // Be careful to remove exceptional factors from the total pullback of C
    // but _not_ to remove the birl pullbacks of the original axes.
    if M[1,1] eq 1 and M[1,2] eq 0 then
	g := R!(blowup(f)/(R.1^m));
    elif M[2,1] eq 0 and M[2,2] eq 1 then
	g := R!(blowup(f)/(R.2^n));
    else
	g := R!(blowup(f)/(R.1^m*R.2^n));
    end if;
    return Curve(Ambient(C),g),m,n;
end intrinsic;

min_degs := function(f,M)
    a := M[1,1];
    b := M[2,1];
    c := M[1,2];
    d := M[2,2];
    m := Minimum([a*Degree(m,1)+b*Degree(m,2) : m in Monomials(f)]);
    n := Minimum([c*Degree(m,1)+d*Degree(m,2) : m in Monomials(f)]);
    return m,n;
end function;

