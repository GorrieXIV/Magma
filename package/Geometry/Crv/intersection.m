freeze;

///////////////////////////////////////////////////////////////////////
// intersection_crv.m
// ABT Jan 1998; GDB Nov 2000
///////////////////////////////////////////////////////////////////////

intrinsic IsTransverse(C::Crv,D::Crv,p::Pt) -> BoolElt
{True iff C and D intersect transversely at p}
    require p in C and p in D:
	"Arguments do not intersect at given point";
    if IsSingular(C,p) or IsSingular(D,p) then
	return false;
    else
    	return TangentSpace(C,p) ne TangentSpace(D,p);
    end if;
end intrinsic;

intrinsic IntersectionNumber(C::Crv,D::Crv,p::Pt) -> RngIntElt
{The local intersection number of the curves C and D at p}
    // This algorithm is taken from Winkler's as yet unpublished notes
    // on computational algebraic geometry. But it is standard; adapted from
    // Fulton, for example.
    require Ambient(C) eq Ambient(D):
        "Arguments do not lie in the same ambient";
    A := Ambient(C);

    // First the case that p does not lie on C and D.
    if not p in C or not p in D then
        return 0;
    end if;

    // Go to an affine patch if curves are projective.
    // I don't need to save projective curves for later so reuse their names.
    // I assume that the rightmost nonzero coord of p is a 1.
    if Type(A) eq Prj then
	coords,indices := NonZeroCoordinates(p);
	ind := Length(A) - indices[#indices] + 1;
	C := AffinePatch(C,ind);
	D := AffinePatch(D,ind);
	A := AffinePatch(A,ind);
	p := A ! [ p[i] : i in [1..#Coordinates(p)] | i ne indices[#indices] ];
    end if;

    // Move p to the origin.
    phi := Translation(A,Minus(p));
    f := Polynomial(C@@phi);
    g := Polynomial(D@@phi);

    GrtCD := GCD(f,g);
    GrtCDVal := Evaluate(GrtCD, [0,0]);
    // Prefer to return infinity rather than an error.
    // require GrtCDVal ne 0:
      // "Curve arguments have a common component through the point";
    if GrtCDVal eq 0 then
	return Infinity();
    end if;
 
    f0 := Evaluate(f, 2, 0);  //f evaluated at y = 0; poly in x (posbly const)
    r := Degree(f0, 1);       //Degree of f0 w.r.t. x
    g0 := Evaluate(g, 2, 0);
    s := Degree(g0, 1);
    if (r gt s) then         // Want r < s or r = s; due to symmetry we can
        tmpPoly := f;        // just swap the curves.
        tmpPly0 := f0;
        tmpDegr := r;
        f := g;
        f0 := g0;
        r := s;
        g := tmpPoly;
        g0 := tmpPly0;
        s := tmpDegr;
    end if;
 
    while (r gt 0) do
        // Intersection number only depends on the residue of g mod f;
	// using this employ a Euclidean algorithm.
        g := g div LeadingCoefficient(g0)
               -  f div LeadingCoefficient(f0)*A.1^(s-r);
        g0 := Evaluate(g, 2, 0);
        s := Degree(g0, 1);
        if (r gt s) then
            tmpPoly := f;
            tmpPly0 := f0;
            tmpDegr := r;
            f := g;
            f0 := g0;
            r := s;
            g := tmpPoly;
            g0 := tmpPly0;
            s := tmpDegr;
        end if;
    end while;
 
    // We now have r = 0 or -1; thus, f0 is a constant and so y divides f
    // since f(0,0) = 0.
    h := f div A.2;
    m := TotalDegree(TrailingTerm(g0));
    D := Curve(A, g);
    if TotalDegree(h) ge 1 then
	Ch := Curve(A, h);
	// Recursively call the next intersection number.
	M := m + IntersectionNumber(Ch, D, Origin(A));
    else
        M := m;
    end if;
    return M;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//			Global calculations
///////////////////////////////////////////////////////////////////////

intrinsic IntersectionNumber(C::Crv,D::Crv) -> RngIntElt
{The intersection number (C,D)}
    require ISA(Type(Ambient(C)),Prj) and Ambient(C) eq Ambient(D):
	"Arguments must lie in a common projective space";
    return Degree(C)*Degree(D);
end intrinsic;

intrinsic IntersectionPoints(C::Crv,D::Crv) -> SetIndx
{The rational points of the intersection of C and D}
    Z := Intersection(C,D);
    require Dimension(Z) le 0 : 
	"The arguments must not have a common component.";
    return RationalPoints(Z,BaseRing(C));
end intrinsic;
 
intrinsic IntersectionPoints(C::Crv,D::Crv,K::Rng) -> SetIndx
{The intersection points of C and D defined over K}
    Z := Intersection(C,D);
    require Dimension(Z) le 0 : 
	"The arguments must not have a common component.";
    return RationalPoints(Z,K);
end intrinsic;
 
intrinsic NumberOfPunctures(C::Crv) -> RngIntElt
    {The number of geometric punctures of the affine curve C at infinity}
    PC := ProjectiveClosure(C);
    if Ambient(PC)![0,1,0] in PC then
        punct := 1;
    else
        punct := 0;
    end if;
    f := Polynomial(PC);
    finf := Evaluate(f,[1,PC.1,0]);
    dfinf := Derivative(finf,1);
    fred := finf/GCD(finf,dfinf);
    return punct + TotalDegree(fred);
end intrinsic;
 
