freeze;

///////////////////////////////////////////////////////////////////////
// singularity.m
///////////////////////////////////////////////////////////////////////

intrinsic GeometricGenus(C::Crv) -> RngIntElt
{The geometric genus of C}
    return Genus(C);
end intrinsic;

///////////////////////////////////////////////////////////////////////
//		Flexes, nodes, etc
///////////////////////////////////////////////////////////////////////


intrinsic IsFlex(C::Crv,p::Pt) -> BoolElt,RngIntElt
{True iff p is a flex on plane curve C}
    require (Dimension(Ambient(C)) eq 2):
	"Curve must be in 2D space";
    require IsNonsingular(C,p):
	"Point is not nonsingular on the curve";
    T := TangentLine(C,p);
    i := IntersectionNumber(C,T,p);
    if i ge 3 then
	return true,i;
    else
	return false,_;
    end if;
end intrinsic;


intrinsic IsFlexFast(C::Crv,p::Pt) -> BoolElt
{Slightly faster version of the test for an inflection point on a
 plane curve that doesn't return the multiplicity}
    require (Dimension(Ambient(C)) eq 2):
	"Curve must be in 2D space";
    if IsProjective(C) then
	C,p := AffinePatch(C,p);
    end if;
    pol := Polynomial(Translation(Ambient(C),p)(C));
    f1 := &+[ Parent(pol) | t : t in Terms(pol) | TotalDegree(t) eq 1];
    f2 := &+[ Parent(pol) | t : t in Terms(pol) | TotalDegree(t) eq 2];
    require (f1 ne 0):
	"Point is not nonsingular on the curve";
    return IsDivisibleBy(f2,f1);
end intrinsic;

intrinsic IsFlex(p::Pt) -> BoolElt,RngIntElt
    {True iff p is a flex on a plane curve C}
    X := Scheme(Parent(p));
    b,C := IsCurve(X);
    b and:= Dimension(Ambient(X)) eq 2; 
    require b: "Argument must lie on a curve in 2D space";
    b,m := IsFlex(C,p);
    if b then
	return b,m;
    else
	return b,_;
    end if;
end intrinsic;

intrinsic IsInflectionPoint(p::Pt) -> BoolElt,RngIntElt
    {True iff p is a flex on a plane curve C}
    X := Scheme(Parent(p));
    b,C := IsCurve(X);
    b and:= Dimension(Ambient(X)) eq 2; 
    require b: "Argument must lie on a curve in 2D space";
    b,m := IsFlex(C,p);
    if b then
	return b,m;
    else
	return b,_;
    end if;
end intrinsic;

intrinsic IsDoublePoint(C::Crv,p::Pt) -> BoolElt
{True iff p is a double point of curve C}
    return Multiplicity(C,p) eq 2;
end intrinsic;

intrinsic IsDoublePoint(p::Pt) -> BoolElt
{True iff p is a double point of its scheme, which should be a curve}
    X := Scheme(Parent(p));
    b,C := IsCurve(X);
    require b: "Argument must lie on a curve";
    return IsDoublePoint(C,p);
end intrinsic;

intrinsic IsCusp(C::Crv,p::Pt) -> BoolElt
{True iff p is a nonordinary double point of curve C}
    return not IsOrdinarySingularity(C,p) and IsDoublePoint(C,p);
end intrinsic;

intrinsic IsCusp(p::Pt) -> BoolElt
{True iff p is a nonordinary double point of its scheme, which should be a curve}
    X := Scheme(Parent(p));
    b,C := IsCurve(X);
    require b: "Argument must lie on a curve";
    return IsCusp(C,p);
end intrinsic;

