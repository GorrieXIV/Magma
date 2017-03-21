freeze;

///////////////////////////////////////////////////////////////////////
// tangent_crv.m
// GDB Nov 2000
///////////////////////////////////////////////////////////////////////


intrinsic TangentLine(C::Crv,p::Pt) -> Crv
{Tangent line to curve C at the nonsingular rational point p}
    require p in C:
	"Argument 2 must be a point on argument 1";
    require IsNonsingular(C,p):
	"Argument 2 must be nonsingular point of argument 1";
    return TangentSpace(C,p);
end intrinsic;

intrinsic TangentLine(p::Pt) -> Crv
{Tangent line to curve C (p's Parent) at nonsingular rational point p }
    X := Scheme(Parent(p));
    b,C := IsCurve(X);
    require b: "Argument does not lie on a curve";
    //require IsCoercible(C, p) : "Point must be a rational point of its parent";
    return TangentLine(C,p);
end intrinsic;

intrinsic TangentCone(C::CrvPln,p::Pt) -> Sch
{The tangent cone to C at the rational point p embedded in the
same ambient as C}
// Still used for plane curves but there is a version now for
//  general schemes in Sch/tangent.m
    require p in C:
	"Point is not a point of the curve";
    A := Ambient(C);
    if IsAffine(A) then
	if not(Ring(Parent(p)) cmpeq BaseRing(A)) then
	    A := BaseChange(A,Ring(Parent(p)));
	    p := A!Eltseq(p);
	end if;
	return Curve(A,f_min)@@phi
	    where f_min is &+[ m : m in terms | TotalDegree(m) eq min_deg]
	    where min_deg is Minimum([ TotalDegree(m) : m in terms ])
		where terms := Terms(Evaluate(Polynomial(C),
			InverseDefiningPolynomials(phi)))
		where phi is Translation(A,p);
    else
	return ProjectiveClosure(TangentCone(C@@phi,p))
		where phi is ProjectiveClosureMap(A)
		where A,p := AffinePatch(A,p);
    end if;
end intrinsic;

intrinsic IsTangent(C::Crv,D::Crv,p::Pt) -> BoolElt
{True iff C and D have a common tangent cone component at rational point p}
    require IsPlaneCurve(C) and IsPlaneCurve(D):
	"Arguments 1 and 2 must be curves lying in the same plane";
    require p in C(BaseRing(C)) and p in D(BaseRing(D)):
	"Point is not a common rational point of the curves";
    // A bit silly, but avoids equality testing and only uses GCDs.
    return IntersectionNumber(TangentCone(C,p),TangentCone(D,p),p) eq Infinity();
end intrinsic;


