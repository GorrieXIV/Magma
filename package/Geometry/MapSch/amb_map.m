freeze;

///////////////////////////////////////////////////////////////////////
// amb_map.m
///////////////////////////////////////////////////////////////////////


intrinsic BasePoints(f::MapSch) -> SetIndx
{The set of base points of f defined over the extension L of the base field
(or the base field itself if L is omitted) if that set of points is finite}
    B := BaseScheme(f);
    if IsEmpty(B) then
	return {@ Domain(f)(BaseRing(Domain(f))) | @};
    end if;
    bool, Z := IsCluster(B);
    require bool: "Base scheme of argument is not zero-dimensional";
    return RationalPoints(Z);
end intrinsic;

intrinsic BasePoints(f::MapSch,L::Fld) -> SetIndx
{"} // "
    B := BaseScheme(f);
    if IsEmpty(B) then
	return {@ Domain(f)(BaseRing(Domain(f))) | @};
    end if;
    bool, Z := IsCluster(B);
    require bool : "Base scheme of argument is not zero-dimensional";
    return RationalPoints(Z,L);
end intrinsic;

intrinsic IsPolynomial(f::MapSch) -> BoolElt
{True iff f defined by polynomials on the ambient space of its domain}
    return Universe(DefiningPolynomials(f)) cmpeq
	CoordinateRing(Ambient(Domain(f)));
end intrinsic;

intrinsic IsEndomorphism(f::MapSch) -> BoolElt
{True iff the domain and range of f are equal}
    return Domain(f) eq Codomain(f);
end intrinsic;

// CHANGED 13/11/08 mch - Changed function to return MINIMUM degree if
// there are alternative defining equations.
// TO DO: function is still wrong really if the gradings have
// non-trivial weightings. Maybe will return to this but no time now!
intrinsic FunctionDegree(f::MapSch) -> RngIntElt
{The degree of the functions which define f assuming its domain
and codomain are projective}
    require Type(Codomain(f)) eq Prj and #Gradings(Domain(f)) eq 1:
	"Domain and codomain of the argument must be projective";
    ADPs := AllDefiningPolynomials(f);
    degs := [];
    for DPs in ADPs do
      if #DPs eq 0 then
	deg := 0;
      else
	i := 1;
	while DPs[i] eq 0 do i +:=1; end while;
	deg := TotalDegree(DPs[i]);
      end if;
      Append(~degs,deg);
    end for;
    deg := Min(degs);
    return deg;
end intrinsic;

forward constant_term;
intrinsic IsLinear(f::MapSch) -> BoolElt
{True iff f is a morphism defined by linear polynomials}
    A := Ambient(Domain(f));
    B := Ambient(Codomain(f));
    if (Type(A) eq Aff and Type(B) eq Aff) or
	(Type(A) eq Aff and ISA(Type(B),Prj)) then
	return IsPolynomial(f) and
	    &and[ (TotalDegree(p) eq 1 or p eq 0) and constant_term(p) eq 0 :
		p in DefiningPolynomials(f) ];
    else
	return IsPolynomial(f) and
	    TotalDegree(DefiningPolynomials(f)[1]) eq 1 and IsRegular(f);
    end if;
end intrinsic;

function constant_term(p)
    return Evaluate(p,[ 0 : i in [1..Rank(Parent(p))]]);
end function;

intrinsic IsAffineLinear(f::MapSch) -> BoolElt
{True iff f is defined by polynomials of degree at most one}
    return IsPolynomial(f) and
	&and[ TotalDegree(fi) le 1 : fi in DefiningPolynomials(f) ];
end intrinsic;

intrinsic IsDominant(f::MapSch) -> BoolElt
{True iff f is dominant}
    B := Codomain(f);
    if Dimension(Domain(f)) lt Dimension(B) then
	return false;
    else
	return Radical(DefiningIdeal(Image(f))) eq Radical(DefiningIdeal((B)));
    end if;
end intrinsic;

