freeze;

///////////////////////////////////////////////////////////////////////
// hypersurface.m
// April 2001 GDB
///////////////////////////////////////////////////////////////////////

intrinsic IsHypersurface(X::Sch) -> BoolElt,RngMPolElt
{True iff X can be defined by a single equation, in which case also
return the defining equation}
    E := DefiningPolynomials(X);
    if forall{f : f in E | f eq 0} then
        return false,_;
    elif #E gt 1 then
	require HasGroebnerBasis(X):
	    "Groebner basis methods not available for this scheme";
	IX := EasyIdeal(DefiningIdeal(X));
        E := GroebnerBasis(IX);
        if #E gt 1 then
            return false,_;
        end if;
    end if;
    f := CoordinateRing(Ambient(X)) ! E[1];
    deg := TotalDegree(f);
    if deg le 0 then
        return false,_;
    else
        return true,f;
    end if;
end intrinsic;
 
intrinsic DefiningPolynomial(X::Sch) -> RngMPolElt
{The polynomial defining the hypersurface X.}
    b,f := IsHypersurface(X);
    require b: "Argument is not a hypersurface.";
    return f;
end intrinsic;
 
intrinsic CommonComponent(X::Sch,Y::Sch) -> BoolElt
{The hypersurface which is a common component of X and Y}
    require IdenticalAmbientSpace(X,Y):
	"Arguments lie in different ambient spaces";
    require IsHypersurface(X) and IsHypersurface(Y):
	"Arguments are not hypersurfaces";
    require HasGCD(X):
	"GCD methods are not available for this calculation";
    gcd := GCD(Polynomial(X),Polynomial(Y));
    A := Ambient(X);
    if TotalDegree(gcd) ge 1 and Type(X) eq Crv then
	return Curve(A,gcd);
    else
	return Scheme(A,gcd);
    end if;
end intrinsic;

intrinsic NoCommonComponent(X::Sch,Y::Sch) -> BoolElt
{True iff the hypersurfaces X and Y do not have a common irreducible component}
    require IdenticalAmbientSpace(X,Y):
	"Arguments lie in different ambient spaces";
    require IsHypersurface(X) and IsHypersurface(Y):
	"Arguments are not hypersurfaces";
    require HasGCD(X):
	"GCD methods are not available for this calculation";
    gcd :=  GCD(Polynomial(X),Polynomial(Y));
    return gcd eq Parent(gcd) ! 1;
end intrinsic;

