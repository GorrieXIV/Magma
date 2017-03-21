freeze;

///////////////////////////////////////////////////////////////////////
// comparison.m
// April 2001 GDB
///////////////////////////////////////////////////////////////////////

intrinsic 'subset'(X::Sch,Y::Sch) -> BoolElt
{Same as IsSubscheme(X,Y)}
    return IsSubscheme(X,Y);
end intrinsic;


intrinsic IsSubscheme(X::Sch,Y::Sch) -> BoolElt
{True iff the scheme X is a subscheme of the scheme Y, 
in the same ambient space.}
    // trivial checks:
    // if they live in different ambients, then false.
    if Ambient(X) ne Ambient(Y) then 
        return false;
    end if;
    // if Y is the ambient, then true.
    if IsAmbient(Y) or &and[IsZero(equ) : equ in Equations(Y)] then 
        return true;
    end if;
    // since by now Y is not eq to ambient, if X is ambient,
    // then false.
    if IsAmbient(X) or &and[IsZero(equ) : equ in Equations(X)] then 
        return false;
    end if;
    // THINK (JaBuczyn): I would compare the dimensions first,
    // this should be cheap.
    // THINK (JaBuczyn): I would try to make cheap test,
    // if equations of Y are subset of equations of X...
    if IsHypersurface(X) and IsHypersurface(Y) then
        // THINK: this isn't going to work in ToricGeometry.
        // IsHypersurface seems to be an expensive check,
        // compared to what is needed in this case...
	return IsDivisibleBy(Polynomial(Y),Polynomial(X));
    end if;
    require HasGroebnerBasis(X) and HasGroebnerBasis(Y):
	"Groebner basis methods required but unavailable";
    // THINK (JaBuczyn): I would rather saturate both ideals,
    // rather then calculate the Difference(X,Y).
    if IsAffine(X) and IsAffine(Y) then
         return DefiningIdeal(Y) subset DefiningIdeal(X);
    end if;
    return IsEmpty(Difference(X, Y));
end intrinsic;

