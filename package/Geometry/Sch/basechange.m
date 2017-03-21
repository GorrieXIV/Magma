freeze;

///////////////////////////////////////////////////////////////////////
// basechange.m
// April 2001 GDB
///////////////////////////////////////////////////////////////////////

// X is a scheme with base ring k. m : k -> K is a ring map which is
// coercion if K appears alone among the arguments.
// The basic intrinsics
//	BaseChange(X,K);
//	BaseChange(X,m);
// are in the kernel.
// The idea is to make a new scheme whose DefiningPolynomials are those of X but
// having undergone coefficient change by the map m.
//
// Two extra things are done here.
// 1. BaseChange to a nominated ambient space, possibly also with a map.
// 2. BaseChange of a sequence to ensure a common ambient space.
// Note that BaseExtend is a synonym for BaseChange.
//
// 2001/08/30: ChangeRing imported.
// ChangeRing allows base change by coercion of DefiningPolynomials where the
// base ring does not have a homomorphism into the new base.
///////////////////////////////////////////////////////////////////////

intrinsic ChangeRing(X::Sch, R::Rng) -> Sch
    {Returns a scheme defined by the DefiningPolynomials of X interpreted
    over R using the default coercion.}

    n := Dimension(Ambient(X));
    if IsProjective(X) then n +:= 1; end if;
    bool := CanChangeUniverse(DefiningPolynomials(X),PolynomialRing(R,n));
    require bool :
        "Argument 1 can not be coerced to scheme over argument 2.";
    return BaseChange(X, Coercion(BaseRing(X), R));
end intrinsic;

intrinsic BaseChange(S::Sch,A::Sch) -> Sch
{A is an ambient affine or projective scheme matching that of S but possibly
having a different base ring. Return the scheme defined by the DefiningPolynomials of
S in A subject to coercion of coefficients or the coefficient map m}
    AS := Ambient(S);
    require Gradings(AS) eq Gradings(A) and Dimension(AS) eq Dimension(A):
        "The second argument is not similar to the ambient space of the first";
    E := [ h(f) : f in DefiningPolynomials(S) ]
        where h is hom< CoordinateRing(AS) -> CoordinateRing(Ambient(A)) |
                                [ A.i : i in [1..Length(A)]] >;
    if ISA(Type(S), Crv) then
	return Curve(Ambient(A),E);
    else
	return Scheme(A,E);
    end if;
    // Note the Ambient(A) to ensure cod(h) is a poly ring rather than a
    // trivial quotient ring.
end intrinsic;

intrinsic BaseChange(S::Sch,A::Sch,m::Map) -> Sch
    {"} // "
    AS := Ambient(S);
    require Gradings(AS) eq Gradings(A) and Dimension(AS) eq Dimension(A):
        "The second argument is not similar to the ambient space of the first";
    require Domain(m) eq BaseRing(AS) and Codomain(m) eq BaseRing(A):
	"The third argument does not map the base ring of the first to that "
				    * "of the second";
    E := [ h(f) : f in DefiningPolynomials(S) ]
        where h is hom< CoordinateRing(AS) -> CoordinateRing(Ambient(A)) |
                                m, [ A.i : i in [1..Length(A)]] >;
    if ISA(Type(S), Crv) then
	return Curve(Ambient(A),E);
    else
	return Scheme(A,E);
    end if;
end intrinsic;

/*
DON'T define both BaseChange AND BaseExtend -- they are identified at the bind level!

intrinsic BaseExtend(S::Sch,A::Sch) -> Sch
{"} // "
    AS := Ambient(S);
    require Gradings(AS) eq Gradings(A) and Dimension(AS) eq Dimension(A):
        "The second argument is not similar to the ambient space of the first";
    E := [ h(f) : f in DefiningPolynomials(S) ]
        where h is hom< CoordinateRing(AS) -> CoordinateRing(Ambient(A)) |
                                [ A.i : i in [1..Length(A)]] >;
    if ISA(Type(S), Crv) then
	return Curve(Ambient(A),E);
    else
	return Scheme(A,E);
    end if;
    // Note the Ambient(A) to ensure cod(h) is a poly ring rather than a
    // trivial quotient ring.
end intrinsic;

intrinsic BaseExtend(S::Sch,A::Sch,m::Map) -> Sch
{"} // "
    AS := Ambient(S);
    require Gradings(AS) eq Gradings(A) and Dimension(AS) eq Dimension(A):
        "The second argument is not similar to the ambient space of the first";
    require Domain(m) cmpeq BaseRing(A) and Codomain(m) cmpeq BaseRing(AS):
	"The third argument does not map the base ring of the first to that "
				    * "of the second";
    E := [ h(f) : f in DefiningPolynomials(S) ]
        where h is hom< CoordinateRing(AS) -> CoordinateRing(Ambient(A)) |
                                m, [ A.i : i in [1..Length(A)]] >;
    if ISA(Type(S), Crv) then
	return Curve(Ambient(A),E);
    else
	return Scheme(A,E);
    end if;
end intrinsic;
*/

intrinsic BaseChange(F::[Sch],K::Rng) -> SeqEnum
{The base change of the schemes in the sequence F by coercion of the
base rings or the map m of base rings}
    require IsComplete(F):
        "First argument must be a complete sequence";
    require #F ne 0:
        "First argument must be a nonempty sequence";
    A := Ambient(F[1]);
    require &and[ Ambient(F[j]) eq A : j in [2..#F] ]:
        "Schemes in the sequence must lie in a common ambient space";
    return [ BaseChange(S,B) : S in F ]
		where B is BaseChange(A,K);
end intrinsic;
 
intrinsic BaseChange(F::[Sch],m::Map) -> SeqEnum
{"} // "
    require IsComplete(F):
        "First argument must be a complete sequence";
    require #F ne 0:
        "First argument must be a nonempty sequence";
    A := Ambient(F[1]);
    require &and[ Ambient(F[j]) eq A : j in [2..#F] ]:
        "Schemes in the sequence must lie in a common ambient space";
    return [ BaseChange(S,B,m) : S in F ]
    		where B is BaseChange(A,m);
end intrinsic;

/*
DON'T define both BaseChange AND BaseExtend -- they are identified at the bind level!

intrinsic BaseExtend(F::[Sch],K::Rng) -> SeqEnum,MapSch
{"} // "
    require IsComplete(F):
        "First argument must be a complete sequence";
    require #F ne 0:
        "First argument must be a nonempty sequence";
    A := Ambient(F[1]);
    require &and[ Ambient(F[j]) eq A : j in [2..#F] ]:
        "Schemes in the sequence must lie in a common ambient space";
    return [ BaseChange(S,B) : S in F ]
		where B is BaseChange(A,K);
end intrinsic;
 
intrinsic BaseExtend(F::[Sch],m::Map) -> SeqEnum,MapSch
{"} // "
    require IsComplete(F):
        "First argument must be a complete sequence";
    require #F ne 0:
        "First argument must be a nonempty sequence";
    A := Ambient(F[1]);
    require &and[ Ambient(F[j]) eq A : j in [2..#F] ]:
        "Schemes in the sequence must lie in a common ambient space";
    return [ BaseChange(S,B,m) : S in F ]
    		where B is BaseChange(A,m);
end intrinsic;
*/
