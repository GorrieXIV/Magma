freeze;

///////////////////////////////////////////////////////////////////////
// linsys.m
///////////////////////////////////////////////////////////////////////

intrinsic BaseScheme(L::LinearSys) -> Sch
{The base scheme of L}
    return Scheme(Ambient(L),Sections(L));
end intrinsic;

intrinsic BasePoints(L::LinearSys) -> SetEnum
{The points of the base scheme of L defined over the extension K of the
base ring (or the base ring itself if K is omitted) if the base scheme
is zero-dimensional}
    bool, Z := IsCluster(BaseScheme(L));
    require bool: "Base scheme of argument is not zero-dimensional";
    return RationalPoints(Z);
end intrinsic;

intrinsic BasePoints(L::LinearSys,K::Rng) -> SetEnum
{"} // "
    bool, Z := IsCluster(BaseScheme(L));
    require bool: "Base scheme of argument is not zero-dimensional";
    return RationalPoints(Z,K);
end intrinsic;

intrinsic IsBasePointFree(L::LinearSys) -> BoolElt
{True iff the hypersurfaces of L have no common geometric points}
    return IsEmpty(BaseScheme(L));
end intrinsic;

intrinsic IsFree(L::LinearSys) -> BoolElt
{True iff the hypersurfaces of L have no common geometric points}
    return IsEmpty(BaseScheme(L));
end intrinsic;

intrinsic BaseComponent(L::LinearSys) -> Sch
{The hypersurface common to all elements of L}
    ss := Sections(L);
    if #ss eq 0 then
        return EmptyScheme(Ambient(L));
    end if;
    g := GCD(ss);
    if TotalDegree(g) eq 0 then
        return EmptyScheme(Ambient(L));
    else
        return Scheme(Ambient(L),g);
    end if;
end intrinsic;
 
intrinsic Complement(L::LinearSys,S::Sch) -> LinearSys
{A complement in L to the space of sections which contain the hypersurface S}
    require IsHypersurface(S):
        "The scheme must be a hypersurface";
    P := Ambient(L);
    require Ambient(S) eq P:
        "Arguments lie in different spaces";
    deg_diff := Degree(L) - Degree(S);
    if deg_diff lt 0 then
        return L;
    end if;
    return LinearSystem(L,Complement(VL,bad_space))
        where bad_space is sub< VL | [ CoefficientMap(L)(p) : p in poly_span ]>
        where poly_span is [ f*m : m in MonomialsOfDegree(Parent(f),deg_diff) ]
        where VL is CoefficientSpace(L)
        where f is Polynomial(S);
end intrinsic;

