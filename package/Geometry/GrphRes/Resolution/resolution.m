freeze;

///////////////////////////////////////////////////////////////////////
// resolution.m
//	Headers for resolution routines
///////////////////////////////////////////////////////////////////////

intrinsic ResolutionGraph(C::Crv,p::Pt: M:=1, K:=1) -> GrphRes
{The dual graph of the minimal transverse resolution of the singularity p of C}
    b,p := IsCoercible(C,p);
    require b and IsRationalPoint(C,p):
	"Second argument must be a rational point on the first argument";
    require IsSingular(C,p):
	"Point is not singular on curve";
    require K in { 0,1 } and M in { 0,1 }:
	"Parameters lie in { 0,1 }";
    if IsAffine(C) then
	C := ProjectiveClosure(C);
	p := C ! p;
    end if;
    g := RecursiveGrphRes(C,p);
    if M eq 1 then
	CalculateMultiplicities(~g);
    end if;
    if K eq 1 then
	CalculateCanonicalClass(~g);
    end if;
    return g;
end intrinsic;

intrinsic ResolutionGraph(C::Crv) -> GrphRes
{"} // "
    require Type(Ambient(C)) eq Aff:
	"Argument must be an affine curve with a singularity at the origin";
    p := Origin(Ambient(C));
    require IsSingular(C,p):
	"Point is not singular on curve";
    G := ResolutionGraph(C,p: K:=1,M:=1);
    return G;
end intrinsic;

