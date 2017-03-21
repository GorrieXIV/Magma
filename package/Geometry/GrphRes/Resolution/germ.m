freeze;

///////////////////////////////////////////////////////////////////////
// germ.m
// Simulate a 'singularity germ' type.
///////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////
//			Creation
///////////////////////////////////////////////////////////////////////

intrinsic Germ(p::Pt,C::Crv) -> Pt
{The germ of p as a point of C}
    require p in C:
	"Point does not lie on curve";
    return C ! p;
end intrinsic;

intrinsic IsGerm(p::Pt) -> BoolElt
{Return true iff p is a point on a curve}
    return ISA(Type(Scheme(p)),Crv);
end intrinsic;


///////////////////////////////////////////////////////////////////////	
//			Attribute retrieval
///////////////////////////////////////////////////////////////////////	

intrinsic AffineRepresentative(p::Pt) -> Pt,Crv
{A point and an affine curve which represent the germ p}
    require IsGerm(p): "Point is not a germ";
    C := Curve(p);
    if not IsAffine(C) then
	 C1 := CentredAffinePatch(C,p);
	 return C1 ! Origin(Ambient(C1)),C1;
    else
	return p,C;
    end if;
end intrinsic;

intrinsic ProjectiveRepresentative(p::Pt) -> Pt,Crv
{A point and an projective curve which represent p}
    require IsGerm(p): "Point is not a germ";
    C := Curve(p);
    if IsAffine(C) then
	C1 := ProjectiveClosure(C);
	return C1 ! p,C1;
    else
	return p,C;
    end if;
end intrinsic;

intrinsic BaseBlowupContribution(p::Pt) -> RngIntElt
{Minus the number of blowups that the x-axis suffers on extracting
the resolution spine}
    require IsGerm(p): "Point is not a germ";
    return BaseBlowupContribution(ResolutionSpine(p));
end intrinsic;

intrinsic NeighbouringGerms(p::Pt) -> SeqEnum
{A list of the germs that lie on the first toric neighbourhood of p}
    require IsGerm(p): "Point is not a germ";
    return NeighbouringGerms(ResolutionSpine(p));
end intrinsic;

intrinsic DualGraphMultiplicities(p::Pt) -> SeqEnum
{The sequence of multiplicities of exceptional curves in the total
pullback of p along its first toric neighbourhood}
    require IsGerm(p): "Point is not a germ";
    return Multiplicities(ResolutionSpine(p));
end intrinsic;

intrinsic DualGraphCanonical(p::Pt) -> SeqEnum
{The sequence of multiplicities of exceptional curves in the canonical
class along the first toric neighbourhood of p}
    require IsGerm(p): "Point is not a germ";
    return CanonicalClass(ResolutionSpine(p));
end intrinsic;

intrinsic Selfintersections(p::Pt) -> SeqEnum
{The sequence of selfintersections of exceptional curves in
the resolution spine of p}
    require IsGerm(p): "Point is not a germ";
    return Selfintersections(ResolutionSpine(p));
end intrinsic;

