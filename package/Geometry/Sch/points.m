freeze;

///////////////////////////////////////////////////////////////////////
// points.m
//	Test for the existence of points over extensions of the base field.
//	Find a nonsingular point of a scheme over a finite field.
///////////////////////////////////////////////////////////////////////

intrinsic IsRationalPoint(p::Pt) -> BoolElt,Pt
{True iff p lies in the base ring point set of X (or the scheme on which it
lies if the second argument is omitted) or it can be coerced there.
In that case, also return p coerced into the base ring point set}
    X := Scheme(p);
    bool,p1 := IsCoercible(X(BaseRing(X)),p);
    if bool then
	return bool,p1;
    else
	return bool,_;
    end if;
end intrinsic;

intrinsic IsRationalPoint(X::Sch,p::Pt) -> BoolElt,Pt
{"} // "
    bool,p1 := IsCoercible(X(BaseRing(X)),p);
    if bool then
	return bool,p1;
    else
	return bool,_;
    end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//		Points over extensions?
///////////////////////////////////////////////////////////////////////

intrinsic HasPointsOverExtension(X::Sch) -> BoolElt
{True unless the scheme X is zero-dimensional and all points of X are
defined over the base field.}
    require HasGroebnerBasis(X):
        "Groebner basis methods required but unavailable";
    if IsEmpty(X) then
	return false;
    end if;
    b,Z := IsCluster(X);
    if not b then
	// X is not zero-dimensional so certainly has points over an extension.
	return true;
    end if;
    // The following distinction is necessary since Radical doesn't work
    // for a nonzero-dimensional ideal over a nonperfect field.
    // Projective clusters have such ideals.
    if IsAffine(X) then
	return DefiningIdeal(Cluster(RationalPoints(Z))) ne Radical(DefiningIdeal(X));
    else
	return &or[ HasPointsOverExtension(AffinePatch(X,i)) : i in [1..n] ]
		where n is NumberOfAffinePatches(X);
    end if;	    
end intrinsic;

intrinsic HasPointsOverExtension(X::Sch,L::Rng) -> BoolElt
{True unless the scheme X is zero-dimensional and all points of X are
defined over the field L.}
    // The first tests and requirements are easy.
    require HasGroebnerBasis(X):
        "Groebner basis methods required but unavailable";
    if IsEmpty(X) then
	return false;
    end if;
    b,Z := IsCluster(X);
    if not b then
	// X is not zero-dimensional so certainly has points over an extension.
	return true;
    end if;
    // Now solve the problem by basechanging and using the previous
    // absolute version of the function.
    return HasPointsOverExtension(BaseChange(X,L));
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Nonsingular point
///////////////////////////////////////////////////////////////////////

intrinsic HasNonsingularPoint(X::Sch,L::FldFin) -> BoolElt,Pt
    {True iff X contains a nonsingular point defined over L, 
    in which case returns such a point}
    FF := BaseRing(X);
    require Type(FF) eq FldFin : 
	"Base ring of the argument must be a finite field";
    require IsDivisibleBy(#L,#FF):
	"Argument field is not an algebra over the base field";
    if IsEmpty(X) then
	return false,_;
    end if;
    if Type(Ambient(X)) eq Aff then
	for tuple in CartesianPower(L,Length(X)) do
	    b,p := IsCoercible(X,[tuple[i] : i in [1..#tuple]]);
	    if not b then
		continue tuple;
	    elif IsNonsingular(X,p) then
		return true,p;
	    end if;
	end for;
	return false,_;
    else
	require IsOrdinaryProjective(X):
	    "Scheme must be defined in ordinary affine or projective space";
	P := Ambient(X);
	AD,pt := AffineDecomposition(P);
	b,p := IsCoercible(X,pt);
	if b and IsNonsingular(X,p) then
	    return true,p;
	end if;
	Reversion(~AD);
	for phi in AD do
	    b,p := HasNonsingularPoint(X@@phi);
	    if not b then
		continue phi;
	    else
		return true,X!phi(p);
	    end if;
	end for;
	return false,_;
    end if;
end intrinsic;

intrinsic HasNonsingularPoint(X::Sch) -> BoolElt,Pt
    {True iff X contains a nonsingular point defined over the finite
    base field of X, in which case returns such a point}
    FF := BaseRing(X);
    require Type(FF) eq FldFin : 
	"Base ring of the argument must be a finite field";
    return HasNonsingularPoint(X,FF);
end intrinsic;

