freeze;

////////////////////////////////////////////////////////////////////////
//        Constructors for Clusters from Collections of Points        //
////////////////////////////////////////////////////////////////////////

intrinsic Cluster(P::{Pt}) -> Clstr
    {The cluster supported on the given point or points,
    inside S (when given) or the ambient space.}
    return Cluster(A,P) where A is Ambient(Scheme(Universe(P)));
end intrinsic;

intrinsic Cluster(P::SetIndx) -> Clstr
    {"} // "
    require not IsNull(P) : "Argument 2 must have non-null universe.";
    require ElementType(Universe(P)) eq Pt :
        "Argument 2 must be a set of scheme points."; 
    A := Ambient(Scheme(Universe(P)));
    return Cluster(A,{ Universe(P) | p : p in P });
end intrinsic;

intrinsic Cluster(S::Sch,P::SetIndx) -> Clstr
    {"} // "
    require not IsNull(P) : "Argument 2 must have non-null universe.";
    require ElementType(Universe(P)) eq Pt :
        "Argument 2 must be a set of scheme points."; 
    require P subset S:
       "Elements of argument 2 must lie on argument 1.";
    return Cluster(S,{ Universe(P) | p : p in P });
end intrinsic;

intrinsic Cluster(S::Sch,P::{Pt}) -> Clstr
    {"} // "
    require P subset S:
       "Elements of argument 2 must lie on argument 1.";
    if #P eq 0 then
	return EmptySubscheme(S);
    elif #P eq 1 then
	return Cluster(S,Representative(P));
    else
	A := Ambient(S);
	require HasGroebnerBasis(A):
	    "Groebner basis methods required but unavailable";
	clusters := [ Cluster(S,p) : p in P ];
	Z := clusters[1];
	for qq in clusters[2..#clusters] do
	    Z := Union(Z,qq);
	end for;
	_,Z := IsCluster(Z);
	return Z;
    end if;
end intrinsic;
