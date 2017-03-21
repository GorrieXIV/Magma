freeze;

intrinsic UniversalMap(C::Cop, S::Str, Q::[Map]) -> Map
{The universal map from C to S given by Q}

    require #C eq #Q: "Argument 3 should have length", #C;

    for i := 1 to #C do
	f := Q[i];

	require Domain(f) cmpeq Constituent(C, i):
		"Domain of map number", i,
		"does not equal corresponding constituent";

	require Codomain(f) cmpeq S:
		"Codomain of map number", i,
		"does not equal argument 2";
    end for;

    return map<C -> S | x :-> Q[Index(x)](Retrieve(x))>;
end intrinsic;
