freeze;

intrinsic ChangeRing(M::ModED, S::Rng) -> ModRng, Map
{Given a module M with base ring R, together with a ring S,
construct the module N with base ring S obtained by coercing
the components of elements of M into N, together with the homomorphism
from M to N};

    R := BaseRing(M);
    N := RModule(S, Dimension(M));
    return N, hom<M -> N | x :-> N ! Eltseq(x), y :-> M ! Eltseq(y)>;
end intrinsic;

intrinsic ChangeRing(M::ModED, S::Rng, f::Map) -> ModRng, Map
{Given a module M with base ring R, together with a ring S, and a
homomorphism f: R -> S, construct the module N with base ring S
obtained by mapping the components of elements of M into N by f,
together with the homomorphism from M to N};

    R := BaseRing(M);
    N := RModule(S, Dimension(M));
    return N,
	hom<M -> N | x :-> N ! f(Eltseq(x)), y :-> M ! Eltseq(y)@@f>;
end intrinsic;

intrinsic Submodules(M::ModRng: CodimensionLimit := Dimension(M)) -> []
{Return all the submodules of M as a sequence (sorted by dimension)}
    if Dimension(M) eq 0 then
	return [M];
    end if;
    L := SubmoduleLattice(M: CodimensionLimit := CodimensionLimit);
    Q := [Module(L!i): i in [1 .. #L]];
    d := Dimension(M);
    if CodimensionLimit lt d then
	// Safety filter for irreducible case:
	Q := [M: M in Q | Dimension(M) + CodimensionLimit ge d];
    end if;
    Sort(~Q, func<x,y|Dimension(x) - Dimension(y)>);
    return Q;
end intrinsic;

// Synonym for consistency with other types
intrinsic DirectSumDecomposition(M::ModRng) -> SeqEnum
{The indecomposable summands of the module M}
    return IndecomposableSummands(M);
end intrinsic;

intrinsic DirectSum( M::ModAlg, N::ModAlg ) -> ModAlg
{The direct sum of M and N}
	A := Algebra(M);
	require A cmpeq Algebra(N) : "Modules must be over the same algebra";

	left := IsLeftModule(M);
	require left eq IsLeftModule(N) : "Modules must act on same side";

	R := BaseRing(M);
	d := Dimension(M);  e := Dimension(N);
	V := RModule( R, d+e );
  
	if left then
		act := func< v, a | a^v >;
		return Module(A,
			map< CartesianProduct(A, V)-> V | t :-> V!(Eltseq(av1) cat Eltseq(av2))
			where av1 := act(M!v1, a) where av2 := act(N!v2, a) 
			where v1 := ev[1..d] where v2 := ev[d+1..d+e]
			where ev := Eltseq(t[2]) where a := t[1] >);
	else
		act := func< v, a | v^a >;
		return Module(A,
			map< CartesianProduct(V, A)-> V | t :-> V!(Eltseq(av1) cat Eltseq(av2))
			where av1 := act(M!v1, a) where av2 := act(N!v2, a) 
			where v1 := ev[1..d] where v2 := ev[d+1..d+e]
			where ev := Eltseq(t[1]) where a := t[2] >);
	end if;
	  
end intrinsic;


intrinsic IsProjective(M::ModGrp) -> BoolElt
{Returns true if the KG-module M is projective}

    // JF Carlson, 2016

    require IsField(BaseRing(M)): "Coefficient ring must be a field";

    G := Group(M);
    p := Characteristic(BaseRing(M));
    if p eq 0 then
	    return true;
    end if;

    if not IsDivisibleBy(#G,p) then
	    return true;
    end if;

    S := Sylow(G,Characteristic(BaseRing(M)));
    if not IsDivisibleBy(Dimension(M),#S) then
       return false;
    end if;

    MM := Restriction(M,S);
    nn := Dimension(M) div #S;
    V := &+[RowSpace(Action(MM).i- Action(MM)!1): i in [1 .. Ngens(S)]];

    return Dimension(M) - Dimension(V) eq nn;

end intrinsic;
