freeze;

/* 
 * Dan Roozemond, 2010. 
 */

quo_with_pullback := function(L, I)
	local b, phi, pullback, LHSphi, LmodI, T, ok, ns;

	LmodI, phi := quo<L|I>;

	LHSphi := Matrix([ phi(L!b) : b in Basis(L) ]);

	pullback := function(x)
		local RHS;

		V := VectorSpace(BaseRing(L), Dimension(L));
		RHS := Vector(LmodI!x);

		ok, sol, ns := IsConsistent(LHSphi, RHS);
		if not ok then return false; end if;

		return L!Vector(sol), sub<V | ns>;
	end function;
	
	pullback_subalg := function(x)
		local y,ns;
		y,ns := pullback(x);
		return sub<L | [y] cat [ L!b : b in Basis(ns)]>;
	end function;

	return LmodI, 
		map<L -> LmodI | x :-> LmodI!phi(x)>, 
		pullback,
		pullback_subalg;
end function;

intrinsic QuotientWithPullback(L::AlgLie, I::AlgLie) -> AlgLie, Map, UserProgram, UserProgram
{ L/I, x in L -> x in L/I, x in L/I -> x in L, and x in L/I -> subalgebra of L}
	return quo_with_pullback(L, I);
end intrinsic;
