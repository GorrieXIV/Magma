freeze;


AddAttribute(NilpOrbAlgLie, "R");

intrinsic CreateNilpOrbAlgLie(R::RootDtm) -> NilpOrbAlgLie
{ Create }
	x := HackobjCreateRaw(NilpOrbAlgLie);
	x`R := R;
	
	return x;
end intrinsic;

intrinsic HackobjPrintNilpOrbAlgLie(x::NilpOrbAlgLie, level::MonStgElt)
{ Print x }
	printf "Nilpotent orbit in Lie algebra of type %o", CartanName(x`R);
end intrinsic;

intrinsic HackobjCoerceNilpOrbAlgLie(x::NilpOrbAlgLie, y::.) -> BoolElt, .
{ Coerce y into x}
	return false, "Illegal coercion";
end intrinsic;

intrinsic HackobjInNilpOrbAlgLie(x::., y::NilpOrbAlgLie) -> BoolElt
{ Return whether x is in y }
	
	//'require' statements should check that x has valid type.

	return false;
end intrinsic;

