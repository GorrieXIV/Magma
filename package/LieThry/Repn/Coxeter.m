freeze;

/* Bruhat Ordering */
// SHM: I have shortened the in-line documentation and removed the "_" from the
// intrinsic name, to conform with Magma's naming conventions

/* Ported some functions to C-level -- see src/grp_fp/coxeter_bruhat.c */

intrinsic BruhatLessOrEqual(x::GrpFPCoxElt, y::GrpFPCoxElt) -> BoolElt
{True iff x is less than y in the Bruhat ordering}
	W := Parent(x);
    require Parent(y) eq W : "Arguments must be elements of the same coxeter group";
	return BruhatLessOrEqual(W, x, y);
end intrinsic;


intrinsic BruhatLessOrEqual(x::GrpPermElt, y::GrpPermElt) -> BoolElt
{True iff x is less than y in the Bruhat ordering (only applies to Coxeter group elements)}
	W := Parent(x);
    require Parent(y) eq W : "Arguments must be elements of the same coxeter group";

	Wfp, phi := CoxeterGroup(GrpFPCox, W);
	return BruhatLessOrEqual(Wfp, phi(x), phi(y));
end intrinsic;

intrinsic BruhatLessOrEqual(x::GrpMatElt, y::GrpMatElt) -> BoolElt
{True iff x is less than y in the Bruhat ordering (only applies to Coxeter group elements)}
	W := Parent(x);
    require Parent(y) eq W : "Arguments must be elements of the same coxeter group";

	Wfp, phi := CoxeterGroup(GrpFPCox, W);
	return BruhatLessOrEqual(Wfp, phi(x), phi(y));
end intrinsic;


intrinsic BruhatDescendants(x::GrpFPCoxElt : z := false) -> SetEnum
{ The set of Bruhat descendents v of x }
	if z cmpeq false then
		return InternalBruhatDescendants(x);
	else
	    require z cmpeq false or Parent(z) eq Parent(x) : "Arguments must be elements of the same coxeter group";
		return InternalBruhatDescendants(x, z);
	end if;
end intrinsic;

intrinsic BruhatDescendants(X::{GrpFPCoxElt} : z := false) -> SetEnum
{ The set of Bruhat descendents v of x }

	if z cmpeq false then
		return &join{ InternalBruhatDescendants(x) : x in X };
	else
	    require z cmpeq false or Parent(z) eq Universe(X) : "Arguments must be elements of the same coxeter group";
		return &join{ InternalBruhatDescendants(x, z) : x in X };
	end if;
end intrinsic;

intrinsic BruhatDescendants(x::GrpPermElt : z := false) -> SetEnum
{ The set of Bruhat descendents v of x }
  
    W := Parent(x);
	require Type(W) eq GrpPermCox : "x must be a Coxeter group element";

	Wfp, h := CoxeterGroup(GrpFPCox, W);
	
	if z cmpeq false then
		desc := InternalBruhatDescendants(h(x));
	else
		require Parent(z) eq W : "Arguments must be elements of the same coxeter group";
		desc := InternalBruhatDescendants(h(x), h(z));
    end if;

	return { d @@ h : d in desc };
end intrinsic;

intrinsic BruhatDescendants(X::{GrpPermElt} : z := false) -> SetEnum
{ The set of Bruhat descendents v of x }
  
	return &join{ BruhatDescendants(x : z := z) : x in X };
end intrinsic;


intrinsic BruhatDescendants(x::GrpMatElt : z := false) -> SetEnum
{ The set of Bruhat descendents v of x }
  
    W := Parent(x);

	Wfp, h := CoxeterGroup(GrpFPCox, W);
	
	if z cmpeq false then
		desc := InternalBruhatDescendants(h(x));
	else
		require Parent(z) eq W : "Arguments must be elements of the same coxeter group";
		desc := InternalBruhatDescendants(h(x), h(z));
    end if;

	return { d @@ h : d in desc };
end intrinsic;

intrinsic BruhatDescendants(X::{GrpMatElt} : z := false) -> SetEnum
{ The set of Bruhat descendents v of x }
  
	return &join{ BruhatDescendants(x : z := z) : x in X };
end intrinsic;

