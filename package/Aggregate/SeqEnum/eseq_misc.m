freeze;

intrinsic '&join'(S::{SetMulti}) -> SetMulti
{ The join of all elements of S }
    ret := {* *};
    for i in S do
        ret := ret join i;
    end for;
    return ret;
end intrinsic;

intrinsic '&join'(S::[SetMulti]) -> SetMulti
{ The join of all elements of S }
    if #S eq 0 then return {* *}; end if;
    ret := S[1];
    for i in [2..#S] do
        ret := ret join S[i];
    end for;
    return ret;
end intrinsic;

function reduct(S, op, allow_empty, id, ids)
    if IsNull(S) then
	return false, "Illegal null set/sequence";
    end if;

    if #S eq 0 then
	if allow_empty then
	    l, s := IsCoercible(Universe(S), id);
	    if l then
		return true, s;
	    end if;
	    return false, Sprintf("Universe has no %s element", ids);
	else
	    return false, "Illegal empty set/sequence";
	end if;
    end if;

    // Try/catch inserted to tidy up the error message
    try
	first := true;
	for x in S do
	    if first then
		s := x;
		first := false;
	    else
		s := op(s, x);
	    end if;
	end for;
    catch E
	// Produce a more pleasant error message if the operation is not
	// defined on the setq element type:
	if E`Type eq "Err"
	and Regexp("Runtime error.*: Bad argument types", E`Object)
	then
	    return false, "Operation not defined on elements of type " cat Sprint(Type(s));
	end if;
	// Otherwise throw the error again
	error E;
    end try;

    return true, s;
end function;

intrinsic InternalAdd(S::Setq) -> .
{The sum of all elements of S}
    l, s := reduct(S, '+', true, 0, "zero");
    require l: s;
    return s;
end intrinsic;

intrinsic '&+'(S::Setq) -> .
{The sum of all elements of S}
    return InternalAdd(S);
end intrinsic;

intrinsic InternalMult(S::Setq) -> .
{The product of all elements of S}
    l, s := reduct(S, '*', true, 1, "one");
    require l: s;
    return s;
end intrinsic;

intrinsic '&*'(S::Setq) -> .
{The product of all elements of S}
    return InternalMult(S);
end intrinsic;

intrinsic '&meet'(S::Setq) -> .
{The intersection of all elements of S}
    l, s := reduct(S, 'meet', false, 0, 0);
    require l: s;
    return s;
end intrinsic;

intrinsic '&join'(S::Setq) -> .
{The union of all elements of S}
    l, s := reduct(S, 'join', false, 0, 0);
    require l: s;
    return s;
end intrinsic;

intrinsic Flat(S::SeqEnum : Depth := Infinity()) -> SeqEnum
{Returns the flattened version of S.}
    require Depth ge 0: "Depth must be non-negative";

    while Depth gt 0 and not IsEmpty(S) and Type(S[1]) eq SeqEnum do
	S := &cat S;
	Depth -:= 1;
    end while;
    return S;
end intrinsic;

function is_zero(S)
    try
        for s in S do
            if not IsZero(s) then
                return true,false;
            end if;
        end for;
    catch e;
        return false,"Operation not defined on elements of type " cat
            Sprint(Type(S[1])) cat ".";
    end try;
    return true,true;
end function;

intrinsic IsZero( S::SeqEnum ) -> BoolElt
{True iff IsZero(x) is true for every element x in the sequence S}
    success,bool:=is_zero(S);
    require success: bool;
    return bool;
end intrinsic;
