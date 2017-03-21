freeze;

intrinsic Multiset(S::Setq) -> SetMulti
{The multiset derived from S}
    if IsNull(S) then
	return {* *};
    else
	return {* Universe(S) | x : x in S *};
    end if;
end intrinsic;
