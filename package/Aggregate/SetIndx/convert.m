freeze;

intrinsic IndexedSet(S::Setq) -> SetIndx
{The indexed set derived from S}
    if IsNull(S) then
	return {@@};
    else
	return {@ Universe(S) | x: x in S @};
    end if;
end intrinsic;
