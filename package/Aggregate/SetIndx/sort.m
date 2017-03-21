freeze;

intrinsic Sort(S::SetIndx) -> .
{The indexed set obtained by sorting the elements of S}
    if S eq {@@} then
	return S;
    end if;
    Q := IndexedSetToSequence(S);
    Sort(~Q);
    return {@ Universe(S) | x: x in Q @};
end intrinsic;

intrinsic Sort(~S::SetIndx)
{Sort the indexed set S in place}
    if #S eq 0 then
	return;
    end if;
    Q := IndexedSetToSequence(S);
    Sort(~Q);
    S := {@ Universe(S) | x: x in Q @};
end intrinsic;

intrinsic Sort(~S::SetIndx, ~permut)
{Sort the indexed set S in place (and assign the permutation to 'permut').}
    if #S eq 0 then
	return;
    end if;
    Q := IndexedSetToSequence(S);
    Sort(~Q, ~permut);
    S := {@ Universe(S) | x: x in Q @};
end intrinsic;

intrinsic Sort(S::SetIndx, compare::UserProgram) -> .
{The indexed set obtained by sorting the elements of S using the given
comparison function}
    if S eq {@@} then
	return S;
    end if;
    Q := IndexedSetToSequence(S);
    Sort(~Q, compare);
    return {@ Universe(S) | x: x in Q @};
end intrinsic;

intrinsic Sort(~S::SetIndx, compare::UserProgram)
{Sort the indexed set S in place using the given comparison function}
    if #S eq 0 then
	return;
    end if;
    Q := IndexedSetToSequence(S);
    Sort(~Q, compare);
    S := {@ Universe(S) | x: x in Q @};
end intrinsic;

intrinsic Sort(~S::SetIndx, compare::UserProgram, ~permut)
{Sort the indexed set S in place using the given comparison function
(and assign the permutation to 'permut').} 
    if #S eq 0 then
	return;
    end if;
    Q := IndexedSetToSequence(S);
    Sort(~Q, compare, ~permut);
    S := {@ Universe(S) | x: x in Q @};
end intrinsic;
