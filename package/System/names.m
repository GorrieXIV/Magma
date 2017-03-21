freeze;

intrinsic SysAssignNamesNum(~S, ~Q, prefix)
{Assign Q to the names of S}
    n := NumberOfNames(S);
    AssignNames(
	~S, [prefix cat "[" cat IntegerToString(i) cat "]": i in [1 .. n]]
    );
    Q := [Name(S, i): i in [1 .. n]];
end intrinsic;

intrinsic Names(S::Str) -> []
{The print names of S as strings}
  try return [Sprint(Name(S, i)): i in [1 .. NumberOfNames(S)]];
  catch e; error "Names do not exist for this structure"; end try;
end intrinsic;

intrinsic CopyNames(S::Str, T::Str)
{Copy names of S to T}
    AssignNames(~T, Names(S));
end intrinsic;
