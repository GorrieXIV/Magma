freeze;

// The irreducible matrix groups database access package.
//     (based on the Small Groups package)
// 
// This package contains functions to access the database of irreducible matrix
// groups. It includes the following functions:
// 
// IrreducibleMatrixGroup(predicate f)
//    Return the first (non-trivial) group g in the database which
//    satisfies f(g).  This will return the same group each time it
//    is called.
// 
// IrreducibleMatrixGroup(k, p, predicate f)
//    Returns the first subgroup g of GL(k,p) which satisfies f(g).
//    If s is a sequence of pairs, it attempts to return a group g
//    of each degree in s which satisfies f(g).
// 
// IrreducibleMatrixGroups(k, p, predicate f)
//    Returns all subgroups g of GL(k,p) which satisfy f(g).  If s is a 
//    sequence, returns all groups g of degree in s which satisfy f(g).
// 
// 
// A process P is an object used to iterate through the groups database.
// To use a process, one creates the process with IrreducibleMatrixGroupProcess().
// The standard process functions IsEmpty, CurrentObject,
// CurrentObjectLabel and Advance can then be applied.
// 
// 
// IrreducibleMatrixGroupProcess(degrees s, predicate f)
//    Returns a process which iterates through all groups with degree s
//    that satisfy the predicate f (which may be omitted).
// 
// Internal functions:
//
// InternalIrreducibleMatrixGroupProcessRestart(process_tuple ~p)
//    Return a process tuple to its first group.
// 
// InternalIrreducibleMatrixGroupProcessIsEmpty(process_tuple p)
//    Returns true if p points to a group or false if no more groups
//    satisfying the given conditions are available.
// 
// InternalNextIrreducibleMatrixGroup(process_tuple ~p)
//    Moves p to the next group satisfying the given conditions or to
//    an empty state if no more groups are found.
// 
// InternalExtractIrreducibleMatrixGroup(process_tuple p)
//    Extracts the current group of p.
// 
// InternalCurrentObjectLabel(process_tuple p)
//    Returns the label (s, n) of the current group of p.
//    ExtractIrreducibleMatrixGroup(p) eq IrreducibleMatrixGroup(s,n).
// 
// ----------------------------------------------------------------------------

// Set up necessary variables

_img_lim     := PrimitiveGroupDatabaseLimit();
_img_all     := {@ <t[1,2],t[1,1]>:d in [1.._img_lim]|#t eq 1 
		    where t := Factorization(d) @};
_img_lengths := [NumberOfIrreducibleMatrixGroups(t[1],t[2]) : t in _img_all];

_img_next := function(labs, p1, p2)
    if (Type(p1) ne RngIntElt) then
        error "Argument s should be an integer";
    end if;
    if (Type(p2) ne RngIntElt) then
        error "Argument n should be an integer";
    end if;
    if (p1 gt #labs) or (p1 lt 1) then
        return 0,0;
    elif (p1 eq #labs and 
        p2 eq #labs[p1,2]) then
        return 0,0;
    elif p2 ge #labs[p1,2] then
        return p1+1, 1;
    else
        return p1, p2+1;
    end if;
end function;

_img_check_degree := procedure(d)
    error if (d le 0),
	"Error: Degree must be positive";
    error if (d gt _img_lim),
	"Error: Degree must be less than", _img_lim;
end procedure;

_img_warn_lots := procedure(Number, Warning)
    if (Number gt 100000) then
	printf "Warning:  Returning more than 100,000 groups -- this will " cat
	       "take a VERY long time.  " cat
	       "Would a IrreducibleMatrixGroupProcess be more appropriate?\n";
    elif (Number gt 10000) and (Warning) then
	printf "Warning: Returning more than 10,000 groups -- " cat
	       "perhaps a IrreducibleMatrixGroupProcess would be more appropriate?\n";
	printf "\n(To turn off this message, use Warning := false)\n";
    elif (Number gt 1000) and (Warning) then
	printf "Warning: Returning more than 1,000 groups -- " cat
	       "this may take a while.\n";
	printf "\n(To turn off this message, use Warning := false)\n";
    end if;
end procedure;


// Process is a tuple  <labels, which pair, which grp, group predicate>
// labels is a sequence of pairs <deg, [grp number in db]>
// Process will loop through all groups with degree first of pair in labels
// and database number in second in pair, 
// which further satisfy the predicate (or all if Predicate eq true).

intrinsic InternalIrreducibleMatrixGroupProcessIsEmpty(p::Tup) -> BoolElt
{ Returns true if the primitive group process has passed its last group. }

    return (p[2] eq 0);
end intrinsic;

intrinsic InternalNextIrreducibleMatrixGroup(~p::Tup)
{ Moves the primitive group process tuple p to its next group }
    error if InternalIrreducibleMatrixGroupProcessIsEmpty(p),
        "Process finished";
    repeat
        p[2], p[3] := _img_next(p[1], p[2], p[3]);
    until (p[2] eq 0) or
	  (p[3] ne 0 and
	   p[4](IrreducibleMatrixGroup(p[1][p[2],1], p[1][p[2],2][p[3]])));
end intrinsic;

procedure InternalIrreducibleMatrixGroupProcessRestart(~p)
/* Returns the primitive group process tuple p to its first group */
    p[2] := 1;
    p[3] := 0;
    InternalNextIrreducibleMatrixGroup(~p);
    error if (p[2] eq 0),
        "No primitive groups in the specified range satisfy the predicate";
end procedure;

intrinsic IrreducibleMatrixGroupProcess(Degrees::[RngIntElt]:Filter:="All") -> Process
{Returns a primitive group process.  This will iterate through all
groups with degree in Degrees.}

    return IrreducibleMatrixGroupProcess(Degrees, func<x|true>:Filter:=Filter);

end intrinsic;

_img_get_labels := function(R, Filter)

    case Filter:
    when "All": 
	labels := [ <d, [1..NumberOfIrreducibleMatrixGroups(d[1],d[2])]>: d in R];
    when "Soluble": 
	labels := [ t : d in R | #t[2] gt 0 where t is
		<d, [1..NumberOfSolubleIrreducibleMatrixGroups(d[1],d[2])]>];
    else
	error "Unrecognised Filter value";
    end case;
    return labels;
end function;


intrinsic IrreducibleMatrixGroupProcess(Degrees::[Tup], Predicate::Program:Filter:="All") -> Process
{Returns an irreducible matrix group process which will iterate through 
all groups (g) with degree in Degrees which satisfy Predicate(g).}

    if #Set(Degrees) ne #Degrees then
        R := [d : d in Degrees | not d in Self()];
    else
        R := Degrees;
    end if;
    for d in R do
	_img_check_degree(d);
    end for;

    case Type(Predicate):
        when Intrinsic:
            Pred := func<x|Predicate(x)>;
        else
            Pred := Predicate;
    end case;

    labels := _img_get_labels(R, Filter);

    tup := <labels, 0, 0, Pred>;
    InternalIrreducibleMatrixGroupProcessRestart(~tup);
    P := InternalCreateProcess("Irreducible Matrix Group", tup, InternalIrreducibleMatrixGroupProcessIsEmpty, InternalNextIrreducibleMatrixGroup, InternalExtractIrreducibleMatrixGroup, InternalExtractIrreducibleMatrixGroupLabel);

    return P;

end intrinsic;

intrinsic IrreducibleMatrixGroupProcess(k::RngIntElt, p::RngIntElt:Filter := "All") -> Process
{Returns a primitive group process.  This will iterate through all groups
of degree d.}
    return IrreducibleMatrixGroupProcess([<k,p>], func<x|true>:Filter := Filter);
end intrinsic;

intrinsic IrreducibleMatrixGroupProcess(k::RngIntElt, p::RngIntElt, Predicate::Program:Filter:="All") -> Process
{Returns a primitive group process.  This will iterate through all groups
of degree d which satisfy Predicate(g).}
    return IrreducibleMatrixGroupProcess([<k,p>], Predicate:Filter:=Filter);
end intrinsic;

intrinsic IrreducibleMatrixGroupProcess(:Filter:="All") -> Process
{Returns a primitive group process.  This will iterate through all groups}
    return IrreducibleMatrixGroupProcess([1.._img_lim], func<x|true>:Filter:=Filter);
end intrinsic;

intrinsic IrreducibleMatrixGroupProcess(Predicate::Program:Filter:="All") -> Process
{Returns a primitive group process.  This will iterate through all groups
which satisfy Predicate(g)}
    return IrreducibleMatrixGroupProcess([1.._img_lim], Predicate:Filter:=Filter);
end intrinsic;

intrinsic InternalExtractIrreducibleMatrixGroup(p::Tup) -> GrpPerm, MonStgElt, MonStgElt
{ Returns the current group of the primitive group process tuple p }
    error if InternalIrreducibleMatrixGroupProcessIsEmpty(p),
        "Process finished";
    t := p[1, p[2]];
    return IrreducibleMatrixGroup(t[1], t[2,p[3]]);
end intrinsic;

intrinsic InternalExtractIrreducibleMatrixGroupLabel(p::Tup) -> RngIntElt, RngIntElt
{ Returns the label (s,n) of the primitive group process tuple p.
This is the degree and number of the current group of p }
    error if InternalIrreducibleMatrixGroupProcessIsEmpty(p),
        "Process finished";
    t := p[1, p[2]];
    return t[1], t[2,p[3]];
end intrinsic;


intrinsic IrreducibleMatrixGroup(d::RngIntElt, Predicate::Program:Filter:="All") -> GrpPerm, MonStgElt, MonStgElt
{Returns the first group (g) of degree d which satisfies Predicate.}

    _img_check_degree(d);
    T := IrreducibleMatrixGroupProcess([d], Predicate : Filter := Filter);
    if IsEmpty(T) then
	error "No group of the specified degree satisfies the predicate";
    end if;
    return Current(T);
end intrinsic;

intrinsic IrreducibleMatrixGroup(Degrees::[RngIntElt], Predicate::Program:Filter:="All") -> GrpPerm, MonStgElt
{Returns the first group (g) with degree in Degrees which satisfies the 
predicate.}

    for d in Degrees do
        _img_check_degree(d);
	T := IrreducibleMatrixGroupProcess([d], Predicate : Filter := Filter);
	if IsEmpty(T) then
	    continue d;
	end if;
	return Current(T);
    end for;
    if (#Degrees eq 1) then
        plural := "";
    else
        plural := "s";
    end if;
    printf "Error: No groups of the specified degree%o satisfy the predicate",
	   plural;
    error "";
end intrinsic;


intrinsic IrreducibleMatrixGroup(d::RngIntElt) -> GrpPerm, MonStgElt
{Returns the first primitive group of degree d.}
    return IrreducibleMatrixGroup(d, 1);
end intrinsic;

intrinsic IrreducibleMatrixGroups(d::RngIntElt : Filter := "All", 
		      Warning := true) -> SeqEnum
{Returns a sequence of all primitive groups of degree d.  Some degrees
will produce a very large sequence of groups -- in such cases a warning
will be printed unless the user specifies Warning := false}

    _img_check_degree(d);

    labels := _img_get_labels([d], Filter);
    labels := labels[1,2];

    _img_warn_lots(#labels, Warning);

    return [IrreducibleMatrixGroup(d, n) : n in labels ];

end intrinsic;

intrinsic IrreducibleMatrixGroups(Degrees::[RngIntElt] : Filter := "All",
		      Warning := true) -> SeqEnum
{As above, but with a list of degrees}

    S := Set(Degrees);
    for i in S do
	_img_check_degree(i);
    end for;

    labels := _img_get_labels(S, Filter);

    Number := &+ [#t[2] : t in labels];
    _img_warn_lots(Number, Warning);

    Result := [];
    for t in labels do
	Result cat:= [IrreducibleMatrixGroup(t[1], n) : n in t[2]];
    end for;
    return Result;
end intrinsic;

intrinsic IrreducibleMatrixGroups(: Filter := "All", Warning := true) -> SeqEnum
{As above, but with all legal degrees}
    return IrreducibleMatrixGroups([1.._img_lim]:Filter:=Filter,Warning:=Warning);
end intrinsic;

intrinsic IrreducibleMatrixGroups(d::RngIntElt, Predicate::Program : Filter := "All") -> SeqEnum
{Returns a list of all groups (g) with degree d which satisfy Predicate(g) eq true.}

    _img_check_degree(d);

    labels := _img_get_labels([d], Filter);
    labels := labels[1,2];

    return [g: n in labels| Predicate(g) where g is IrreducibleMatrixGroup(d,n)];

end intrinsic;

intrinsic IrreducibleMatrixGroups(Degrees::[RngIntElt], Predicate::Program : Filter := "All") -> SeqEnum
{As above, but with a list of degrees.}

    S := Set(Degrees);
    for d in S do
	_img_check_degree(d);
    end for;
    labels := _img_get_labels(S, Filter);
    Result := [];
    for t in labels do
	Result cat:= [g : n in t[2] | Predicate(g) where g is 
			IrreducibleMatrixGroup(t[1], n)];
    end for;
    return Result;
end intrinsic;

intrinsic IrreducibleMatrixGroups(Predicate::Program : Filter := "All") -> SeqEnum
{Returns a list of all primitive groups (g) in the database which satisfy Predicate(g)}

    return IrreducibleMatrixGroups([1.._img_lim], Predicate:Filter := Filter);
end intrinsic;

intrinsic IrreducibleMatrixGroupDescription(d::RngIntElt, n::RngIntElt) -> MonStgElt
{Return the string description of the n-th primitive group of degree d.}
    return s where _, s is IrreducibleMatrixGroup(d, n);
end intrinsic;

delete _img_lim, _img_lengths, _img_next;

