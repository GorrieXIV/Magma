freeze;

// Most of the transitive group functions are obsoleted by the new
// database format, where iteration through the database is likely to
// be syntactically clearer.  This file contains compatibility versions
// of the original functionality.

intrinsic NumberOfTransitiveGroups(d::RngIntElt) -> RngIntElt
{The number of groups of degree d stored in the database of transitive
groups of small degree}
    return #TransitiveGroupDatabase(d);
end intrinsic;


intrinsic TransitiveGroup(d::RngIntElt, n::RngIntElt) -> GrpPerm, MonStgElt
{Return the n-th transitive group of degree d, together with a description
string}
    return TransitiveGroup(TransitiveGroupDatabase(d), n);
end intrinsic;

intrinsic TransitiveGroupDescription(d::RngIntElt, n::RngIntElt) -> MonStgElt
{Return the string description of the n-th transitive group of degree d}
    return s where _, s is TransitiveGroup(d, n);
end intrinsic;

intrinsic TransitiveGroupDescription(G::GrpPerm) -> MonStgElt
{Return the string description of the transitive group G}
    require IsTransitive(G) and Degree(G) le 20: "The group must be transitive of degree at most 20";
    n, d := TransitiveGroupIdentification(G);
    return s where _, s is TransitiveGroup(d, n);
end intrinsic;


intrinsic TransitiveGroup(d::RngIntElt) -> GrpPerm, MonStgElt
{Returns the first group of degree d in the transitive group database,
along with a string giving a description of the group}
    return TransitiveGroup(d, 1);
end intrinsic;

intrinsic TransitiveGroup(Degrees::[RngIntElt], Predicate::Program) -> GrpPerm, MonStgElt
{Returns the first transitive group with degree in Degrees which
satisfies Predicate, along with a string giving a description of the group}

    for d in Degrees do
	// It would be simpler to iterate through the groups in the database,
	// but then we would need to create the group a second time simply to
	// get the description.  Hence the explicit use of the index.

	D := TransitiveGroupDatabase(d);
	for n in [1..#D] do
	    G, desc := TransitiveGroup(D, n);
	    if Predicate(G) then
		return G, desc;
	    end if;
	end for;
    end for;

    error "Error: There are no groups of given degree in the database that satisfy the predicate";
end intrinsic;

intrinsic TransitiveGroup(d::RngIntElt, Predicate::Program) -> GrpPerm, MonStgElt
{Returns the first transitive group of degree d which satisfies Predicate,
along with a string giving a description of the group}
    return TransitiveGroup([d], Predicate);
end intrinsic;


intrinsic TransitiveGroups(d::RngIntElt) -> SeqEnum
{Returns a sequence of all transitive groups of degree d}
    return [ G : G in TransitiveGroupDatabase(d) ];
end intrinsic;

intrinsic TransitiveGroups(Degrees::[RngIntElt]) -> SeqEnum
{Returns a sequence of all transitive groups from the database whose
degree is in the given sequence}
    return &cat [ TransitiveGroups(d) : d in Degrees ];
end intrinsic;

intrinsic TransitiveGroups(d::RngIntElt, Predicate::Program) -> SeqEnum
{Returns a sequence of all transitive groups with degree d which satisfy
Predicate}
    return [ G : G in TransitiveGroupDatabase(d) | Predicate(G) ];
end intrinsic;

intrinsic TransitiveGroups(Degrees::[RngIntElt], Predicate::Program) -> SeqEnum
{Returns a sequence of all transitive groups with degree in Degrees
which satisfy Predicate}
    return &cat [ TransitiveGroups(d, Predicate) : d in Degrees ];
end intrinsic;


// The Process layer is below here.  Its use is not recommended.
//
// A process P is an object used to iterate through the groups database.
// To use a process, one creates the process with TransitiveGroupProcess().
// The standard process functions IsEmpty, CurrentObject,
// CurrentObjectLabel and Advance can then be applied.
//
//
// TransitiveGroupProcess(degrees s, predicate f)
//    Returns a process which iterates through all groups with degree s
//    that satisfy the predicate f (which may be omitted).
// 
// Internal functions:
//
// InternalTransitiveGroupProcessIsEmpty(process_tuple p)
//    Returns true if p points to a group or false if no more groups
//    satisfying the given conditions are available.
// 
// InternalNextTransitiveGroup(process_tuple ~p)
//    Moves p to the next group satisfying the given conditions or to
//    an empty state if no more groups are found.
// 
// InternalExtractTransitiveGroup(process_tuple p)
//    Extracts the current group of p.
// 
// InternalCurrentObjectLabel(process_tuple p)
//    Returns the label (s, n) of the current group of p.
//    ExtractTransitiveGroup(p) eq TransitiveGroup(s,n).
// 
// ----------------------------------------------------------------------------


// Process is a tuple <degrees, predicate, database, group number>.
// Process will loop through all groups with degree in "degrees"
// which further satisfy the predicate (or all if Predicate eq true).
//
// At each stage the database will be the transitive group database for
// the first degree in degrees.  Once a degree is exhausted, it is
// removed from the sequence.  When the sequence is empty, then we are
// done.

intrinsic InternalTransitiveGroupProcessIsEmpty(p::Tup) -> BoolElt
{Returns true iff the transitive group process has passed its last group}
    return (#p[1] eq 0);
end intrinsic;

intrinsic InternalNextTransitiveGroup(~p::Tup)
{Moves the transitive group process tuple p to its next group}
    error if InternalTransitiveGroupProcessIsEmpty(p), "Process finished";

    degrees, predicate, D, n := Explode(p);

    while true do
	while n lt #D do
	    n +:= 1;
	    if predicate(D[n]) then
		p := <degrees, predicate, D, n>;
		return;
	    end if;
	end while;

	degrees := degrees[[2..#degrees]];
	if #degrees eq 0 then
	    break;
	end if;

	n := 0;
	D := TransitiveGroupDatabase(degrees[1]);
    end while;

    // No more groups left in process
    p := <[], predicate, [], 0>;

end intrinsic;

intrinsic InternalExtractTransitiveGroup(p::Tup) -> GrpPerm, MonStgElt
{Returns the current group of the transitive group process tuple p}
    error if InternalTransitiveGroupProcessIsEmpty(p), "Process finished";

    return TransitiveGroup(p[3], p[4]);
end intrinsic;

intrinsic InternalExtractTransitiveGroupLabel(p::Tup) -> RngIntElt, RngIntElt
{Returns the label (d,n) of the transitive group process tuple p.
This is the degree and number of the current group of p}
    error if InternalTransitiveGroupProcessIsEmpty(p), "Process finished";

    return Degree(p[3]), p[4];
end intrinsic;



intrinsic TransitiveGroupProcess(Degrees::[RngIntElt], Predicate::Program) -> Process
{Returns a transitive group process which will iterate through 
all groups with degree in Degrees which satisfy Predicate}

    // remove duplicates but otherwise retain order 
    Degrees := Isetseq({@ d : d in Degrees @});

    // check for validity of degrees
    maxdeg := TransitiveGroupDatabaseLimit();
    for d in Degrees do
	error if (d le 0), "Error: Degree must be positive";
	error if (d gt maxdeg), "Error: Degree must be less than", maxdeg;
    end for;

    // adjust predicate so that we always are dealing with functions
    if Type(Predicate) eq Intrinsic then
	Predicate := func<x|Predicate(x)>;
    end if;

    // tuple is <degrees, predicate, db for current degree, current index>
    // We prepend a 0 to the degrees for the initial advance
    tup := <[0] cat Degrees, Predicate, [], 0>;

    // advance to first group (if any)
    InternalNextTransitiveGroup(~tup);

    P := InternalCreateProcess(
    		"Transitive Group",
		tup,
    		InternalTransitiveGroupProcessIsEmpty,
		InternalNextTransitiveGroup,
		InternalExtractTransitiveGroup,
		InternalExtractTransitiveGroupLabel
	    );

    return P;
end intrinsic;

intrinsic TransitiveGroupProcess(Degrees::[RngIntElt]) -> Process
{Returns a transitive group process which will iterate through all
groups with degree in Degrees}
    return TransitiveGroupProcess(Degrees, func<x|true>);
end intrinsic;

intrinsic TransitiveGroupProcess(d::RngIntElt) -> Process
{Returns a transitive group process which will iterate through all groups
of degree d}
    return TransitiveGroupProcess([d], func<x|true>);
end intrinsic;

intrinsic TransitiveGroupProcess(d::RngIntElt, Predicate::Program) -> Process
{Returns a transitive group process which will iterate through all groups
of degree d which satisfy Predicate}
    return TransitiveGroupProcess([d], Predicate);
end intrinsic;

