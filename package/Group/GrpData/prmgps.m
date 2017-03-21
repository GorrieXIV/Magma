freeze;

declare verbose Primitive, 2;

// The primitive groups database access package.
//     (based on the Small Groups package)
// 
// This package contains functions to access the database of primitive
// groups. It includes the following functions:
// 
// PrimitiveGroup(predicate f)
//    Return the first (non-trivial) group g in the database which
//    satisfies f(g).  This will return the same group each time it
//    is called.
// 
// PrimitiveGroupOfDegree(degree s, predicate f)
//    Returns the first group g of degree s which satisfies f(g).
//    If s is a sequence of integers, it attempts to return a group g
//    of each degree in s which satisfies f(g).
// 
// PrimitiveGroups(degree s, predicate f)
//    Returns all groups g of degree s which satisfy f(g).  If s is a 
//    sequence, returns all groups g of degree in s which satisfy f(g).
// 
// 
// A process P is an object used to iterate through the groups database.
// To use a process, one creates the process with PrimitiveGroupProcess().
// The standard process functions IsEmpty, CurrentObject,
// CurrentObjectLabel and Advance can then be applied.
// 
// 
// PrimitiveGroupProcess(degrees s, predicate f)
//    Returns a process which iterates through all groups with degree s
//    that satisfy the predicate f (which may be omitted).
// 
// Internal functions:
//
// InternalPrimitiveGroupProcessRestart(process_tuple ~p)
//    Return a process tuple to its first group.
// 
// InternalPrimitiveGroupProcessIsEmpty(process_tuple p)
//    Returns true if p points to a group or false if no more groups
//    satisfying the given conditions are available.
// 
// InternalNextPrimitiveGroup(process_tuple ~p)
//    Moves p to the next group satisfying the given conditions or to
//    an empty state if no more groups are found.
// 
// InternalExtractPrimitiveGroup(process_tuple p)
//    Extracts the current group of p.
// 
// InternalCurrentObjectLabel(process_tuple p)
//    Returns the label (s, n) of the current group of p.
//    ExtractPrimitiveGroup(p) eq PrimitiveGroup(s,n).
// 
// ----------------------------------------------------------------------------

// Set up necessary variables

_pg_lim     := PrimitiveGroupDatabaseLimit();
_pg_last_n  := NumberOfPrimitiveGroups(_pg_lim);
_pg_lengths := [NumberOfPrimitiveGroups(s) : s in [1.._pg_lim]];

_pg_simples := [
[], [], [], [], [ 4 ], [ 1, 3 ], [ 5, 6 ], [ 4, 6 ], [ 8, 10 ], [ 1, 3, 8 ],
[ 5, 6, 7 ], [ 1, 3, 4, 5 ], [ 7, 8 ], [ 1, 3 ], [ 1, 3, 4, 5 ], [ 21 ],
[ 6, 9 ], [ 1, 3 ], [ 7 ], [ 1, 3 ], [ 2, 4, 8 ], [ 1, 3 ], [ 5, 6 ],
[ 1, 3, 4 ], [ 27 ], [ 1, 6 ], [ 12, 14 ], [ 2, 4, 5, 8, 12, 13 ], [ 7 ],
[ 1, 3 ], [ 9, 10, 11 ], [ 4, 6 ], [ 1, 3 ], [ 1 ], [ 1, 3, 5 ],
[ 9, 14, 16, 18, 20, 21 ], [ 10 ], [ 1, 3 ], [ 1 ], [ 1, 2, 5, 7 ], [ 9 ],
[ 1, 3 ], [ 9 ], [ 1, 3 ], [ 4, 6, 8 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 39 ],
[ 1, 5, 8 ], [ 1 ], [ 2 ], [ 7 ], [ 1, 3 ], [ 1, 4, 5, 7 ], [ 1, 2, 8 ],
[ 1, 2, 4 ], [ 1 ], [ 5 ], [ 6, 8 ], [ 13 ], [ 1, 3 ], [ 1, 2, 5, 6, 7 ],
[ 73 ], [ 1, 3, 4, 8, 12 ], [ 2, 3, 4, 6 ], [ 9 ], [ 1, 4, 6 ], [ 1 ],
[ 1 ], [ 9 ], [ 1, 3 ], [ 13, 15 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 3 ],
[ 1, 3, 5 ], [ 9 ], [ 1, 3 ], [ 154 ], [ 1, 9 ], [ 5 ], [ 1, 2, 5 ],
[ 1, 3, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1, 2, 5, 7, 9 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 33, 35, 37 ], [ 10 ],
[ 1, 2, 4 ], [ 9 ], [ 1, 3 ], [ 8, 10 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 13 ],
[ 1, 3 ], [ 1 ], [ 1, 9 ], [ 11 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 2, 4 ], [ 1 ],
[ 1, 3 ], [ 1, 5, 11, 12, 13, 14, 17, 19, 20, 22 ], [ 55, 56 ], [ 1, 6 ],
[ 1 ], [ 1 ], [ 44 ], [ 1, 2, 7, 8, 11, 18 ], [ 13, 14 ], [ 4, 6 ], [ 1, 3 ],
[ 1, 6 ], [ 9 ], [ 1, 3 ], [ 1, 2 ], [ 1 ], [ 1, 2, 4 ],
[ 1, 2, 6, 8, 10, 11, 13 ], [ 9 ], [ 1, 3 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 11, 13, 16 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 13 ],
[ 1, 3 ], [ 1, 3, 5 ], [ 1 ], [ 1, 2 ], [ 1, 2, 5, 8 ], [ 13 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1, 6 ], [ 11 ], [ 1, 3 ], [ 1, 2, 3, 6 ], [ 1 ], [ 5 ],
[ 6, 8 ], [ 74 ], [ 1, 6 ], [ 1, 3, 5 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1, 3, 5 ],
[ 1, 2, 4, 5 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 19 ], [ 1, 3 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 2 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 9 ], [ 1, 3 ], [ 15 ],
[ 1, 3 ], [ 1 ], [ 9 ], [ 10 ], [ 1, 3 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1, 2 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 4 ], [ 1 ], [ 1, 3, 5 ], [ 17 ],
[ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 21 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 2, 4 ], [ 1 ],
[ 1 ], [ 9 ], [ 1, 3 ], [ 11 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 13 ], [ 1, 3 ],
[ 1, 3, 5 ], [ 1 ], [ 9 ], [ 1, 3, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ],
[ 1, 3 ], [ 21 ], [ 1, 3 ], [ 35 ], [ 1, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 2 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1, 2, 4, 5, 6, 8 ], [ 1 ], [ 1, 2, 3 ], 
[ 243 ], [ 10, 14 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ],
[ 1 ], [ 1, 2 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 17 ], [ 1, 3 ], [ 1, 7 ],
[ 1 ], [ 1, 3 ], [ 1, 3, 4, 5, 7 ], [ 13 ], [ 1, 3 ], [ 1 ],
[ 1, 10, 13, 15, 23 ], [ 17 ], [ 1, 3 ], [ 9 ], [ 1, 3 ], [ 2 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 96 ], [ 1, 6 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1, 3 ], [ 1 ], [ 1 ], [ 1, 6, 8, 10 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 13, 14 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 17 ], [ 1, 3 ],
[ 1, 3, 4 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ],
[ 1, 6, 8, 11, 13 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 17 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 7, 8 ], [ 21 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ],
[ 89 ], [ 1, 3, 7 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 13 ], [ 1, 3 ],
[ 1, 5, 6, 8, 10 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 6 ], [ 1 ],
[ 5 ], [ 17, 19 ], [ 91 ], [ 1, 6 ], [ 1 ], [ 1, 2, 3, 6, 8, 10 ], [ 1 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 1, 4 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1, 5, 6, 8, 10 ], [ 17 ], [ 1, 3 ], [ 1, 3 ], [ 1 ], [ 5 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1, 3 ], [ 19 ], [ 1, 3 ], [ 1 ], [ 9, 10, 13, 15 ], [ 16 ], [ 1, 3 ], [ 1 ],
[ 1 ], [ 1 ], [ 1, 3, 5 ], [ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1, 4, 6 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 25 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 2 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 21 ],
[ 1, 3 ], [ 1, 3, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 23 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 15 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1, 3 ], [ 3 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 13 ],
[ 1, 3, 5, 7 ], [ 17 ], [ 1, 3 ], [ 1, 4, 6 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 2, 5, 7, 9 ], [ 1, 3, 6, 8, 9, 11 ], [ 1 ],
[ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 5 ], [ 5, 7 ], [ 1 ], [ 1, 2 ], [ 1 ],
[ 1 ], [ 7 ], [ 1, 3 ], [ 1, 2 ], [ 57 ], [ 1, 10, 13 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1, 8 ], [ 17 ], [ 1, 3 ], [ 13 ], [ 1, 3 ], [ 1, 4, 7 ],
[ 1 ], [ 1, 3 ], [ 1, 3, 5, 6, 8 ], [ 64 ], [ 1, 6 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 9 ], [ 25 ], [ 1, 3 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 2 ],
[ 1 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1, 3, 5 ], [ 1, 3 ], [ 1 ],
[ 5 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 6 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 17 ],
[ 1, 3 ], [ 1 ], [ 1, 2 ], [ 1 ], [ 10 ], [ 22 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 11 ], [ 1, 3 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 25 ],
[ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 19 ], [ 1, 3 ], [ 1 ], [ 1, 3 ], [ 17 ], [ 1, 3 ], [ 9 ], [ 1, 2, 4 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 697 ], [ 1, 9 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 17 ], [ 1, 3 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1, 2, 6 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 3 ], [ 1 ], [ 9 ],
[ 6, 8 ], [ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1, 3 ], [ 1, 3, 7 ], [ 25 ], [ 1, 3 ], [ 1 ], [ 29 ], [ 10 ],
[ 1, 3 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1, 5 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 19 ], [ 1, 3 ], [ 1, 3, 5 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 500 ], [ 1, 4, 14 ], [ 1 ],
[ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ],
[ 1, 3 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 2 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 6 ], [ 25, 27 ], [ 1, 3 ],
[ 1, 2 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 19 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 2 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1, 2 ], [ 1 ], [ 1 ], [ 37 ], [ 1 ],
[ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1, 9 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 21 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 5, 7 ],
[ 1, 3, 4, 13, 21, 23 ], [ 13 ],
[ 1, 3 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 19 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3, 5, 7 ],
[ 115 ], [ 1, 6 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 17 ], [ 1, 3 ],
[ 1, 3, 5 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1, 2 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 2 ],
[ 21 ], [ 1, 3 ], [ 19 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ],
[ 1 ], [ 1 ], [ 1, 3, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 4 ],
[ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 17 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 25 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1, 3, 5 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 6, 7, 9 ],
[ 133 ], [ 1, 6 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1, 3 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 11 ], [ 1, 3 ], [ 1 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ],
[ 25 ], [ 1, 3 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 106 ],
[ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 8 ], [ 31 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 2 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ],
[ 25 ], [ 1, 3 ], [ 1, 2, 3 ], [ 114 ], [ 1, 3, 7 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 17 ], [ 1, 3 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 2, 6 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 2 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ],
[ 13 ], [ 1, 3 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1, 6 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ],
[ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 4, 5, 10 ],
[ 1, 3, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 2 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 9 ], [ 1 ],
[ 9 ], [ 6, 8 ], [ 25, 26 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1, 2, 5 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1, 3, 6 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 7 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 19 ], [ 1, 3 ], [ 1 ], [ 1, 3, 4, 7, 15 ],
[ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 17 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 13 ], [ 1, 3 ], [ 25 ], [ 1, 3 ], [ 1 ], [ 5 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 6, 8, 10 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 31 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 2 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 15 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 13, 18, 20, 22 ], [ 1 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ],
[ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 25 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 13 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1, 2, 3 ], [ 17 ], [ 1, 3 ],
[ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 132, 134 ], [ 26 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 19 ], [ 1, 3 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3, 5 ],
[ 33 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1, 3 ],
[ 91 ], [ 1, 5, 9 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 4 ],
[ 21 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 2, 5, 7, 11 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 141 ], [ 1, 6 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 1 ], [ 1 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1, 3, 5 ], [ 17 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 25 ], [ 1, 3 ],
[ 1, 3, 5 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1, 2 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 13 ], [ 1, 3 ], [ 19 ], [ 1, 3 ], [ 1 ], [ 1, 4 ], [ 1 ], [ 1 ], [ 15 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1, 2 ], [ 1, 2, 5, 7 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 17 ], [ 1, 3 ], [ 17 ], [ 1, 3 ], [ 1, 3 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 21 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 5 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 2, 4, 6 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 19 ], [ 1, 3, 7 ],
[ 1 ], [ 1 ], [ 11 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 9 ], [ 2, 4 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 25 ], [ 1, 3 ], [ 1 ], [ 17, 20, 21 ],
[ 22 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 17 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ],
[ 31 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 25 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 13 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 193 ], [ 1, 6 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 19 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ],
[ 1, 2, 4, 6 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 17 ], [ 1, 3 ], [ 17, 18 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 25 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 5 ],
[ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ],
[ 1, 2, 3, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 21 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1, 3 ], [ 21 ], [ 1, 3 ], [ 4 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 13 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ],
[ 37 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ],
[ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 131 ], [ 1, 6 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 17 ], [ 1, 3 ], [ 31 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ],
[ 1, 2, 4, 6 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 19 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 25 ], [ 1, 3 ], [ 1 ], [ 9 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ],
[ 25 ], [ 1, 3 ], [ 2, 4 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 17 ], [ 1, 3 ],
[ 1 ], [ 1, 3 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1, 3, 7, 9, 12, 14, 16, 17, 19 ], [ 37 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1, 2, 4 ], [ 34, 35 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 19 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 2 ], [ 13 ], [ 1, 3 ], [ 1 ],
[ 1 ], [ 1 ], [ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1, 3, 7, 9, 11, 13, 15, 16, 18 ],
[ 25 ], [ 1, 3 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 25 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 6 ], [ 1, 3 ], [ 1 ], [ 1, 3 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 29 ], [ 1, 3 ], [ 1 ], [ 5 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 21 ], [ 1, 3 ],
[ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 13 ], [ 1, 3 ], [ 25 ], [ 1, 3 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 41 ], [ 1, 2, 4 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 19 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 72 ], [ 1, 5 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 171 ], [ 1, 3, 7 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 5 ], [ 1, 3 ], [ 75 ], [ 1, 6 ],
[ 1, 3, 5 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 9 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 25 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 2 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 31 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 1 ], [ 1 ],
[ 33 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1, 2, 3 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1, 2, 4 ],
[ 1 ], [ 1 ], [ 1 ], [ 9, 11 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ],
[ 33 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 37 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 13 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 33 ], [ 1, 3 ], [ 1 ], [ 1, 2, 5, 7, 10 ],
[ 25 ], [ 1, 3 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 13 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 9 ], [ 1, 3 ],
[ 55 ], [ 1, 9 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 11 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 9 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 25 ], [ 1, 3 ], [ 1 ], [ 1, 3 ],
[ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 5 ], [ 6, 8 ], [ 1 ], [ 1 ],
[ 1, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 5 ], [ 1, 3 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3 ], [ 1 ], [ 13 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 17 ], [ 1, 3 ], [ 1 ], [ 1 ], [ 7 ], [ 1, 3 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1, 3, 5 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ],
[ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ], [ 1 ] ];


_pg_next := function(labs, p1, p2)
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

_pg_check_degree := procedure(d)
    error if (d le 0),
	"Error: Degree must be positive";
    error if (d gt _pg_lim),
	"Error: Degree must be less than", _pg_lim;
end procedure;

_pg_warn_lots := procedure(Number, Warning)
    if (Number gt 100000) then
	printf "Warning:  Returning more than 100,000 groups -- this will " cat
	       "take a VERY long time.  " cat
	       "Would a PrimitiveGroupProcess be more appropriate?\n";
    elif (Number gt 10000) and (Warning) then
	printf "Warning: Returning more than 10,000 groups -- " cat
	       "perhaps a PrimitiveGroupProcess would be more appropriate?\n";
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

intrinsic InternalPrimitiveGroupProcessIsEmpty(p::Tup) -> BoolElt
{ Returns true if the primitive group process has passed its last group. }

    return (p[2] eq 0);
end intrinsic;

intrinsic InternalNextPrimitiveGroup(~p::Tup)
{ Moves the primitive group process tuple p to its next group }
    error if InternalPrimitiveGroupProcessIsEmpty(p),
        "Process finished";
    repeat
        p[2], p[3] := _pg_next(p[1], p[2], p[3]);
    until (p[2] eq 0) or
	  (p[3] ne 0 and
	   p[4](PrimitiveGroup(p[1][p[2],1], p[1][p[2],2][p[3]])));
end intrinsic;

procedure InternalPrimitiveGroupProcessRestart(~p)
/* Returns the primitive group process tuple p to its first group */
    p[2] := 1;
    p[3] := 0;
    InternalNextPrimitiveGroup(~p);
    error if (p[2] eq 0),
        "No primitive groups in the specified range satisfy the predicate";
end procedure;

intrinsic PrimitiveGroupProcess(Degrees::[RngIntElt]:Filter:="All") -> Process
{Returns a primitive group process.  This will iterate through all
groups with degree in Degrees.}

    return PrimitiveGroupProcess(Degrees, func<x|true>:Filter:=Filter);

end intrinsic;

_pg_get_labels := function(R, Filter)

    case Filter:
    when "All": 
	labels := [ <d, [1..NumberOfPrimitiveGroups(d)]>: d in R];
    when "Soluble": 
	labels := [ t : d in R | #t[2] gt 0 where t is
			<d, [1..NumberOfPrimitiveSolubleGroups(d)]>];
    when "Affine": 
	labels := [ t : d in R | #t[2] gt 0 where t is 
			<d, [1..NumberOfPrimitiveAffineGroups(d)]>];
    when "Diagonal": 
	labels := [];
	for d in R do
	    N := NumberOfPrimitiveDiagonalGroups(d);
	    if N gt 0 then
		S := NumberOfPrimitiveAffineGroups(d) + 1;
		Append(~labels, <d, [S..S+N-1]>);
	    end if;
	end for;
    when "Product": 
	labels := [];
	for d in R do
	    N := NumberOfPrimitiveProductGroups(d);
	    if N gt 0 then
		S := NumberOfPrimitiveAffineGroups(d) + 
			NumberOfPrimitiveDiagonalGroups(d) + 1;
		Append(~labels, <d, [S..S+N-1]>);
	    end if;
	end for;
    when "AlmostSimple":
	labels := [];
	for d in R do
	    N := NumberOfPrimitiveAlmostSimpleGroups(d);
	    if N gt 0 then
		S := NumberOfPrimitiveGroups(d)  - N + 1;
		Append(~labels, <d, [S..S+N-1]>);
	    end if;
	end for;
    when "Simple":
	labels := [t:d in R|#t[2] gt 0 where t is <d, _pg_simples[d]>];
    when "SimpleNA":
	labels := [t:d in R|#t[2] gt 0 where t is 
	    <d, [i:i in _pg_simples[d] | i ne NumberOfPrimitiveGroups(d)-1]>];
    else
	error "Unrecognised Filter value";
    end case;
    return labels;
end function;


intrinsic PrimitiveGroupProcess(Degrees::[RngIntElt], Predicate::Program:Filter:="All") -> Process
{Returns a primitive group process which will iterate through 
all groups (g) with degree in Degrees which satisfy Predicate(g).}

    if #Set(Degrees) ne #Degrees then
        R := [d : d in Degrees | not d in Self()];
    else
        R := Degrees;
    end if;
    for d in R do
	_pg_check_degree(d);
    end for;

    case Type(Predicate):
        when Intrinsic:
            Pred := func<x|Predicate(x)>;
        else
            Pred := Predicate;
    end case;

    labels := _pg_get_labels(R, Filter);

    tup := <labels, 0, 0, Pred>;
    InternalPrimitiveGroupProcessRestart(~tup);
    P := InternalCreateProcess("Primitive Group", tup, InternalPrimitiveGroupProcessIsEmpty, InternalNextPrimitiveGroup, InternalExtractPrimitiveGroup, InternalExtractPrimitiveGroupLabel);

    return P;

end intrinsic;

intrinsic PrimitiveGroupProcess(d::RngIntElt:Filter := "All") -> Process
{Returns a primitive group process.  This will iterate through all groups
of degree d.}
    return PrimitiveGroupProcess([d], func<x|true>:Filter := Filter);
end intrinsic;

intrinsic PrimitiveGroupProcess(d::RngIntElt, Predicate::Program:Filter:="All") -> Process
{Returns a primitive group process.  This will iterate through all groups
of degree d which satisfy Predicate(g).}
    return PrimitiveGroupProcess([d], Predicate:Filter:=Filter);
end intrinsic;

intrinsic PrimitiveGroupProcess(:Filter:="All") -> Process
{Returns a primitive group process.  This will iterate through all groups}
    return PrimitiveGroupProcess([1.._pg_lim], func<x|true>:Filter:=Filter);
end intrinsic;

intrinsic PrimitiveGroupProcess(Predicate::Program:Filter:="All") -> Process
{Returns a primitive group process.  This will iterate through all groups
which satisfy Predicate(g)}
    return PrimitiveGroupProcess([1.._pg_lim], Predicate:Filter:=Filter);
end intrinsic;

intrinsic InternalExtractPrimitiveGroup(p::Tup) -> GrpPerm, MonStgElt, MonStgElt
{ Returns the current group of the primitive group process tuple p }
    error if InternalPrimitiveGroupProcessIsEmpty(p),
        "Process finished";
    t := p[1, p[2]];
    return PrimitiveGroup(t[1], t[2,p[3]]);
end intrinsic;

intrinsic InternalExtractPrimitiveGroupLabel(p::Tup) -> RngIntElt, RngIntElt
{ Returns the label (s,n) of the primitive group process tuple p.
This is the degree and number of the current group of p }
    error if InternalPrimitiveGroupProcessIsEmpty(p),
        "Process finished";
    t := p[1, p[2]];
    return t[1], t[2,p[3]];
end intrinsic;


intrinsic PrimitiveGroup(d::RngIntElt, Predicate::Program:Filter:="All") -> GrpPerm, MonStgElt, MonStgElt
{Returns the first group (g) of degree d which satisfies Predicate.}

    _pg_check_degree(d);
    T := PrimitiveGroupProcess([d], Predicate : Filter := Filter);
    if IsEmpty(T) then
	error "No group of the specified degree satisfies the predicate";
    end if;
    return Current(T);
end intrinsic;

intrinsic PrimitiveGroup(Degrees::[RngIntElt], Predicate::Program:Filter:="All") -> GrpPerm, MonStgElt
{Returns the first group (g) with degree in Degrees which satisfies the 
predicate.}

    for d in Degrees do
        _pg_check_degree(d);
	T := PrimitiveGroupProcess([d], Predicate : Filter := Filter);
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


intrinsic PrimitiveGroup(d::RngIntElt) -> GrpPerm, MonStgElt
{Returns the first primitive group of degree d.}
    return PrimitiveGroup(d, 1);
end intrinsic;

intrinsic PrimitiveGroups(d::RngIntElt : Filter := "All", 
		      Warning := true) -> SeqEnum
{Returns a sequence of all primitive groups of degree d.  Some degrees
will produce a very large sequence of groups -- in such cases a warning
will be printed unless the user specifies Warning := false}

    _pg_check_degree(d);

    labels := _pg_get_labels([d], Filter);
    labels := labels[1,2];

    _pg_warn_lots(#labels, Warning);

    return [PrimitiveGroup(d, n) : n in labels ];

end intrinsic;

intrinsic PrimitiveGroups(Degrees::[RngIntElt] : Filter := "All",
		      Warning := true) -> SeqEnum
{As above, but with a list of degrees}

    S := Set(Degrees);
    for i in S do
	_pg_check_degree(i);
    end for;

    labels := _pg_get_labels(S, Filter);

    Number := &+ [#t[2] : t in labels];
    _pg_warn_lots(Number, Warning);

    Result := [];
    for t in labels do
	Result cat:= [PrimitiveGroup(t[1], n) : n in t[2]];
    end for;
    return Result;
end intrinsic;

intrinsic PrimitiveGroups(: Filter := "All", Warning := true) -> SeqEnum
{As above, but with all legal degrees}
    return PrimitiveGroups([1.._pg_lim]:Filter:=Filter,Warning:=Warning);
end intrinsic;

intrinsic PrimitiveGroups(d::RngIntElt, Predicate::Program : Filter := "All") -> SeqEnum
{Returns a list of all groups (g) with degree d which satisfy Predicate(g) eq true.}

    _pg_check_degree(d);

    labels := _pg_get_labels([d], Filter);
    labels := labels[1,2];

    return [g: n in labels| Predicate(g) where g is PrimitiveGroup(d,n)];

end intrinsic;

intrinsic PrimitiveGroups(Degrees::[RngIntElt], Predicate::Program : Filter := "All") -> SeqEnum
{As above, but with a list of degrees.}

    S := Set(Degrees);
    for d in S do
	_pg_check_degree(d);
    end for;
    labels := _pg_get_labels(S, Filter);
    Result := [];
    for t in labels do
	Result cat:= [g : n in t[2] | Predicate(g) where g is 
			PrimitiveGroup(t[1], n)];
    end for;
    return Result;
end intrinsic;

intrinsic PrimitiveGroups(Predicate::Program : Filter := "All") -> SeqEnum
{Returns a list of all primitive groups (g) in the database which satisfy Predicate(g)}

    return PrimitiveGroups([1.._pg_lim], Predicate:Filter := Filter);
end intrinsic;

intrinsic PrimitiveGroupDescription(d::RngIntElt, n::RngIntElt) -> MonStgElt
{Return the string description of the n-th primitive group of degree d.}
    return s where _, s is PrimitiveGroup(d, n);
end intrinsic;

delete _pg_lim, _pg_last_n, _pg_lengths, _pg_next;



signature := function(G)
    ord := #G;
    k := Transitivity(G);
    if IsAltsym(G) then
        H := sub<G|>;
    else
        H := BasicStabilizer(G, k+1);
    end if;
    orbs := [t[1]:t in OrbitRepresentatives(H)];
    cf := {* t:t in ChiefFactors(G) *};
    return <ord, k, orbs, cf, IsAffine(G), [#x:x in DerivedSeries(G)]>;
end function;

class_signature := function(G)
    if IsSoluble(G) then
	P,f := PCGroup(G);
	cl := Classes(P);
	return {<c[1], c[2], CycleStructure(c[3] @@ f)>:c in cl};
    else
	cl := Classes(G);
	return {<c[1], c[2], CycleStructure(c[3])>:c in cl};
    end if;
end function;

mat_class_signature := function(G, P)
    cl := Classes(G);
    return {* <c[1], c[2], P!CharacteristicPolynomial(c[3]), 
                P!MinimalPolynomial(c[3])>:c in cl *};
end function;

search_for_order := function(d, ord, f, l)
    if #PrimitiveGroup(d,f) eq ord then
	i := f+1;
	res := [f];
	while  i le l and #PrimitiveGroup(d,i) eq ord do
	    Append(~res, i);
	    i +:= 1;
	end while;
	return res;
    end if;
    if #PrimitiveGroup(d,l) eq ord then
	i := l-1;
	res := [l];
	while  i ge f and #PrimitiveGroup(d,i) eq ord do
	    Append(~res, i);
	    i -:= 1;
	end while;
	return res;
    end if;
    assert #PrimitiveGroup(d,f) lt ord;
    assert #PrimitiveGroup(d,l) gt ord;
    assert l - f gt 1;
    m := (f + l) div 2;
    while m gt f do
	o := #PrimitiveGroup(d, m);
	if o eq ord then
	    res := [m];
	    i := m-1;
	    while  i ge f and #PrimitiveGroup(d,i) eq ord do
		Append(~res, i);
		i -:= 1;
	    end while;
	    i := m+1;
	    while i le l and #PrimitiveGroup(d,i) eq ord do
		Append(~res, i);
		i +:= 1;
	    end while;
	    return res;
	elif o lt ord then
	    f := m;
	else
	    l := m;
	end if;
	m := (f + l) div 2;
    end while;
    return [];
end function;

intrinsic PrimitiveGroupIdentification(G :: GrpPerm) -> RngIntElt, RngIntElt
{Return number and degree of the group conjugate to G in the primitive group database}
    d := Degree(G);
    require d ge 1 and d le PrimitiveGroupDatabaseLimit(): "Degree of group outside database limits";
    require IsPrimitive(G): "Group is not primitive";
    N := NumberOfPrimitiveGroups(d);
    if IsAltsym(G) then
	if IsSymmetric(G) then
	    return N, d;
	else
	    return N-1, d;
	end if;
    end if;
    S := Socle(G);
    if IsAffine(G) then
	nsol := NumberOfPrimitiveSolubleGroups(d);
	if IsSoluble(G) then
	    possibles := search_for_order(d, #G, 1, nsol);
	else
	    possibles := search_for_order(d, #G, nsol +1,
		NumberOfPrimitiveAffineGroups(d));
	end if;
    else
	if IsSimpleOrder(#S) then
	    last := N-2;
	    first := N - NumberOfPrimitiveAlmostSimpleGroups(d) + 1;
	else
	    last := N - NumberOfPrimitiveAlmostSimpleGroups(d);
	    first := NumberOfPrimitiveAffineGroups(d) + 1;
	end if;
	possibles := search_for_order(d, #G, first, last);
    end if;

    vprintf Primitive: "Identify primitive: %o groups after order\n", #possibles;
    vprintf Primitive, 2: "%o\n",  possibles;
    assert #possibles gt 0;
    if #possibles eq 1 then 
	return possibles[1], d;
    end if;

    sig := signature(G);
    possibles := [<i,H>: i in possibles|signature(H) eq sig 
	where H is PrimitiveGroup(d, i)];

    vprintf Primitive: "Identify primitive: %o groups after signature\n", #possibles;
    vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];
    assert #possibles gt 0;
    if #possibles eq 1 then 
	return possibles[1,1], d;
    end if;

    sig := AbelianInvariants(AbelianQuotient(G));
    possibles := [t : t in possibles | AbelianInvariants(AbelianQuotient(t[2]))
			eq sig];
    vprintf Primitive: "Identify primitive: %o groups after AQI\n", #possibles;
    vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];
    assert #possibles gt 0;
    if #possibles eq 1 then 
	return possibles[1,1], d;
    end if;

    sig := [signature(H): H in DerivedSeries(G)];
    possibles := [t : t in possibles | [signature(H): H in DerivedSeries(t[2])]
	eq sig ];

    vprintf Primitive: "Identify primitive: %o groups after derived\n", #possibles;
    vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];
    assert #possibles gt 0;
    if #possibles eq 1 then 
	return possibles[1,1], d;
    end if;

    sig := [signature(Sylow(G, r[1])): r in FactoredOrder(G)];
    // [Sylow(G, r[1]) : r in FactoredOrder(G)]:Magma;
    possibles := [t : t in possibles | sig eq
	[signature(Sylow(t[2], r[1])): r in FactoredOrder(t[2])]];

    vprintf Primitive: "Identify primitive: %o groups after sylow\n", #possibles;
    vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];
    assert #possibles gt 0;
    if #possibles eq 1 then 
	return possibles[1,1], d;
    end if;

    sig := [[AbelianQuotientInvariants(x): x in LowerCentralSeries(PCGroup(
		Sylow(G, r[1])))]: r in FactoredOrder(G)];
    possibles := [t : t in possibles | sig eq
	[[AbelianQuotientInvariants(x): x in LowerCentralSeries(PCGroup(
	    Sylow(t[2], r[1])))]: r in FactoredOrder(G)] ];

    vprintf Primitive: "Identify primitive: %o groups after sylow lcs\n", #possibles;
    vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];
    assert #possibles gt 0;
    if #possibles eq 1 then 
	return possibles[1,1], d;
    end if;

    if IsAffine(G) then
	sig := MatrixQuotient(G);
	possibles := [t : t in possibles | 
	    IsGLConjugate(sig, MatrixQuotient(t[2]))];
	vprintf Primitive: "Identify primitive: %o groups GL conjugacy\n",
	    #possibles;
	vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];
	assert #possibles eq 1;
	if #possibles eq 1 then
	    return possibles[1,1], d;
	end if;
    end if; /* affine test */

    if HasComputableSubgroups(G) then
	possibles := [ t: t in possibles | IsIsomorphic(G, t[2]) ];
	vprintf Primitive: "Identify primitive: %o groups after isomorphism\n",
			#possibles;
	vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];
	assert #possibles gt 0;
	if #possibles eq 1 then
	    return possibles[1,1], d;
	end if;
    end if;

    for r in FactoredOrder(G) do
	sig := class_signature(Sylow(G, r[1]));
	possibles := [t : t in possibles | sig eq
	    class_signature(Sylow(t[2], r[1]))];
	assert #possibles gt 0;
	if #possibles eq 1 then 
	    vprintf Primitive: "Identify primitive: %o groups after sylow classes\n", #possibles;
	    vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];
	    return possibles[1,1], d;
	end if;
    end for;

    vprintf Primitive: "Identify primitive: %o groups after sylow classes\n", #possibles;
    vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];

/*
    if IsAffine(G) then
	f := Factorization(d);
	P := PolynomialRing(GF(f[1,1]));
	sig := mat_class_signature(MatrixQuotient(G), P);
	possibles := [t : t in possibles | sig eq
	    mat_class_signature(MatrixQuotient(t[2]), P)];
	vprintf Primitive: "Identify primitive: %o groups after matrix classes\n",
	    #possibles;
	vprintf Primitive, 2: "%o\n", [t[1]: t in possibles];
	assert #possibles gt 0;
	if #possibles eq 1 then
	    return possibles[1,1], d;
	end if;
    end if; 
*/

    /* ERROR - haven't got it yet !!! */
    G:Magma;
    error "Failed to identify primitive group: please report to magma@maths.usyd.edu.au";

end intrinsic;

_pg_sims_to_new := 
[
  [ 1 ],
  [ 1 ],
  [ 1, 2 ],
  [ 1, 2 ],
  [ 1, 2, 3, 4, 5 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7 ],
  [ 1, 2, 4, 5, 3, 6, 7 ],
  [ 1, 4, 2, 3, 5, 6, 7, 8, 9, 10, 11 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8 ],
  [ 1, 2, 3, 4, 5, 6 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 12, 9, 11, 10, 14, 13, 15, 16, 17, 18, 19, 20, 21, 
  22 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7 ],
  [ 1, 2, 3, 4, 5 ],
  [ 1, 2, 3, 6, 4, 5, 7, 8, 9, 10, 11, 15, 12, 13, 14, 16, 17, 18, 19, 20, 21, 
  23, 22, 24, 25, 26, 27, 28 ],
  [ 1, 2, 3, 4, 5, 6, 7 ],
  [ 1, 2, 3, 5, 4, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 ],
  [ 1, 2, 4, 5, 3, 6, 7 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2 ],
  [ 1, 2, 3, 4, 5, 6 ],
  [ 9, 11, 10, 12, 13, 14, 1, 15, 2, 3, 16, 4, 17, 18, 5, 19, 6, 7, 8, 20, 21, 
  22 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
  [ 1, 2, 3, 4 ],
  [ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
  [ 1, 2 ],
  [ 1, 2, 3, 4, 5, 6 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 16, 19, 20, 21, 
  22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 33, 35, 36, 37, 38, 39, 40 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ]
];

_pg_new_to_sims :=
[
  [ 1 ],
  [ 1 ],
  [ 1, 2 ],
  [ 1, 2 ],
  [ 1, 2, 3, 4, 5 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7 ],
  [ 1, 2, 5, 3, 4, 6, 7 ],
  [ 1, 3, 4, 2, 5, 6, 7, 8, 9, 10, 11 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8 ],
  [ 1, 2, 3, 4, 5, 6 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 11, 9, 14, 13, 15, 16, 17, 18, 19, 20, 21, 
  22 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7 ],
  [ 1, 2, 3, 4, 5 ],
  [ 1, 2, 3, 5, 6, 4, 7, 8, 9, 10, 11, 13, 14, 15, 12, 16, 17, 18, 19, 20, 21, 
  23, 22, 24, 25, 26, 27, 28 ],
  [ 1, 2, 3, 4, 5, 6, 7 ],
  [ 1, 2, 3, 5, 4, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 ],
  [ 1, 2, 5, 3, 4, 6, 7 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2 ],
  [ 1, 2, 3, 4, 5, 6 ],
  [ 7, 9, 10, 12, 15, 17, 18, 19, 1, 3, 2, 4, 5, 6, 8, 11, 13, 14, 16, 20, 21, 
  22 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
  [ 1, 2, 3, 4 ],
  [ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
  [ 1, 2 ],
  [ 1, 2, 3, 4, 5, 6 ],
  [ 1, 2, 3, 4 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 16, 17, 19, 20, 21, 
  22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 33, 35, 36, 37, 38, 39, 40 ],
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ]
];

intrinsic PrimitiveGroupSims(d::RngIntElt, n::RngIntElt) -> GrpPerm, MonStgElt, MonStgElt
{Primitive group (d,n) in the numbering of Sims lists for degree <= 50}
    require 1 le d and d le 50 : "Degree out of range [1..50]";
    require 1 le n and n le #_pg_sims_to_new[d] : "Group number out of range";
    return PrimitiveGroup(d, _pg_sims_to_new[d, n]);
end intrinsic;

intrinsic PrimitiveGroupLabelToSims(d::RngIntElt, n::RngIntElt) -> RngIntElt, RngIntElt
{The number and degree of PrimitiveGroup(d,n) in Sims lists for degree <= 50}
    require 1 le d and d le 50 : "Degree out of range [1..50]";
    require 1 le n and n le #_pg_sims_to_new[d] : "Group number out of range";
    return _pg_new_to_sims[d,n], d;
end intrinsic;

intrinsic PrimitiveGroupLabelFromSims(d::RngIntElt, n::RngIntElt) -> RngIntElt, RngIntElt
{The number and degree in the current database of primitive groups corresponding to the group (d,n) in Sims lists for degree <= 50}
    require 1 le d and d le 50 : "Degree out of range [1..50]";
    require 1 le n and n le #_pg_new_to_sims[d] : "Group number out of range";
    return _pg_sims_to_new[d,n], d;
end intrinsic;

delete _pg_sims_to_new, _pg_new_to_sims;
