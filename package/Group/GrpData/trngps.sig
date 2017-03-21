174,1
S,NumberOfTransitiveGroups,The number of groups of degree d stored in the database of transitive groups of small degree,0,1,0,0,0,0,0,0,0,148,,148,-38,-38,-38,-38,-38
S,TransitiveGroup,"Return the n-th transitive group of degree d, together with a description string",0,2,0,0,0,0,0,0,0,148,,0,0,148,,224,298,-38,-38,-38,-38
S,TransitiveGroupDescription,Return the string description of the n-th transitive group of degree d,0,2,0,0,0,0,0,0,0,148,,0,0,148,,298,-38,-38,-38,-38,-38
S,TransitiveGroupDescription,Return the string description of the transitive group G,0,1,0,0,0,0,0,0,0,224,,298,-38,-38,-38,-38,-38
S,TransitiveGroup,"Returns the first group of degree d in the transitive group database, along with a string giving a description of the group",0,1,0,0,0,0,0,0,0,148,,224,298,-38,-38,-38,-38
S,TransitiveGroup,"Returns the first transitive group with degree in Degrees which satisfies Predicate, along with a string giving a description of the group",1,0,1,82,0,148,2,0,0,0,0,0,0,0,-42,,0,0,82,,224,298,-38,-38,-38,-38
S,TransitiveGroup,"Returns the first transitive group of degree d which satisfies Predicate, along with a string giving a description of the group",0,2,0,0,0,0,0,0,0,-42,,0,0,148,,224,298,-38,-38,-38,-38
S,TransitiveGroups,Returns a sequence of all transitive groups of degree d,0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,TransitiveGroups,Returns a sequence of all transitive groups from the database whose degree is in the given sequence,1,0,1,82,0,148,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,TransitiveGroups,Returns a sequence of all transitive groups with degree d which satisfy Predicate,0,2,0,0,0,0,0,0,0,-42,,0,0,148,,82,-38,-38,-38,-38,-38
S,TransitiveGroups,Returns a sequence of all transitive groups with degree in Degrees which satisfy Predicate,1,0,1,82,0,148,2,0,0,0,0,0,0,0,-42,,0,0,82,,82,-38,-38,-38,-38,-38
S,InternalTransitiveGroupProcessIsEmpty,Returns true iff the transitive group process has passed its last group,0,1,0,0,0,0,0,0,0,303,,36,-38,-38,-38,-38,-38
S,InternalNextTransitiveGroup,Moves the transitive group process tuple p to its next group,0,1,0,0,1,0,0,1,1,303,,-38,-38,-38,-38,-38,-38
S,InternalExtractTransitiveGroup,Returns the current group of the transitive group process tuple p,0,1,0,0,0,0,0,0,0,303,,224,298,-38,-38,-38,-38
S,InternalExtractTransitiveGroupLabel,"Returns the label (d,n) of the transitive group process tuple p. This is the degree and number of the current group of p",0,1,0,0,0,0,0,0,0,303,,148,148,-38,-38,-38,-38
S,TransitiveGroupProcess,Returns a transitive group process which will iterate through all groups with degree in Degrees which satisfy Predicate,1,0,1,82,0,148,2,0,0,0,0,0,0,0,-42,,0,0,82,,255,-38,-38,-38,-38,-38
S,TransitiveGroupProcess,Returns a transitive group process which will iterate through all groups with degree in Degrees,1,0,1,82,0,148,1,0,0,0,0,0,0,0,82,,255,-38,-38,-38,-38,-38
S,TransitiveGroupProcess,Returns a transitive group process which will iterate through all groups of degree d,0,1,0,0,0,0,0,0,0,148,,255,-38,-38,-38,-38,-38
S,TransitiveGroupProcess,Returns a transitive group process which will iterate through all groups of degree d which satisfy Predicate,0,2,0,0,0,0,0,0,0,-42,,0,0,148,,255,-38,-38,-38,-38,-38
