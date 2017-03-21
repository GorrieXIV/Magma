174,1
V,Primitive,2
S,InternalPrimitiveGroupProcessIsEmpty,Returns true if the primitive group process has passed its last group,0,1,0,0,0,0,0,0,0,303,,36,-38,-38,-38,-38,-38
S,InternalNextPrimitiveGroup,Moves the primitive group process tuple p to its next group,0,1,0,0,1,0,0,1,1,303,,-38,-38,-38,-38,-38,-38
S,PrimitiveGroupProcess,Returns a primitive group process. This will iterate through all groups with degree in Degrees,1,0,1,82,0,148,1,0,0,0,0,0,0,0,82,,255,-38,-38,-38,-38,-38
S,PrimitiveGroupProcess,Returns a primitive group process which will iterate through all groups (g) with degree in Degrees which satisfy Predicate(g),1,0,1,82,0,148,2,0,0,0,0,0,0,0,-42,,0,0,82,,255,-38,-38,-38,-38,-38
S,PrimitiveGroupProcess,Returns a primitive group process. This will iterate through all groups of degree d,0,1,0,0,0,0,0,0,0,148,,255,-38,-38,-38,-38,-38
S,PrimitiveGroupProcess,Returns a primitive group process. This will iterate through all groups of degree d which satisfy Predicate(g),0,2,0,0,0,0,0,0,0,-42,,0,0,148,,255,-38,-38,-38,-38,-38
S,PrimitiveGroupProcess,Returns a primitive group process. This will iterate through all groups,0,0,0,0,0,0,0,255,-38,-38,-38,-38,-38
S,PrimitiveGroupProcess,Returns a primitive group process. This will iterate through all groups which satisfy Predicate(g),0,1,0,0,0,0,0,0,0,-42,,255,-38,-38,-38,-38,-38
S,InternalExtractPrimitiveGroup,Returns the current group of the primitive group process tuple p,0,1,0,0,0,0,0,0,0,303,,224,298,298,-38,-38,-38
S,InternalExtractPrimitiveGroupLabel,"Returns the label (s,n) of the primitive group process tuple p. This is the degree and number of the current group of p",0,1,0,0,0,0,0,0,0,303,,148,148,-38,-38,-38,-38
S,PrimitiveGroup,Returns the first group (g) of degree d which satisfies Predicate,0,2,0,0,0,0,0,0,0,-42,,0,0,148,,224,298,298,-38,-38,-38
S,PrimitiveGroup,Returns the first group (g) with degree in Degrees which satisfies the predicate,1,0,1,82,0,148,2,0,0,0,0,0,0,0,-42,,0,0,82,,224,298,-38,-38,-38,-38
S,PrimitiveGroup,Returns the first primitive group of degree d,0,1,0,0,0,0,0,0,0,148,,224,298,-38,-38,-38,-38
S,PrimitiveGroups,Returns a sequence of all primitive groups of degree d. Some degrees will produce a very large sequence of groups -- in such cases a warning will be printed unless the user specifies Warning := false,0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,PrimitiveGroups,"As above, but with a list of degrees",1,0,1,82,0,148,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,PrimitiveGroups,"As above, but with all legal degrees",0,0,0,0,0,0,0,82,-38,-38,-38,-38,-38
S,PrimitiveGroups,Returns a list of all groups (g) with degree d which satisfy Predicate(g) eq true,0,2,0,0,0,0,0,0,0,-42,,0,0,148,,82,-38,-38,-38,-38,-38
S,PrimitiveGroups,"As above, but with a list of degrees",1,0,1,82,0,148,2,0,0,0,0,0,0,0,-42,,0,0,82,,82,-38,-38,-38,-38,-38
S,PrimitiveGroups,Returns a list of all primitive groups (g) in the database which satisfy Predicate(g),0,1,0,0,0,0,0,0,0,-42,,82,-38,-38,-38,-38,-38
S,PrimitiveGroupDescription,Return the string description of the n-th primitive group of degree d,0,2,0,0,0,0,0,0,0,148,,0,0,148,,298,-38,-38,-38,-38,-38
S,PrimitiveGroupIdentification,Return number and degree of the group conjugate to G in the primitive group database,0,1,0,0,0,0,0,0,0,224,,148,148,-38,-38,-38,-38
S,PrimitiveGroupSims,"Primitive group (d,n) in the numbering of Sims lists for degree <= 50",0,2,0,0,0,0,0,0,0,148,,0,0,148,,224,298,298,-38,-38,-38
S,PrimitiveGroupLabelToSims,"The number and degree of PrimitiveGroup(d,n) in Sims lists for degree <= 50",0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,148,-38,-38,-38,-38
S,PrimitiveGroupLabelFromSims,"The number and degree in the current database of primitive groups corresponding to the group (d,n) in Sims lists for degree <= 50",0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,148,-38,-38,-38,-38
