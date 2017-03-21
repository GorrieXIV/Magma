174,1
S,IsInSmallGroupDatabase,Return true iff the small groups database contains the groups of order o,0,1,0,0,0,0,0,0,0,148,,36,-38,-38,-38,-38,-38
S,IsInSmallGroupDatabase,Return true iff D contains the groups of order o,0,2,0,0,0,0,0,0,0,148,,0,0,53,,36,-38,-38,-38,-38,-38
S,CanIdentifyGroup,Return true iff groups of order o can be identified in the small groups database,0,1,0,0,0,0,0,0,0,148,,36,-38,-38,-38,-38,-38
S,IsSoluble,"Return true iff SmallGroup(D, o, n) is soluble",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,53,,36,-38,-38,-38,-38,-38
S,SmallGroup,Returns the group number n of order o from the small groups database,0,2,0,0,0,0,0,0,0,148,,0,0,148,,-27,-38,-38,-38,-38,-38
S,SmallGroupIsSolvable,"Return true if SmallGroup(D, o, n) is soluble (does not load the group)",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,53,,36,-38,-38,-38,-38,-38
S,SmallGroupIsSoluble,"Return true if SmallGroup(D, o, n) is soluble (does not load the group)",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,53,,36,-38,-38,-38,-38,-38
S,SmallGroupIsSolvable,"Return true if SmallGroup(o, n) is soluble (does not load the group)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,SmallGroupIsSoluble,"Return true if SmallGroup(o, n) is soluble (does not load the group)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,SmallGroupIsInsolvable,"Return true if SmallGroup(o, n) is insoluble (does not load the group)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,SmallGroupIsInsoluble,"Return true if SmallGroup(o, n) is insoluble (does not load the group)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,SmallGroupIsInsolvable,"Return true if SmallGroup(D, o, n) is insoluble (does not load the group)",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,53,,36,-38,-38,-38,-38,-38
S,SmallGroupIsInsoluble,"Return true if SmallGroup(D, o, n) is insoluble (does not load the group)",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,53,,36,-38,-38,-38,-38,-38
S,IdentifyGroup,The size and number of the group isomorphic to G in the small groups database,0,1,0,0,0,0,0,0,0,-27,,303,-38,-38,-38,-38,-38
S,NumberOfSmallGroups,The number of groups of order n stored in the database D,0,2,0,0,0,0,0,0,0,148,,0,0,53,,148,-38,-38,-38,-38,-38
S,NumberOfSmallGroups,The number of groups of order n stored in the database of small groups,0,1,0,0,0,0,0,0,0,148,,148,-38,-38,-38,-38,-38
S,SmallGroupDatabaseLimit,The order up to which the small groups database D contains all groups,0,1,0,0,0,0,0,0,0,53,,148,-38,-38,-38,-38,-38
S,SmallGroupDatabaseLimit,The order up to which the small groups database contains all groups,0,0,0,0,0,0,0,148,-38,-38,-38,-38,-38
S,SmallGroupDatabase,"Return the small groups database, opened for an extended search",0,0,0,0,0,0,0,53,-38,-38,-38,-38,-38
S,OpenSmallGroupDatabase,"Return the small groups database, opened for an extended search",0,0,0,0,0,0,0,53,-38,-38,-38,-38,-38
S,CloseSmallGroupDatabase,Close the smallgroup database,0,1,0,0,1,0,0,1,1,53,,-38,-38,-38,-38,-38,-38
S,InternalNextSmallGroup,Moves the small group process tuple p to its next group,0,1,0,0,1,0,0,1,1,303,,-38,-38,-38,-38,-38,-38
S,InternalSmallGroupProcessRestart,Returns the small group process tuple p to its first group,0,1,0,0,1,0,0,1,1,303,,-38,-38,-38,-38,-38,-38
S,SmallGroupProcess,"Returns a small group process. This will iterate through all groups with order in Orders. To extract the current group from a process, use ExtractGroup(). To move to the next group in a process, use NextGroup(). To find out which group the process currently points to, use ExtractLabel(). The user may limit the process to soluble or insoluble groups by setting Search. Search may take the values ""All"", ""Soluble"" or ""Insoluble"" (or variants thereof)",1,0,1,82,0,148,1,0,0,0,0,0,0,0,82,,255,-38,-38,-38,-38,-38
S,SmallGroupProcess,Returns a small group process as described above. This will iterate through all groups (g) with order in Orders which satisfy Predicate(g),1,0,1,82,0,148,2,0,0,0,0,0,0,0,-42,,0,0,82,,255,-38,-38,-38,-38,-38
S,SmallGroupProcess,Returns a small group process as described above. This will iterate through all groups with order o,0,1,0,0,0,0,0,0,0,148,,255,-38,-38,-38,-38,-38
S,SmallGroupProcess,Returns a small group process as described above. This will iterate through all groups (g) of order o which satisfy Predicate(g),0,2,0,0,0,0,0,0,0,-42,,0,0,148,,255,-38,-38,-38,-38,-38
S,InternalSmallGroupProcessIsEmpty,Returns true if the small group process tuple has passed its last group,0,1,0,0,0,0,0,0,0,303,,36,-38,-38,-38,-38,-38
S,InternalExtractSmallGroup,Returns the current group of the small group process tuple p,0,1,0,0,0,0,0,0,0,303,,-27,-38,-38,-38,-38,-38
S,InternalExtractSmallGroupLabel,"Returns the label (s,n) of the small group process tuple p. This is the order and number of the current group of p",0,1,0,0,0,0,0,0,0,303,,148,148,-38,-38,-38,-38
S,SmallGroup,"Returns the first group of order o which satisfies Predicate. The user may limit the the search to soluble or insoluble groups by setting the parameter Search. Search may take the values ""All"", ""Soluble"" or ""Insoluble"" (or variants)",0,3,0,0,0,0,0,0,0,-42,,0,0,148,,0,0,53,,-27,-38,-38,-38,-38,-38
S,SmallGroup,"Returns the first group of order o which satisfies Predicate. The user may limit the the search to soluble or insoluble groups by setting the parameter Search. Search may take the values ""All"", ""Soluble"" or ""Insoluble"" (or variants)",0,2,0,0,0,0,0,0,0,-42,,0,0,148,,-27,-38,-38,-38,-38,-38
S,SmallGroup,Returns the first group with order in Orders which satisfies the predicate and the search condition specified by Search (see above),0,2,0,0,0,0,0,0,0,-42,,0,0,82,,-27,-38,-38,-38,-38,-38
S,SmallGroup,Returns the first group with order in Orders which satisfies the predicate and the search condition specified by Search (see above),0,3,0,0,0,0,0,0,0,-42,,0,0,82,,0,0,53,,-27,-38,-38,-38,-38,-38
S,SmallGroup,Returns the first group of order o which satisfies the search condition specified by Search (see above),0,1,0,0,0,0,0,0,0,148,,-27,-38,-38,-38,-38,-38
S,SmallGroup,Returns the first group of order o which satisfies the search condition specified by Search (see above),0,2,0,0,0,0,0,0,0,148,,0,0,53,,-27,-38,-38,-38,-38,-38
S,SmallGroups,"Returns a list of all groups of order o. The user may limit the search to soluble or insoluble groups by setting the parameter Search. Search may take the value ""All"", ""Soluble"" or ""Insoluble"" (or variants thereof). Some orders will produce a very large list of groups -- in such cases a warning will be printed unless the user specifies Warning := false",0,2,0,0,0,0,0,0,0,148,,0,0,53,,168,-38,-38,-38,-38,-38
S,SmallGroups,"Returns a list of all groups of order o. The user may limit the search to soluble or insoluble groups by setting the parameter Search. Search may take the value ""All"", ""Soluble"" or ""Insoluble"" (or variants thereof). Some orders will produce a very large list of groups -- in such cases a warning will be printed unless the user specifies Warning := false",0,1,0,0,0,0,0,0,0,148,,168,-38,-38,-38,-38,-38
S,SmallGroups,"As above, but with a list of orders",0,2,0,0,0,0,0,0,0,82,,0,0,53,,168,-38,-38,-38,-38,-38
S,SmallGroups,"As above, but with a list of orders",0,1,0,0,0,0,0,0,0,82,,168,-38,-38,-38,-38,-38
S,SmallGroups,Returns a list of all groups (g) with order o which satisfy Predicate(g) eq true and the search condition specified by Search,0,3,0,0,0,0,0,0,0,-42,,0,0,148,,0,0,53,,168,-38,-38,-38,-38,-38
S,SmallGroups,Returns a list of all groups (g) with order o which satisfy Predicate(g) eq true and the search condition specified by Search,0,2,0,0,0,0,0,0,0,-42,,0,0,148,,168,-38,-38,-38,-38,-38
S,SmallGroups,"As above, but with a list of orders",0,3,0,0,0,0,0,0,0,-42,,0,0,82,,0,0,53,,168,-38,-38,-38,-38,-38
S,SmallGroups,"As above, but with a list of orders",0,2,0,0,0,0,0,0,0,-42,,0,0,82,,168,-38,-38,-38,-38,-38
S,SmallGroupEncoding,Encode a pc-group as an integer using the small groups data coding,0,1,0,0,0,0,0,0,0,129,,148,148,-38,-38,-38,-38
S,SmallGroupDecoding,Decode a small groups data code representing a pc-group,0,2,0,0,0,0,0,0,0,148,,0,0,148,,129,-38,-38,-38,-38,-38
