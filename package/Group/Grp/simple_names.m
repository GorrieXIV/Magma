freeze;
 
family_names := [
"A", "B", "C", "D", "G", "F", "E", "E", "E", "2A", "2B", "2D", "3D", "2G",
"2F", "2E", "Alt", "Sporadic", "Cyclic"];

alt_names := [ "L", "O", "S", "O+", "", "", "", "", "", "U", "Sz", "O-",
"", "R", "R", "", "", "", ""];

sporadic_names := [ "M11", "M12",  "M22", "M23", "M24", "J1", "HS", "J2",
"McL", "Suz", "J3", "Co1", "Co2", "Co3", "He", "Fi22", "Fi23", "Fi24'",
"Ly", "Ru", "O'N", "Th", "HN", "B", "M", "J4"];

simple_name := function(tup)
    fn := family_names[tup[1]];
    an := alt_names[tup[1]];

    case tup[1]:
	when 19: name := &cat[fn, "(", IntegerToString(tup[3]), ")"];
	when 18: name := &cat[fn, " ", sporadic_names[tup[2]]];
	when 17:  name := &cat[fn, "(", IntegerToString(tup[2]), ")"];
	when 1: name := &cat[fn, "(", IntegerToString(tup[2]), ", ",
		    IntegerToString(tup[3]), ")"];
	when 2: name := &cat[fn, "(", IntegerToString(tup[2]), ", ",
		    IntegerToString(tup[3]), ")"];
	when 3: name := &cat[fn, "(", IntegerToString(tup[2]), ", ",
		    IntegerToString(tup[3]), ")"];
	when 4: name := &cat[fn, "(", IntegerToString(tup[2]), ", ",
		    IntegerToString(tup[3]), ")"];
	when 5: name := &cat[fn, "(2, ", IntegerToString(tup[3]), ")"];
	when 6: name := &cat[fn, "(4, ", IntegerToString(tup[3]), ")"];
	when 7: name := &cat[fn, "(6, ", IntegerToString(tup[3]), ")"];
	when 8: name := &cat[fn, "(7, ", IntegerToString(tup[3]), ")"];
	when 9: name := &cat[fn, "(8, ", IntegerToString(tup[3]), ")"];
	when 10: name := &cat[fn, "(", IntegerToString(tup[2]), ", ",
			IntegerToString(tup[3]), ")"];
	when 11: name := &cat[fn, "(2, ", IntegerToString(tup[3]), ")"];
	when 12: name := &cat[fn, "(", IntegerToString(tup[2]), ", ",
			IntegerToString(tup[3]), ")"];
	when 13: name := &cat[fn, "(4, ", IntegerToString(tup[3]), ")"];
	when 14: name := &cat[fn, "(2, ", IntegerToString(tup[3]), ")"];
	when 15: name := &cat[fn, "(4, ", IntegerToString(tup[3]), ")"];
		if tup[3] eq 2 then name cat:= "'"; end if;
	when 16: name := &cat[fn, "(6, ", IntegerToString(tup[3]), ")"];
    end case;

    if #an eq 0 then return name; end if;
    name cat:= &cat["[= ", an, "("];
    case tup[1]:
	when 1: name cat:= &cat[IntegerToString(tup[2]+1), ", ",
		    IntegerToString(tup[3])];
	when 2: name cat:= &cat[IntegerToString(2*tup[2]+1), ", ",
		    IntegerToString(tup[3])];
	when 3: name cat:= &cat[IntegerToString(2*tup[2]), ", ",
		    IntegerToString(tup[3])];
	when 4: name cat:= &cat[IntegerToString(2*tup[2]), ", ",
		    IntegerToString(tup[3])];
	when 10: name cat:= &cat[IntegerToString(tup[2]+1), ", ",
		    IntegerToString(tup[3])];
	when 12: name cat:= &cat[IntegerToString(2*tup[2]), ", ",
		    IntegerToString(tup[3])];
	else
	    name cat:= IntegerToString(tup[3]);
    end case;
    name cat:= ")]";

    return name;
end function;

simple_short_name := function(tup)
    fn := family_names[tup[1]];
    an := alt_names[tup[1]];

    case tup[1]:
	when 19: name := IntegerToString(tup[3]); // cyclic
	when 18: name := sporadic_names[tup[2]];
	when 17:  name := &cat["A(", IntegerToString(tup[2]), ")"];
	when 1: name := &cat[an, "(", IntegerToString(tup[2]+1), ",",
		    IntegerToString(tup[3]), ")"];
	when 2: name := &cat[an, "(", IntegerToString(2*tup[2]+1), ",",
		    IntegerToString(tup[3]), ")"];
	when 3: name := &cat[an, "(", IntegerToString(2*tup[2]), ",",
		    IntegerToString(tup[3]), ")"];
	when 4: name := &cat[an, "(", IntegerToString(2*tup[2]), ",",
		    IntegerToString(tup[3]), ")"];
	when 5: name := &cat[fn, "(2,", IntegerToString(tup[3]), ")"];
	when 6: name := &cat[fn, "(4,", IntegerToString(tup[3]), ")"];
	when 7: name := &cat[fn, "(6,", IntegerToString(tup[3]), ")"];
	when 8: name := &cat[fn, "(7,", IntegerToString(tup[3]), ")"];
	when 9: name := &cat[fn, "(8,", IntegerToString(tup[3]), ")"];
	when 10: name := &cat[an, "(", IntegerToString(tup[2]+1), ",",
		    IntegerToString(tup[3]), ")"];
	when 11: name := &cat[an, "(", IntegerToString(tup[3]), ")"];
	when 12: name := &cat[an, "(", IntegerToString(2*tup[2]), ",",
		    IntegerToString(tup[3]), ")"];
	when 13: name := &cat[fn, "(4,", IntegerToString(tup[3]), ")"];
	when 14: name := &cat[fn, "(2,", IntegerToString(tup[3]), ")"];
	when 15: name := &cat[fn, "(4,", IntegerToString(tup[3]), ")"];
		if tup[3] eq 2 then name cat:= "'"; end if;
	when 16: name := &cat[fn, "(6,", IntegerToString(tup[3]), ")"];
    end case;

    return name;
end function;

simple_nickname := function(tup)
    fn := family_names[tup[1]];
    an := alt_names[tup[1]];

    case tup[1]:
	when 19: name := "Z(" cat IntegerToString(tup[3]) cat ")"; // cyclic
	when 18: name := sporadic_names[tup[2]];
	when 17:  name := &cat["Alt(", IntegerToString(tup[2]), ")"];
	when 1: name := &cat[an, "(", IntegerToString(tup[2]+1), ", ",
		    IntegerToString(tup[3]), ")"];
	when 2: name := &cat[an, "(", IntegerToString(2*tup[2]+1), ", ",
		    IntegerToString(tup[3]), ")"];
	when 3: name := &cat[an, "(", IntegerToString(2*tup[2]), ", ",
		    IntegerToString(tup[3]), ")"];
	when 4: name := &cat[an, "(", IntegerToString(2*tup[2]), ", ",
		    IntegerToString(tup[3]), ")"];
	when 5: name := &cat[fn, "(2, ", IntegerToString(tup[3]), ")"];
	when 6: name := &cat[fn, "(4, ", IntegerToString(tup[3]), ")"];
	when 7: name := &cat[fn, "(6, ", IntegerToString(tup[3]), ")"];
	when 8: name := &cat[fn, "(7, ", IntegerToString(tup[3]), ")"];
	when 9: name := &cat[fn, "(8, ", IntegerToString(tup[3]), ")"];
	when 10: name := &cat[an, "(", IntegerToString(tup[2]+1), ", ",
		    IntegerToString(tup[3]), ")"];
	when 11: name := &cat[an, "(", IntegerToString(tup[3]), ")"];
	when 12: name := &cat[an, "(", IntegerToString(2*tup[2]), ", ",
		    IntegerToString(tup[3]), ")"];
	when 13: name := &cat[fn, "(4, ", IntegerToString(tup[3]), ")"];
	when 14: name := &cat[fn, "(2, ", IntegerToString(tup[3]), ")"];
	when 15: name := &cat[fn, "(4, ", IntegerToString(tup[3]), ")"];
		if tup[3] eq 2 then name cat:= "'"; end if;
	when 16: name := &cat[fn, "(6, ", IntegerToString(tup[3]), ")"];
    end case;

    return name;
end function;

simple_grps_with_order_dividing := function(n)
    divs := Divisors(n);
    res := [];
    for d in divs do fl, tup := IsSimpleOrder(d);
	if fl then 

	    Append(~res, tup);

	    if d eq 20160 then
		if tup[1] eq 17 then Append(~res, <1, 2, 4>); 
	    else Append(~res, <17, 8, 0>); end if;
	    end if;

	    if tup[1] eq 2 and IsOdd(tup[3]) and tup[2] gt 2 then
		Append(~res, <3, tup[2], tup[3]>);
	    end if;

	    if tup[1] eq 3 and IsOdd(tup[3]) and tup[2] gt 2 then
		Append(~res, <2, tup[2], tup[3]>);
	    end if;

	end if;
    end for;
    return res;
end function;

simple_grps_with_order := function(n)
    res := [];
    fl, tup := IsSimpleOrder(n);
    if fl then 

	Append(~res, tup);

	if n eq 20160 then
	    if tup[1] eq 17 then Append(~res, <1, 2, 4>); 
	else Append(~res, <17, 8, 0>); end if;
	end if;

	if tup[1] eq 2 and IsOdd(tup[3]) and tup[2] gt 2 then
	    Append(~res, <3, tup[2], tup[3]>);
	end if;

	if tup[1] eq 3 and IsOdd(tup[3]) and tup[2] gt 2 then
	    Append(~res, <2, tup[2], tup[3]>);
	end if;

    end if;
    return res;
end function;

intrinsic SimpleGroupName(T::Tup) -> MonStgElt
{A name (and a possible alias) for the simple group specified by the tuple T. 
T is assumed to be a tuple as returned by IsSimpleOrder or as part of the 
sequence returned by CompositionFactors}

   return simple_name(T);
end intrinsic;

intrinsic SimpleGroupAlternateName(T::Tup) -> MonStgElt
{A name for the simple group specified by the tuple T. 
T is assumed to be a tuple as returned by IsSimpleOrder or as part of the 
sequence returned by CompositionFactors}

   return simple_nickname(T);
end intrinsic;

intrinsic SimpleGroupsWithOrderDividing(n::RngIntElt:IncludeCyclics:=false) ->
SeqEnum
{Returns a sequence of names for the simple groups that have order dividing n}

   if n le 1 then return []; end if; 

   Q := simple_grps_with_order_dividing(n);
   if IncludeCyclics then 
       return [simple_name(t): t in Q];
   else
       return [simple_name(t): t in Q | t[1] ne 19];
   end if;
end intrinsic;

intrinsic SimpleGroupsWithOrder(n::RngIntElt:IncludeCyclics:=false) ->
SeqEnum
{Returns a sequence of names for the simple groups that have order n}

   if n le 1 then return []; end if; 

   Q := simple_grps_with_order(n);
   if IncludeCyclics then 
       return [simple_name(t): t in Q];
   else
       return [simple_name(t): t in Q | t[1] ne 19];
   end if;
end intrinsic;

delete simple_name, simple_grps_with_order_dividing, family_names, alt_names,
sporadic_names, simple_grps_with_order;

intrinsic SimpleGroupOrder(T::Tup) -> RngIntElt
{The order of the simple group specified by the tuple T. 
T is assumed to be a tuple as returned by IsSimpleOrder or as part of the 
sequence returned by CompositionFactors}
 
    return Integers()!SimpleGroupOrder(T[1], T[2], T[3]);
end intrinsic;

intrinsic HasComputableSubgroups(G::Grp) -> BoolElt
{Can the Subgroups family of functions be applied to G}

    if ISA(Category(G), GrpPC) then return true; end if;

    if not ISA(Category(G), GrpPerm) then
	 if ISA(Category(G), GrpMat) then
	     if not IsFinite(G) then return false; end if;
	     K := BaseRing(G);
	     if not (IsField(K) or IsDomain(K) or Type(K) eq RngIntRes) then
		return false;
	    end if;
	 else
	     return false;
	 end if;
    end if;

    if #G le 16000000 then 
	return true; 
    end if;

    cf := Seqset(CompositionFactors(G));
    D := AlmostSimpleGroupDatabase();

    for c in cf do
	if c[1] eq 19 then continue; end if; //prime order
	if c[1] eq 17 and c[2] le 2499 then continue; end if; //alternating
	if c[1] eq 1 and c[2] le 6  then 
	    continue; // L(2,q), L(3,q), L(4,q), L(5,q), L(6,q), L(7,q)
	end if; 
	if c[1] eq 1 and c[2] lt 14 and c[3] eq 2 then
	    continue;	// L(d,2), d <= 14
	end if;
	if c[1] eq 10 and
	    (c[2] le 3  or (c[2] eq 4 and c[3] eq 3) or
	    (c[2] le 7 and c[3] eq 2))
	then
		continue; // U(3,q), U(4,q), U(5,3), U(6,2), U(7,2), U(8,2)
	end if;
	if c[1] eq 3 and
	    ( c[2] eq 2 or (c[2] eq 3 and c[3] le 5) or
	    (c[2] eq 4 and c[3] eq 3) or (c[2] le 6 and c[3] eq 2) )
	then 
	    continue; // S(4,q), S(6,4), S(6,5), S(8, 3), S((6,8,10,12), 2)
	end if;
	o := SimpleGroupOrder(<c[1], c[2], c[3]>);
	if o le 16000000 then
	    continue;
	end if;
	// trap the extras
	if o in {17971200, // Tits'
		174182400, // O+(8,2)
		197406720, // O-(8,2)
		211341312, // 3D4(2)
		251596800, //G24
		4030387200, // He
		4585351680, //S63 or O73
		5859000000, //G25
		145926144000, // Ru
		448345497600, // Suz
		460815505920, // O'Nan
		495766656000, // Co3
		4952179814400,  // O+(8,3)
		10151968619520, // O-(8,3)
		23499295948800, // O+(10,2)
		25015379558400, // O-(10,2)
		42305421312000, // Co2
		64561751654400,  // Fi22
		228501000000000, // O(7,5)
		65784756654489600,	// O(9,3)
		67010895544320000,	// O+(8,4)
		67536471195648000,	// O-(8,4)
		1289512799941305139200, //O+(10,3)
		650084965259666227200,  //O-(10,3)
		50027557148216524800,	// O+(12,2)
		51615733565620224000	// O-(12,2)
		} then continue; end if;
	if not ExistsGroupData(D, o, o) then return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic ChiefFactorsToString(Q::SeqEnum[Tup]) -> MonStgElt
{A string representing the chief factors sequence Q}
    str := "";
    for i := #Q to 1 by -1 do
	t := Q[i];
	s := <t[1],t[2],t[3]>;
	str cat:= simple_short_name(s);
	if t[4] gt 1 then 
	    str cat:= "^";
	    str cat:= IntegerToString(t[4]);
	end if;
	if i gt 1 then str cat:= "."; end if;
    end for;
    return str;
end intrinsic;

