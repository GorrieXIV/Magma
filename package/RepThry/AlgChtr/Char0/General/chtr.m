freeze;

char_cmp := func<chi, psi |
    case<true | nc lt np: -1, nc eq np: 0, default: 1>
	where nc is Norm(chi)
	where np is Norm(psi)
>;

rem_irrs := func<Irr, chi |
    #Irr eq 0 select
	chi
    else
	psi where _, psi := Decomposition(Irr, chi)
>;

Z := Integers();

red := function(Chs1, Chs2)
    norms := [Z!Norm(x): x in Chs1];
    found := {@ @};
    remainders := {@ @};
    for i in [1 .. #Chs2] do
	chi := Chs2[i];
	for j in [1 .. #Chs1] do
	    psi := Chs1[j];
	    ip := InnerProduct(chi, psi);
	    error if not IsIntegral(ip), "Non-character in one or both lists";
	    if not IsZero(ip) then
		chi := chi - (Z!ip div norms[j]) * psi;
	    end if;
	end for;
	if not IsZero(chi) then
	    if Z!Degree(chi) lt 0 then
		chi := -chi;
	    end if;
	    if Norm(chi) eq 1 then
		Include(~found, chi);
	    else
		Include(~remainders, chi);
	    end if;
	end if;
    end for;
    if #found eq 0 then
	return [], Sort([y: y in remainders], char_cmp);
    else
	irr, remainders := $$(found, remainders);
	found := {@ x: x in irr @} join found;
	return Sort([y: y in found], char_cmp),
	       Sort([y: y in remainders], char_cmp);
    end if;
end function;

red1 := function(Chs1)
    norms := [Z!Norm(x): x in Chs1];
    found := {@ @};
    remainders := {@ @};
    for i in [1 .. #Chs1] do
	chi := Chs1[i];
	for j in [1 .. i - 1] do
	    psi := Chs1[j];
	    ip := InnerProduct(chi, psi);
	    error if not IsIntegral(ip), "Non-character in lists";
	    if not IsZero(ip) then
		chi := chi - (Z!ip div norms[j]) * psi;
	    end if;
	end for;
	if not IsZero(chi) then
	    if Z!Degree(chi) lt 0 then
		chi := -chi;
	    end if;
	    if Norm(chi) eq 1 then
		Include(~found, chi);
	    else
		Include(~remainders, chi);
	    end if;
	end if;
    end for;
    if #found eq 0 then
	return [], Sort([y: y in remainders], char_cmp);
    else
	irr, remainders := red(found, remainders);
	found := {@ x: x in irr @} join found;
	return Sort([y: y in found], char_cmp),
	       Sort([y: y in remainders], char_cmp);
    end if;
end function;

ri := function(Irrs, Chs)
    NewIrrs := [];
    X := Irrs;
    Y := Chs;
    repeat
	Y := {@ rem_irrs(X, chi): chi in Y @};
	pos := {@ i: i in [1 .. #Y] | Norm(Y[i]) eq 1 @};
	X := [Z!Degree(Y[i]) gt 0 select Y[i] else -Y[i]: i in pos];
	NewIrrs cat:= X;
	Y := [Y[i]: i in [1 .. #Y] | i notin pos and not IsZero(Y[i])];
    until #pos eq 0 or #Y eq 0;
    return NewIrrs, Sort(Y, char_cmp);
end function;

inn_prods := func<Chs1, Chs2 |
    [[Z!InnerProduct(Chs1[i], Chs2[j]): j in [1 .. #Chs2]]: i in [1 .. #Chs1]]
>;

inn_prods_tri := func<Chs |
    [[Z!InnerProduct(Chs[i], Chs[j]): j in [1 .. i]]: i in [1 .. #Chs]]
>;

is_irr_diff := func<IP, i, j | IP[i][i] + IP[j][j] - 2 * IP[i][j] eq 1>;

irr_diffs := function(Chs1, Chs2: InnerProducts := inn_prods(Chs1, Chs2))
    irr_diffs := {@ @};
    norms1 := [Z!Norm(x): x in Chs1];
    norms2 := [Z!Norm(x): x in Chs2];
    for i in [1 .. #Chs1] do
	for j in [1 .. #Chs2] do
	    if norms1[i] + norms2[j] - 2 * InnerProducts[i][j] eq 1 then
		if Z!Degree(Chs1[i]) gt Z!Degree(Chs2[j]) then
		    Include(~irr_diffs, Chs1[i] - Chs2[j]);
		else
		    Include(~irr_diffs, Chs2[j] - Chs1[i]);
		end if;
	    end if;
	end for;
    end for;
    return Sort([chi: chi in irr_diffs], char_cmp);
end function;

irr_diffs_tri := function(Chs: InnerProducts := inn_prods_tri(Chs))
    irr_diffs := {@ @};
    for i in [1 .. #Chs] do
	for j in [1 .. i - 1] do
	    if is_irr_diff(InnerProducts, i, j) then
		if Z!Degree(Chs[i]) gt Z!Degree(Chs[j]) then
		    Include(~irr_diffs, Chs[i] - Chs[j]);
		else
		    Include(~irr_diffs, Chs[j] - Chs[i]);
		end if;
	    end if;
	end for;
    end for;
    return Sort([chi: chi in irr_diffs], char_cmp);
end function;

is_subtractible := func<IP, i, j |
    ni ne nj and ni*nj - nij^2 lt Max(ni, nj)
    where ni is IP[i][i]
    where nj is IP[j][j]
    where nij is IP[i][j]
>;

char_diffs_tri := function(Chs: InnerProducts := inn_prods_tri(Chs))
    char_diffs := {@ @};
    for i in [1 .. #Chs] do
	for j in [1 .. i - 1] do
	    if is_subtractible(InnerProducts, i, j) then
		if InnerProducts[i][i] gt InnerProducts[j][j] then
		    Include(~char_diffs, Chs[i] - Chs[j]);
		else
		    Include(~char_diffs, Chs[j] - Chs[i]);
		end if;
	    end if;
	end for;
    end for;
    return Sort([chi: chi in char_diffs], char_cmp);
end function;

intrinsic RemoveIrreducibles(Irr::[AlgChtrElt], Chs::[AlgChtrElt]) -> [], []
{Remove occurrences of the irreducibles in Irr from the characters in Chs and
look for new irreducibles in the reduced set.  Return a sequence of new
irreducibles found and the sequence of reduced characters}
    return red(Irr, Chs);
end intrinsic;

intrinsic ReduceCharacters(Irr::[AlgChtrElt], Chs::[AlgChtrElt]) -> [], []
{Make the norms of the characters in Chs smaller by computing the differences
of appropriate pairs.  Return a sequence of new irreducibles found and
a sequence of reduced characters}
    X, Y := red(Irr, Chs);
    A, Y := red1(Y);
    return X cat A, Y;
end intrinsic;
