freeze;

procedure print_burnside_matrix(L)
    S := Parent("");
    ndigs := function(i)
	if i eq 0 then
	    return 0;
	end if;
	return 1 + $$(i div 10);
    end function;

    get_finish := function(colsin, start, widths)
	leftcols := colsin;
	leftcols -:= widths[start];
	if leftcols lt 0 then return #widths; end if;
	finish := start;
	while leftcols - widths[finish + 1] ge 0 do
	    finish +:= 1;
	    leftcols -:= widths[finish];
	    if finish eq #widths then
		break;
	    end if;
	end while;
	return finish;
    end function;

    build_number := function(n, width)
	if n eq 0 then
	    num := ".";
	else
	    num := IntegerToString(n);
	end if;
	return &cat [S | " ": i in [1 .. width - #num - 1]] cat num cat " ";
    end function;

    build_hdr := function(clwidth, ordwidth, widths, start, finish)
	hdr := &cat [S | " ": i in [1 .. clwidth - 3]] cat "CL ";
	hdr cat:= &cat [S | " ": i in [1 .. ordwidth - 4]] cat "ORD ";
	for i in [start .. finish] do
	    hdr cat:= build_number(i, widths[i]);
	end for;
	return hdr;
    end function;

    build_line := function(L, BM, ix, clwidth, ordwidth, widths, start, finish)
	line := build_number(ix, clwidth);
	line cat:= build_number(Order(L!ix), ordwidth);
	for i in [start .. finish] do
	    line cat:= build_number(BM[ix][i], widths[i]);
	end for;
	return line;
    end function;

    BM := [[NumberOfInclusions(i, j): j in L]: i in L];
    clwidth := Max(2, ndigs(#L)) + 1;
    ordwidth := Max(3, ndigs(Order(Top(L)))) + 1;
    widths := [1 + ndigs(Max(i, Max({x[i]: x in BM}))): i in [1 .. #L]];
    cols := GetColumns();
    start := 1;
    print "";
    repeat
	finish := get_finish(cols - clwidth - ordwidth, start, widths);
	print build_hdr(clwidth, ordwidth, widths, start, finish);
	print "";
	for i in [1 .. #L] do
	    print build_line(L,BM, i, clwidth, ordwidth, widths, start, finish);
	end for;
	start := finish + 1;
	print "";
    until finish eq #L;
end procedure;

intrinsic DisplayBurnsideMatrix(L::SubGrpLat)
{Display the Burnside matrix corresponding to the lattice of subgroups L}
    print_burnside_matrix(L);
end intrinsic;

intrinsic DisplayBurnsideMatrix(G::GrpPerm)
{Display the Burnside matrix corresponding to the lattice of subgroups of G}
    print_burnside_matrix(SubgroupLattice(G));
end intrinsic;

intrinsic DisplayBurnsideMatrix(G::GrpPC)
{Display the Burnside matrix corresponding to the lattice of subgroups of G}
    print_burnside_matrix(SubgroupLattice(G));
end intrinsic;

intrinsic BurnsideMatrix(G::GrpPerm) -> AlgMatElt
{The Burnside matrix corresponding to the lattice of subgroups of G}
    L := SubgroupLattice(G);
    return BurnsideMatrix(L);
end intrinsic;

intrinsic BurnsideMatrix(G::GrpPC) -> AlgMatElt
{The Burnside matrix corresponding to the lattice of subgroups of G}
    L := SubgroupLattice(G);
    return BurnsideMatrix(L);
end intrinsic;

intrinsic BurnsideMatrix(L::SubGrpLat) -> AlgMatElt
{The Burnside matrix corresponding to the lattice of subgroups L}
    n := #L;
    Z := MatrixAlgebra(Integers(), n) ! 0;
    for i := 1 to n do
	for j := 1 to n do
	    Z[i, j] := NumberOfInclusions(L ! i, L ! j);
	end for;
    end for;
    return Z;
end intrinsic;

intrinsic TableOfMarks(L::SubGrpLat) -> AlgMatElt
{The Burnside table of marks corresponding to the lattice of subgroups L}
    n := #L;
    Z := MatrixAlgebra(Integers(), n) ! 0;
    Gord := Order(Top(L));
    for j := 1 to n do
	Lj := L!j;
	ind_j := Gord div Order(Lj);
	for i := 1 to j do
	    Li := L!i;
	    Z[j, i] := (NumberOfInclusions(Li, Lj) * ind_j)
			    div Length(Li);
	end for;
    end for;
    return Z;
end intrinsic;

intrinsic TableOfMarks(G::GrpPerm) -> AlgMatElt
{The Burnside table of marks corresponding to the lattice of subgroups of G}
    L := SubgroupLattice(G);
    return TableOfMarks(L);
end intrinsic;

intrinsic TableOfMarks(G::GrpPC) -> AlgMatElt
{The Burnside table of marks corresponding to the lattice of subgroups of G}
    L := SubgroupLattice(G);
    return TableOfMarks(L);
end intrinsic;

