freeze;

/*
Compute automorphism group of a matrix - defined to be the set of
permutations of the rows and columns of the matrix that leave the matrix
unchanged. If the matrix has r rows and c columns, then the permutations
returned have degree r+c, where each permutation fixes the set R = {1..r}
and the set C = {r+1..r+c}. The permutation of R may be taken as the row
permutation while the column permutation is given by the action on C.

The method used is to convert the matrix into a graph, using an idea from
the nauty 2.4 manual, and compute the automorphism group of the graph by
nauty. The graph has (r+c)*Ceiling(Log(2,s)) vertices, where s is the number
of different values in the matrix.

One could use ideas in Leon's 1991 exposition of partition backtrack methods
to avoid the Log factor above if one were to write specialized code for
this task.

Bill Unger, November 2011.
*/

make_graph := function(M, elts, row_colours, r_set, col_colours, c_set)

    local nr, nc, d, nl, edges, i, j, r, c, Gr, labels, base;

    nr := Nrows(M);
    nc := Ncols(M);
    d := nr + nc;
    if row_colours cmpeq 0 then
	row_colours := [1: i in [1..nr]];
	base := 1;
    else
	assert #row_colours eq nr;
	row_colours := [Index(r_set, i) : i in row_colours];
	base := #r_set;
    end if;
    if col_colours cmpeq 0 then
	col_colours := [base+1: i in [1..nc]];
	ncolours := base + 1;
    else
	assert #col_colours eq nc;
	col_colours := [base+Index(c_set, i) : i in col_colours];
	ncolours := base + #c_set;
    end if;
    colours := row_colours cat col_colours;

    /* how many levels do we need? */
    nl := Ilog(2, #elts);
    if 2^nl lt #elts then nl +:= 1; end if;

    if d*nl ge 2^30 then
	error "Problem too large for graph construction";
    end if;

    assert 2^nl ge #elts;

    /* build up the edge set */
    edges := {};

    /* vertical edges */
    for i := 0 to nl-2 do
	for j := 1 to d do
	    Include(~edges, { i*d+j, (i+1)*d+j} );
	end for;
    end for;

    /* horizontal edges */
    for r := 1 to nr do for c := 1 to nc do
	e := Index(elts, M[r,c]) - 1;
	base := 0;
	while e gt 0 do
	    if IsOdd(e) then
		Include(~edges, { base + r, base + nr + c} );
	    end if;
	    e div:= 2;
	    base +:= d;
	end while;
    end for; end for;

    /* make the graph */
    Gr := Graph< nl*d | edges >;

    /* Set vertex labels to keep vertices at each level separate,
     * and to keep rows and columns separate.
     */
    AssignVertexLabels(~Gr, 
	&cat [ [j + i*ncolours : j in colours] : i in [0..nl-1]]);

    return Gr;

end function;

intrinsic AutomorphismGroup(M::Mtrx : RowColours := 0, ColColours := 0) -> GrpPerm
{The group of row and column permutations of M that leave m invariant}

    R := BaseRing(Parent(M));
    elts := Eltseq(M);
    elts_mset := SequenceToMultiset(elts);
    elts := SequenceToSet(elts);

    /* Trivial cases */
    if Nrows(M) le 1 and Ncols(M) le 1 then
	if Nrows(M) eq 0 or Ncols(M) eq 0 then
	    return Sym(1);
	else
	    A := sub<Sym(2) | >;
	    return A;
	end if;
    end if;

    if Type(R) eq FldFin and IsPrime(#R) and #R le 255 
	and RowColours cmpeq 0 and ColColours cmpeq 0
    then
	return AutomorphismGroupFF(M);
    end if;

    elts := SetToSequence(elts);

    sort_cmp := function(x,y)
	return Multiplicity(elts_mset, y) - Multiplicity(elts_mset, x);
    end function;

    Sort(~elts, sort_cmp);
    elts := {@ x : x in elts @};
    r_set := RowColours cmpeq 0 select 0 else {@ c : c in RowColours @};
    c_set := ColColours cmpeq 0 select 0 else {@ c : c in ColColours @};
    Gr := make_graph(M, elts, RowColours, r_set, ColColours, c_set);
    AGr := AutomorphismGroup(Gr);
    d := Nrows(M) + Ncols(M);
    A := PermutationGroup<d | [ Eltseq(g)[1..d] : g in Generators(AGr) ]>;
    A`Order := #AGr;
    return A;

end intrinsic;

intrinsic IsIsomorphic(M1::Mtrx, M2::Mtrx : LeftRowColours := 0, RightRowColours := 0, LeftColColours := 0, RightColColours := 0) -> BoolElt, GrpPermElt
{Find a permutation of the rows and columns that takes M1 to M2}

    if Nrows(M1) ne Nrows(M2) or Ncols(M1) ne Ncols(M2) then
	return false, _;
    end if;

    R1 := BaseRing(Parent(M1));
    if R1 ne BaseRing(Parent(M2)) then
	return false, _;
    end if;

    elts := Eltseq(M1);
    elts_mset := SequenceToMultiset(elts);

    if elts_mset ne SequenceToMultiset(Eltseq(M2)) then
	return false, _;
    end if;

    elts := SequenceToSet(elts);
    
    /* Trivial cases */
    if Nrows(M1) le 1 and Ncols(M1) le 1 then
	d := Nrows(M1) + Ncols(M1);
	if d eq 0 then d := 1; end if;
	return true, Sym(d).0;
    end if;

    if Type(R1) eq FldFin and IsPrime(#R1) and #R1 le 255 
	and LeftRowColours cmpeq 0 and LeftColColours cmpeq 0
	and RightRowColours cmpeq 0 and RightColColours cmpeq 0
    then
	return IsIsomorphicFF(M1, M2);
    end if;

    elts := SetToSequence(elts);

    sort_cmp := function(x,y)
	return Multiplicity(elts_mset, y) - Multiplicity(elts_mset, x);
    end function;

    Sort(~elts, sort_cmp);

    elts := {@ x : x in elts @};

    r_set := LeftRowColours cmpeq 0 select {@1@}
	else {@c:c in LeftRowColours@};
    temp := RightRowColours cmpeq 0 select {@1@}
	else {@c:c in RightRowColours@};

    if temp ne r_set then return false, _; end if;

    c_set := LeftColColours cmpeq 0 select {@1@}
	else {@c:c in LeftColColours@};
    temp := RightColColours cmpeq 0 select {@1@}
	else {@c:c in RightColColours@};

    if temp ne c_set then return false, _; end if;

    delete temp;

    Gr1 := make_graph(M1, elts, LeftRowColours, r_set, LeftColColours, c_set);
    Gr2 := make_graph(M2, elts,RightRowColours,r_set, RightColColours, c_set);
    fl, m := IsIsomorphic(Gr1, Gr2);
    if not fl then
	return false, _;
    end if;

    d := Nrows(M1) + Ncols(M2);
    V1 := Vertices(Gr1);
    V2 := Vertices(Gr2);
    x := Sym(d) ! [ Index(V2, V1[i]@m) : i in [1..d]];
    // assert M1^x eq M2;
    return true, x;

end intrinsic;

/* Put into C code to resolve conflicts with perm action on code words.
 * I leave this here to define the action of a permutation on a matrix 
 * that this package assumes.
intrinsic '^'(M::Mtrx, x::GrpPermElt) -> Mtrx
{The image of M under the action of x}
    nr:=NumberOfRows(M);
    nc:=NumberOfColumns(M);
    // Sanity check
    d := Degree(Parent(x));
    error if nr + nc ne d or
	{1..nr}^x ne {1..nr},
	"The permutation is incompatible with the matrix";
    // Apply the permutation
    cs:=Eltseq(x^-1);
    rows:=RowSequence(M);
    M:=Matrix([rows[cs[i]] : i in [1..nr]]);
    cols:=RowSequence(Transpose(M));
    return Transpose(Matrix([cols[cs[i + nr] - nr] : i in [1..nc]]));
end intrinsic;
*/

intrinsic IsIsomorphic(X :: SeqEnum[AlgChtrElt], Y :: SeqEnum[AlgChtrElt] : UseClassesData := false) -> BoolElt, GrpPermElt
{}
    XX := [[ [Conductor(Parent(b))] cat Eltseq(b) where b := Minimize(a): 
	    a in Eltseq(x)] : x in X];
    Z := {@ a : a in &cat XX @};
    XX := Matrix([ [ Index(Z, a) : a in x] : x in XX] );
    YY := [[ [Conductor(Parent(b))] cat Eltseq(b) where b := Minimize(a): 
	    a in Eltseq(x)] : x in Y];
    YY := Matrix([ [ Index(Z, a) : a in x] : x in YY] );
    delete Z;
    if UseClassesData then
	cd1 := ClassesData(Universe(X));
	cd2 := ClassesData(Universe(Y));
	if {*x : x in cd1*} ne {*x:x in cd2 *} then return false, _; end if;
	return IsIsomorphic(XX, YY :
	    LeftColColours := cd1, RightColColours := cd2);
    else
	cd1 := [t[2] : t in ClassesData(Universe(X))];
	cd2 := [t[2] : t in ClassesData(Universe(Y))];
	if {*x : x in cd1*} ne {*x:x in cd2 *} then return false, _; end if;
	return IsIsomorphic(XX, YY :
	    LeftColColours := cd1, RightColColours := cd2);
    end if;
end intrinsic;

intrinsic AutomorphismGroup(X :: SeqEnum[AlgChtrElt] : UseClassesData := false) -> GrpPerm
{}
    XX := [[ [Conductor(Parent(b))] cat Eltseq(b) where b := Minimize(a): 
	    a in Eltseq(x)] : x in X];
    Z := {@ a : a in &cat XX @};
    XX := Matrix([ [ Index(Z, a) : a in x] : x in XX] );
    delete Z;
    if UseClassesData then
	cd := ClassesData(Universe(X));
	return AutomorphismGroup(XX : ColColours := cd);
    else
	cd := [t[2] : t in ClassesData(Universe(X))];
	return AutomorphismGroup(XX : ColColours := cd);
    end if;
end intrinsic;
