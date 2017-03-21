freeze;

chief_character_spaces := function(CP, D)
    V := CP`V;
    K := CP`K;
    one := K!1;
    known := sub<V|CP`Irreds>;
    bm := BasisMatrix(known);
    dim := Dimension(known);
    n := CP`n_Classes;
    mat := ZeroMatrix(K, dim, n);
    invs := CP`Invs;
    sizes := CP`Sizes;
    for i := 1 to n do
	size := sizes[i];
	c := invs[i];
	for r := 1 to dim do
	    mat[r, c] := bm[r, i] * size;
	end for;
    end for;
    work_space := NullspaceOfTranspose(mat); /* space of unknown irreds */
    delete mat;
    cs := ChiefSeries(CP`G);
    cs := [H:H in cs |#H gt 1 and not D subset H];
    Reverse(~cs);
    oldQ := CP`G;
    oldfuse := [1..n];
    oldcl := Classes(oldQ);
    spaces := [Parent(V)|];
    while #cs gt 0 and Dimension(work_space) gt 0 do
	H := cs[1];
	Q, toQ := quo<oldQ| H >;
	clQ := Classes(Q);
	dim := #clQ;
	cm := ClassMap(Q);
	fuse := [cm(c[3]@toQ): c in oldcl];
	oldfuse := [fuse[oldfuse[i]]:i in [1..n]];
	bm := ZeroMatrix(K, dim, n);
	for i := 1 to n do
	    bm[oldfuse[i],i] := one;
	end for;
	space1 := sub<V|[bm[i]:i in [1..dim]]>;
	assert Dimension(space1) eq dim;
	mat := ZeroMatrix(K, dim, n);
	for i := 1 to n do
	    size := sizes[i];
	    c := invs[i];
	    for r := 1 to dim do
		mat[r, c] := bm[r, i] * size;
	    end for;
	end for;
	space2 := NullspaceOfTranspose(mat); 
	delete bm, mat;
	Append(~spaces, work_space meet space2);
	work_space := work_space meet space1;
	delete space1, space2;
	oldQ := Q;
	oldcl := clQ;
	cs := [HinQ:H in cs|#HinQ gt 1 where HinQ := H@toQ];
    end while;
    Append(~spaces, work_space);
    spaces := [U:U in spaces|Dimension(U) gt 0];
    assert &+[Dimension(U):U in spaces] + Dimension(known) eq n;
    return spaces;
end function;
