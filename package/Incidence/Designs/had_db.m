freeze;

declare verbose HadamardDB, 3;


/*
The record structure for the database information.
The meanings of the fields are:

    storecanon:	true -> store canonical forms, false -> store original forms
		So, for instance, the skew database would set this false.

    degs:	The indexed set of degrees.

    changed:	Whether any changes have been made to the data for this
		degree since it was created from the database information.

    stored:	The sequences of integers that will be stored in the database
		for the matrices.  If storecanon is true these are the true
		canonical forms, otherwise they are the original matrices.

    canon:	The indexed sets of integers with the canonical forms for the
		matrices.  They have been "reversed" for sorting purposes.
		NB: a set in it may be empty if the data has not yet been
		    changed (and so the canonical forms are not needed).
*/
dbfmt := recformat<storecanon : BoolElt, degs : SetIndx,
		    changed, stored, canon : SeqEnum>;



B := 256;		// size of byte
Z := Integers();	// just a generally handy thing to have

/*
CheckIntseq(x, base, n) -> [ integer ]
Same as Intseq(x, base, n), with an error if too many entries result
*/
function CheckIntseq(x, base, n)
    S := Intseq(x, base, n);
    error if #S gt n,
		Sprintf("Intseq(%o, %o, %o) produced too many entries (%o)",
							    x, base, n, #S);
    return S;
end function;

/*
mat_size(n) -> integer
Number of bytes used for a matrix of given degree
*/
mat_size := func<n | Ceiling(n^2/8)>;

/*
mat_bytes(x, n) -> [ integer ]
Byte sequence for the matrix of degree n corresponding to x
*/
mat_bytes := func<x, n | CheckIntseq(x, B, mat_size(n))>;

/*
zmat_from_mat(m) -> integer
An integer corresponding to the given matrix <=> HadamardMatrixToInteger(m)
*/
zmat_from_mat := func<m | Seqint(HadamardEltseq(m), 2)>;

/*
zmat_from_mat_sort(m) -> integer
An integer corresponding to the given matrix, in useful sorting order.
This is equivalent to reverse_zmat(HadamardMatrixToInteger(m))
*/
zmat_from_mat_sort := func<m | Seqint(Reverse(HadamardEltseq(m)), 2)>;

/*
zmats_from_mat(m) -> [ integer ]
A two-element sequence of the integers corresponding to the given matrix
in storage order, and in sorting order.
i.e., [ zmat_from_mat(m), zmat_from_mat_sort(m) ]
*/
zmats_from_mat := func<m | [Seqint(S,2), Seqint(Reverse(S),2)] where S is
			    HadamardEltseq(m)>;

/*
reverse_zmat(x, n) -> integer
Produce the integer corresponding to the (padded) base-2 reverse of x,
representing a matrix of degree n.
*/
reverse_zmat := func<x, n | Seqint(Reverse(CheckIntseq(x, 2, n^2)), 2)>;


/*
compute_canonical_forms(~data, k)
Computes the entries in data`canon[k] from the stored versions.
*/
procedure compute_canonical_forms(~data, k)
    len := #data`stored[k];
    if #data`canon[k] ne len then
	assert #data`canon[k] eq 0;
	assert data`storecanon eq false;

	vprintf HadamardDB,1:
	    "Computing canonical forms for %o matrices of degree %o\n",
	    len, #data`stored[k];

	t := Cputime();
	data`canon[k] := {@ zmat_from_mat_sort(HadamardCanonicalForm(m)) :
						    m in data`stored[k] @};
	vprintf HadamardDB,2: "Took %o seconds\n", Cputime(t);

        assert #data`canon[k] eq len;
    end if;
end procedure;

/*
WriteDataFile(name, ~data, ~indextable)
Writes a database file  name.dat  from the information in data, and stores
the indexing information in indextable.  This may cache some computed
information in the data.
*/
procedure WriteDataFile(name, ~data, ~indextable)

    ndegs := #data`degs;
    assert #data`changed eq ndegs;
    assert #data`canon eq ndegs;
    assert #data`stored eq ndegs;

    vprint HadamardDB,1: "Sorting matrices by canonical forms";

    for k in [1..ndegs] do
	if data`changed[k] and #data`stored[k] gt 1 then
	    // Ensure that the canonical forms exist, since we must sort
	    compute_canonical_forms(~data, k);
	    tmp := IndexedSetToSequence(data`canon[k]);
	    ParallelSort(~tmp, ~data`stored[k]);
	    data`canon[k] := {@ x : x in tmp @};
	    data`changed[k] := false;
	    delete tmp;
	end if;
    end for;

    vprint HadamardDB,1: "Sorting by degrees";

    degs := IndexedSetToSequence(data`degs);
    perm := [1..ndegs];
    ParallelSort(~degs, ~perm);

    data`degs := {@ n : n in degs @};
    data`changed := data`changed[perm];
    data`stored  := data`stored[perm];
    data`canon   := data`canon[perm];
    delete perm;

    stored := data`stored;

    vprint HadamardDB,1: "Computing size information";

    size_rep := 2;			// 2 bytes for matrix sizes

    sizes := [ size_rep + mat_size(d) : d in degs ];
    total := &+[ sizes[k] * #stored[k] : k in [1..ndegs] ];
    num := &+[ #S : S in stored ];

    // Set header values
    dat_magic := Seqint([13,7,4,2], B);	// magic number ^M^G^D^B
    dat_type := 36;			// DB_TYPE_HADAMARD
    major, minor := Explode([0, 0]);	// version 0.0
    format := 0;			// DB_FMT_ORIG
    db_start := 32;			// offset of start of data
    db_size := total;			// size of data (bytes)
    db_num := num;			// number of stored matrices
    min_size := Min(sizes);		// minimum size of any entry (bytes)
    max_size := Max(sizes);		// maximum size of any entry (bytes)

    hdr := [
	< dat_magic, 4>,
	< dat_type, 2>,
	< minor, 1>,
	< major, 1>,
	< format, 4>,
	< db_start, 4>,
	< db_size, 4>,
	< db_num, 4>,
	< min_size, 2>,
	< max_size, 2>,
	< size_rep, 4>
    ];

    vprint HadamardDB,1: "Writing data file";

    dat := Open(name cat ".dat", "w");

    // Write header
    hdr_bytes := &cat [ CheckIntseq(h[1], B, h[2]) : h in hdr ];
    WriteBytes(dat, hdr_bytes);

    // Write matrices by degree
    nmats := 0;
    offset := db_start;
    indextable := [];
    for k in [1..ndegs] do
	d := degs[k];
	nbytes := mat_size(d);
	size := CheckIntseq(nbytes, B, size_rep);
	S := stored[k];
	n := #S;

	Append(~indextable, [d, n, offset]);

	if n eq 0 then continue; end if;
	if n eq 1 then
	    vprintf HadamardDB,3: "Writing 1 matrix of degree %o\n", d;
	else
	    vprintf HadamardDB,3: "Writing %o matrices of degree %o\n", n, d;
	end if;

	// Write matrices in chunks of 100
	ndone := 0;
	stepsize := 100;
	q,r := Quotrem(n, stepsize);
	for i in [1..q] do
	    mats := &cat [ size cat mat_bytes(m, d) where m is S[ndone+i]:
							i in [1..stepsize] ];
	    WriteBytes(dat, mats);
	    offset +:= #mats;

	    ndone +:= stepsize;
	    vprintf HadamardDB,3: " - %o matrices written\n", ndone;
	end for;

	mats := &cat [ size cat mat_bytes(m, d) where m is S[ndone+i] :
							    i in [1..r] ];
	WriteBytes(dat, mats);
	offset +:= #mats;

	ndone +:= r;
	nmats +:= ndone;
    end for;

    delete dat;

    vprintf HadamardDB,1: "Data file written (%o matrices total)\n\n", nmats;
end procedure;


/*
WriteIndexFile(name, indextable)
Writes an index file  name.ind  from the indexing information in indextable.
*/
procedure WriteIndexFile(name, indextable)

    // Set header values
    ind_magic := Seqint([13,7,4,9], B);	// magic number ^M^G^D^I
    ind_type := 36;			// DB_TYPE_HADAMARD
    major, minor := Explode([0, 0]);	// version 0.0
    subtype := 0;			// no subtype

    hdr := [
	< ind_magic, 4>,
	< ind_type, 2>,
	< minor, 1>,
	< major, 1>,
	< subtype, 4>
    ];

    vprint HadamardDB,1: "Writing index file";

    ind := Open(name cat ".ind", "w");

    // Write header
    hdr_bytes := &cat [ CheckIntseq(h[1], B, h[2]) : h in hdr ];
    WriteBytes(ind, hdr_bytes);

    // First item is number of degrees (4 bytes)
    ndegs := #indextable;
    WriteBytes(ind, CheckIntseq(ndegs, B, 4));

    indexbytes := &cat [ CheckIntseq(x, B, 4) : x in &cat indextable ];
    WriteBytes(ind, indexbytes);

    delete ind;

    vprint HadamardDB,1: "Index file written";
end procedure;


intrinsic HadamardDatabaseInformationEmpty(: Canonical := true) -> Rec
{Produces an internal representation of a Hadamard database with no
entries in it.  Set the parameter Canonical to false if the database
should store the original forms of matrices rather than the canonical ones}

    data := rec<dbfmt | storecanon := Canonical,
			degs := {@ Z| @},
			changed := [ Booleans()| ],
			stored := [ Parent([ Z| ]) | ],
			canon := [ Parent({@ Z| @}) | ]
			>;
    return data;
end intrinsic;

intrinsic HadamardDatabaseInformation(D::DB : Canonical := true) -> Rec
{Produces an internal representation of the Hadamard database for use
by other intrinsics.  Set the parameter Canonical to false if the entries
in the database are not in canonical form (e.g., the skew database)}

    assert DatabaseType(D) eq "hadamard";

    degs := {@ d : d in Degrees(D) @};
    changed := [ false: k in [1..#degs] ];
    if Canonical then
	tmp := [ [ zmats_from_mat(m) : m in Matrices(D, n) ] : n in degs ];
	stored := [  [ t[1] : t in degseq ]  : degseq in tmp ];
	canon  := [ {@ t[2] : t in degseq @} : degseq in tmp ];
	assert [ #S : S in canon ] eq [ #S : S in stored ];
	delete tmp;
    else
	stored := [ [ zmat_from_mat(m) : m in Matrices(D, n) ] : n in degs ];
	canon  := [ {@ Z| @} : n in degs ];
    end if;

    data := rec<dbfmt | storecanon := Canonical, degs := degs,
			changed := changed, stored := stored, canon := canon>;
    return data;
end intrinsic;

intrinsic UpdateHadamardDatabase(~data::Rec, S::[AlgMatElt] :
					    Canonical := false)
{Add new inequivalent matrices from S to the data in the given tuple.
Set the parameter Canonical to true if these matrices are known to be in
canonical form already}

    if #S eq 0 then return; end if;

    n := Degree(Universe(S));
    k := Index(data`degs, n);
    if k eq 0 then			// not in current degree set

	vprintf HadamardDB,1: "New degree %o being added\n", n;

	Include(~data`degs, n);
	Append(~data`changed, true);
	Append(~data`stored, [ Z| ]);
	Append(~data`canon, {@ Z| @});
	k := #data`degs;
    end if;

    // Ensure that the canonical entries exist, since we now need to compare
    compute_canonical_forms(~data, k);

    len := #data`stored[k];
    origlen := len;
    for m in S do
	if Canonical then
	    x_stored, x_canon := Explode(zmats_from_mat(m));
	elif data`storecanon then
	    m1 := HadamardCanonicalForm(m);
	    x_stored, x_canon := Explode(zmats_from_mat(m1));
	else
	    x_stored := zmat_from_mat(m);
	    x_canon  := zmat_from_mat_sort(HadamardCanonicalForm(m));
	end if;
	Include(~data`canon[k], x_canon);
	if #data`canon[k] ne len then
	    assert #data`canon[k] eq len + 1;
	    vprint HadamardDB,3: "New matrix found";
	    Append(~data`stored[k], x_stored);
	    data`changed[k] := true;
	    len +:= 1;
	end if;
    end for;

    nnew := len - origlen;
    if nnew ne 0 then
	if nnew eq 1 then
	    vprintf HadamardDB,1: "1 new matrix added\n";
	else
	    vprintf HadamardDB,1: "%o new matrices added\n", nnew;
	end if;
    end if;
end intrinsic;

intrinsic WriteHadamardDatabase(name::MonStgElt, ~data::Rec)
{Creates new database files from the given data}
    indextable := [];
    WriteDataFile(name, ~data, ~indextable);
    WriteIndexFile(name, indextable);
end intrinsic;

intrinsic WriteRawHadamardData(name::MonStgElt, data::Rec)
{Creates a loadable Magma file with the raw data for a database.  This is
useful when the stored entries are not in canonical form (i.e., the skew
database), since the canonical information is stored in the raw data.
WARNING: This will destroy the old contents of the file}
    Write(name, "data :=" : Overwrite := true);
    Write(name, data, "Magma");
    Write(name, ";\n");
end intrinsic;

