freeze;

/*
SaveGroup(group, filename)

    Writes Magma code to the given filename that can then be eval'ed
    to produce the original group.  Additionally -- and this is the
    part that makes it non-trivial -- the conjugacy classes and the
    character table information are also saved so that they will not
    need to be recomputed after the eval.

There are three components involved: The group, its conjugacy classes,
and its character table.  Here's the breakdown of the steps involved
in each:

1. Group.  This is trivial -- we just use the print level of "Magma"
   (or %m in printf-like constructs).  This only prints out defining
   information for the group, though, not derived values, which is
   why we need to do steps 2 and 3 also.

2. Conjugacy classes.  These can also be written out using the
   "Magma" print level, and then assigned to the group via the
   "Classes" attribute.  There is one annoying wrinkle, however:
   Magma sorts the classes internally via order and length.  This
   is not a total order, and the sort used is not stable.  As a
   result, the order can change -- the order after the assignment
   may differ from the order used in the assignment!

   This counterintuitive behaviour is rather unhelpful, needless
   to say.  This has been fixed for version 2.21-5.  For earlier
   versions, a workaround is implemented: Since the sort used is
   deterministic, the same permutation is applied each time.  So
   we use the returned order of the classes to deduce that
   permutation, apply its inverse, and repeat the whole process
   with the inverse-permuted classes.

   This will only be done if necessary, so should not adversely
   affect newer versions.  (For that matter, it should not be very
   expensive for the old versions, either.)

3. Character table.  We re-create this by creating each character
   in turn, and asserting (via the "IsIrreducible" attribute) that
   it is irreducible.  Magma detects this assertion and adds the
   character to the table.  Once the right number have been added
   the character table is then known to be complete.

   The main wrinkle here is that we do not have (as yet) a proper
   "Magma" level printing routine for characters.  So we have to
   delve a bit lower in order to produce something that works;
   this is the chtr_string() function below.  Essentially, we turn
   the character into a sequence of cyclotomic field elements, and
   turn those elements into sequences of integers.  We have some
   special cases -- which save considerable space -- where either
   the cyclotomic elements or the character itself are simply
   integers.

   Another point addressed is that the Schur value for each
   character is also saved, as that can be expensive to compute.
   Also, in versions prior to 2.21-6 (this fix did not make it
   into 2.21-5), the CharacterTable() intrinsic would compute
   these values if not known, even if the character table was
   regarded as complete.

   At the end, we ask for the character table with no checking
   (setting Check := 0 in the intrinsic).  In 2.21-6 and above
   this will prevent the default checks from being done when the
   character table data is later wanted.
*/

chtr_print := procedure(file, x)
    S := Minimize(Eltseq(x));
    L := Universe(S);
    Z := Integers();

    K := L;
    if Degree(K) eq 1 then
	str := Sprintf("x := CR!%m;\n", ChangeUniverse(S, Z));
    else
	str := Sprintf("K := %m;\n", K);
	str cat:= Sprintf("S := [ K |\n");
	for i in [1..#S] do
	    u := K!S[i];
	    inZ, e := IsCoercible(Z, u);
	    if not inZ then
		try
		    e := ChangeUniverse(Eltseq(u), Z);
		catch E
		    printf "K = %o\n", K;
		    printf "S[%o] = %o\n", i, S[i];
		    printf "u = %o\n", u;
		    printf "Parent(u) = %o\n", Parent(u);
		    error E;
		end try;
	    end if;
	    str cat:= Sprintf("%m", e);
	    if i lt #S then
		str cat:= ", ";
	    end if;
	end for;
	str cat:= "\n];";
	str cat:= "x := CR!S;\n";
    end if;

    fprintf file, "%o", str;
    fprintf file, "x`IsCharacter := true;\n";
    fprintf file, "x`Schur := %o;\n", Indicator(x);
    fprintf file, "x`IsIrreducible := true;\n";
    fl, si := HasAttribute(x, "SchurIndices");
    if fl then
	fprintf file, "x`SchurIndices := %o;\n", si;
    end if;
end procedure;

powermap_print := procedure(file, CR)
    fl, pm := HasAttribute(CR, "PowerMap");
    if not fl then
	return;
    end if;
    C := ClassesData(CR);
    fprintf file, "pm := PowerMap(CR, %m);\n",
	    [ [pm(i,j) : j in [1..C[i,1]]] : i in [1..#C] ];
end procedure;

sorthack :=
"// Compensate for older versions that may re-sort the classes
    C2 := G`Classes;
    if C2 ne C then
	assert Set(C2) eq Set(C);
	I := IndexedSet(C);
	p := Sym(#C)![ Index(I, c) : c in C2 ];
	newC := C[Eltseq(p^-1)];
	ordG := #G;
	G := sub<Generic(G)|G>;
	G`Order := ordG;
	G`Classes := newC;
	assert G`Classes eq C;
    end if;
";

intrinsic SaveGroup(G::Grp, file::MonStgElt)
{Write group G, its conjugacy classes and its character table to file file.
Reading file defines G with classes and character table}

    C := Classes(G);
    X := CharacterTable(G);
    fprintf file, "G := %m;\n", G;
    fprintf file, "C := %m;\n", C;
    fprintf file, "G`Classes := C;\n";
    fprintf file, sorthack, G;
    fprintf file, "CR := CharacterRing(G);\n";
    for x in X do
	chtr_print(file, x);
    end for;
    fprintf file, "_ := CharacterTable(G : Check := 0);\n";
    powermap_print(file, CharacterRing(G));
    fprintf file, "return G;\n";
end intrinsic;

intrinsic SaveCharacterTable(X::SeqEnum[AlgChtrElt], file::MonStgElt)
{Write the character table X to file "file". Reading file will define
a character table without a group}

    CR := Universe(X);
    C := ClassesData(CR);
    fprintf file, "C := %m;\n", C;
    fprintf file, "CR := CharacterRing(C);\n";
    for x in X do
	chtr_print(file, x);
    end for;
    powermap_print(file, CR);
    fprintf file, "return KnownIrreducibles(CR);\n";

end intrinsic;

intrinsic SaveGroup(G::GrpPerm, file::MonStgElt)
{Write group G, its conjugacy classes and its character table to file file.
Reading file defines G with classes and character table}

    C := Classes(G);
    BSGS(G);
    b := Base(G);
    C := [ <t[1], t[2], b^t[3]> : t in C ];
    X := CharacterTable(G);
    fprintf file, "G := %m;\n", G;
    fprintf file, "b := %m;\n", b;
    fprintf file, "C := %m;\n", C;
    fprintf file, "BSGS(G); R := Representation(G);\n";
    fprintf file, "R := RandomBaseChange(R, b);\n";
    fprintf file, "C := [ <t[1],t[2],Permutation(R,t[3])>:t in C];\n";
    fprintf file, "G`Classes := C;\n";
    fprintf file, sorthack, G;
    fprintf file, "CR := CharacterRing(G);\n";
    for x in X do
	chtr_print(file, x);
    end for;
    fprintf file, "_ := CharacterTable(G : Check := 0);\n";
    powermap_print(file, Universe(X));
    fprintf file, "return G;\n";
end intrinsic;

intrinsic SaveGroup(G::GrpPerm, n::MonStgElt, file::MonStgElt)
{Write group G, its conjugacy classes and its character table to file file.
Assumes the group is "PermutationGroup(n, 1)" i.e. an ATLASGroup.
Reading file defines G with classes and character table}

    C := Classes(G);
    BSGS(G);
    b := Base(G);
    C := [ <t[1], t[2], b^t[3]> : t in C ];
    X := CharacterTable(G);
    fprintf file, "G := PermutationGroup(%m, 1);\n", n;
    fprintf file, "b := %m;\n", b;
    fprintf file, "C := %m;\n", C;
    fprintf file, "BSGS(G); R := Representation(G);\n";
    fprintf file, "R := RandomBaseChange(R, b);\n";
    fprintf file, "C := [ <t[1],t[2],Permutation(R,t[3])>:t in C];\n";
    fprintf file, "G`Classes := C;\n";
    fprintf file, sorthack, G;
    fprintf file, "CR := CharacterRing(G);\n";
    for x in X do
	chtr_print(file, x);
    end for;
    fprintf file, "_ := CharacterTable(G : Check := 0);\n";
    powermap_print(file, Universe(X));
    fprintf file, "return G;\n";
end intrinsic;

intrinsic SaveGroup(G::GrpMat, n::MonStgElt, file::MonStgElt)
{Write group G, its conjugacy classes and its character table to file file.
Reading file defines G with classes and character table}

    C := Classes(G);
    X := CharacterTable(G);
    fprintf file, "G := MatrixGroup(%m, 1);\n", n;
    fprintf file, "C := %m;\n", C;
    fprintf file, "G`Classes := C;\n";
    fprintf file, sorthack, G;
    fprintf file, "CR := CharacterRing(G);\n";
    for x in X do
	chtr_print(file, x);
    end for;
    fprintf file, "_ := CharacterTable(G : Check := 0);\n";
    powermap_print(file, Universe(X));
    fprintf file, "return G;\n";
end intrinsic;
