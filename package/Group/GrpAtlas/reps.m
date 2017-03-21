freeze;

declare attributes DBAtlas:
    MatRepInfo,
    PrmRepInfo;

declare attributes GrpAtlas:
    MatReps,
    PrmReps;

declare attributes GrpMat:
    AtlasName;

declare attributes GrpPerm:
    AtlasName;

import "DBAtlas.m": ATLASDatabase;
import "mreps.m" : mrepinfo;
import "preps.m" : prepinfo;
import "filesinfo.m" : ATLASFileName;
import "files.m" : FilePosRange;
import "keys.m" : matKey, permKey, fileId, filePos;
import "config.m" : libroot;

all := func<x | true>;

function ATLASwithMrepInfo()
    D := ATLASDatabase();
    if not assigned D`MatRepInfo then
	D`MatRepInfo := mrepinfo();
    end if;
    return D;
end function;

procedure GroupCacheMatReps(G)
    if not assigned G`MatReps then
	D := ATLASwithMrepInfo();
	G`MatReps := [ matKey(G, x): x in D`MatRepInfo | x[1] eq InternalId(G) ];
    end if;
end procedure;

intrinsic MatRepKeys(G::GrpAtlas: Select := all) -> SeqEnum
{Selectable information about the matrix representations available for
ATLAS group G satisfying the criterion Select}
    GroupCacheMatReps(G);
    return [x: x in G`MatReps | Select(x)];
end intrinsic;

intrinsic NMatReps(G::GrpAtlas: Select := all) -> RngIntElt
{The number of matrix representations available for ATLAS group G satisfying
selection criterion Select}
    GroupCacheMatReps(G);
    return #[x: x in G`MatReps | Select(x)];
end intrinsic;

intrinsic MatRepDegrees(G::GrpAtlas: Select := all) -> SetEnum
{The set of degrees of matrix representations available for ATLAS group G}
    GroupCacheMatReps(G);
    return {Degree(x): x in G`MatReps | Select(x)};
end intrinsic;

intrinsic MatRepCharacteristics(G::GrpAtlas: Select := all) -> SeqEnum
{The field characteristics for which a matrix representation is available for ATLAS group G}
    GroupCacheMatReps(G);
    return {FieldCharacteristic(x): x in G`MatReps | Select(x)};
end intrinsic;

intrinsic MatRepFieldSizes(G::GrpAtlas: Select := all) -> SeqEnum
{The field sizes for which a matrix representation is available for ATLAS group G}
    GroupCacheMatReps(G);
    return {FieldSize(x): x in G`MatReps | Select(x)};
end intrinsic;

intrinsic Generators(K::DBAtlasKeyMatRep) -> SeqEnum
{The generators of the matrix group designated by database key K}
    return [
	ReadAtlasMatrix(F, r[1], r[2], FieldSize(K), Degree(K))
	    where r is FilePosRange(fileId(K), filePos(K) + i - 1)
	: i in [1 .. Ngens(K)]
    ] where F is ATLASFileName(fileId(K));
end intrinsic;

intrinsic MatRep(K::DBAtlasKeyMatRep) -> SeqEnum
{The generators of the matrix group designated by database key K}
    return Generators(K);
end intrinsic;

intrinsic MatRep(G::GrpAtlas: Select := all, Index := 1) -> SeqEnum
{The sequence of generators for a matrix representation for ATLAS group G
of degree d over a field of size q.}
    require Index gt 0 : "Index must be greater than zero";
    GroupCacheMatReps(G);
    Q := [x: x in G`MatReps | Select(x)];
    require Index le #Q : #Q eq 0 select "No such representation available"
	else "Only " cat IntegerToString(#Q) cat " representations available";
    return MatRep(Q[Index]);
end intrinsic;

intrinsic MatrixGroup(K::DBAtlasKeyMatRep) -> GrpMat
{The matrix group designated by database key K}
    G := MatrixGroup<Degree(K), Field(K) | Generators(K)>;
    A := Group(K);
    G`Order := #A;
    G`AtlasName := Name(A);
    return G;
end intrinsic;

intrinsic MatrixGroup(G::GrpAtlas: Select := all, Index := 1) -> GrpMat
{The matrix group corresponding to the Index-th available matrix
representation for ATLAS group G satisfying Select}
    require Index gt 0 : "Index must be greater than zero";
    GroupCacheMatReps(G);
    Q := [x: x in G`MatReps | Select(x)];
    require Index le #Q : #Q eq 0 select "No such representation available"
	else "Only " cat IntegerToString(#Q) cat " representations available";
    return MatrixGroup(Q[Index]);
end intrinsic;

/*	Unfortunately, there is already a Group intrinsic on the reps
intrinsic Group(K::DBAtlasKeyMatRep) -> GrpMat
{The group designated by database key K}
    return MatrixGroup(K);
end intrinsic;
*/

function ATLASwithPrepInfo()
    D := ATLASDatabase();
    if not assigned D`PrmRepInfo then
	D`PrmRepInfo := prepinfo();
    end if;
    return D;
end function;

procedure GroupCachePrmReps(G)
    if not assigned G`PrmReps then
	D := ATLASwithPrepInfo();
	G`PrmReps := [ permKey(G, x) : x in D`PrmRepInfo | x[1] eq InternalId(G) ];
    end if;
end procedure;

intrinsic PermRepKeys(G::GrpAtlas: Select := all) -> SeqEnum
{Selectable information about the permutation representations available for
ATLAS group G satisfying the criterion Select}
    GroupCachePrmReps(G);
    return [x: x in G`PrmReps | Select(x)];
end intrinsic;

intrinsic NPermReps(G::GrpAtlas: Select := all) -> RngIntElt
{The number of permutation representations available for ATLAS group G
satisfying selection criterion Select}
    GroupCachePrmReps(G);
    return #[x: x in G`PrmReps | Select(x)];
end intrinsic;

intrinsic PermRepDegrees(G::GrpAtlas: Select := all) -> SetEnum
{The set of degrees of the permutation representations available for
ATLAS group G satisfying selection criterion Select}
    GroupCachePrmReps(G);
    return {Degree(x): x in G`PrmReps | Select(x)};
end intrinsic;

function ReadAtlasPermutation(filename, s, e, d)
    F := LibFileOpen(libroot() cat filename cat ".dat", "rb");
    Seek(F, s, 0);
    b := 0;
    x := d;
    while x gt 0 do
	x div:= 256;
	b +:= 1;
    end while;
    n := e - s;
    assert n eq b * d;
    m := 1024 - (1024 mod b);
    Q := [];
    repeat
	l := Min(n, m);
	n -:= l;
	buf := ReadBytes(F, l);
	assert #buf eq l;
	Q cat:= [Seqint(buf[i .. i + b - 1], 256): i in [1 .. #buf by b]];
    until n eq 0;
    return Sym(d) ! Q;
end function;

intrinsic PermRep(K::DBAtlasKeyPermRep) -> SeqEnum
{The generators of the permutation group designated by database key K}
    return Generators(K);
end intrinsic;

intrinsic Generators(K::DBAtlasKeyPermRep) -> SeqEnum
{The generators of the permutation group designated by database key K}
    return [
	ReadAtlasPermutation(F, r[1], r[2], Degree(K))
	    where r is FilePosRange(fileId(K), filePos(K) + i - 1)
	: i in [1 .. Ngens(K)]
    ] where F is ATLASFileName(fileId(K));
end intrinsic;

intrinsic PermRep(G::GrpAtlas: Select := all, Index := 1) -> SeqEnum
{The sequence of generators for the Index-th available permutation
representation for ATLAS group G satisfying Select}
    require Index gt 0 : "Index must be greater than zero";
    GroupCachePrmReps(G);
    Q := [x: x in G`PrmReps | Select(x)];
    require Index le #Q : #Q eq 0 select "No such representation available"
	else "Only " cat IntegerToString(#Q) cat " representations available";
    return PermRep(Q[Index]);
end intrinsic;

intrinsic PermutationGroup(K::DBAtlasKeyPermRep) -> GrpPerm
{The permutation group designated by database key K}
    G := PermutationGroup<Degree(K) | Generators(K)>;
    A := Group(K);
    G`Order := #A;
    G`AtlasName := Name(A);
    return G;
end intrinsic;

intrinsic PermutationGroup(G::GrpAtlas: Select := all, Index := 1) -> GrpPerm
{The permutation group corresponding to the Index-th available permutation
representation for ATLAS group G satisfying Select}
    require Index gt 0 : "Index must be greater than zero";
    GroupCachePrmReps(G);
    Q := [x: x in G`PrmReps | Select(x)];
    require Index le #Q : #Q eq 0 select "No such representation available"
	else "Only " cat IntegerToString(#Q) cat " representations available";
    return PermutationGroup(Q[Index]);
end intrinsic;

/*	Unfortunately, there is already a Group intrinsic on the reps
intrinsic Group(K::DBAtlasKeyPermRep) -> GrpPerm
{The group designated by database key K}
    return PermutationGroup(K);
end intrinsic;
*/


// Various convenience intrinsics follow
intrinsic PermutationGroup(G::GrpAtlas, i::RngIntElt) -> GrpPerm
{The permutation group corresponding to the i-th available permutation
representation for the ATLAS group G}
    return PermutationGroup(G : Index := i);
end intrinsic;

intrinsic PermutationGroup(N::MonStgElt, i::RngIntElt) -> GrpPerm
{The permutation group corresponding to the i-th available permutation
representation for the ATLAS group named N}
    return PermutationGroup(ATLASGroup(N), i);
end intrinsic;


intrinsic MatrixGroup(G::GrpAtlas, i::RngIntElt) -> GrpMat
{The matrix group corresponding to the i-th available matrix
representation for the ATLAS group G}
    return MatrixGroup(G : Index := i);
end intrinsic;

intrinsic MatrixGroup(N::MonStgElt, i::RngIntElt) -> GrpMat
{The matrix group corresponding to the i-th available matrix
representation for the ATLAS group named N}
    return MatrixGroup(ATLASGroup(N), i);
end intrinsic;

intrinsic MatrixGroup(G::GrpAtlas, p::RngIntElt, i::RngIntElt) -> GrpMat
{The matrix group corresponding to the i-th available matrix
representation of characteristic p for the ATLAS group G}
    return MatrixGroup(G : Select := func<x | Characteristic(x) eq p>,
			    Index := i);
end intrinsic;

intrinsic MatrixGroup(N::MonStgElt, p::RngIntElt, i::RngIntElt) -> GrpMat
{The matrix group corresponding to the i-th available matrix
representation of characteristic p for the ATLAS group named N}
    return MatrixGroup(ATLASGroup(N), p, i);
end intrinsic;

