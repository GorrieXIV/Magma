freeze;

import "elem_chtrs_conlon.m": ElementaryInduction;
import "quotient_character_spaces.m": chief_character_spaces;

forward AddPermChtr, split_using_chtr_spaces, ChtrTable, LiftIrreds, 
	    GaloisOrbit, CheckIrreds, can_use_p;

GrpPCDSSL := 20;

Blkfmt := recformat<
    CS		: ModTupFld,
    DoFactors	: BoolElt,
    Irreds	: SetIndx,
    Reds	: SeqEnum,
    Gram	: AlgMatElt,
    Rank	: RngIntElt,
    MaxRank	: RngIntElt,
    Trace	: RngIntElt,
    LLLcount	: RngIntElt,
    Det, BM >;

CPfmt := recformat<
    G		: Grp,
    G_order	: RngIntElt,
    Classes	: SeqEnum,
    n_Classes	: RngIntElt,
    ChtrRng	: AlgChtr,
    PowerMap	: Map,
    ClassMap	: Map,
    Invs	: SeqEnum,
    Sizes	: SeqEnum,
    InvSizes	: SeqEnum,
    Irreds	: SetIndx,
    CSBlocks	: SeqEnum,
    Z		: RngInt,
    Q		: FldRat,
    K		: FldFin,
    zeta	: FldFinElt,
    p		: RngIntElt,
    p_on_2	: RngIntElt,
    G_ord_inv	: FldFinElt,
    V		: ModTupFld,
    TopClasses	: SetEnum,
    lift_ords	: SetIndx,
    lift_K_mats	: List,
    roots_of_unity	: List,
    lift_irreds	: SeqEnum,
    CS_matrix	: Mtrx,
    IntClasses	: SetEnum,
    GalOrbits	: SeqEnum,
    GalGroup	: SeqEnum,
    DoLift	: BoolElt,
    LiftTime    : FldReElt,
    OrbLiftTime    : FldReElt,
    HardLiftTime    : FldReElt,
    AddChtrTime    : FldReElt,
    FoundIrreds	: SeqEnum,
    Check	: RngIntElt,
    use_split	: BoolElt,
    SqrsQueue	: SeqEnum,
    ClassInvariants : Tup,
    LLLDelta	: FldReElt
    /* final line of CPfmt*/ >;

get_full_det := function(blks)
    res := Factorization(1);
    for b in blks do
	if b`Det cmpeq 0 then return 0; end if;
	if Type(b`Det) eq RngIntEltFact then res *:= b`Det; continue; end if;
	if Type(b`Det) eq RngIntElt then res *:= Factorization(b`Det); end if;
    end for;
    return res;
end function;

ip_K := function(CP, x, y)
    return InternalChtrTableIPRK(CP`K, x, y, CP`Invs, CP`Sizes);
    /*
    sum := CP`K!0;
    invs := CP`Invs;
    sizes := CP`Sizes;
    for i := 1 to CP`n_Classes do
	sum +:= x[i]*y[invs[i]]*sizes[i];
    end for;
    return sum;
    */
end function;

/*
ip_K_2 := function(K, mask, x, y)
    sum := K!0;
    for i in mask do
	sum +:= x[i]*y[i];
    end for;
    return sum;
end function;

ip_int := function(K, mask, x, y)
    sum := K!0;
    for i in mask do
	sum +:= x[i]*y[i];
    end for;
    res := Integers() ! sum;
    p := #K;
    if res gt p div 2 then res := res - p; end if;
    return res;
end function;
*/

gram_matrix_1 := function(CP, b, b2, mask)
// mask, b, b2;
    K := CP`K;
    norms := [InternalChtrTableIPZ(K, mask, b[i], b2[i]): i in [1..#b]];
    M := DiagonalMatrix(norms);
    for i := 2 to #b do
	for j := 1 to i-1 do
	    M[i, j] := InternalChtrTableIPZ(K, mask, b[i], b2[j]);
	    M[j,i] := M[i,j];
	end for;
    end for;
    return M;
end function;

gram_matrix_2 := function(CP, b, b2, c1, c2, mask)
    n := Nrows(c1);
    m := Nrows(c2);
    K := CP`K;
    if m*n ne 0 then
	L:=Matrix(m,n,[InternalChtrTableIPZ(K,mask,b[j],b2[i]):
		j in [1..n],i in [1 .. #b2]]);
    else
	L:=Matrix(m,n,[CP`Z|]);
    end if;
    M := VerticalJoin(c1, L);
    R := VerticalJoin(Transpose(L), c2);
    M := HorizontalJoin(M, R);
    return M;
end function;

get_tops := function(c_table, p_map)
    prims := [true : i in [1..#c_table]];
    prims[1] := false;
    for i := #c_table to 2 by -1 do
	if prims[i] then
	    for j := 2 to c_table[i][1] -1 do
		im := p_map(i, j);
		if im ne i then prims[im] := false; end if;
	    end for;
	end if;
    end for;
    return {i : i in [1..#c_table] | prims[i] };
end function;

get_fusion := function(cl_num, ord, p_map)
// "fusion";
    up := {@ 1 @};
    down := [{0}];
    for i := 1 to ord - 1 do
	im := p_map(cl_num, i);
	pos := Position(up, im);
	if pos eq 0 then
	    Include(~up, im);
	    Include(~down, {i});
	else
	    Include(~down[pos], i);
	end if;
    end for;
    if ord eq 1 then return up, down, [0]; end if;
    flag := exists(grp){x : x in down | 1 in x};
    assert flag;
    if #grp eq 1 then
	return (up), down, [0..ord - 1];
    end if;
    orbits := [0];
    x := {1..ord - 1};
    while #x gt 0 do
	y := Rep(x);
	Append(~orbits, y);
	x diff:= { (y*i) mod ord : i in grp };
    end while;
    return (up), down, orbits;
end function;

induce := function(pows, ord, up, down, CP)
    sizes := CP`InvSizes;
    K := CP`K;
    index := K!(CP`G_order div ord);
    z := CP`zeta ^ ((CP`p - 1) div ord);
    res := [ CP`V | ];
    for p in pows do
	zeta := z^p;
	s := [ K | 0 : i in [1..#sizes]];
	for i := 1 to #up do
	    j := up[i];
	    s[j] := &+[zeta^k : k in down[i]] * index * sizes[j] ;
	end for;
	Append(~res, s);
    end for;
    return res;
end function;

rem_irrs := procedure(CP, irrs, ~reds, reds2, mask)
    K := CP`K;
    for i := 1 to #reds do
	x := reds2[i];
	rem := CP`V!0;
	for j := 1 to #irrs do
	    a := InternalChtrTableIPK(K, mask, irrs[j], x);
	    if not IsZero(a) then
		rem +:= a*irrs[j];
	    end if;
	end for;
	reds[i] := reds[i] - rem;
    end for;
end procedure;

GaloisGroup := procedure(~CP)
    if assigned CP`GalGroup then return; end if;
    e := Exponent(CP`G);
    U, f := UnitGroup(Integers(Exponent(CP`G)));
    Z := CP`Z;
    gens := [Z | g@f : g in Generators(U) ];
    pm := CP`PowerMap;
    d := CP`n_Classes;
    S := Sym(d);
    gens := [ p : g in gens | not IsIdentity(p) where
		p is S![pm(i,g): i in [1..d]] ];
    grp := sub<S|gens>;
    P, f :=  PCGroup(grp);
    CP`GalGroup := [Eltseq((P.i)@@f):i in [NPCgens(P)..1 by -1]];
    CP`GalOrbits := Orbits(grp);
    Sort(~(CP`GalOrbits), func<x,y|Min(x) - Min(y)>);
end procedure;

IntegralClasses := procedure(~CP)
    if assigned CP`IntClasses then return; end if;
    if assigned CP`GalOrbits then
	CP`IntClasses := {Rep(x):x in CP`GalOrbits|#x eq 1};
	return;
    end if;
    pm := CP`PowerMap;
    ords := {@ @};
    hold_gens := [];
    cl := CP`Classes;
    res := {};
    for i := 1 to #cl do
	ord := cl[i,1];
	if ord le 2 then Include(~res, i); continue i; end if;
	ind := Index(ords, ord);
	if ind gt 0 then
	    gens := hold_gens[ind];
	else
	    A, f := UnitGroup(Integers(ord));
	    gens := [CP`Z!(a@f): a in Generators(A)];
	    Include(~ords, ord);
	    Append(~hold_gens, gens);
	end if;
	if forall{g:g in gens|pm(i, g) eq i} then
	    Include(~res, i); 
	end if;
    end for;
    CP`IntClasses := res;
end procedure;

InitialiseChtrProc := function(G : Irreducibles := [], Modulus := 0)
    CP := rec<CPfmt| G := G, G_order := #G, 
	Z := Integers(), Q := Rationals() >;
    zeit := Cputime();
    CP`Classes := Classes(G);
    vprintf Chtr, 1:"Time to compute Classes %o secs\n", Cputime(zeit);
    CP`n_Classes := #(CP`Classes);
    CP`ChtrRng := CharacterRing(G);
    chars := KnownIrreducibles(G) cat Irreducibles;
    /* horrible hack follows ... Should fix derived subgroup of matrix group*/
    if not ISA(Type(G), GrpMat) then chars cat:= LinearCharacters(G); end if;
    chars := SequenceToSet(chars);
    chars := SetToSequence(chars);
    if #chars eq 0 then chars := [CP`ChtrRng!1]; end if;
    if #chars eq #CP`Classes then return CP; end if;
    e := Exponent(G);
    if Modulus gt 0 then
	p := Modulus;
	CP`DoLift := false;
    else
	CP`DoLift := true;
	p := 2*#G + 1;
	while not IsPrime(p) do p +:= e; end while;
    end if;
    K := GF(p);
    CP`K := K;
    CP`p := p;
    CP`p_on_2 := p div 2;
    CP`G_ord_inv := K ! (1/#G);
    CP`zeta := PrimitiveElement(K);
    vprintf Chtr, 2: ".ChtrTable: Field is %o, primitive elt is %o\n", K, CP`zeta;
    CP`V := VectorSpace(K, CP`n_Classes);
    CP`Irreds := {@ CharacterToModular(x, CP`zeta): x in chars @};
    CP`ClassMap := ClassMap(G);
    zeit := Cputime();
    pm := PowerMap(G);
    vprintf Chtr, 1:".ChtrTable: Time to compute PowerMap %o secs\n", Cputime(zeit);
    CP`PowerMap := pm;
    invs := [pm(i,-1): i in [1..CP`n_Classes]];
    inv := CP`G_ord_inv;
    sizes := [K!c[2]* inv : c in CP`Classes];
    CP`Invs := invs;
    CP`Sizes:= sizes;
    CP`InvSizes := [inv/x: x in sizes];
    CP`CSBlocks := [];
    CP`lift_ords := {@ CP`Z| @};
    CP`lift_K_mats := [* *];
    CP`roots_of_unity := [* *];
    CP`lift_irreds := chars;
    CP`TopClasses := get_tops(CP`Classes, CP`PowerMap);
    CP`LiftTime := RealField(5) ! 0;
    CP`OrbLiftTime := RealField(5) ! 0;
    CP`HardLiftTime := RealField(5) ! 0;
    CP`AddChtrTime := RealField(5) ! 0;
    CP`FoundIrreds := [];
    CP`SqrsQueue := [];
    CP`LLLDelta := 0.75;
    return CP;
end function;

processLLLresult := function(s, L, T, r, lim)
    zeit := Cputime();
    vprint Chtr, 3: "process";
    assert #s eq Ncols(L);
    assert #s eq Ncols(T);
    assert r le #s;

    R := Universe(s);
    irrs := [R|];
    reds := [R|];
    n_irrs := 0;
    mat_size := Ncols(T);
//T;
//[L[i,i]:i in [1..mat_size]];
    if exists{i : i in [1..mat_size] | (L[i,i] ge lim) or (L[i,i] eq 1 and 
	    exists{j:j in [1..#s]|L[i,j] ne 0 and j ne i}) } then
	vprint Chtr, 3: "Using PairReduce";
	L, TP := PairReduceGram(L);
	T := ChangeRing(TP, BaseRing(T)) * T;
	vprint Chtr, 3: "Pair reduce result:", [L[i,i]:i in [1..mat_size]];
    end if;
    good_i := [i:i in [1..mat_size]|L[i,i] ne 0];
    assert #good_i eq r;
    s_mat := T*Matrix(s);
    old_i := [];
    for i := 1 to r do
	j := good_i[i];
        x := s_mat[j];
        if L[j,j] eq 1 then
	    assert forall{k:k in [1..#s]|L[j,k] eq 0 or j eq k};
            Append(~irrs, x);
        elif L[j,j] lt lim then
            Append(~reds, x);
	    Append(~old_i, j);
	else
	    print "WARNING: norm too large, discarding information";
        end if;
    end for;
    if #old_i gt 0 then
	subm := Matrix(#old_i, #old_i, [L[i, j]:i, j in old_i]);
    else
	subm := Matrix(0, 0, [Integers()|]);
    end if;
    // assert IsSymmetric(subm);
    vprintf Chtr, 3: "end process: %o secs\n", Cputime(zeit);
    return irrs, reds, subm;
end function;

processLLLresultweak := function(s, s2, L, T, r)
    zeit := Cputime();
    vprint Chtr, 3: "process weak";
    assert #s eq Ncols(L);
    assert #s eq Ncols(T);
    assert r le #s;

    R := Universe(s);
    reds := [R|];
    reds2 := [R|];
    old_i := [];
    for i := 1 to #s do
	if L[i,i] eq 0 then continue i; end if;
	Append(~old_i, i);
        x := R!0;
        x2 := R!0;
        for j := 1 to #s do
            if T[i,j] ne 0 then
                x +:= T[i,j] * s[j];
                x2 +:= T[i,j] * s2[j];
            end if;
        end for;
	Append(~reds, x);
	Append(~reds2, x2);
    end for;
    assert #reds eq r;
    vprintf Chtr, 3: "end process weak: %o secs\n", Cputime(zeit);;
    return  reds, reds2, Matrix(r, r, [L[i,j]:i, j in old_i]);
end function;

tidy_irrs := procedure(CP, ~irrs)
    for i := 1 to #irrs do
	d := CP`Z ! irrs[i][1];
	if d gt CP`p_on_2 then
	    irrs[i] := -irrs[i];
	end if;
    end for;
end procedure;

SequenceToIndexedSet := function(Q)
    return {@ t : t in Q @};
end function;

ProcessLLL_CP := procedure(~CP, i, L, T, r, sqr_lev)
/* process block i of CP */
    blk := CP`CSBlocks[i];
    irrs, reds, gram := processLLLresult(
	blk`Reds, L, ChangeRing(T, CP`K), r, CP`p_on_2);
    // r := r - #irrs;
    r := #reds;
vprintf Chtr, 2: "Norms in chtr space %o:\n%o\n", i, [gram[i,i]:i in [1..r]];
    if #irrs gt 0 then
	tidy_irrs(CP, ~irrs);
	blk`MaxRank -:= #irrs;
	blk`Irreds join:= SequenceToIndexedSet(irrs);
	if CP`DoLift then LiftIrreds(~CP, irrs); end if;
	if sqr_lev gt 0 and blk`MaxRank gt 0 then 
	    CP`SqrsQueue cat:= irrs; 
	end if;
    end if;
    blk`Reds := reds;
    blk`Gram := gram;
    if #reds gt 0 then
	trace :=  Trace(gram);
    else
	trace := 0;
    end if;
    if not blk`DoFactors then
	blk`DoFactors := r eq blk`MaxRank;
	if not blk`DoFactors then
	    det := 0;
	else
	    assert r eq blk`MaxRank;
	    det := Determinant(gram);
	    assert not IsZero(det);
	    det := Factorization(det);
	    blk`DoFactors := not (det cmpeq blk`Det and blk`Trace eq trace);
	end if;
    else
	assert r eq blk`MaxRank;
	det := Determinant(gram);
	assert not IsZero(det);
	det := Factorization(det);
    end if;
    blk`Det := det;
    blk`Trace := trace;
    blk`Rank := #reds;
    CP`CSBlocks[i] := blk;
end procedure;

ProcessCharacters := procedure(~CP, C, mask, sqr_lev:LLLSort := false)
    if #C eq 0 or #CP`Irreds eq CP`n_Classes then return; end if;
    timer := Cputime();
    G := CP`G;
    G_ord := CP`G_order;
    cl := CP`Classes;
    I := SequenceToSet(C);
    vprintf Chtr, 1: "+ProcessCharacters: %o chtrs, %o unequal\n", #C, #I;
    invs := CP`Invs;
    sizes := CP`Sizes;
    I := SetToSequence(I);
    /*
    if exists(v){v:v in I|exists{i:i in [1..CP`n_Classes]|i notin mask and
	not IsZero(v[i])}} then
	"Error in mask", v, mask;
	assert false;
    end if;
    */
    I_ip := [CP`V|];
    for j := 1 to #I do
	v1 := I[j]; v2 := [CP`K|0:k in [1..CP`n_Classes]];
	for k in mask do
	    v2[invs[k]] := v1[k]*sizes[k];
	end for;
	I_ip[j] := v2;
    end for;
    split_using_chtr_spaces(~CP, I, ~split_I);
    assert forall{s:s in split_I|#s eq #I or #s eq 0};
    for i := 1 to #split_I do
	J := split_I[i];
	Ji := [i:i in [1..#J]|not IsZero(J[i])];
	if #Ji eq 0 then continue i; end if;
	I := [I_ip[i]: i in Ji];
	J := [J[i]: i in Ji];
	blk := CP`CSBlocks[i];
	rem_irrs(CP, blk`Irreds, ~J, I, mask);
	Ji := [i:i in [1..#J]|not IsZero(J[i])];
	if #Ji eq 0 then continue i; end if;
	I := [I[i]: i in Ji];
	J := [J[i]: i in Ji];
	m := gram_matrix_1(CP, J, I, mask);
	vprint Chtr, 3:"norms", [m[j,j] : j in [1..#J]];
	vprintf Chtr, 3: ".ProcessCharacters: adding %o to list\n", #I;
	m := gram_matrix_2(CP, blk`Reds, I, blk`Gram, m, mask);
	vprintf Chtr, 2: ".ProcessCharacters: doing LLL\n";
	LLLzeit := Cputime();
	L, T, r := LLLGram(m: Delta:=CP`LLLDelta,Sort:=false,
	    InitialSort:=LLLSort,Proof:=false,Fast:=1);
	
	// "norms after LLL", [L[j,j] : j in [1..Nrows(L)]];
	CP`CSBlocks[i]`LLLcount +:= 1;

	vprintf Chtr, 2: ".ProcessCharacters: LLL in %o secs\n",
		Cputime(LLLzeit);
	CP`CSBlocks[i]`Reds cat:= J;
	ProcessLLL_CP(~CP, i, L, T, r, sqr_lev);
	blk := CP`CSBlocks[i];
	vprintf Chtr, 2: ".ProcessCharacters: #Reds %o, Tr %o, Det %o\n", 
	     #(blk`Reds), blk`Trace, blk`Det;
	/* vprintf Chtr, 3: ".ProcessCharacters: Gram Det %o: %o\n", i, 
	    Determinant(ChangeRing(blk`Gram,RealField(6))); */
    end for;
  
    vprintf Chtr, 1: "-ProcessCharacters: #Irreds %o, Trace %o, Rank of unknowns %o\n", #CP`Irreds, &+[blk`Trace:blk in CP`CSBlocks], &+[blk`Rank:blk in CP`CSBlocks];
    if GetVerbose("Chtr") gt 1 and forall{blk:blk in CP`CSBlocks|#blk`Reds eq
     blk`MaxRank} then
	 printf "-ProcessCharacters: Determinant = %o\n", get_full_det(CP`CSBlocks);
    end if;
    vprintf Chtr, 2: "-ProcessCharacters: time %o\n", Cputime(timer);
    if #CP`FoundIrreds gt 0 then
	chtrs := CP`FoundIrreds;
	CP`FoundIrreds := [];
	$$(~CP, chtrs, {1..CP`n_Classes}, sqr_lev:LLLSort:=true);
    end if;
    if #CP`SqrsQueue gt 0 then
	CP`SqrsQueue := [];
	/*
	do_factors_solution(~CP);
	vprintf Chtr, 1: "Adding Squares\n";
	chtrs := [];
	pm := CP`PowerMap;
	for x in CP`SqrsQueue do
	    a := CP`V ! [x[j]^2 : j in [1..CP`n_Classes]];
	    b := CP`V ! [ x[pm(j,2)] : j in [1..CP`n_Classes]];
	    // Append(~chtrs, (a+b)/2);
	    Append(~chtrs, (a-b)/2);
	end for;
	ProcessCharacters(~CP, chtrs, [1..CP`n_Classes], sqr_lev-1);
	*/
    end if;
end procedure;

ProcessIrreds := procedure(~CP, i, I)
    if #I eq 0 then return; end if;
    timer := Cputime();
    tidy_irrs(CP, ~I);
    blk := CP`CSBlocks[i];
    if #I eq blk`MaxRank then
	/* quick finish */
	blk`Irreds join:= SequenceToIndexedSet(I);
	blk`MaxRank := 0;
	blk`Reds := [];
	blk`Det := [];
	blk`Trace := 0;
	blk`Rank := 0;
	if CP`DoLift then LiftIrreds(~CP, I); end if;
	blk`Gram := Matrix(0,0,[Integers()|]);
	CP`CSBlocks[i] := blk;
    vprintf Chtr, 2: "-ProcessIrreds: #Irreds %o, Trace %o, Rank of unknowns %o\n", #CP`Irreds, &+[blk`Trace:blk in CP`CSBlocks], &+[blk`Rank:blk in CP`CSBlocks];
    if GetVerbose("Chtr") gt 0 and forall{blk:blk in CP`CSBlocks|#blk`Reds eq
     blk`MaxRank} then
	 printf "-ProcessIrreds: Determinant = %o\n", get_full_det(CP`CSBlocks);
    end if;
    vprintf Chtr, 2: "-ProcessIrreds: time %o\n", Cputime(timer);
	return;
    end if;
    G := CP`G;
    G_ord := CP`G_order;
    cl := CP`Classes;
    n_cl := #cl;
    invs := CP`Invs;
    sizes := CP`Sizes;
    I_ip := [CP`V|];
    for j := 1 to #I do
	v1 := I[j]; v2 := [CP`K|0:k in [1..CP`n_Classes]];
	for k := 1 to n_cl do
	    v2[invs[k]] := v1[k]*sizes[k];
	end for;
	I_ip[j] := v2;
    end for;
    mask := {1..n_cl};
    m := ScalarMatrix(#I, 1);
    vprintf Chtr, 3: ".ProcessIrreds: adding %o to list\n", #I;
    m := gram_matrix_2(CP, blk`Reds, I_ip, blk`Gram, m, mask);
    vprintf Chtr, 3: ".ProcessIrreds: doing LLL\n", #I;
    L, T, r := LLLGram(m:Delta:=CP`LLLDelta,Sort:=false,InitialSort:=false,Proof:=false,Fast:=1);
    blk`Reds cat:= I;
    CP`CSBlocks[i] := blk;
    ProcessLLL_CP(~CP, i, L, T, r, 0);
    blk := CP`CSBlocks[i];
    vprintf Chtr, 2: ".ProcessIrreds: #Reds %o, Tr %o, Det %o\n", 
	 #(blk`Reds), blk`Trace, blk`Det;
  
    vprintf Chtr, 2: "-ProcessIrreds: #Irreds %o, Trace %o, Rank of unknowns %o\n", #CP`Irreds, &+[blk`Trace:blk in CP`CSBlocks], &+[blk`Rank:blk in CP`CSBlocks];
    if GetVerbose("Chtr") gt 1 and forall{blk:blk in CP`CSBlocks|#blk`Reds eq
     blk`MaxRank} then
	 printf "-ProcessIrreds: Determinant = %o\n", get_full_det(CP`CSBlocks);
    end if;
    vprintf Chtr, 2: "-ProcessIrreds: time %o\n", Cputime(timer);
end procedure;

CyclicInduction := procedure(~CP, i)
    zeit := Cputime();
    ord := CP`Classes[i][1];
    vprintf Chtr, 2: "+CyclicInduction: class %o, order %o\n", i, ord;
    up, down, pows := get_fusion(i, ord, CP`PowerMap);
    b := induce(pows, ord, up, down, CP);
    //assert forall{i:i in up|CP`Invs[i] in up};
    up := IndexedSetToSet(up);
    Chtr_lim := Max(50, CP`n_Classes div 20);
    blks := Ceiling(#b/Chtr_lim);
    blk := Ceiling(#b/blks);
    for i := 1 to blks do
	ProcessCharacters(~CP, b[(i-1)*blk+1..Min(#b,i*blk)], up, 0);
    end for;
    vprintf Chtr, 2: "-CyclicInduction: %o secs\n", Cputime(zeit);
end procedure;

LiftIrreds := procedure(~CP, irreds)
    zeit := Cputime();
    IntegralClasses(~CP);
    GaloisGroup(~CP);
    lifted := {@ @};
    to_lift := SequenceToSet(irreds);
    cl := CP`Classes;
    pm := CP`PowerMap;
    for x in to_lift do
	if x in lifted or x in CP`Irreds then continue; end if;
	vprintf Chtr, 3:"Lifting: Degree %o\n", x[1];
	zeith := Cputime();
	/* work out classes that must have integer chtr values */
	int_classes := CP`IntClasses; /* these are for all chtrs */
	for orb in CP`GalOrbits do
	    if #orb eq 1 then continue; end if;
	    rep := Rep(orb);
	    val := x[rep];
	    if exists{i:i in orb|x[i] ne val} then continue; end if;
	    if forall{p:p in PrimeDivisors(cl[rep,1]) | 
		    pm(rep, p) in int_classes} then
		int_classes join:= {i:i in orb};
	    end if;
	end for;
	ss := ChtrLiftIrredInternal(
	    CP`ChtrRng, x, int_classes, CP`lift_ords, CP`lift_K_mats, CP`zeta
	);
	CP`HardLiftTime +:= RealField(5)!Cputime(zeith);
	zeith := Cputime();
	orbp := {@ x @};
	orb0 := {@ ss @};
	if #int_classes lt #cl then
	    GaloisOrbit(~CP, ~orbp, ~orb0);
	end if;
	lifted join:= orbp;
	CP`OrbLiftTime +:= RealField(5)!Cputime(zeith);
	vprintf Chtr, 3:"Lifting: orbit has length %o\n", #orbp;
	zeith := Cputime();
	s_ind := Schur(ss, 2);
	for ss in orb0 do
	    Append(~CP`lift_irreds, ss);
	    AssertAttribute(ss, "IsCharacter", true);
	    if not HasAttribute(ss, "Schur") then 
		AssertAttribute(ss, "Schur", s_ind);
	    end if;
	    if not HasAttribute(ss, "Norm") then 
		AssertAttribute(ss, "Norm", 1);
	    end if;
	    AssertAttribute(ss, "IsIrreducible", true);
	end for;
	CP`AddChtrTime +:= RealField(5)!Cputime(zeith);
    end for;
    CP`LiftTime +:= RealField(5)!Cputime(zeit);
    vprintf Chtr, 2:"Accumulated lifting time is %o seconds\n", CP`LiftTime;
    vprintf Chtr, 3:"Accumulated lifting times: O:%o H:%o A:%o\n", 
	    CP`OrbLiftTime, CP`HardLiftTime, CP`AddChtrTime;
    leftovers := [x: x in lifted | x notin to_lift];
    CP`Irreds join:= lifted;
    if #leftovers gt 0 then
	vprintf Chtr, 2: "Galois action found %o new irreds\n", #leftovers;
	CP`FoundIrreds cat:= leftovers;
    end if;
end procedure;

AddCharacter := procedure(~CP, x)
    r := [CharacterToModular(x, CP`zeta)];
    ProcessCharacters(~CP, r, [1..CP`n_Classes], 2);
end procedure;

orthog_factors := function(gr, max)
vprint Chtr: "Factorizing Gram matrix";
    r := Nrows(gr);
    assert r eq Ncols(gr);
    gr_inv := ChangeRing(gr, Rationals())^-1;
    L := LatticeWithGram(gr_inv:CheckPositive:=false);
vprintf Chtr, 3: "Got lattice, getting short vectors (max %o)\n", max;
    P := ShortVectorsProcess(L,1,1);
    v1 := [];
    while not IsEmpty(P) and #v1 lt max do
	Append(~v1, NextVector(P));
    end while;
    /*
    try 
	v1 := [x[1]: x in ShortVectors(L, 1, 1:Max := max)];
    catch e
	return [];
    end try;
    */
    if #v1 ge max then /* too many */ return []; end if;
    assert #v1 ge r; /* this is a consequence of the assumption that 
			we've reached full rank */
    if #v1 eq r then /* one solution only */
        res := [Matrix(r, r, [v1[j][i] : j in [1..r], i in [1..r]])];
        // assert forall{A : A in res | A*Transpose(A) eq gr};
        return res;
    end if;
    /* have to search for solutions */

vprintf Chtr, 3: "Got %o short vectors, getting cliques\n", #v1;
    M1 := Matrix(#v1, r, [[v1[i,j]:j in [1..r]]:i in [1..#v1]]);
    M2 := M1*gr_inv*Transpose(M1); /* M2 = gram matrix for all v1's */
    perp_graph := Graph<#v1 |
	    {{i,j} : j in [1..i-1], i in [2..#v1] | IsZero(M2[i,j]) }>;
    cliks := AllCliques(perp_graph, r:Limit := max);//cliques wanted are maximal
    if #cliks eq max then /* too many */ return []; end if;
    res := [Transpose(VerticalJoin([v1[Index(j)]:j in cl])) : cl in cliks];
    // assert forall{A : A in res | A*Transpose(A) eq gr};
    return res;
end function;

solutions_construct_and_filter := function(CP, sols, b)
    G_ord := CP`G_order;
    Z := CP`Z;
    K := CP`K;
    T_seq := [];
    indicators := [K|];
    Km1 := K!(-1);
    poss := {K | Km1, 0, 1};
    one := CP`V ! [1: i in [1..CP`n_Classes]];
    sqrs := [ CP`PowerMap(i, 2) : i in [1..CP`n_Classes]];
    indicators := [
	ip_K(CP, CP`V![x[sqrs[i]]: i in [1..CP`n_Classes]], one) : x in b ];
	
    for A in sols do
	T := ChangeRing(A, K)^-1;
	for i := 1 to #b do
	    d :=  Z!(&+[T[i,j]*b[j,1]:j in [1..#b]]);
	    if d gt CP`p_on_2 then
		n := true;
		d := CP`p - d;
	    else
		n := false;
	    end if;
	    if d eq 0 or G_ord mod d ne 0 then
		vprintf Chtr, 3: "reject sol: bad degree %o\n", d;
		continue A;
	    end if;
	    ind := &+[T[i,j]*indicators[j]:j in [1..#b]];
	    if n then ind := -ind; end if;
	    if ind notin poss  then
		vprintf Chtr,3: "reject sol: frob-schur indicator %o\n", ind;
		continue A;
	    end if;
	    if ind eq Km1 and d mod 2 eq 1 then
		vprint Chtr,3: "reject sol: frob-schur & degree";
		continue A;
	    end if;
	end for;
	Append(~T_seq, T);
    end for;

    vec_sols := {};
    for T in T_seq do
	vecs := {};
	for i := 1 to #b do
	    v := &+[ T[i, j] * b[j] : j in [1..#b]|T[i,j] ne 0]; 
	    d := CP`Z ! v[1];
	    if d gt CP`p_on_2 then v := -v; end if;
	    Include(~vecs, v);
	    if #vecs lt i then 
		vprint Chtr,3: "reject sol: not enough different";
		continue T;
	    end if;
	end for;
	Include(~vec_sols, vecs);
    end for;

    if #vec_sols eq 1 then
	return SetToSequence(vec_sols);
    end if;

    common := &meet vec_sols;
    // vprintf Chtr, 3:"Found %o common characters", #common;
    vec_sols := { vecs diff common: vecs in vec_sols };
    
    hold := vec_sols;
    vec_sols := [];
    p_on_2 := CP`p_on_2;
    for vecs in hold do
	for v in vecs do
	    a1 := CP`V ! [ v[i]^2 : i in [1..CP`n_Classes]];
	    a2 := CP`V ! [ v[sqrs[i]] : i in [1..CP`n_Classes]];
	    v2 := (a1 -a2)/2;
	    v3 := (a1 +a2)/2;
	    n := CP`Z!ip_K(CP, v2, v2);
	    if n gt p_on_2 then 
		vprint Chtr,3: "reject sol: bad norm for sqr";
		continue vecs;
	    end if;
	    deg := CP`Z!v2[1];
	    if exists(ipy){ipy:y in vecs|ipy gt p_on_2 or ipy^2 gt n or 
			ipy gt deg div CP`Z!y[1]
			    where ipy is CP`Z!ip_K(CP, y, v2)} then
		vprintf Chtr,3: "reject sol: bad inner prod A with sol %o\n", ipy;
		continue vecs;
	    end if;
	    n := CP`Z!ip_K(CP, v3, v3);
	    if n gt p_on_2 then 
		vprint Chtr,3: "reject sol: bad norm for sqr";
		continue vecs;
	    end if;
	    deg := CP`Z!v3[1];
	    if exists(ipy){ipy:y in vecs|ipy gt p_on_2 or ipy^2 gt n or 
			ipy gt deg div CP`Z!y[1]
			    where ipy is CP`Z!ip_K(CP, y, v3)} then
		vprintf Chtr,3: "reject sol: bad inner prod S with sol %o\n", ipy;
		continue vecs;
	    end if;
	end for;
	Append(~vec_sols, vecs);
    end for;

    return [vecs join common : vecs in vec_sols];
end function;

/*
split_using_chtr_spaces := procedure(~CP, v_seq, ~res)
    if not CP`use_split then res := [v_seq]; return; end if;
vprint Chtr, 2: "+Chtr space split";
    timer := Cputime();
    blocks := CP`CSBlocks;
    CS := [blk`CS:blk in blocks];
    if not assigned CP`CS_matrix then
vprint Chtr, 3: ".Chtr space split: getting projection matrices";
	list := <>;
	for i := 1 to #CS do
	    BM := BasisMatrix(CS[i]);
	    Append(~list, BM);
	end for;
	unk_dim := &+[Nrows(m): m in list];
	Append(~list, Matrix([CP`Irreds[i]:i in [1..CP`n_Classes-unk_dim]]));
	m := VerticalJoin(list);
	m := m^-1;
	K := CP`K;
	i := 1;
	BM := BasisMatrix(CS[i]);
	dim := Nrows(BM);
	ncols := Ncols(m);
	blocks[i]`BM := m*VerticalJoin(<BM, ZeroMatrix(K, ncols-dim, ncols)>);
	done_rows := dim;
	for i := 2 to #CS do
	    BM := BasisMatrix(CS[i]);
	    dim := Nrows(BM);
	    blocks[i]`BM := m*VerticalJoin(
		<ZeroMatrix(K, done_rows, ncols), BM, 
			ZeroMatrix(K, ncols-done_rows-dim, ncols)>);
	    done_rows +:= dim;
	end for;
	CP`CS_matrix := m;
	CP`CSBlocks := blocks;
    end if;
    res := [[CP`V|]:i in [1..#CS]];
    v_mat := Matrix(v_seq);
    nrows := Nrows(v_mat);
    for i := 1 to #blocks do
	BM := blocks[i]`BM;
	dim := Nrows(BM);
	if blocks[i]`MaxRank gt 0 then
	    vects_mat := v_mat * BM;
	    if not IsZero(vects_mat) then
		res[i] := [CP`V|vects_mat[j]:j in [1..nrows]];
	    end if;
	end if;
    end for;
vprintf Chtr, 2: "-Chtr space split: %o secs\n", Cputime(timer);
end procedure;
*/

split_using_chtr_spaces := procedure(~CP, v_seq, ~res)
    if not CP`use_split then res := [v_seq]; return; end if;
vprint Chtr, 2: "+Chtr space split";
    timer := Cputime();
    blocks := CP`CSBlocks;
    CS := [blk`CS:blk in blocks];
    if not assigned CP`CS_matrix then
	list := <>;
	for i := 1 to #CS do
	    BM := BasisMatrix(CS[i]);
	    Append(~list, BM);
	    blocks[i]`BM := BM;
	end for;
	unk_dim := &+[Nrows(m): m in list];
	Append(~list, Matrix([CP`Irreds[i]:i in [1..CP`n_Classes-unk_dim]]));
	m := VerticalJoin(list);
	CP`CS_matrix := m^-1;
	delete m;
	CP`CSBlocks := blocks;
    end if;
    m := CP`CS_matrix;
    res := [[CP`V|]:i in [1..#CS]];
    c_mat := Matrix(v_seq) * m;
    nrows := Nrows(c_mat);
    ptr := 0;
    for i := 1 to #blocks do
	BM := blocks[i]`BM;
	dim := Nrows(BM);
	if blocks[i]`MaxRank gt 0 then
	    vects_mat := Submatrix(c_mat, 1, ptr+1, nrows, dim) * BM;
	    if not IsZero(vects_mat) then
		/* Do NOT remove zero vectors from the following! */
		res[i] := [CP`V|vects_mat[j]:j in [1..nrows]];
	    end if;
	end if;
	ptr +:= dim;
    end for;
vprintf Chtr, 2: "-Chtr space split: %o secs\n", Cputime(timer);
end procedure;

finish_up := procedure(~CP, do_lift, timer, cent_count)
    for x in CP`lift_irreds do
	AssertAttribute(x, "IsCharacter", true);
	fl := IsIrreducible(x);
	assert fl;
    end for;
    if CP`Check gt 0 then
	vprintf Chtr, 2:"Checking character table to level %o\n", CP`Check;
	zeit := Cputime();
	CheckIrreds(~CP, CP`Check);
	vprintf Chtr, 2:"Checked character table: %o secs\n", Cputime(zeit);
    end if;
    vprintf Chtr, 2: "Character table computed %o centralisers\n", cent_count;
    vprintf Chtr: "Character table in %o secs\n", Cputime(timer);
end procedure;

do_factors_solution := procedure(~CP)
    /* return; turn off for testing */
    repeat
	blks := CP`CSBlocks;
	comm := 0;
	flag := false;
	for i := 1 to #blks do
	    blk := CP`CSBlocks[i];
	    if not blk`DoFactors then continue; end if;
	    if blk`MaxRank gt 0 and blk`MaxRank eq blk`Rank and
	       blk`Rank le 100 and 
	       CP`Z!(blk`Det) le 10^10 and CP`Z!(blk`Trace) le 10^4 then
		flag := true;
		sols := orthog_factors(blk`Gram, 5*blk`Rank);
vprintf Chtr, 2:"Factorization of Gram matrix: %o solutions\n", #sols;
		if #sols eq 0 then continue; end if;
		sols_2 := solutions_construct_and_filter(CP, sols, blk`Reds);
		comm_i := &meet sols_2;
vprintf Chtr, 2:"Factorization of Gram matrix: %o irreds\n", #comm_i;
		if #comm_i gt 0 then
		    ProcessIrreds(~CP, i, SetToSequence(comm_i));
		    comm +:= #comm_i;
		end if;
	    end if;
	end for;
if flag then
vprintf Chtr:"Found %o irreducibles by factorising Gram matrices\n", comm;
end if;
	for i := 1 to #blks do
	    CP`CSBlocks[i]`DoFactors := false;
	end for;
    until forall{blk:blk in CP`CSBlocks|not blk`DoFactors};
end procedure;

GaloisOrbit:= procedure(~CP, ~orbp, ~orb0)
    GaloisGroup(~CP);
    V := CP`V;
    R := CP`ChtrRng;
    K := CP`K;
    gens := CP`GalGroup;
    if #gens eq 0 then return; end if;
    len := CP`n_Classes;
    for g in gens do
	blkp := orbp;
	blk0 := orb0;
	repeat
	    xp := Rep(blkp);
	    imp := InternalChtrTablePermute(K, xp, g);
	    if imp in orbp then break; end if;
	    nextblk := {@ InternalChtrTablePermute(K, xp1, g) :
				xp1 in blkp | xp ne xp1@}; 
	    Include(~nextblk, imp);
	    orbp join:= nextblk;
	    blkp := nextblk;

	    // HACK! this following acts as g^-1, not as g does above
	    // Doesn't matter because we get full orbits in the long run
	    nextblk := {@ R![x0[g[i]]:i in [1..len]] : x0 in blk0 @}; 
	    orb0 join:= nextblk;
	    blk0 := nextblk;
	until false;
    end for;
end procedure;

AddPermChtr := procedure(~CP:Power := 4)
    zeit := Cputime();
    G := CP`G;
    if Type(G) ne GrpPerm then return; end if;
    OR := OrbitRepresentatives(G);
    R := CP`ChtrRng;
    if #OR eq 1 then
	x := PermutationCharacter(G) - 1;
	sc := SymmetricComponents(x, Power);
	Include(~sc, R!1);
	Include(~sc, x);
	sc := SetToSequence(sc);
    else
	cl := CP`Classes;
	OR := [t[2]:t in OR|t[1] gt 1];
	chtrs := {R|1};
	for i in OR do
	    f := OrbitAction(G, i);
	    x := R![#Fix(ClassRepresentative(G,i)@f)-1:i in [1..#cl]];
	    sc := SymmetricComponents(x, Power);
	    Include(~sc, x);
	    chtrs join:= {x:x in sc};
	end for;
	sc := SetToSequence(chtrs);
    end if;
    M := ScalarMatrix(#sc, 0);
    for i := 1 to #sc do for j := i to #sc do
	M[i,j] := InnerProduct(sc[i],sc[j]);
	M[j,i] := M[i,j];
    end for; end for;
    L, T, r := LLLGram(M:Delta:=0.999, Sort:=false, Proof:=false, Fast:=1);
    int_chtrs := [];
    for i := 1 to r do
	if L[i,i] lt CP`p_on_2 then
	    Append(~int_chtrs, 
		CharacterToModular(&+[T[i,j]*sc[j]:j in [1..#sc]], CP`zeta)
	    );
	end if;
    end for;
    ProcessCharacters(~CP, int_chtrs, {1..CP`n_Classes}, 0);
    vprintf Chtr, 2: "Added permutation chtrs and powers in %o secs\n",
	RealField(5)!Cputime(zeit);
end procedure;

AddOrderChtr := procedure(~CP)
    zeit := Cputime();
    G := CP`G;
    E := Exponent(G);
    cl := CP`Classes;
    ordset := {c[1] : c in cl};
    Exclude(~ordset, 1);
    sc := [];
    sc := [CP`ChtrRng|1];
    G_ord := #G;
    for ord in ordset do
	m := E div ord;
	assert G_ord mod m eq 0;
	val := G_ord div m;
	x := [0:i in [1..#cl]];
	for i := 1 to #cl do
	    if m mod cl[i,1] eq 0 then
		x[i] := val;
	    end if;
	end for;
	Append(~sc, x);
    end for;
    G_ord := FactoredOrder(G);
    for i := 1 to #G_ord do
	p := G_ord[i,1];
	val := p^G_ord[i,2];
	x := [0:i in [1..#cl]];
	for i := 1 to #cl do
	    if cl[i,1] mod p ne 0 then
		x[i] := val;
	    end if;
	end for;
	Append(~sc, x);
    end for;
    M := ScalarMatrix(#sc, 0);
    for i := 1 to #sc do 
	M[i,i] := Norm(sc[i]);
    end for;
    for i := 1 to #sc-1 do for j := i+1 to #sc do
	M[i,j] := InnerProduct(sc[i],sc[j]);
	M[j,i] := M[i,j];
    end for; end for;
    L, T, r := LLLGram(M:Delta:=0.999, Sort := false, Proof:=false,Fast:=1);
    int_chtrs := [];
    for i := 1 to r do
	if L[i,i] lt CP`p_on_2 then
	    Append(~int_chtrs, 
		CharacterToModular(&+[T[i,j]*sc[j]:j in [1..#sc]], CP`zeta)
	    );
	end if;
    end for;
    ProcessCharacters(~CP, int_chtrs, {1..CP`n_Classes}, 0);
    vprintf Chtr, 2: "Added order chtrs in %o secs\n",
	RealField(5)!Cputime(zeit);
end procedure;

CheckIrreds := procedure(~CP, level)
    if level le 0 then return; end if;

    /* level 1: Check degrees */
    Z := CP`Z;
    G := CP`G;
    sos := 0;
    N := Index(G, Centre(G));
    irreds := KnownIrreducibles(G);
    for x in irreds do
	flag, deg := IsCoercible(Z, Degree(x));
	if not flag then
	    printf "WRONG - degree is not an integer\n";
	    return;
	end if;
	if deg le 0  or N mod deg ne 0 then
	    printf "WRONG - degree %o is impossible\n", deg;
	    return;
	end if;
	sos +:= deg^2;
    end for;
    if sos ne CP`G_order then
	printf "WRONG - Sum of degree squares is not group order\n";
	return;
    end if;
    if level le 1 then return; end if;

    /* level 2: Check Frob-Schur indicators */
    sos := 0;
    for x in irreds do
	s := Schur(x, 2);
	flag, s_Z := IsCoercible(Z, s);
	if not flag then 
	    printf "WRONG - Schur indicator not an integer\n"; 
	    return;
	end if;
	if s_Z notin {0,1,-1} then 
	    printf "WRONG - Schur indicator %o\n", s_Z;
	    return;
	end if;
	if s_Z eq -1 and Z!Degree(x) mod 2 ne 0 then
	    printf "WRONG - Schur indicator %o, degree %o\n", s_Z, Z!Degree(x);
	    return;
	end if;
	sos +:= s_Z * Degree(x);
    end for;
    cl := CP`Classes;
    if sos ne &+[c[2]:c in cl|c[1] le 2] then
	printf "WRONG - Count of involutions is incorrect\n";
	return;
    end if;
    if level le 2 then return; end if;

    /* Level 3: Check norms - have to compute from scratch */
    invs := CP`Invs;
    for x in irreds do
	y := Eltseq(x);
	K := Universe(y);
	sum := 0;
	for i := 1 to #cl do
	    sum +:= cl[i,2]*y[i]*y[invs[i]];
	end for;
	flag, sum := IsCoercible(Z, sum);
	if not flag then 
	    printf "WRONG - Norm not an integer\n"; 
	    return;
	end if;
	if sum ne #G then 
	    printf "WRONG - Norm not 1 (%o)\n", sum;
	    return;
	end if;
    end for;
    if level le 3 then return; end if;

    /* Level 4: Number theoretic congruences */
    G_ord := FactoredOrder(G);
    pm := CP`PowerMap;
    ppc := []; /* p-prime classes */
    for t in G_ord do
	p := t[1];
	ppp := [];
	for i := 1 to #cl do
	    v, r := Valuation(cl[i,1], p);
	    _,a,_:= Xgcd(p^v, r);
	    ppp[i] := pm(i, a*p^v);
	end for;
	Append(~ppc, ppp);
    end for;
    for x in irreds do
	y := [x[i]:i in [1..#cl]];
	K := Universe(y);
	R := IntegerRing(K);
	ChangeUniverse(~y, R);
	for i := 1 to #G_ord do
	    ppp := ppc[i];
	    p := G_ord[i,1];
	    for j := 1 to #cl do
		pppj := ppp[j];
		if not IsZero(Modexp(y[j]-y[pppj], cl[j,1] div cl[pppj,1], p)) 
		then
		    printf "WRONG - congruence with p'-part\n";
		    printf "Prime: %o, Class: %o, p' class: %o\n",p,j,pppj;
		    printf "Values: %o, %o\n", K!y[j], K!y[pppj];
		end if;
	    end for;
	end for;
    end for;
    if level le 4 then return; end if;

    /* Level 5: Row orthogonality */
    for i := 2 to #cl do
	for j := 1 to i-1 do
	    ip := InnerProduct(irreds[i], irreds[j]);
	    if not IsZero(ip) then
		printf "WRONG - Inner product (%o,%o) not zero (%o)\n",
		    i,j,ip;
		return;
	    end if;
	end for;
    end for;
end procedure;

do_extra_cyclics := procedure(~CP)
    zeit := Cputime();
    vprintf Chtr, 2: "ChtrTable: Induction from extra cyclic subgroups\n"; 
    mat := Matrix([x:x in CP`Irreds]);
    for blk in CP`CSBlocks do
	if #blk`Reds gt 0 then
	    mat := VerticalJoin(mat, Matrix(blk`Reds));
	end if;
    end for;
    mat := EchelonForm(mat);
    leads := {};
    for i := 1 to Nrows(mat) do
	dummy := exists(j){j:j in [1..Ncols(mat)]|not IsZero(mat[i,j])};
	assert dummy;
	Include(~leads, j);
    end for;
    missing := {1..Ncols(mat)} diff leads;
    do_cycs := {};
    pm := CP`PowerMap;
    cl := CP`Classes;
    while #missing gt 0 do
	m := Rep(missing);
	dummy := exists(j){j:j in CP`TopClasses|exists{k:k in [1..cl[j,1]]|
		pm(j, k) eq m}};
	assert dummy;
	Include(~do_cycs, j);
	missing := {m:m in missing|m notin {pm(j,k):k in [1..cl[j,1]]}};
    end while;
    vprintf Chtr, 2: "ChtrTable: chosen extra cyclics %o after %o secs\n", 
	    do_cycs, Cputime(zeit); 
    for i in do_cycs do
	CyclicInduction(~CP, i);
    end for;
    do_factors_solution(~CP);
    vprintf Chtr, 2: "ChtrTable: done extra cyclics: %o secs\n", 
		Cputime(zeit);
end procedure;

do_missed_cyclics := procedure(~CP, det)
/*
This tidies up the fact that the can_use_p mechanism may stop us
doing induction from certain cyclic subgroups that are in fact
necessary to get the full lattice of generalised characters.
This routine does these inductions explicitly.
Hopefully not called very often!
*/
    zeit := Cputime();
    vprintf Chtr, 2: "ChtrTable: Induction from cyclic subgroups\n"; 
    do_cycs := CP`TopClasses;
    if not (det cmpeq 0) then 
	primes := [t[1]: t in det];
	cl := CP`Classes;
	do_cycs := [i: i in do_cycs | exists{p: p in primes |
	    cl[i, 1] mod p eq 0} ];
    end if;
    vprintf Chtr, 2: "ChtrTable: chosen cyclics %o after %o secs\n", 
	    do_cycs, Cputime(zeit); 
    for i in do_cycs do
	CyclicInduction(~CP, i);
	det := get_full_det(CP`CSBlocks);
	if det cmpeq [] then 
	    do_factors_solution(~CP);
	    vprintf Chtr, 2: "ChtrTable: done cyclics: %o secs\n",
		Cputime(zeit);
	    return;
	end if;
    end for;
    do_cycs := CP`TopClasses diff
	(ISA(Type(do_cycs), SeqEnum) select Seqset(do_cycs) else do_cycs);
    for i in do_cycs do
	CyclicInduction(~CP, i);
	det := get_full_det(CP`CSBlocks);
	if det cmpeq [] then 
	    do_factors_solution(~CP);
	    vprintf Chtr, 2: "ChtrTable: done cyclics: %o secs\n",
		Cputime(zeit);
	    return;
	end if;
    end for;
    assert false; /* this routine should finish up induction phase */
end procedure;

ChtrTable := function(G:Modulus:=0,ClassSizeLimit:=-1, Check:=2, ECThresh := 5,
Characters:=[])
    ChtrTable_timer := Cputime();
    Centralizer_count := 0;
    CP := InitialiseChtrProc(G:Modulus:=Modulus);
    CP`Check := Check;
    cl := CP`Classes;
    X := KnownIrreducibles(G);
    if #X eq #cl then return X; end if;
    csl := ClassSizeLimit;
    if csl eq -1 then
        if Type(G) eq GrpPC then
            csl := [0,1];
        else
            csl := 1;
        end if;
    end if;
    if Type(csl) eq SeqEnum then
        max := csl[#csl];
        for i := #csl-1 to 1 by -1 do max *:= #cl; max +:= csl[i]; end for;
    else
        max := csl;
    end if;
    if max eq 0 and Type(G) eq GrpPC  and CP`n_Classes le 5000 then
	CS := chief_character_spaces(CP, DerivedGroup(G));
	blks := [];
        for V in CS do
            Append(~blks, rec<Blkfmt|CS := V, MaxRank := Dimension(V), 
            Rank := 0, Trace := 0, Det := 1, Reds := [], DoFactors := false,
            Gram := Matrix(0,0,[Integers()|]), Irreds := {@ @}, LLLcount := 0>);
        end for;
        CP`CSBlocks := blks;
	CP`use_split := true;
	
    elif exists{c: c in cl|c[1] ne 1 and c[2] le max} then
        vprintf Chtr: "Using D-S with ClassSizeLimit %o\n", max;
        X, CS := CharacterTableDS(CP`G:Modulus:=CP`p,ClassSizeLimit:= max);
vprintf Chtr: "CS = %o, %o irreducible(s) known (out of %o)\n", [Dimension(V): V in
 CS], #KnownIrreducibles(G), #cl;
        if #X eq #cl then 
            finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
            return KnownIrreducibles(CP`G); 
        end if;
        CP := InitialiseChtrProc(CP`G);
        blks := [];
        for V in CS do
            Append(~blks, rec<Blkfmt|CS := V, MaxRank := Dimension(V), 
            Rank := 0, Trace := 0, Det := 1, Reds := [], DoFactors := false,
            Gram := Matrix(0,0,[Integers()|]), Irreds := {@ @}, LLLcount := 0>);
        end for;
        CP`CSBlocks := blks;
	CP`use_split := true;
    else
        CS := [];
        CP`CSBlocks := [rec<Blkfmt|CS := CP`V, Rank := 0, Trace := 0, 
            MaxRank := #cl - #CP`Irreds, Det := 1, Reds := [], DoFactors := false,
            Gram := Matrix(0,0,[Integers()|]), Irreds := CP`Irreds, LLLcount := 0>];
	CP`use_split := false;
    end if;

    CP`Check := Check;
    if #Characters gt 0 then
	chars := [CharacterToModular(x, CP`zeta): x in Characters];
	ProcessCharacters(~CP, chars, {1..CP`n_Classes}, 0);
    end if;
    AddPermChtr(~CP);
    if #KnownIrreducibles(G) le 1 then
	AddOrderChtr(~CP);
    end if;
vprintf Chtr: "CS = %o, %o irreducible(s) known (out of %o)\n", [b`MaxRank: b in
 CP`CSBlocks], #KnownIrreducibles(G), #cl;
    if #CP`Irreds eq #cl then 
	finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
	return KnownIrreducibles(CP`G); 
    end if;
    covered := [false:i in [1..#cl]];
    done := [false:i in [1..#cl]];
    done_primes := [{t[1]:t in Factorization(cl[i,1])}:i in [1..#cl]];
    non_abelian := [];
    pm := CP`PowerMap;
    assert_order := Type(G) eq GrpPerm or Type(G) eq GrpMat;

    for i := #cl to 1 by -1 do
	if done[i] then continue; end if;
        if #KnownIrreducibles(G) eq #cl then 
            finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
            return KnownIrreducibles(CP`G); 
        end if;
	c := cl[i];
	down := {pm(i,j):j in [1..c[1]]};
	for j in down do
	    if cl[j,1] eq c[1] then done[j] := true; end if;
	end for;
	f_ord := Factorization(c[1]);
	f_cent := Factorization(#G div c[2]);
	el_primes := {t[1]: t in f_cent};
	el_primes diff:= done_primes[i];
	if #el_primes gt 0 then
	    x := ClassRepresentative(G, i);
	    C := ClassCentralizer(G, i);
	    Centralizer_count +:= 1;
	    print_info := true;
	else
	    print_info := false;
	end if;
	covs := {};
	for p in el_primes do
	    vprintf Chtr: "Constructing elementary subgroup (%o, %o) after %o secs\n", c[1], p, Cputime(ChtrTable_timer);
	    assert c[1] mod p ne 0; 
	    S := Sylow(C,p);
	    assert FactoredOrder(S)[1,1] eq p;
	    val := FactoredOrder(S)[1,2];
	    H := sub<C|x, S>;
	    if assert_order then
		H`Order := c[1] * p^val;
	    end if;
	    delete S;
	    JJ := 0;
	    ElementaryInduction(~CP, H, p, ~JJ, ~fusion, ~sizes, ~mults, 
		~P, ~pp_V, []);
	    covs join:= Seqset(fusion);
	    if #KnownIrreducibles(G) eq #cl then 
		finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
		return KnownIrreducibles(CP`G); 
	    end if;
	    if JJ ge 0 then
		store_tup := [* p, FactoredOrder(H), fusion, sizes, mults, 
				    P, pp_V, covs, JJ, #H *];
		Append(~non_abelian, store_tup);
	    end if;
	    delete H;

	    /* set p done for some things further down */
	    for j in down do
		if done[j] or p in done_primes[j] then continue; end if;
		if Valuation(#G div cl[j,2], p) eq val then
		    Include(~done_primes[j], p);
		end if;
	    end for;
	end for;

	/* we may be able to set some more p's done */
	for t in f_ord do
	    p := t[1]; val := t[2];
	    for j in covs join down do
		if not (done[j] or p in done_primes[j]) and
			Valuation(#G div cl[j,2], p) eq val 
		then
		    Include(~done_primes[j], p);
		end if;
	    end for;
	end for;

	/* we've got some cyclics covered too */
	for j in covs do covered[j] := true; end for;

if print_info then
vprintf Chtr: "CS = %o, %o irreducible(s) known (out of %o)\n", [b`MaxRank: b in
 CP`CSBlocks], #KnownIrreducibles(G), #cl;
end if;

    end for;

    /* deal with cyclics that got skipped above */
    for i := #cl to 1 by -1 do
	if not covered[i] then
	    CyclicInduction(~CP, i);
	    down := {pm(i,k):k in [1..cl[i,1]]};
	    for j in down do
		covered[j] := true;
	    end for;
vprintf Chtr: "CS = %o, %o irreducible(s) known (out of %o)\n", [b`MaxRank: b in
 CP`CSBlocks], #KnownIrreducibles(G), #cl;
        if #KnownIrreducibles(CP`G) eq #cl then 
            finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
            return KnownIrreducibles(CP`G); 
        end if;
	end if;
    end for;

    do_factors_solution(~CP);
    if #CP`Irreds eq #cl then 
	finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
	return KnownIrreducibles(CP`G); 
    end if;

    while #non_abelian gt 0 and #CP`Irreds lt #cl do
vprintf Chtr, 2:"Starting layer loop: %o incomplete, %o, det = %o, layer sum %o\n", #non_abelian, {*t[1]:t in non_abelian*}, get_full_det(CP`CSBlocks), &+[t[9]:t in non_abelian];

	deficit := CP`n_Classes - 
		(#CP`Irreds + &+[#blk`Reds: blk in CP`CSBlocks]);
	if deficit gt 0 and deficit le ECThresh then
	    do_extra_cyclics(~CP);
	    if #CP`Irreds eq #cl then 
		finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
		return KnownIrreducibles(CP`G); 
	    end if;
	end if;
	pos := 0;
	min_lev := #G;
	max_ord := 0;
	R := {};
	for j := 1 to #non_abelian do
	    t := non_abelian[j];
	    if can_use_p(CP, t[1]) then
	    /* t[9] is the level this one is up to, t[10] is the group order */
		if t[9] lt min_lev or (t[9] eq min_lev and t[10] gt max_ord)
		then
		    pos := j;
		    min_lev := t[9];
		    max_ord := t[10];
		end if;
	    else
		Include(~R, j);
	    end if;
	end for;
	if pos gt 0 then
	    t := non_abelian[pos];
	    lev := t[9];
	    ElementaryInduction(
		~CP, t[2], t[1], ~lev, ~t[3], ~t[4], ~t[5], ~t[6], ~t[7], []);
	    if lev eq -1 then
		Include(~R, pos);
	    end if;

vprintf Chtr: "CS = %o, %o irreducible(s) known (out of %o)\n", [b`MaxRank: b in
 CP`CSBlocks], #KnownIrreducibles(G), #cl;

	    t[9] := lev;
	    non_abelian[pos] := t;
	end if;
	do_factors_solution(~CP);
	if #CP`Irreds eq #cl then 
	    finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
	    return KnownIrreducibles(CP`G); 
	end if;
	non_abelian := [non_abelian[i]:i in [1..#non_abelian]|i notin R];
    end while;

    det := get_full_det(CP`CSBlocks);
    vprintf Chtr: "After elementary induction: det %o\n", det;

    if not (det cmpeq []) then
	deficit := CP`n_Classes - 
		(#CP`Irreds + &+[#blk`Reds: blk in CP`CSBlocks]);
	if deficit gt 0 then
	    do_extra_cyclics(~CP);
	    if #CP`Irreds eq #cl then 
		finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
		return KnownIrreducibles(CP`G); 
	    end if;
	end if;
	det := get_full_det(CP`CSBlocks);
	if not (det cmpeq []) then
	    do_missed_cyclics(~CP, det);
	    if #CP`Irreds eq #cl then
		finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count);
		return KnownIrreducibles(CP`G);
	    end if;
	end if;
    end if;

    irrs := [];
    for blk in CP`CSBlocks do
	reds := blk`Reds;
	r := #reds;
	if r eq 0 then continue blk; end if;
	g1, T1 := LLLGram(blk`Gram: Delta := 0.999, Proof:=false);
	g2, T2 := LLLGram(g1 : Delta := 0.999, Proof:=false,
	    DeepInsertions := true);
	lat := LatticeWithGram(g2:CheckPositive:=false);
	sv := [(t[1]*T2)*T1 :
		t in ShortVectors(lat, 1, 1 : Max := r, Proof := false)];
	for v in sv do
	    Append(~irrs, &+[v[j]*reds[j]:j in [1..r]]);
	end for;
    end for;
    ProcessCharacters(~CP, irrs, {1..CP`n_Classes}, 0:LLLSort:=true);
    finish_up(~CP, CP`DoLift, ChtrTable_timer, Centralizer_count); 
    return KnownIrreducibles(CP`G);

end function;

can_use_p := function(CP, p)
    rank := #CP`Irreds + &+[#blk`Reds:blk in CP`CSBlocks];
    assert rank le CP`n_Classes;
    if rank lt CP`n_Classes then return true; end if;
    full_det := get_full_det(CP`CSBlocks);
    if full_det cmpeq 0 then return true; end if;
    return exists{t:t in full_det| p eq t[1]};
end function;

intrinsic ChtrTableWrapper(G:ClassSizeLimit:=1, Al :="Default", Check:=2,Characters := []) -> SeqEnum
{}
    if #ClassesData(G) eq #KnownIrreducibles(G) then 
	T := CharacterTableDS(G);
	fl := CheckCharacterTable(T, 1 : Print := false);
	require fl : "Error in character table test";
	return T;
    end if;
    if Al eq "Default" then 
	if #G le 5000 then
	    T := CharacterTableDS(G);
	    fl := CheckCharacterTable(T, Check : Print := false);
	    require fl : "Error in character table test";
	    return T;
	elif #FactoredOrder(G) eq 1 then
	    if Type(G) ne GrpPC then
		P,f := PCGroup(G);
		XP := CharacterTableConlon(P);
		XP := LiftCharacters(XP, f, G);
		for x in XP do
		    AssertAttribute(x, "IsIrreducible", true);
		end for;
		T := KnownIrreducibles(G);
		fl := CheckCharacterTable(T, Check : Print := false);
		require fl : "Error in character table test";
		return T;
	    else
		T := CharacterTableConlon(G);
		fl := CheckCharacterTable(T, Check : Print := false);
		require fl : "Error in character table test";
		return T;
	    end if;
	elif Type(G) ne GrpPC and IsSoluble(G) then
	    P,f := PCGroup(G);
	    XP := CharacterTable(P:DSSizeLimit:=Max(ClassSizeLimit, GrpPCDSSL),Check:=Check);
	    XP := LiftCharacters(XP, f, G);
	    for x in XP do
		AssertAttribute(x, "IsIrreducible", true);
	    end for;
	    T := KnownIrreducibles(G);
	    fl := CheckCharacterTable(T, Check : Print := false);
	    require fl : "Error in character table test";
	    return T;
	else
	    return ChtrTable(G:ClassSizeLimit:=ClassSizeLimit, Check:=Check,Characters:=Characters);
	end if;
    elif Al eq "DS" then
	T := CharacterTableDS(G);
	T := KnownIrreducibles(G);
	fl := CheckCharacterTable(T, Check : Print := false);
	require fl : "Error in character table test";
	return T;
    elif Al eq "IR" then
	return ChtrTable(G:ClassSizeLimit:=ClassSizeLimit, Check:=Check,Characters:=Characters);
    elif Al eq "Conlon" then
	if #FactoredOrder(G) gt 1 then
	    error "Cannot use Conlon's character algorithm for non p-group";
	end if;
	if Type(G) ne GrpPC then
	    P,f := PCGroup(G);
	    XP := CharacterTableConlon(P);
	    XP := LiftCharacters(XP, f, G);
	    for x in XP do AssertAttribute(x, "IsIrreducible", true); end for;
	    T := KnownIrreducibles(G);
	    fl := CheckCharacterTable(T, Check : Print := false);
	    require fl : "Error in character table test";
	    return T;
	else
	    T := CharacterTableConlon(G);
	    fl := CheckCharacterTable(T, Check : Print := false);
	    require fl : "Error in character table test";
	    return T;
	end if;
    else
	error "Unknown algorithm (", Al, ") selected";
    end if;
end intrinsic;

intrinsic CharacterTable(G :: GrpMat:Al := "Default", DSSizeLimit:=0, Check := 2, Characters := []) -> SeqEnum
{Character Table of finite group G}
    return ChtrTableWrapper(G:Al:=Al,ClassSizeLimit:=DSSizeLimit, Check:=Check,Characters:=Characters);
end intrinsic;

intrinsic CharacterTable(G :: GrpPC:Al := "Default", DSSizeLimit:=GrpPCDSSL, Check := 2, Characters := []) -> SeqEnum
{"} // "
    return ChtrTableWrapper(G:Al:=Al,ClassSizeLimit:=DSSizeLimit, Check:=Check,Characters:=Characters);
end intrinsic;

intrinsic CharacterTable(G :: GrpPerm: Al := "Default", DSSizeLimit:=0, Check:=2, Characters := [] ) -> SeqEnum
{"} // "
  return ChtrTableWrapper(G:Al:=Al,ClassSizeLimit:=DSSizeLimit, Check:=Check,Characters:=Characters);
end intrinsic;

intrinsic CharacterTable(G :: GrpAb: Al := "Default", DSSizeLimit:=0, Check:=2, Characters := [] ) -> SeqEnum
{"} // "
  return LinearCharacters(G);
end intrinsic;
