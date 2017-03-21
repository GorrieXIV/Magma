freeze;
 
Z := IntegerRing();
Q := RationalField();

/*******************************************************************************
				Attributes
*******************************************************************************/

declare attributes GrpMat: Expand;
declare attributes ModGrp: Expand;

/*******************************************************************************
				Integral module
*******************************************************************************/

intrinsic IntegralModule(M::ModGrp) -> ModGrp
{Given a G-module M over Q, for finite G, return an equivalent
G-module over Z}

    if BaseRing(M) ne RationalField() then
	return M, MatrixRing(Z, Dimension(M))!1;
    end if;
    L := [ActionGenerator(M, i): i in [1 .. Nagens(M)]];
//"First L", L;
    if L eq [] then
      return GModule(Group(M), [GL(Dimension(M), Integers())|]), IdentityMatrix(Rationals(), Dimension(M));
    end if;
    L, T := IntegralGroup(L);
//"Now L", L;
//Universe(L);
    L := ChangeUniverse(L, ChangeRing(Universe(L), Z));
    return GModule(Group(M), L), T;
end intrinsic;

/*******************************************************************************
				Clean
*******************************************************************************/

function get_transform(G, steps)

    vprint Clean: "PositiveDefiniteForm";
    vtime Clean: F := PositiveDefiniteForm(G);

    if steps gt 1 then
	vprintf Clean: "Do %o steps\n", steps;

	U := MatrixRing(Z, Nrows(F))!1;
	for i := 1 to steps do
	    F, T := LLLGram(
		F: Delta := 0.999, Check := false, FinalSort, Proof := false
	    );
	    U := T*U;
	    /*
	    F, T := PairReduceGram(F);
	    U := T*U;
	    */
	end for;

	F, T := SeysenGram(F);
	U := T*U;
    else
	vprint Clean: "LLL";
	vtime Clean: FL, TL :=
	    LLLGram(F: Delta := 0.999, Check := false, FinalSort);

	vprint Clean: "Seysen";
	vtime Clean: FS, TS := SeysenGram(FL);

	U := TS*TL;
    end if;

    UI := U^-1;

    return U, UI;

end function;

intrinsic Clean(G::GrpMat: Steps := 1) -> GrpMat, GrpMatElt
{Return a group H equivalent to G such that the entries of the
generators of H are hopefully smaller than those of G; return
also the relevant conjugating matrix};

    require BaseRing(G) cmpeq Z: "Matrix group must be integral";

    /*
    if BaseRing(G) cmpeq RationalField() then
	G := IntegralGroup(G);
    end if;
    */

    U, UI := get_transform(G, Steps);

    Q := [U*Matrix(G.i)*UI: i in [1 .. Ngens(G)]];

    H := MatrixGroup<Degree(G), Z | Q>;

    if assigned G`Order then H`Order := G`Order; end if;
    if assigned G`FactoredOrder then H`FactoredOrder := G`FactoredOrder; end if;

    return H, GL(Degree(G),Z)!U; /* return transform as GL object */

end intrinsic;

intrinsic Clean(M::ModGrp: Steps := 1) -> ModGrp, GrpMatElt
{Return a G-module equivalent to M such that the entries of the
action generators of the new module are hopefully smaller than those of M;
return also the relevant conjugating matrix};

    require BaseRing(M) cmpeq Z: "G-module must be integral";

    if Nagens(M) eq 0 then
      return M, GL(Degree(MatrixGroup(M)), Z)!1;
    end if;

    U, UI := get_transform(MatrixGroup(M: Check := false), Steps);

    L := [U*ActionGenerator(M, i)*UI: i in [1 .. Nagens(M)]];
    H := GModule(Group(M), L: Check := false);

    return H, GL(Degree(MatrixGroup(M)),Z)!U; /* transform as GL object */

end intrinsic;

/*******************************************************************************
				Expand (over ANF)
*******************************************************************************/

intrinsic Expand(L::[Mtrx]: S := Q) -> []
{Given matrices over an ANF, return the corresponding matrices over subfield
S (default Q) via companion matrix expansion}

    if IsNull(L) then
	return L;
    end if;

    K := BaseRing(Universe(L));
    if K cmpeq S then
	return L;
    end if;

    if ISA(Type(K), AlgAssV) then /* MW 03 Sep 2010 */
	require S cmpeq Q: "Subfield must be Q";
	return [RepresentationMatrixOfMatrix(l) : l in L];
    end if;

    require IsSubfield(S, K): "S must be a subfield of base ring";

    n := Ncols(L[1]);

    d := ExactQuotient(Degree(K), Degree(S));
    M := MatrixRing(S, d);

    /*
    D := DefiningPolynomial(K);
    if ISA(Type(D), SeqEnum) then
	require #D eq 1: "Can only handle one defining polynomial";
	D := D[1];
    else
	f := hom<K -> M | CompanionMatrix(D)>;
    end if;
    */

    if S cmpeq Q then
	f := map<K -> M | x :-> RepresentationMatrix(x)>;
    else
	mp := MinimalPolynomial(K.1, S);
	cm := CompanionMatrix(mp);
	//f := map<K -> M | M!cm>; // GROAN: should work but doesn't!
	dK := Degree(K);
	cmp := [cm^i: i in [0 .. dK - 1]];
	f := map<K -> M |
	    x :-> &+[c[i]*cmp[i]: i in [1 .. dK]] where c:=Eltseq(x)>;
    end if;

    LL := [];
    nd := n*d;
    for X in L do
	Y := MatrixRing(S, nd) ! 0;
	for i,j in [1 .. n] do
	    B := f(X[i, j]);
	    InsertBlock(~Y, B, d*(i - 1) + 1, d*(j - 1) + 1);
	end for;
	Append(~LL, Y);
    end for;

    return LL;

end intrinsic;

intrinsic Expand(G::GrpMat: S := Q) -> GrpMat
{Given matrix group G over an ANF, return the corresponding matrix group
over subfield S (default Q) via companion matrix expansion}

    if S cmpeq Q and assigned G`Expand then
	return G`Expand;
    end if;

    L := [G.i: i in [1 .. Ngens(G)]];
    K := BaseRing(Universe(L));
    L := Expand(L: S := S);

    if ISA(Type(K), AlgAssV) then /* MW 03 Sep 2010 */
	require S cmpeq Q: "Subfield must be Q";
        GE:=MatrixGroup<Degree(K)*Degree(G),Q|L : Check:=false>;
    else
        GE := MatrixGroup<Degree(G)*Degree(BaseRing(G), S), S |
			    L: Check := false>;
    end if;
    if S cmpeq Q then
	G`Expand := GE;
    end if;

    return GE;
end intrinsic;

intrinsic Expand(M::ModGrp: S := Q) -> ModGrp
{Given G-module M over an ANF, return the corresponding G-module over subfield
S (default Q) via companion matrix expansion}

    if S cmpeq Q then 
	if assigned M`Expand then
	    return M`Expand;
	end if;

	if Type(BaseRing(M)) in {RngInt, FldRat} then
	    return M;
	end if;
    end if;

    L := [ActionGenerator(M, i): i in [1 .. Nagens(M)]];
    if L eq [] then
	ME := GModule(Group(M), [GL(Dimension(M), S)|]);
    else
	L := Expand(L: S := S);
	ME := GModule(Group(M), L: Check := false);
    end if;

    if S cmpeq Q then
	M`Expand := ME;
    end if;

    return ME;
end intrinsic;

intrinsic ExpandZ(M::ModGrp: DoClean := 0) -> ModGrp
{Given G-module M over an ANF, return the corresponding G-module over Z
via companion matrix expansion}

    I, T := IntegralModule(Expand(M));

    if DoClean cmpeq 0 then
        DoClean := Dimension(M) le 100 and IsFinite(Group(M));
    end if;

    if DoClean then
	I := Clean(I);
    end if;

    if Nagens(M) eq 0 then
	return I, T;
    end if;

    MZ := GModule(
	Group(M), [ActionGenerator(I, i): i in [1 .. Nagens(M)]]: Check := false
    );
    return MZ, T;

end intrinsic;
