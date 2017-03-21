freeze;

/*
Operations on complexes and their modules.
AKS, Oct 08.
*/

/*******************************************************************************
			    Betti Table
*******************************************************************************/

intrinsic BettiTable(C::ModCpx) -> SeqEnum, RngInt
{Return the Betti table of the complex C and the shift of the degree}

    Q := Reverse(Terms(C));
    Q := [M: M in Q | Degree(M) gt 0];
    C := [{* w: w in ColumnWeights(f) *}: f in Q];

    min := Min(C[1]);

    maxi := 0;
    for j := 1 to #C do
	// i + j - 1 = m
	m := Max(C[j]);
	i := m + 1 - j;
	maxi := Max(maxi, i);
    end for;

// C; "m:", m; "diff:", m - #C, "maxi:", maxi;

    T := [[Multiplicity(C[j], i + j - 1): j in [1..#C]]: i in [min .. maxi]];
    return T, min;
end intrinsic;

/*******************************************************************************
			    Betti Number
*******************************************************************************/

intrinsic BettiNumber(
    M::ModMPol, i::RngIntElt, j::RngIntElt: Minimal
) -> RngIntElt
{The graded Betti number beta_{i,j\} for M, which is the number of generators
of degree j in the i-th term F_i of the free resolution of M.}

    requirege i, 0;
    T, s := BettiTable(M: Minimal := Minimal);
    j -:= s;
    if j - i + 1 notin [1 .. #T] or i + 1 gt #T[1] then
	return 0;
    end if;
    return T[j - i + 1, i + 1];

end intrinsic;

intrinsic MaximumBettiDegree(M::ModMPol, i::RngIntElt: Minimal) -> RngIntElt
{The maximum degree of the generators in the i-th term F_i of the free
resolution of M.}

    requirege i, 0;
    T, s := BettiTable(M: Minimal := Minimal);
    if i + 1 gt #T[1] then
	return 0;
    end if;
    // t = j - i + 1, j = t + i - 1
    for t := #T to 1 by -1 do
	if T[t, i + 1] gt 0 then
	    j := t + i - 1;
	    return j + s;
	end if;
    end for;
    return 0;
end intrinsic;

/*******************************************************************************
			    Regularity
*******************************************************************************/

intrinsic Regularity(M::ModMPol) -> RngIntElt
{The Castelnuovo-Mumford regularity of the graded (or local) module M}

    require IsHomogeneous(M) or IsLocal(M):
	"M must be homogeneous or over a local ring";

    T, s := BettiTable(M);
    D := [Max({t - 1: t in [1 .. #T] | T[t, j + 1] ne 0}): j in [0 .. #T[1]-1]];
//D;
    r := Max(D) + s;
    return r;
end intrinsic;

/*******************************************************************************
			    Dimension
*******************************************************************************/

intrinsic HomologicalDimension(M::ModMPol) -> RngIntElt
{The homological or projective dimension of module M}

    return #BettiNumbers(M) - 1;
end intrinsic;

intrinsic ProjectiveDimension(M::ModMPol) -> RngIntElt
{The homological or projective dimension of module M}

    return #BettiNumbers(M) - 1;
end intrinsic;
