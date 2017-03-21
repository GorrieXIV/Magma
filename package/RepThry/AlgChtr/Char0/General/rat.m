freeze;

/*
Functions for handling rational characters.
AKS, June 09.
*/

/*******************************************************************************
			    Attributes
*******************************************************************************/

declare attributes Grp:
    RationalCharacterTable, RationalCharacterTableIndices,
    RationalCharacterTableRSpace, RationalCharacterTableSchurIndex;

Z := IntegerRing();

/*******************************************************************************
			    RationalCharacterTable
*******************************************************************************/

intrinsic RationalCharacterTable(G::Grp) -> SeqEnum[AlgChtrElt]
{The table T of irreducible rational characters of the finite group G,
together with a index sequence I, so that I[i] gives the indices of the
characters in the complex character table which sum to T[i]}

    if assigned G`RationalCharacterTable then
	return G`RationalCharacterTable, G`RationalCharacterTableIndices;
    end if;

    CT := CharacterTable(G);

    CT := {@ c: c in CT @};
    done := {};
    rats := [];
    ratsi := [];
    for C in CT do
        if C in done then
            continue;
        end if;
        o := GaloisOrbit(C);
        done join:= Set(o);
        Append(~rats, &+o);
        Append(~ratsi, Sort([Index(CT, x): x in o]));
    end for;
    Q := [<rats[i], ratsi[i]>: i in [1 .. #rats]];
    Sort(
        ~Q,
        func<x, y |
            d eq 0 select Min(x[2]) - Min(y[2]) else d
            where d := x[1, 1] - y[1, 1]
        >
    );

    rats := [t[1]: t in Q];
    ratsi := [t[2]: t in Q];

    G`RationalCharacterTable := rats;
    G`RationalCharacterTableIndices := ratsi;

    return rats, ratsi;

end intrinsic;

/*******************************************************************************
				Schur index
*******************************************************************************/

intrinsic RationalCharacterSchurIndex(G::Grp, i::RngIntElt) -> RngIntElt
{Return the Schur index of an ordinary character in the orbit whose sum
is the i-th rational character of G}

    CT, CTI := RationalCharacterTable(G);
    requirerange i, 1, #CT;

    if assigned G`RationalCharacterTableSchurIndex then
	SI := G`RationalCharacterTableSchurIndex;
	if IsDefined(SI, i) then
	    return SI[i];
	end if;
    else
	SI := [];
    end if;

    si := SchurIndex(CharacterTable(G)[CTI[i, 1]]);
    SI[i] := si;
    G`RationalCharacterTableSchurIndex := SI;
    return si;

end intrinsic;

/*******************************************************************************
	    RationalCharacterTableRSpace and RationalCharacterDecomposition
*******************************************************************************/

intrinsic RationalCharacterTableRSpace(G::Grp) -> ModTupRng
{The RSpace over Z whose basis is the rational character of G}

    if assigned G`RationalCharacterTableRSpace then
	return G`RationalCharacterTableRSpace;
    end if;

    rats := RationalCharacterTable(G);
    rats_mat := Matrix(Z, #rats[1], [c[i]: i in [1 .. #c], c in rats]);
    S := RSpaceWithBasis(rats_mat);

    G`RationalCharacterTableRSpace := S;
    return S;

end intrinsic;

intrinsic RationalCharacterDecomposition(c::AlgChtrElt) -> []
{The decomposition of the integral character c w.r.t. the rational character
table}

    l, q := CanChangeUniverse(Eltseq(c), Z);
    require l: "Character is not integral";
    
    S := RationalCharacterTableRSpace(Group(Parent(c)));
    return Coordinates(S, Vector(q));

end intrinsic;
