freeze;

intrinsic BrauerCharacterTable(G::GrpPC, p::RngIntElt) -> SeqEnum, Mtrx, SeqEnum
{The Brauer character table of G modulo the prime p}
    T := CharacterTable(G);
    if #G mod p ne 0 then
	return T, IdentityMatrix(Integers(), #T), T;
    end if;
    for i := 1 to #T-1 do
	assert Degree(T[i]) le Degree(T[i+1]);
    end for;
    Z := Integers();
    L := Z!Degree(T[#T]);
    e := Exponent(G);
    _, e := Valuation(e, p);
    if e ge L then q := e+1;
    elif L mod e eq 0 then q := L+1;
    else q := ((L div e) + 1)*e + 1;
    end if;
    while not IsPrime(q) do q +:= e; end while;
    K := GF(q);
    zeta := PrimitiveElement(K);
    B := [CharacterRing(G)|];
    BK := ZeroMatrix(K, #T, #T);
    D := [];
    for i := 1 to #T do
	x := BrauerCharacter(T[i], p);
	xK := CharacterToModular(x, zeta);
	fl, sol := IsConsistent(BK, xK);
	if fl then
	    Append(~D, Eltseq(ChangeRing(sol, Z))[1..#B]);
	else
	    Append(~D, [0:j in [1..#B]] cat [1]);
	    Append(~B, x);
	    BK[#B] := xK;
	end if;
    end for;
    for i := 1 to #D do
	if #D[i] lt #B then
	    D[i] := D[i] cat [0:j in [1..#B-#D[i]]];
	else
	    assert  #D[i] eq #B ;
	end if;
    end for;
    D := Matrix(D);
    P := [CharacterRing(G)|];
    for i := 1 to Ncols(D) do
	pim := CharacterRing(G)!0;
	for j := 1 to Nrows(D) do
	    a := D[j, i];
	    if a ne 0 then pim := pim + a*T[j]; end if;
	end for;
	Append(~P, pim);
    end for;
    return B, D, P;
end intrinsic;
