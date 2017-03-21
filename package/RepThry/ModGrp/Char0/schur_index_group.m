freeze;

grp := function(n, q)
    a := Integers()!(PrimitiveElement(GF(q)) ^ ((q-1) div n));
    assert Modorder(a, q) eq n;
    f := Factorization(n);
    if n eq 1 then ngens := 1; else
	ngens := 2 * &+[t[2]:t in f] + 1;
    end if;
    F := FreeGroup(ngens);
    rels := [];
    gen := 0;
    for t in f do
	for i := 1 to t[2] do
	    gen +:= 1;
	    Append(~rels, F.gen^t[1] = F.(gen+1));
	end for;
    end for;
    for t in f do
	for i := 1 to t[2] do
	    gen +:= 1;
	    if gen lt ngens - 1 then
		Append(~rels, F.gen^t[1] = F.(gen+1));
	    else
		Append(~rels, F.gen^t[1] = F.0);
	    end if;
	end for;
    end for;
    Append(~rels, F.ngens^q = F.0);
    gen := 0;
    for t in f do
	for i := 1 to t[2] do
	    gen +:= 1;
	    Append(~rels, F.ngens^F.gen = F.ngens^a);
	    a := Modexp(a, t[1], q);
	end for;
    end for;
    G := quo<F|rels:Class := "PolycyclicGroup">;
    return G;
end function;

chtr_with_schur := function(n, q)
    G := grp(n, q);
    N := Sylow(G, q);
    C := Centralizer(G, N);
    nq := n*q;
    // assert #C eq nq;
    // assert IsCyclic(C);
    c := &* AbelianBasis(C);
    // assert Order(c) eq #C;
    cm := ClassMap(C);
    z := RootOfUnity(nq, CyclotomicField(nq:Sparse:=true));
    lambda := [Parent(z)|];
    zi := Parent(z)!1;
    ci := C!1;
    for i := 1 to nq do
	zi := zi*z;
	ci := ci*c;
	lambda[cm(ci)] := zi;
    end for;
    lambda := CharacterRing(C)!lambda;
    AssertAttribute(lambda, "IsCharacter", true);
    chi := Induction(lambda, G);
    // assert Norm(chi) eq 1;
    // fl, x := HasAttribute(chi, "IsCharacter");
    // assert fl and x;
    // AssertAttribute(chi, "IsCharacter", true);
    AssertAttribute(chi, "IsIrreducible", true);
    return chi, G;
end function;

intrinsic SchurIndexGroup(n::RngIntElt:Prime := 0) -> GrpPC
{A group having an irreducible character with Schur index n}

    require n ge 1: "n must be positive";

    if Prime cmpeq 0 then
	p := 1;
	k := 0;
	repeat
	    p +:= n;
	    k +:= 1;
	until GCD(n,k) eq 1 and IsPrime(p);
    else
	p := Prime;
    end if;
    G := grp(n, p);
    return G;

end intrinsic;

intrinsic CharacterWithSchurIndex(n::RngIntElt:Prime := 0) -> AlgChtrElt, GrpPC
{A character with Schur index n}

    require n ge 1: "n must be positive";

    if Prime cmpeq 0 then
	p := 1;
	k := 0;
	repeat
	    p +:= n;
	    k +:= 1;
	until GCD(n,k) eq 1 and IsPrime(p);
    else
	p := Prime;
    end if;
    x, G := chtr_with_schur(n, p);
    return x, G;

end intrinsic;

