freeze;

intrinsic RandomIrreduciblePolynomial(K::FldFin, n::RngIntElt) -> RngUPolElt
{A random irreducible polynomial of degree n over the field K.}

    requirege n, 1;

    f := IrreduciblePolynomial(K, n);
    L := ext<K | f: Default := false>;
    repeat
	a := Random(L);
	g := MinimalPolynomial(a);
    until Degree(g) eq n;
    return g;

end intrinsic;

intrinsic RandomExtension(K::FldFin, n::RngIntElt) -> RngUPolElt
{An extension of K by a random irreducible polynomial of degree n}

    requirege n, 1;

    return ext<K | RandomIrreduciblePolynomial(K, n): Check := false>;

end intrinsic;
