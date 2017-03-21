freeze;

intrinsic InternalIndecomposableSummands(M::ModRng) -> []
{Internal}

    require Type(BaseRing(M)) eq FldFin: "Module not over finite field";

    vprint Decomposition: "Decompose:", M;

    if IsIrreducible(M) then
	vprint Decomposition: "Irreducible";
	return [M];
    end if;

    vprint Decomposition: "Get endomorphism ring";
    vtime Decomposition: E := EndomorphismRing(M);
    vprint Decomposition: E;
    e := Dimension(E);

    best_X := 0;
    best_cost := Infinity();

    vprint Decomposition: "Find best element"; vtime Decomposition:
    for i := 1 to 10 do
	X := Random(E);
	fcp := FactoredCharacteristicPolynomial(X: Proof := false);
	if #fcp gt 1 then
	    cost := &+[(Degree(t[1])*t[2])^2: t in fcp];
	    vprint Decomposition: i, fcp, cost;
	    if cost lt best_cost then
		vprint Decomposition: "NEW BEST";
		best_X := X;
		best_cost := cost;
	    end if;
	elif fcp[1, 2] eq 1 and Degree(fcp[1, 1]) eq e then
	    vprint Decomposition: "Proven indecomposable via random elt";
	    return [M];
	end if;
    end for;

    X := best_X;
    if X cmpne 0 then
	fmp := FactoredMinimalPolynomial(X);
	vprint Decomposition: "fmp:", fmp;

	vprint Decomposition: "Get kernels";
	vtime Decomposition: k := [Kernel(Evaluate(t[1], X)^t[2]): t in fmp];

	vprint Decomposition: "Get submodules";
	vtime Decomposition: S := [sub<M|x>: x in k];
	vprint Decomposition: "Split:", S;

	IndentPush();
	SS := &cat[$$(M): M in S];
	Sort(~SS, func<x, y | Dimension(x) - Dimension(y)>);
	IndentPop();
	return SS;
    end if;

    vprint Decomposition: "Get reg rep";
    vtime Decomposition: rr := RegularRepresentation(Basis(E));

    MM := RModule(rr);
    vprint Decomposition: MM;

    vprint Decomposition: "Get Jacobson radical";
    vtime Decomposition: J := JacobsonRadical(MM);
    vprint Decomposition: J;

    Q := MM/J;
    vprint Decomposition: "Quotient:", Q;

    if IsIrreducible(Q) then
	vprint Decomposition: "Proven indecomposable via Jacobson radical";
	return [M];
    end if;

    vprint Decomposition: "Fail Jacobson radical test";
    return $$(M);

end intrinsic;
