freeze;

function RamRep(L)
    if Type(L) eq RngLocA then
	L, m := RamifiedRepresentation(L);
    else
	m := Coercion(L, L);
    end if;
    return L, m;
end function;

function CoeffRingRamRep(L)
    C := CoefficientRing(L);
    return RamRep(C);
end function;

intrinsic Degree(L::RngLocA, C::Rng) -> RngIntElt
{The degree of L as an extension of C};

    if L cmpeq C then
	return 1;
    end if;

    if CoefficientRing(L) cmpeq C then
	return Degree(L);
    end if;

    deg := 1;
    while L cmpne C and L cmpne PrimeRing(L) do
	deg *:= Degree(L);
	L := CoefficientRing(L);
    end while;

    require L cmpeq C : "Argument 2 is not a coefficient ring of argument 1";
    return deg;
end intrinsic;

intrinsic Discriminant(L::RngLocA) -> RngElt
{Discriminant of the local ring L};
    return Discriminant(RamifiedRepresentation(L), CoeffRingRamRep(L));
end intrinsic;

forward auto_group;

intrinsic AutomorphismGroup(L::RngLocA) -> Grp, Map, PowMapAut
{The automorphism group of the local ring L};
    succ, G, mL, A := auto_group(L, true);
    require succ : "Insufficient precision for automorphism computations";
    return G, mL, A;
end intrinsic;

function auto_group(L, check)
    R, rr_m := RamifiedRepresentation(L);
    G, m := AutomorphismGroup(R, ChangePrecision(CoeffRingRamRep(L), Precision(R) div RamificationDegree(L)));
    // Inverse (of mL) does not work for localas so do not create it
    mL := map< G -> PowerStructure(Map) | g :-> hom<L -> L | (rr_m*m(g)*Inverse(rr_m))(L.1)>>;
    mL := map<G -> PowerStructure(Map) | g :-> rr_m*m(g)*Inverse(rr_m)>;
    if check then
	for i in [1 .. Minimum(#G, 5)] do
	//for g in G do
	    g := Random(G);
	    if Valuation((mL(g))(L.1)) ne Valuation(L.1) then
		return false, G, mL, Aut(L);
	    end if;
	    if Valuation((mL(g))(InertialElement(L))) ne 0 then
		return false, G, mL, Aut(L);
	    end if;
	    if Valuation((mL(g))(UniformizingElement(L))) ne 1 then
		return false, G, mL, Aut(L);
	    end if;
	end for;
    end if;
    return true, G, mL, Aut(L);
end function;

intrinsic IsRamified(L::RngLocA) -> BoolElt
{Whether L is a ramified extension of its coefficient ring};
    return RamificationDegree(L) gt 1;
end intrinsic;

intrinsic IsTotallyRamified(L::RngLocA) -> BoolElt
{Whether L is a totally ramified extension of its coefficient ring};
    return RamificationDegree(L) eq Degree(L);
end intrinsic;

intrinsic IsUnramified(L::RngLocA) -> BoolElt
{Whether L is an unramified extension of its coefficient ring};
    return RamificationDegree(L) eq 1;
end intrinsic;

intrinsic IsTamelyRamified(L::RngLocA) -> BoolElt
{Whether L is a tamely ramified extension of its coefficient ring};
    return not IsWildlyRamified(L);
end intrinsic;

intrinsic IsWildlyRamified(L::RngLocA) -> BoolElt
{Whether L is a wildly ramified extension of its coefficient ring};
    return RamificationDegree(L) mod Prime(L) eq 0;
end intrinsic;

intrinsic Prime(L::RngLocA) -> RngIntElt
{The prime of the coefficient ring of L};
    return Prime(RamifiedRepresentation(L));
end intrinsic;

intrinsic ResidueClassField(L::RngLocA) -> Rng, Map
{The residue class field of the local ring L};

    R, rr_m := RamifiedRepresentation(L);
    rf, rf_m := ResidueClassField(Integers(R));

    return rf, rr_m*rf_m;
end intrinsic;

intrinsic FrobeniusAutomorphism(L::RngLocA) -> Map
{Return the lift of the Frobeius automorphism on the residue class field of L};

    require IsUnramified(L) : "Argument 1 must be an unramified extension";

    RR, m := RamifiedRepresentation(L);
    
    return hom<L -> L | GaloisImage(m(L.1), 1) @@ m>;
end intrinsic;

function ramification_grp(L, i)

    //succ, A, m := auto_group(L, true);
    R, rr_m := RamifiedRepresentation(L);
    irr_m := Inverse(rr_m);
    A, m := AutomorphismGroup(R, ChangePrecision(CoeffRingRamRep(L), Precision(R) div RamificationDegree(L)));

    ram_auts := [];
    Z := [InertialElement(L), UniformizingElement(L)];
    for a in A do
	zz := [(rr_m*m(a)*irr_m)(z) : z in Z];
	assert &and[Valuation(zz[j]) eq Valuation(Z[j]) : j in [1 .. #Z]];
	v := [Valuation(zz[j] - Z[j]) : j in [1 .. #Z]];
	assert &and[vj ge 0 : vj in v];
	if &and[v[j] ge i + 1 : j in [1 .. #v]] then
	    Append(~ram_auts, a);
	end if;
    end for;
    S := sub<A | ram_auts>;
    return true, S;
end function;

intrinsic RamificationGroup(L::RngLocA, i::RngIntElt) -> GrpPerm
{The ith ramification group of L, for i > -1}
    require i ge -1 : "Argument 2 must be at least -1";

    succ, S := ramification_grp(L, i);
    require succ : "Insufficient precision for automorphism computations";
    return S;
end intrinsic;

intrinsic InertiaGroup(L::RngLocA) -> GrpPerm
{The inertia group of L}
    succ, S := ramification_grp(L, 0);
    require succ : "Insufficient precision for automorphism computations";
    return S;
end intrinsic;

intrinsic DecompositionGroup(L::RngLocA) -> GrpPerm
{The decomposition group of L}
    succ, S := ramification_grp(L, -1);
    require succ : "Insufficient precision for automorphism computations";
    return S;
end intrinsic;

intrinsic FixedField(L::RngLocA, S::GrpPerm) -> RngLocA
{The field fixed by all automorphisms in the subgroup S of the automorphism
group of L}
    succ, A, m := auto_group(L, true);

    require succ : "Insufficient precision for automorphism computations";

    require #A eq Degree(L) : "Argument 1 must be normal";
    require S subset A : "Argument 2 must be a subgroup of argument 1";

    if S eq A then
	return CoefficientRing(L);
    end if;

    if #S eq 1 then
	return L;
    end if;

    i := RelativeInvariant(A, S);
    pe := L.1;

    // Roots of defining polynomial of L
    rt := [pe@(g@m) where _, g := IsConjugate(A, 1, i) : i in [1 .. #A]];

    t := Polynomial([0, 1]);
    all_t := {t};
    repeat
	// Roots which are not fixed outside of S : only fixed by S
	r := {Evaluate(i, [Evaluate(t, x) : x in PermuteSequence(rt, u)]) : u in Transversal(A, S)};
	repeat
	    t := Polynomial([Random(2) : x in all_t] cat [1]);
	until t notin all_t;
	Include(~all_t, t);
	r_diffs := [RelativePrecision(rseq[k] - rseq[j]) : k in [j + 1 .. #r], j in [1 .. #r]] where rseq is Setseq(r);
    until #r eq #A/#S and #[rd : rd in r_diffs| rd gt 0 ] eq #r_diffs;
    assert #r eq #A/#S;
    assert &and[RelativePrecision(m(g)(x) - x) lt Precision(L)/5 : g in S, x in r];
    f := &*[Polynomial([-s, 1]) : s in r];
    f := [Eltseq(c) : c in Coefficients(f)];
    
    assert &and[&and[RelativePrecision(cc) le Precision(L)/5 or Valuation(cc) eq Infinity(): cc in c[2 .. #c]] : c in f];
    f := Polynomial(BaseRing(L), [c[1] : c in f]);

    prec := 0;
    while not exists(x){x : x in r | sub<A | [g : g in A | RelativePrecision(x@(g@m) - x) le prec]> eq S} do
	prec +:= 1;
	assert prec lt Precision(L)/5;
    end while;
    assert prec lt Precision(L)/5;

    F := LocalField(BaseRing(L), f);
    assert Degree(F) eq #A/#S;
    return F, hom<F -> L | x>;
end intrinsic;

intrinsic Factorization(f::RngUPolElt[RngLocA] : Certificates := false, IsSquarefree := false, Ideals := false) -> SeqEnum, RngElt, Any
{Factorization of the polynomial f into monic irreducible factors and a scalar. 
Also returns certificates as requested};

    L := CoefficientRing(f);
    R, m := RamifiedRepresentation(L);
    ff := Polynomial([m(c) : c in Coefficients(f)]);

    FF, s, CC := Factorization(ff : Certificates := Certificates, IsSquarefree := IsSquarefree, Ideals := Ideals);

    F := [];
    for ff in FF do 
	Append(~F, <Polynomial([c @@ m : c in Coefficients(ff[1])]), ff[2]>);
    end for;

    if Certificates or Ideals then
	C := [rec<Format(CC[1]) | 
    		F := Crec`F, 
		Rho := Polynomial([c @@ m : c in Coefficients(Crec`Rho)]), 
		E := Crec`E, 
		Pi := Polynomial([c @@ m : c in Coefficients(Crec`Pi)])> :
		Crec in CC];
	if Ideals then
	    for i in [1 .. #C] do 
		C[i]`IdealGen1 := Polynomial([c @@ m : c in Coefficients(CC[i]`IdealGen1)]);
		C[i]`IdealGen2 := Polynomial([c @@ m : c in Coefficients(CC[i]`IdealGen2)]); 
	    end for;
	end if;
	return F, s @@ m, C;
    else
	return F, s @@ m, _;
    end if;
end intrinsic;

intrinsic SuggestedPrecision(f::RngUPolElt[RngLocA])->RngIntElt
{}
    L := CoefficientRing(f);
    R, m := RamifiedRepresentation(L);
    ff := Polynomial([m(c) : c in Coefficients(f)]);

    return SuggestedPrecision(ff);
end intrinsic;

intrinsic MinimalPolynomial(x::RngLocAElt) -> RngUPolElt
{The minimal polynomial of x};

    L := Parent(x);
    return MinimalPolynomial(x, BaseRing(L));
    R, m := RamifiedRepresentation(L);
    C, cm := RamRep(BaseRing(L));
    f := MinimalPolynomial(m(x), C);

    return Polynomial([c @@ cm : c in Coefficients(f)]);

end intrinsic;

intrinsic Norm(x::RngLocAElt, F::Rng) -> RngElt
{The Norm of x over the coefficient ring F of the parent of x};
    L := Parent(x);
    R, m := RamifiedRepresentation(L);

    while L cmpne F and L cmpne PrimeRing(L) do
	L := CoefficientRing(L);
    end while;
    require L cmpeq F : "Argument 2 is not a coefficient ring of argument 1";

    return Norm(m(x), RamRep(F));
end intrinsic;

intrinsic Trace(x::RngLocAElt, F::Rng) -> RngElt
{The Trace of x over the coefficient ring F of the parent of x};
    L := Parent(x);
    R, m := RamifiedRepresentation(L);

    while L cmpne F and L cmpne PrimeRing(L) do
	L := CoefficientRing(L);
    end while;
    require L cmpeq F : "Argument 2 is not a coefficient ring of argument 1";

    return Trace(m(x), RamRep(F));
end intrinsic;

intrinsic MinimalPolynomial(x::RngLocAElt, F::Rng) -> RngUPolElt
{The minimal polynomial of x over the coefficient ring F of the parent of x};
    L := Parent(x);
    R, m := RamifiedRepresentation(L);

    while L cmpne F and L cmpne PrimeRing(L) do
	L := CoefficientRing(L);
    end while;
    require L cmpeq F : "Argument 2 is not a coefficient ring of argument 1";

    C, cm := RamRep(F);
    f := MinimalPolynomial(m(x), C);

    return Polynomial([c @@ cm : c in Coefficients(f)]);
end intrinsic;
