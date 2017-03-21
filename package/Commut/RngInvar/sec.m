freeze;

function HomogeneousParts(f)
    return [h: h in HomogeneousComponents(f) | not IsZero(h)];
end function;

function xMinimalExtensionBasis(prim, S, L)

    D := [];
    for f in L do
	d := WeightedDegree(f) + 1;
	if not IsDefined(D, d) then
	    D[d] := [];
	end if;
	Append(~D[d], f);
    end for;
    E := [Universe(prim)|];
    for T in D do
	if #T gt 0 then
	    B := HomogeneousModuleTestBasis(prim, S, T);
	    E cat:= [T[i]: i in B];
	    S cat:= E;
	    vprintf Invariants, 2: "Degree %o: keep %o from %o\n",
		WeightedDegree(T[1]), #B, #T;
	end if;
    end for;
    return E;
end function;

function Minimalize(prim, L)
    D := [];
    for f in L do
	d := TotalDegree(f) + 1;
	if not IsDefined(D, d) then
	    D[d] := [];
	end if;
	Append(~D[d], f);
    end for;
    S := [Universe(prim)|];
    for T in D do
	if #T gt 0 then
	    B := HomogeneousModuleTestBasis(prim, S, T);
	    S cat:= [T[i]: i in B];
	    vprintf Invariants, 2: "Degree %o: keep %o from %o\n",
		TotalDegree(T[1]), #B, #T;
	end if;
    end for;
    return S;
end function;

intrinsic SecondaryInvariants(R::RngInvar, H::Grp) -> []
{Secondary invariants for invariant ring R using subgroup H}

    I := R;
    R := PolynomialRing(I);
    K := BaseRing(R);
    G := Group(I);

    require IsModular(I): "Argument 1 must be modular";
    require Type(G) cmpeq Type(H) and Generic(G) cmpeq Generic(H) and
	H subset G: "Argument 2 must be a subgroup of the group of argument 1";

    if assigned I`SecondaryInvariants then
	return I`SecondaryInvariants;
    end if;

    prim := PrimaryInvariants(I);

    vprint Invariants: "\nMODULAR SECONDARY INVARIANTS";
    vprintf Invariants: "Group size: %o\n", #G;
    vprintf Invariants: "Subgroup size: %o\n", #H;
    vprintf Invariants: "Primary degrees: %o\n", [TotalDegree(f): f in prim];
    T := Cputime();

    vprint Invariants: "Compute quotient monomials";

    if false then
	PI := PrimaryIdeal(I);
	P := Generic(PI);
	M := P / PI;
    else
	P:=PolynomialRing(CoefficientRing(R),Rank(R),"grevlex");
	phi:=hom<R->P | [P.i: i in [1..Rank(R)]]>;
	M:=quo<P | ideal<P | [phi(f): f in prim]>>;
    end if;

    //print "M:",M;
    V,phi:=VectorSpace(M);
    sec:=[P!(g@@phi): g in Basis(V)];
    phi:=hom<P->R | [R.i: i in [1..Rank(P)]]>;
    basis:=[phi(f): f in sec];

    vprintf Invariants: "Number of quotient monomials: %o\n", #basis;

    if #H eq 1 then
	vprint Invariants: "Use quotient monomials for basis";
	sec := basis;
	gens := [g: g in Generators(G)];

	secS := [];
    else
	vprint Invariants: "Compute secondaries for subgroup";

	HI := InvariantRing(H, R);
	if IsModular(HI) then
	    HI`PrimaryInvariants := prim;
	    sec := SecondaryInvariants(HI);
	else
	    sec := SecondaryInvariants(HI, I);
	end if;
	h:=hom<Universe(sec)->R | [R.i: i in [1..Rank(R)]]>;
	sec := [h(f): f in sec];
	gens := [g: g in Generators(G) | g notin H];

	secS := [[r[i]: i in [1..#sec]]: r in Relations(Module(HI))];

	vprint Invariants: "";
    end if;

    vprint Invariants, 1: "Secondary S:", secS;

    vprint Invariants, 3: "Secondary invariants:", sec;
    vprint Invariants, 3: "Over group generators:", gens;

    vprintf Invariants: "Number of secondaries: %o\n", #sec;
    vprintf Invariants: "Number of over group generators: %o\n", #gens;

    TT := Cputime();

    P:=PrimaryAlgebra(I);
    deg := Sort(Setseq({TotalDegree(f): f in sec}));

    vprint Invariants: "Set up phi";
    vprint Invariants: "Degrees:", deg;

    phi:=[z: f in sec] where z is [P|0: i in [1 .. #basis * #gens]];
    phid:=[TotalDegree(f): f in sec];
    h:=hom<R->P | [P.i: i in [1..#prim]]>;
    for d in deg do
	secd := [i: i in [1 .. #sec] | TotalDegree(sec[i]) eq d];
	vprintf Invariants, 2: "Degree %o (%o)\n", d, #secd;
	secg := [sec[s]^g-sec[s]: g in gens, s in secd];
	secgnz := [i: i in [1 .. #secg] | not IsZero(secg[i])];
	//vprint Invariants: "secg:", secg;
	//vprint Invariants: "secgnz:", secgnz;
	vtime Invariants, 2:
	    b,rep0 := HomogeneousModuleTest(prim,basis, [secg[i]: i in secgnz]);
	//vprint Invariants: "b:",b;
	rep := [z: i in [1..#secg]] where z is [R!0: i in [1..#basis]];
	for i := 1 to #secgnz do
	    rep[secgnz[i]] := rep0[i];
	end for;
	//vprint Invariants: "rep:", rep;

	for i := 1 to #secd do
	    phi[secd[i]] := &cat[
		[h(f): f in rep[#gens * (i - 1) + j]]:
		    j in [1 .. #gens]
	    ];
	end for;
    end for;

    //vprint Invariants: "phi:", phi;
    //vprint Invariants: "#phi:", #phi;
    //vprint Invariants: "phi len:", [#q: q in phi];

    vprint Invariants: "Construct module";
    basisd := [TotalDegree(f): f in basis];
    M:=Module(P, &cat[basisd: i in [1..#gens]]);
    vtime Invariants: M:=sub<M | [M!f: f in phi]>;
    vprint Invariants: "Module basis length:",#Basis(M);
//print "first M:", M;

    vprint Invariants: "Calculate the syzygy module";
    vtime Invariants:
	M:=SyzygyModule(M);

    /*
    Recreate M with correct weights for columns because if the first
    M had zero rows, they will give zero weights in the corresponding
    columns of the syzygy M which is wrong.
    */

//"syz M:", M;

//Universe(Basis(M));
    M := sub<Module(P, phid) | Basis(M)>;
    //M := sub<Module(P, phid) | [Eltseq(x): x in Basis(M)]>;
    vprint Invariants: "Initial syzygy basis length:", #Basis(M);

    //print "next M:", M;
    //print "secS:", secS;

    vprint Invariants: "Minimalize syzygies";
    vtime Invariants:
	if #secS gt 0
	then
	    B := Basis(M);
	    M := Module(P, [TotalDegree(f): f in sec]);
	    B := [M | Eltseq(f): f in B];
	    //vprint Invariants: "fixed M", M;
	    //vprint Invariants: "fixed B", B;
	    //vprint Invariants: "secS:", secS;
	    /*
	    B := MinimalExtensionBasis(
		[P.i: i in [1 .. Rank(P)]], ChangeUniverse(secS, M), Basis(M)
	    );
	    */
	    B := MinimalExtensionBasis(ChangeUniverse(secS, M), B);
	    M := sub<M | B>;
	else
	    B := MinimalBasis(M);
	end if;
    vprint Invariants: "Minimalized syzygy basis length:", #B;

    //print "next B:", B;

    h:=hom<P->R | prim>;
    n := #sec;

    vprint Invariants: "Calculate the corresponding secondaries";
    vtime Invariants: if false then
	C := {@ @};
	E := [];
	sec0 := [];
	for b in B do
	    f := 0;
	    for i in [1..n] do
		g := b[i];
		j := Index(C, g);
		if j eq 0 then
		    Include(~C, g);
		    e := h(g);
		    Append(~E, e);
		else
		    e := E[j];
		end if;
		f := f + e*sec[i];
	    end for;
	    Append(~sec0, f);
	end for;
    else
	sec0:=[&+[h(b[i])*sec[i]: i in [1..#sec]]: b in B];
    end if;

    vprint Invariants: "Get homogeneous parts";
    vtime Invariants: sec0:=&cat[HomogeneousParts(g): g in sec0];
    Sort(~sec0,func<x,y | TotalDegree(x)-TotalDegree(y)>);
    sec:=[R!1];

    if false then
	vprint Invariants: "Extract a minimal set of secondaries from",#sec0,
	    "current secondaries";

	vtime Invariants:
	    sec := Minimalize(prim, sec0);
    else
	sec := sec0;
    end if;

    for i := 1 to #sec do
	f := sec[i];
	s := LeadingCoefficient(f)^-1;
	sec[i] := s * f;
	B[i] := s * B[i];
    end for;

    InternalSetMinimalBasis(M, B);

    vprint Invariants: "Final secondaries of degrees",
			[TotalDegree(f): f in sec];
    vprint Invariants: "Secondary construction time:", Cputime(TT);
    vprint Invariants: "Total time:", Cputime(T);

    // SecondarySubmodule must be set first (otherwise assigning
    // SecondaryInvariants will compute it).
    I`SecondarySubmodule := M;
    I`SecondaryInvariants := sec;

    return sec;
end intrinsic;

intrinsic SecondaryInvariants(R::RngInvar) -> []
{Secondary invariants for invariant ring R}
    I := R;

    if assigned I`SecondaryInvariants then
	return I`SecondaryInvariants;
    end if;

    if not IsModular(I) then
	if 1 eq 1 then
	    L, E := SecondaryInvariantsNonModular(I);

	    P := PrimaryInvariants(R);
	    IS := R`IrreducibleSecondaryInvariants;
	    EU := Universe(E);

	    if Type(EU) eq RngMPol then
		B := BaseRing(EU);
	    else
		B := EU;
	    end if;

	    ER := PolynomialRing(
		B,
		[TotalDegree(f): f in P] cat
		[TotalDegree(f): f in IS]
	    );
	    AssignNames(
		~ER,
		[Sprintf("f%o", i): i in [1 .. #P]] cat
		[Sprintf("h%o", i): i in [1 .. #IS]]
	    );
/*
"IS:", IS;
"P:", P;
"E:", E;
*/
	    if #IS eq 0 then
		assert #E eq 1;
		E := [ER | 1];
	    else
		h := hom<EU -> ER | [ER.(#P + i): i in [1 .. #IS]]>;
		E := [h(f): f in E];
	    end if;
	    R`SecondaryInvariantsExpressions := E;

	    return L;
	else
	    return InternalSecondaryInvariantsNonModular(I);
	end if;
    end if;

    p := Characteristic(BaseRing(I));
    G := Group(I);
    F := FactoredOrder(G);
    P := [t: t in F | t[1] ne p];
    if #P gt 0 then
	// Non-p-group case
	m, i := Max([t[1]^t[2]: t in P]);
	q := P[i][1];
	S := SylowSubgroup(G, q);
	// Try to find elements whose order is greater than #S
	for i := 1 to 10 do
	    g := Random(G);
	    o := Order(g);
	    q := 1;
	    while o mod p eq 0 do
		o div:= p;
		q *:= p;
	    end while;
	    if o gt #S then
		S := sub<G | g^q>;
		assert #S eq o;
	    end if;
	end for;
    else
	// p-group case
	if true then
	    // Always use trivial subgroup now
	    S := sub<G|>;
	else
	    if #G eq p then
		S := sub<G|>;
	    else
		S := sub<G | g^(Order(g) div p)> where g is G.1;
	    end if;
	end if;
    end if;
    return SecondaryInvariants(I, S);
end intrinsic;

intrinsic InternalFixSecondarySubmodule(I::RngInvar)
{Internal}
    local R,H,P,prim,secG,secH,sec0,phi,phig,h,g,s,f,M,V,i,j;
    
    vtime Invariants: prim:=PrimaryInvariants(I);
    vprint Invariants: "Primaries have degrees",[TotalDegree(f): f in prim];
    vtime Invariants: secG := SecondaryInvariants(I);
    vprint Invariants: "Secondaries of G have degrees",[TotalDegree(f): f in secG];
    // secG are the secondary invariants of K[V]^G
 
    R:=PolynomialRing(I);
    P:=PolynomialRing(CoefficientRing(R),Rank(R),"grevlex");
    phi:=hom<R->P | [P.i: i in [1..Rank(R)]]>;
    M:=quo<P | ideal<P | [phi(f): f in prim]>>;
    V,phi:=VectorSpace(M);
    secH:=[P!(g@@phi): g in Basis(V)]; // h_1..h_r
    phi:=hom<P->R | [R.i: i in [1..Rank(P)]]>;
    secH:=[phi(f): f in secH];
    P:=PolynomialRing(CoefficientRing(I),[TotalDegree(f): f in prim]);
    vprint Invariants: "Secondaries of H have degrees",[TotalDegree(f): f in secH];
    p :=[];
    for i in [1..#secG] do
    b, p[i] :=  HomogeneousModuleTest(prim,secH,secG[i]);
    end for;
    
    for i in [1..#secG] do
      h:=hom<Parent(p[i][1])->P | [P.i: i in [1..#prim]]>;
      p[i] := [h(f): f in p[i]];
    end for;
    P:=PrimaryAlgebra(I);
    M:=Module(P,[TotalDegree(f): f in secH]);
    M:=sub<M | [M!f: f in p]>;
 
//    S:=SyzygyModule(M);
 
    I`SecondarySubmodule := M;
    //return M;
end intrinsic;
