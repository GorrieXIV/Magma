freeze;

/*
Machinery for dealing with invariants over Algebraic Groups.
Allan Steel, Sep 2006, using code of Gregor Kemper.
*/

NEW_MAT := 1 eq 1;
NEW_NF := 1 eq 0;
USE_IR := 1 eq 1;

/*******************************************************************************
                                Attributes
*******************************************************************************/

declare attributes RngInvar:
    GroupIdeal, Representation, GroupType, DerksenIdeal, FundamentalInvariants,
    HilbertIdeal, SymbolicSecondaryInvariants;

/*******************************************************************************
                                Local access
*******************************************************************************/

function IsAG(IR)
    return assigned IR`GroupType and IR`GroupType in {
        "linearly reductive group",
        "reductive group",
        "linear algebraic group"
    };
end function;

/*******************************************************************************
			    Creation
*******************************************************************************/

function GetGroupType(LinearlyReductive, Reductive)
    if LinearlyReductive then
	return "linearly reductive group";
    elif Reductive then
	return "reductive group";
    else
	return "linear algebraic group";
    end if;
end function;

intrinsic InvariantRing(
    IG::RngMPol, A::Mtrx[RngMPol]:
	Reductive := false, LinearlyReductive := false,
	PolynomialRing := 0
) -> RngInvar
{Create the invariant ring for the algebraic group defined by the
ideal IG and representation matrix A};

    PK := BaseRing(A);
    K := BaseRing(PK);
    require IsField(K): "Base ring must be a field";
    require Generic(IG) cmpeq Generic(PK):
	"Polynomial rings of arguments are not compatible";

    if Reductive and Characteristic(IG) eq 0 then
	LinearlyReductive := true;
    end if;

    n := Ncols(A);
    require Nrows(A) eq n:
	"Representation matrix (argument 2) is not square";
    if PolynomialRing cmpeq 0 then 
	R := InvariantRing(Sym(n), K);
    else
	R := InvariantRing(Sym(n), PolynomialRing);
    end if;
    R`OverAG := true;
    R`GroupIdeal := IG;
    R`Representation := A;
    R`GroupType := GetGroupType(LinearlyReductive, Reductive);

    return R;

end intrinsic;

intrinsic InvariantRing(
    IG::RngMPol, A::[[]]:
	Reductive := false, LinearlyReductive := false,
	PolynomialRing := 0
)
    -> RngInvar
{Create the invariant ring for the algebraic group defined by the
ideal IG and representation matrix A given by a sequence};

    return InvariantRing(
	IG, Matrix(A):
	    Reductive := Reductive, LinearlyReductive := LinearlyReductive,
	    PolynomialRing := PolynomialRing
    );
end intrinsic;

intrinsic GroupIdeal(R::RngInvar) -> RngMPol
{The ideal defining the algebraic group of R}
    require IsAG(R): "Invariant ring is not of an algebraic group";
    return R`GroupIdeal;
end intrinsic;

intrinsic GroupType(R::RngInvar) -> RngMPol
{The ideal defining the algebraic group of R}
    if R`OverAG then
	return R`GroupType;
    end if;
    if Type(Group(R)) eq GrpMat then
	return "finite matrix group";
    end if;
    return "permutation group";
end intrinsic;

intrinsic Representation(R::RngInvar) -> Mtrx
{The representation matrix for R}
    require IsAG(R): "Invariant ring is not of an algebraic group";
    return R`Representation;
end intrinsic;

/*******************************************************************************
			    InvariantsOfDegree
*******************************************************************************/

/*
P<t1,t2,t3,t4>:=PolynomialRing(Rationals(),4);
IG:=ideal<P | [t1*t4-t2*t3-1]>; // defining SL_2
A:=Matrix([[t1,t2,0,0],[t3,t4,0,0],[0,0,t1,t2],[0,0,t3,t4]]);
R:=InvariantRing(IG,A);
InvariantsOfDegree(R,2: Algorithm:="Standard");

[
    x1*x4 - x2*x3
]
*/

MB := func<| GetMaximumMemoryUsage()/2^20.0>;

HomogeneousInvariants:=function(IG,A,d: P:=1, subspacebasis := []);
/*
Compute a K-basis of the homogeneous invariants of degree d
IG is the ideal defining a linear algebraic group G, and A is
a list of lists (technically SeqEnum of SeqEnum's) defining the action
according to Convention 1.8 in paper. The entries of A are the rows of
the matrix. The optional argument P can be a polynomial ring in which
the invariants lie.
*/

    printf "HomogeneousInvariants of degree %o\n", d;
    ZEIT := Cputime();

    //n:=#A;
    n:=Ncols(A);
    K:=CoefficientRing(Parent(A[1][1]));
    if Type(P) eq RngIntElt then
        P:=PolynomialRing(K,n);
	AssignNames(~P,["x"*IntegerToString(i): i in [1..n]]);
    end if;
    S:=Generic(IG);
    PS:=PolynomialRing(S,n);
AssignNames(~PS,["y"*IntegerToString(i): i in [1..n]]);

    "emb setup"; time
    emb:=hom<P->PS | [PS.i: i in [1..n]]>;
    "rho setup"; time
    rho:=hom<P->PS | [&+[A[i][j]*PS.j: j in [1..n]]: i in [1..n]]>;

    PP:=PolynomialRing(K,n+Rank(S));
AssignNames(~PP,
    ["z"*IntegerToString(i): i in [1..n]] cat
    ["u"*IntegerToString(i): i in [1..Rank(S)]]
);
    embPP:=hom<S->PP | [PP.(n+i): i in [1..Rank(S)]]>;
    embPP:=hom<PS->PP | embPP,[PP.i: i in [1..n]]>;
    "MB:", MB();

//subspacebasis := [];
"subspacebasis len:", #subspacebasis;
//"subspacebasis:", subspacebasis;
"full mons:", Binomial(n + d - 1, n - 1);
    if subspacebasis ne [] then
	mons := subspacebasis;
    else
	mons:=MonomialsOfDegree(P,d);
	mons:=[t: t in mons];
    end if;
//"mons:", mons;

    /*
    "equ setup"; time
    equ:=[rho(t)-emb(t): t in mons];
    "MB:", MB();
    */

//"equ:", equ;

    monsG:={@@};
    red:=[];

    KR := USE_IR and K cmpeq RationalField() select IntegerRing() else K;
    B := SparseMatrix(KR, 0, #mons);
    embT := 0;
    nfT := 0;
    rhoT := 0;
    matT := 0;

    "rho+NormalForm+emb loop"; time
    for i := 1 to #mons do
	//f := equ[i];

        if i mod 50 eq 1 or i eq #mons then
	    //i, #mons;
            MemProfile();
        end if;

	t := mons[i];
	ZEIT0 := Cputime();
	f:=rho(t) - emb(t);
/*
if subspacebasis ne [] then
    "rho:", rho(t);
    "emb:", emb(t);
    "f:", f;
end if;
*/
	ZEIT1 := Cputime();
	rhoT +:= ZEIT1 - ZEIT0;

        m:=Monomials(f);
	c:=Coefficients(f);
	nc := #c;
	delete f;

	if NEW_NF then
	    NFQ := NormalForm(c, GroebnerBasis(IG));
	else
	    NFQ := [NormalForm(c[j],IG): j in [1..nc]];
	end if;
	delete c;
	nf := &+[PS|NFQ[j]*m[j]: j in [1..nc]];
	delete m;
	ZEIT2 := Cputime();
	nfT +:= ZEIT2 - ZEIT1;

	nf := embPP(nf);
	ZEIT3 := Cputime();
	embT +:= ZEIT3 - ZEIT2;

	if NEW_MAT then
	    M := Monomials(nf);
	    C := Coefficients(nf);
	    if KR ne K then
		lcm := LCM([IntegerRing() | Denominator(x): x in C]);
		C := [
		    KR!Numerator(x)*ExactQuotient(lcm, Denominator(x)): x in C
		];
	    end if;
	    for j := 1 to #M do
		Include(~monsG, M[j]);
		//SetEntry(~B, i, Index(monsG, M[j]), C[j]);
		SetEntry(~B, Index(monsG, M[j]), i, C[j]);
	    end for;
	    delete M, C;
	    matT +:= Cputime(ZEIT3);
	else
	    Append(~red, nf);
	end if;
	delete nf;
    end for;

    "rho time:", rhoT;
    "NormalForm time:", nfT;
    "emb time:", embT;
    "mat setup time:", matT;
    "MB:", MB();

    if NEW_MAT then

//"monsG:", monsG;
	/*
	B := SparseMatrix(K, #red_ind, #monsG);
	printf "mat setup (%o by %o)\n", #red, #monsG; time
	for i := 1 to #red_ind do
	    C := red_C[i];
	    ind := red_ind[i];
	    for j := 1 to #C do
		B[i, ind[j]] := C[j];
	    end for;
	end for;
	*/

	delete monsG;

//Matrix(Transpose(B));
B;
Density(B);
"MB:", MB();
time

	//B:=Basis(Kernel(B));
	//B:=Basis(NullspaceOfTranspose(B));
	NullspaceOfTransposeMatrix(~B, ~NB);
	B := Basis(Rowspace(Matrix(K, NB)));

    else
"red:", red;

	/*
	"red loop"; time
	red:=[embPP(f): f in red];
	"mapped red:", red;
	"MB:", MB();
	*/

"monsG:", monsG;

	"set loop"; time
	for f in red, m in Monomials(f) do Include(~monsG, m); end for;
	"Sort"; time
	monsG:=Reverse(Sort(Setseq(monsG)));
	monsG:={@ t: t in monsG @};
	"MB:", MB();
	//monsG:={@ t: t in monsG @};

	B := SparseMatrix(K, #red, #monsG);
	"mat setup"; time
	for i := 1 to #red do
	    C := Coefficients(red[i]);
	    M := Monomials(red[i]);
	    for j := 1 to #C do
		B[i, Index(monsG, M[j])] := C[j];
	    end for;
	end for;

	delete monsG;

//Matrix(B);
B; Density(B);
"MB:", MB();
time

	B:=Basis(Kernel(B));
    end if;

    L := [Normalize(&+[b[i]*mons[i]: i in [1..#mons]]): b in B];
    "Total HomogeneousInvariants time:", Cputime(ZEIT);
    return L;
end function;

/*
HomogeneousInvariantsBayer:=function(IG,A,d: P:=1, w:=[]);
// Thomas Bayer's algorithm; same purpose and same input as
// HomogeneousInvariants
// Gewichtsvektor w fuer den Torus
    
    A := [Eltseq(A[i]): i in [1 .. Nrows(A)]];
    n:=#A;
    K:=CoefficientRing(Parent(A[1][1]));
    if Type(P) eq RngIntElt then
        P:=PolynomialRing(K,n);
	AssignNames(~P,["x"*IntegerToString(i): i in [1..n]]);
    end if;
    S:=Parent(A[1][1]);
    m:=Rank(S);

    // Hier wurden einst nur die Grade der Leitterme berucksichtigt
    degs:=[TotalDegree(f): f in &cat[Terms(A[i][j]): i,j in [1..n]]];
    delta:=Max(degs);

    // Homogenize A
    if {e in {-1,delta}: e in degs} ne {true} then
        Ss:=PolynomialRing(K,m+1);
	emb:=hom<S->Ss | [Ss.i: i in [1..m]]>;

	Ah:=[[&+([Ss.(m+1)^(delta-TotalDegree(t))*emb(t): t in Terms(a)] cat [0]): a in l]: l in A];
        // Hier wurde falsch homogenisiert: 0 anhangen, damit nicht leer

	IGh:=ideal<Ss | [emb(f): f in Basis(IG)] cat [Ss.(m+1) - 1]>;
	S:=Ss;
	m +:= 1;
    else
        Ah:=A;
	IGh:=IG;
    end if;
    delta +:= 1; // The degree of the psi's
    IGh:=Homogenization(IGh,false);
    // the homogenizing variable ("X") comes last
    Ss:=Parent(IGh.1);
    emb:=hom<S->Ss | [Ss.i: i in [1..m]]>;
    Ah:=[[emb(a): a in l]: l in Ah];
    m +:= 1;
    S:=Ss;
    PS:=PolynomialRing(K,n+m);
    PS:=PolynomialRing(K,n+m, "elim", m - 1);
    embS:=hom<S->PS | [PS.i: i in [1..m]]>;
    embP:=hom<P->PS | [PS.(m+i): i in [1..n]]>;
    psi:=hom<P->PS | [&+[embS(Ah[i][j])*embP(P.j): j in [1..n]]: i in [1..n]]>;

    if (w cmpeq []) then
     mons:=MonomialsOfDegree(P,d);
    else   
     //mons:=TorusInvariantsSL2(w,d,P);
     mons:=MonomialsOfDegree(P,d);
    end if;

    I:=ideal<PS | [psi(t): t in mons]> +
        ideal<PS | [embS(f): f in Basis(IGh)]>;
    // time
    G:=GroebnerBasis(Basis(I),d*delta: ReduceFinal := false);
    J:=[f: f in G |
      {Exponents(LeadingMonomial(f))[i] eq 0: i in [1..m-1]} eq {true}];
    B:=[f: f in J | TotalDegree(f) eq d*delta];
    spec:=hom<PS->P | [1: i in [1..m]] cat [P.i: i in [1..n]]>;
    return [Normalize(spec(b)): b in B];
end function;
*/

/*
intrinsic InternalInvariantsOfDegree(R::RngInvar, d::RngIntElt) -> []
{Internal}
    IG := R`GroupIdeal;
    A := R`Representation;
    return HomogeneousInvariants(IG, A, d: P := PolynomialRing(R));
end intrinsic;
*/

intrinsic InvariantsOfDegree(
    R::RngInvar, d::RngIntElt:
    Invariants := "Both",
    /* Algorithm:="Standard", */
    subspacebasis := []
) -> []
{A K-basis of the invariants of R of degree d};

    if not R`OverAG then
	return InternalInvariantsOfDegree(R, d: Invariants := Invariants);
    end if;

    IG := R`GroupIdeal;
    A := R`Representation;
    /*
    if Algorithm cmpeq "Bayer" and subspacebasis eq [] then
	return HomogeneousInvariantsBayer(IG, A, d: P := PolynomialRing(R));
    */
    if 1 eq 1 then
	return InternalInvariantsOfDegreeAG(
	    IG, A, d, PolynomialRing(R): SubspaceBasis := subspacebasis
	);
    elif subspacebasis eq [] then
	return InternalInvariantsOfDegreeAG(IG, A, d, PolynomialRing(R));
    else
	return HomogeneousInvariants(
	    IG, A, d: P := PolynomialRing(R), subspacebasis := subspacebasis
	);
    end if;
end intrinsic;

/*******************************************************************************
				Derksen Ideal
*******************************************************************************/

intrinsic OldDerksenIdeal(R::RngInvar) -> RngMPol
{}
/*
The Derksen ideal D of the invariant ring R. This is an ideal in
P[y_1 ... y_n], where P = K[x_1 ... x_n] is the ambient polynomial ring
of R, and the y_i are new indeterminates.
By definition, D is the intersection of all ideals
<y_1 - g(x_1) ... y_n - g(x_n)> with g in G, the group of R.
Geometrically, D is the vanishing ideal of the subset
{(x,g(x)) | x in K^n, g in G} of the cartesian product K^n x K^n.
The function returns a sequence of generators of the Derksen ideal.
*/

    P:=PolynomialRing(R);
    n:=Rank(P);
    K:=CoefficientRing(P);
    Py:=PolynomialRing(P,n);
    AssignNames(~Py,["y"*IntegerToString(i): i in [1..n]]);
    if GroupType(R) in {"finite matrix group","permutation group"} then
        Kxy:=PolynomialRing(K,2*n);
        emb:=hom<P->Kxy | [Kxy.i: i in [1..n]]>;
        D:=&meet[ideal<Kxy | [emb(P.i^g) - Kxy.(n+i): i in [1..n]]>:
            g in Group(R)];
        // the above will be time-critical
        phi:=hom<Kxy->Py | [P.i: i in [1..n]] cat [Py.i: i in [1..n]]>;
        return [phi(f): f in Basis(D)];
    end if;

    // The case of a linear algebraic group
    A:=Representation(R);
    Kt:=Parent(A[1][1]);
    m:=Rank(Kt);

    if 0 eq 1 then
	Kxyt:=PolynomialRing(K,m + 2*n, "elim", m);
	emb:=hom<Kt->Kxyt | [Kxyt.i: i in [1..m]]>;
	B := 
	    [emb(f): f in Basis(GroupIdeal(R))] cat
	    [
		&+[emb(A[i,j])*Kxyt.(m + j): j in [1..n]] - Kxyt.(m+n+i):
		    i in [1..n]
	    ];
	I:=Ideal(B);
	"Elim input I:", B;
	"Elim num vars:", 2*n;
	time G := GroebnerBasis(I: Al := "Direct");
	//time G := F5(Sort(Basis(I)));

	"Groebner Basis:", #G;

	phi:=hom<Kxyt->Py |
	    [Py!0: i in [1..m]] cat [P.i: i in [1..n]] cat [Py.i: i in [1..n]]
	>;

	BD := [
	    f: f in G |
		forall{
		    i: i in [1..m] |
		    Degree(l, i) eq 0 where l := LeadingMonomial(f)
		}
	];

	"BD:", #BD;
    else
	Kxyt:=PolynomialRing(K,2*n+m);
	emb:=hom<Kt->Kxyt | [Kxyt.i: i in [2*n+1..2*n+m]]>;
	I:=ideal<Kxyt | [emb(f): f in Basis(GroupIdeal(R))] cat
	    [&+[emb(A[i,j])*Kxyt.j: j in [1..n]] - Kxyt.(n+i): i in [1..n]]>;
	AssignNames(~Kxyt,["x"*IntegerToString(i): i in [1..Rank(Kxyt)]]);
	"Elim input I:", I;
	"2*n:", 2*n;
	D:=EliminationIdeal(I,{Kxyt.i: i in [1..2*n]});
	"Elim output D:", D;
	BD := Basis(D);

	// the above will be very time-critical
	phi:=hom<Kxyt->Py | [P.i: i in [1..n]] cat [Py.i: i in [1..n]]
	    cat [Py!0: i in [1..m]]>;
    end if;
    return [phi(f): f in BD];
end intrinsic;


/* Need not be made available to the user, since there's DerksenIdeal below. */
DerksenIdealRing:=function(R: verb:=GetVerbose("Invariants"))
/*
The Derksen ideal D of the invariant ring R. This is an ideal in
P[y_1 ... y_n], where P = K[x_1 ... x_n] is the ambient polynomial ring
of R, and the y_i are new indeterminates.
By definition, D is the intersection of all ideals
<y_1 - g(x_1) ... y_n - g(x_n)> with g in G, the group of R.
Geometrically, D is the vanishing ideal of the subset
{(x,g(x)) | x in K^n, g in G} of the cartesian product K^n x K^n.
The function returns a sequence of generators of the Derksen ideal.
*/

    if assigned R`DerksenIdeal then return R`DerksenIdeal; end if;
    if verb ge 1 then "Compute the Derksen ideal"; end if;
    P:=PolynomialRing(R);
    n:=Rank(P);
    K:=CoefficientRing(P);
    Py:=PolynomialRing(P,n);
    AssignNames(~Py,["y"*IntegerToString(i): i in [1..n]]);
    if GroupType(R) in {"finite matrix group","permutation group"} then
        Kxy:=PolynomialRing(K,2*n);
        emb:=hom<P->Kxy | [Kxy.i: i in [1..n]]>;
	if verb ge 2 then
	    "Compute intersection ideal";
	    time
	    D:=&meet[ideal<Kxy | [emb(P.i^g) - Kxy.(n+i): i in [1..n]]>:
                g in Group(R)];
	    // the above will be time-critical
	else
	    D:=&meet[ideal<Kxy | [emb(P.i^g) - Kxy.(n+i): i in [1..n]]>:
                g in Group(R)];
	    // the above will be time-critical
	end if;
        phi:=hom<Kxy->Py | [P.i: i in [1..n]] cat [Py.i: i in [1..n]]>;
	res:=[phi(f): f in Basis(D)];
	delete D;
	R`DerksenIdeal:=res;
        return res;
    end if;

    // The case of a linear algebraic group
    A:=Representation(R);
    Kt:=Parent(A[1][1]);
    m:=Rank(Kt);
//MG    Kxyt:=PolynomialRing(K,2*n+m);
Kxyt:=PolynomialRing(K,2*n+m,"elim",[2*n+1..2*n+m]);
    emb:=hom<Kt->Kxyt | [Kxyt.i: i in [2*n+1..2*n+m]]>;
    I:=ideal<Kxyt | [emb(f): f in Basis(GroupIdeal(R))] cat
        [&+[emb(A[i,j])*Kxyt.j: j in [1..n]] - Kxyt.(n+i): i in [1..n]]>;
    if verb ge 2 then
        "Computing elimination ideal";
Groebner(I:Al:="Direct");
	time D:=EliminationIdeal(I,{Kxyt.i: i in [1..2*n]});
        // the above will be very time-critical
    else
Groebner(I:Al:="Direct");
	D:=EliminationIdeal(I,{Kxyt.i: i in [1..2*n]});
        // the above will be very time-critical
    end if;
    delete I;
    phi:=hom<Kxyt->Py | [P.i: i in [1..n]] cat [Py.i: i in [1..n]]
        cat [Py!0: i in [1..m]]>;
    res:=[Normalize(phi(f)): f in Basis(D)];
    delete D;
    R`DerksenIdeal:=res;
    return res;
end function;

/*
DerksenIdeal:=function(R: verb:=GetVerbose("Invariants"))

    if Type(R) eq RngInvar then
        return DerksenIdealRing(R: verb:=verb);
    elif Type(R) eq FldInvar then
        return DerksenIdealField(R: verb:=verb);
    else
        error "Runtime error in 'DerksenIdeal': wrong argument type";
    end if;
end function;
*/

/*******************************************************************************
			    Hilbert Ideal
*******************************************************************************/

/* This should be made available to the user */
intrinsic HilbertIdeal(
    R::RngInvar: Minimize:=true, Force:=false, verb:=GetVerbose("Invariants")
) -> RngMPol
{The Hilbert ideal of an invariant ring R (where the group acts linearly)}

/*
The Hilbert ideal of an invariant ring R (where the group acts linearly).
This is the ideal in the polynomial ring generated by all non-constant,
homogeneous invariants. Output is a sequence of homogeneous generators (not
necessarily invariant). If Minimize is true, the generators will be minimal.
Force = true will force the application of Derksen's algorithm even though the
group may not be linearly reductive.
*/

    if assigned R`HilbertIdeal then return R`HilbertIdeal; end if;
    P:=PolynomialRing(R);
    n:=Rank(P);
    if GroupType(R) eq "linearly reductive group" then lr:=true;
    elif GroupType(R) in {"finite matrix group","permutation group"} then
        lr:=Characteristic(PolynomialRing(R)) eq 0 or
	    not IsDivisibleBy(#Group(R),Characteristic(PolynomialRing(R)));
    else lr:=Force;
    end if;
    if not lr or assigned R`FundamentalInvariants then
        // for non-linearly-reductive groups calculation "a posteriori"
	gen:=FundamentalInvariants(R);
    else
        D:=DerksenIdealRing(R: verb:=verb);
	if #D eq 0 then
	    R`HilbertIdeal:=[];
	    return [];
	end if;
	Py:=Parent(D[1]);
	spec:=hom<Py->P | [P!0: i in [1..n]]>;
	gen:=[spec(f): f in D];
	delete D;
	gen:=[f: f in gen | f ne 0];
	if false in {IsHomogeneous(f): f in gen} then
	    error
	    "Something went wrong with the homogeneity of the Derksen ideal";
	    /* The Derksen ideal should always have homogeneous generators,
	       since it is part of a Groebner basis of an ideal I generated by
	       polynomials which are homogeneous if the t-variables are
	       assigned degree zero */
	end if;
    end if;
    if Minimize and gen ne [] then
        /*
	Sort(~gen,func<x,y | TotalDegree(x)-TotalDegree(y)>);
	L:=[gen[1]];
	for d:=1 to TotalDegree(gen[#gen]) do
	    B:=[f: f in gen | TotalDegree(f) eq d];
	    ind:=HomogeneousModuleTestBasis([P.i: i in [1..n]],L,B);
	    L:=L cat [B[i]: i in ind];
	end for;
	gen:=L;
	*/
	if verb ge 1 then "Minimize the Hilbert ideal"; end if;
	if verb ge 2 then time gen:=MinimalBasis(ideal<P | gen>);
	else gen:=MinimalBasis(ideal<P | gen>);
	end if;
    end if;
    gen := [Normalize(f): f in gen];
    R`HilbertIdeal:=gen;
    return gen;
end intrinsic;

/*******************************************************************************
			    Derksen Algorithm
*******************************************************************************/

function is_lr(R, force: AllowFinite := false)
    if GroupType(R) eq "linearly reductive group" then lr:=true;
    elif GroupType(R) in {"finite matrix group","permutation group"} then
        lr := AllowFinite or
	    Characteristic(PolynomialRing(R)) eq 0 or
	    not IsDivisibleBy(#Group(R),Characteristic(PolynomialRing(R)));
    else
	lr:=force;    
    end if;
    return lr;
end function;

/*
The next function should be called from FundamentalInvariants(R), but
ONLY IF GroupType(R) eq "linearly reductive group". It would be useful
to also make DerksenAlgorithm() accessible to the user, since he might
in rare occasions wish to apply Derksen's algorithm to finite groups.
*/
DerksenAlgorithm:=function(R: optimize:=true,minimize:=true,
    minimizeHilbert:=true,force:=false,verb:=GetVerbose("Invariants"))
/*
Use Derksen's algorithm to compute a set of generators of the invariant ring
of a linear algebraic group acting linearly. If minimize = true, the generating
set will be minimal. If minimizeHilbert, the basis of the Hilbert ideal will
also be minimized. If optimize is true, optimize the computation of homogeneous
invariants. force = true will force the application of Derksen's algorithm
even though the group may no be linearly reductive.
*/

    if not is_lr(R, force) then
        error "Runtime error in 'DerksenAlgorithm': Derksen's algorithm only applies to linearly reductive groups";
    end if;

    P:=PolynomialRing(R);
    H:=HilbertIdeal(R: Minimize:=minimizeHilbert,Force:=force,verb:=verb);
    degs:={TotalDegree(f): f in H};
    degs:=[d: d in degs];
    Sort(~degs);
    L:=[];
    if verb ge 1 then
        max:=Max([0] cat degs);
	"Compute homogeneous invariants of maximal degree",max;
    end if;
    if verb ge 2 then ZEIT:=Cputime(); end if;
    for d in degs do
        if not optimize then
	    inv:=InvariantsOfDegree(R,d);
	else
	    basis:=&cat[[t*f: t in MonomialsOfDegree(P,d-TotalDegree(f))]:
	        f in H | TotalDegree(f) le d];
	    ind:=HomogeneousModuleTestBasis([P.1^(d+1)],[P!1],basis);
	    basis:=[basis[i]: i in ind];
	    // a basis of the degree-d part of the Hilbert ideal
	    inv:=InvariantsOfDegree(R,d: subspacebasis:=basis);
	    // call extension of InvariantsOfDegree
	end if;
	if minimize and L ne [] then
	    if verb ge 2 then
	        "Minimize number of invariants of degree",d;
	    end if;
	    ind:=HomogeneousModuleTestBasis(L,[P!1],inv);
	    inv:=[inv[i]: i in ind];
	end if;
	L:=L cat inv;
    end for;
    delete H;
    if verb ge 2 then
        "Time for computing homogeneous invariants:",Cputime(ZEIT);
    end if;
    R`FundamentalInvariants:=L;
    return L;
end function;

/*
The next function should be called from FundamentalInvariants(R), but
ONLY IF GroupType(R) eq "linearly reductive group". It would be useful
to also make DerksenAlgorithm() accessible to the user, since he might
in rare occasions wish to apply Derksen's algorithm to finite groups.
*/

/*******************************************************************************
			    Fundamental Invariants
*******************************************************************************/

intrinsic FundamentalInvariants(
    R::RngInvar:
    Al := "King", MaxDegree := 0,
    Optimize := true, Minimize := true,
    MinimizeHilbert := true, Force := false
) -> []
{Fundamental invariants of the invariant ring R}

    require is_lr(R, Force: AllowFinite):
	"Computing fundamental invariants (via Derksen's algorithm) is only possible for linearly reductive groups";

    if assigned R`FundamentalInvariants then
	return R`FundamentalInvariants;
    end if;

    if not R`OverAG then
	require Type(Al) eq MonStgElt and Al in {"King", "MinPrimSec"}:
	    "Al must be \"King\" or \"MinPrimSec\"";
	if Al cmpeq "MinPrimSec" or IsModular(R) then
	    return InternalFundamentalInvariantsMinPrimSec(R);
	end if;
	require Type(MaxDegree) eq RngIntElt and MaxDegree ge 0:
	    "MaxDegree must be a non-negative integer";
	F := FundamentalInvariantsKing(R: MaxDegree := MaxDegree);
    else
	F := DerksenAlgorithm(
	    R: optimize := Optimize, minimize := Minimize,
	    minimizeHilbert := MinimizeHilbert, force := Force
	);
    end if;
    R`FundamentalInvariants := F;
    return R`FundamentalInvariants;
end intrinsic;

intrinsic DerksenIdeal(R::RngInvar) -> RngMPol
{The Derksen ideal of R}

    if not assigned R`DerksenIdeal then
	R`DerksenIdeal := DerksenIdealRing(R);
    end if;
    return R`DerksenIdeal;
end intrinsic;

/*******************************************************************************
			    Membership
*******************************************************************************/

/*
Membership in an invariant ring of an algebraic group. To be run by 'f in R'
*/
MemberInvRingAlgGroup:=function(R,f)

    P:=PolynomialRing(R);
    n:=Rank(P);
    IG:=GroupIdeal(R);
    A:=Representation(R);
    J:=EasyIdeal(IG);
    PJ:=Generic(J);
    PS:=PolynomialRing(PJ,n);
    emb:=hom<P->PS | [PS.i: i in [1..n]]>;
    rho:=hom<P->PS | [&+[PJ!(A[i][j])*PS.j: j in [1..n]]: i in [1..n]]>;
    d:=rho(f)-emb(f);
    coeffs:=Coefficients(d);
    delete d;
    coeffs:=NormalForm(coeffs,J);
    res:=&and[c eq 0: c in coeffs];
    delete coeffs;
    return res;
end function;

intrinsic 'in'(f::RngMPolElt, R::RngInvar) -> BoolElt
{Whether f is in R}
    if IsAG(R) then
	return MemberInvRingAlgGroup(R, f);
    else
	return InternalIn(f, R);
    end if;
end intrinsic;
