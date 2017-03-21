freeze;

/*
Invariant Fields.
Allan Steel, Sep 2006, using code of Gregor Kemper.
*/

/*******************************************************************************
				Attributes
*******************************************************************************/

declare type FldInvar;

declare attributes FldInvar:
    CoefficientRing, FunctionField, GroupType, Group, GroupIdeal,
    Representation, DerksenIdeal, FundamentalInvariants;

import "ag.m": GetGroupType;

/*******************************************************************************
				Local access
*******************************************************************************/

function IsAG(IF)
    return IF`GroupType in {
	"linearly reductive group",
	"reductive group",
	"linear algebraic group"
    };
end function;

/*******************************************************************************
				Print/Coerce/in
*******************************************************************************/

forward MemberOfInvariantField;
                    
intrinsic Print(IF::FldInvar, s::MonStgElt)
{}
    printf "Invariant field ";
    if IsAG(IF) then
	printf "of algebraic group";
	printf "\nField of definition: %o", IF`CoefficientRing;
    else
	printf "of finite group";
	printf "\nCoefficient ring: %o", IF`CoefficientRing;
    end if;
end intrinsic;

intrinsic IsCoercible(IF::FldInvar, x::.) -> BoolElt, .
{}
    l, y := IsCoercible(IF`FunctionField, x);
    if l and MemberOfInvariantField(IF, y) then
	return l, y;
    else
	return false, "Illegal coercion";
    end if;
end intrinsic;

intrinsic 'in'(x::., IF::FldInvar) -> BoolElt
{}
    l := IsCoercible(IF, x);
    return l;
end intrinsic;

/*******************************************************************************
				Base Creation
*******************************************************************************/

function FldInvarCreate(:
    K := 0, F := 0,
    Group := 0, GroupType := 0,
    GroupIdeal := 0, Representation := 0
)
/*
At least one of: 
    [K: base ring (CoefficientRing);]
    F: function field
*/

    if K cmpeq 0 then
	K := BaseRing(F);
    end if;

    IF := New(FldInvar);

    IF`CoefficientRing := K;
    IF`FunctionField := F;

    IF`Group := Group;
    IF`GroupType := GroupType;
    IF`GroupIdeal := GroupIdeal;
    IF`Representation := Representation;

    return IF;
end function;

function CreateFuncField(FF, K, n)
    if FF cmpne 0 then
	if Type(FF) ne FldFunRat or BaseRing(FF) cmpne K or Rank(FF) ne n then
	    return 0;
	end if;
	F := FF;
    else
	F := FunctionField(K, n);
	AssignNames(~F, [Sprintf("x%o", i): i in [1 .. n]]);
    end if;
    return F;
end function;

/*******************************************************************************
		    External Creation (finite group)
*******************************************************************************/

intrinsic InvariantField(G::GrpPerm, K::Fld: FunctionField := 0) -> FldInvar
{Create the invariant field for the group G over the field K}
    F := CreateFuncField(FunctionField, K, Degree(G));
    require F cmpne 0: "Value for FunctionField is not valid";

    return FldInvarCreate(:
	K := K, F := F,
	Group := G, GroupType := "permutation group"
    );
end intrinsic;

intrinsic InvariantField(G::GrpMat: FunctionField := 0) -> FldInvar
{Create the invariant field for the group G over the field K}
    K := BaseRing(G);
    require IsField(K): "Base ring must be a field";

    F := CreateFuncField(FunctionField, K, Degree(G));
    require F cmpne 0: "Value for FunctionField is not valid";

    return FldInvarCreate(:
	K := K, F := F,
	Group := G, GroupType := "finite matrix group"
    );
end intrinsic;

/*******************************************************************************
		    External Creation (algebraic group)
*******************************************************************************/

intrinsic InvariantField(
    IG::RngMPol, A::Mtrx[RngMPol]:
        Reductive := false, LinearlyReductive := false, FunctionField := 0
) -> FldInvar
{Create the invariant field for the algebraic group defined by the
ideal IG and representation matrix A}

    PK := BaseRing(A);
    K := BaseRing(PK);
    require IsField(K): "Base ring must be a field";

    F := CreateFuncField(FunctionField, K, Ncols(A));
    require F cmpne 0: "Value for FunctionField is not valid";

    if Reductive and Characteristic(IG) eq 0 then
        LinearlyReductive := true;
    end if;

    GroupType := GetGroupType(LinearlyReductive, Reductive);

    return FldInvarCreate(:
    	F := F,
	GroupType := GroupType, GroupIdeal := IG, Representation := A
    );
end intrinsic;

intrinsic InvariantField(
    IG::RngMPol, A::[[]]:
        Reductive := false, LinearlyReductive := false, FunctionField := 0
) -> FldInvar
{Create the invariant field for the algebraic group defined by the
ideal IG and representation matrix A}

    return InvariantField(
	IG, Matrix(A):
	    Reductive := Reductive, LinearlyReductive := LinearlyReductive
    );
end intrinsic;

/*******************************************************************************
				Access
*******************************************************************************/

intrinsic FunctionField(IF::FldInvar) -> FldFunRat
{The ambient rational function field of IF}
    return IF`FunctionField;
end intrinsic;

intrinsic GroupType(IF::FldInvar) -> MonStgElt
{The group type of IF}
    return IF`GroupType;
end intrinsic;

intrinsic Group(IF::FldInvar) -> Grp
{The group of IF}
    require not IsAG(IF): "Invariant field must be of a finite group";
    return IF`Group;
end intrinsic;

intrinsic GroupIdeal(IF::FldInvar) -> RngMPol
{The group of IF}
    require IsAG(IF): "Invariant field must be of an algebraic group";
    return IF`GroupIdeal;
end intrinsic;

intrinsic Representation(IF::FldInvar) -> RngMPol
{The representation of IF}
    require IsAG(IF): "Invariant field must be of an algebraic group";
    return IF`Representation;
end intrinsic;

/*******************************************************************************
		    Internal invariants algorithms
*******************************************************************************/

function FixEasyIdeal(D)
    if not HasGrevlexOrder(D) then
        // error "Runtime error in 'DerksenIdealField': The easy ideal of the elimination ideal was assumed to be grevlex, but it's not!";

	return ChangeOrder(D, "grevlex");
    end if;
    return D;
end function;

/* Need not be made available to the user, since there's the more general
function DerksenIdeal below. */
DerksenIdealField:=function(FI: verb:=GetVerbose("Invariants"))
/*
The Derksen ideal D of the invariant field FI. This is an ideal in
F[y_1 ... y_n], where F = K(x_1 ... x_n) is the ambient rational function
field of FI, and the y_i are new indeterminates.
By definition, D is the intersection of all ideals
<y_1 - g(x_1) ... y_n - g(x_n)> with g in G, the group of R.
The function returns D as an ideal with a Groebner basis.
*/

    if assigned FI`DerksenIdeal then return FI`DerksenIdeal; end if;
    F:=FunctionField(FI);
    n:=Rank(F);
    Fy:=PolynomialRing(F,n,"grevlex");
    AssignNames(~Fy,["y"*IntegerToString(i): i in [1..n]]);
    if GroupType(FI) in {"finite matrix group","permutation group"} then
	if verb ge 2 then
	    "Compute intersection ideal";
	    time
	    D:=&meet[ideal<Fy | [Numerator(F.i)^g - Fy.i: i in [1..n]]>:
                g in Group(FI)];
	    // the above will be time-critical
	else
	    D:=&meet[ideal<Fy | [Numerator(F.i)^g - Fy.i: i in [1..n]]>:
                g in Group(FI)];
	    // the above will be time-critical
	end if;
	D:=EasyIdeal(D);
        FI`DerksenIdeal:=D;
	return D;
    end if;

    IG:=GroupIdeal(FI);
    A:=Representation(FI);
    Kt:=Parent(A[1,1]);
    m:=Rank(Kt);
    K:=CoefficientRing(Kt);
    Fyt:=PolynomialRing(F,n+m);
    emb:=hom<Kt->Fyt | [Fyt.i: i in [n+1..n+m]]>;
    AssignNames(~Fyt,
	["a"*IntegerToString(i): i in [1..n]] cat
	["b"*IntegerToString(i): i in [1..m]]
    );
    I:=ideal<Fyt | [emb(f): f in Basis(IG)] cat
        [&+[emb(A[i,j])*F.j: j in [1..n]] - Fyt.i: i in [1..n]]>;
//I, {Fyt.i: i in [1..n]};
    if verb ge 2 then
        "Compute elimination ideal";
        time D:=EliminationIdeal(I,{Fyt.i: i in [1..n]});
    else D:=EliminationIdeal(I,{Fyt.i: i in [1..n]});
    end if;
    delete I;
    D:=EasyIdeal(D);
    D := FixEasyIdeal(D);
    Fyt:=Generic(D);
    phi:=hom<Fyt->Fy | [Fy.i: i in [1..n]] cat [Fy!0: i in [1..m]]>;
    D:=ideal<Fy | [phi(f): f in GroebnerBasis(D)]>;
    MarkGroebner(D);
    FI`DerksenIdeal:=D;
    return D;
end function;

/* This should be made available to the user */
QuadeIdealInner:=function(L: Fy:=1,JustI:=false,verb:=GetVerbose("Invariants"))
/*
L is a non-empty set or sequence of non-constant elements from a rational
function field F = k(x1..xn), generating a subfield K = k(L). The
Quade ideal, introduced in J. Müller-Quade, R. Steinwandt, Basic
Algorithms for Rational Function Fields, J. Symbolic Computation
(1999) 27, 143-170, is the ideal in F[y1..yn] generated by the kernel
of the map K[y1..yn] -> F, yi |-> xi. This function returns the Quade
ideal with a Groebner basis. If set, Fy should be a polynomial ring of
rank n over F. If JustI is true, return an ideal in a larger
polynomial ring whose intersection with F[y1..yn] is the Quade ideal.
*/

    if #L eq 0 then
        error "Runtime error in 'QuadeIdeal': Cannot have an empty set or sequence as argument";
    end if;
    F:=Parent(Random(L));
    /*
    if false in {f in F: f in L} then
        error "Runtime error in 'QuadeIdeal': Wrong argument types. Probably some constants in the argument";
    end if;
    */
    P:=Integers(F);
    n:=Rank(F);
    Fyz:=PolynomialRing(F,n+1);
    pre:=hom<P -> Fyz | [Fyz.i: i in [1..n]]>;
    h:=LCM([Denominator(f): f in L]);
    // This could consume some time, too.
    I:=ideal<Fyz | [Fyz.(n+1)*pre(h)-1] cat
        [f*pre(Denominator(f))-pre(Numerator(f)): f in L]>;
    if JustI then return I; end if;
    if verb ge 2 then
        "Computing the elmination ideal for the Quade ideal";
	time J:=EliminationIdeal(I,{Fyz.i: i in [1..n]});
    else
        J:=EliminationIdeal(I,{Fyz.i: i in [1..n]});
        /*
        another method would be to compute J as the saturation
        <[f*pre(Denominator(f))-pre(Numerator(f)): f in L]>:<pre(h)>^infty.
        */
    end if;
    delete I;
    J := EasyIdeal(J);
    J := FixEasyIdeal(J);
    PJ:=Generic(J);
    if Fy cmpeq 1 then
        Fy:=PolynomialRing(F,n,"grevlex");
	AssignNames(~Fy,["y"*IntegerToString(i): i in [1..n]]);
    end if;
    phi:=hom<PJ->Fy | [Fy.i: i in [1..n]] cat [Fy!0]>;
    J:=ideal<Fy | [phi(f): f in GroebnerBasis(J)]>;
    MarkGroebner(J);
    return J;
end function;

function non_constants(L)
    return forall{f: f in L | not IsConstant(f)};
end function;

/* This would be useful to make available to the user. It's got complicated
arguments, unfortunately, so I'm not sure. */
MemberSubRationalField:=function(f:
    L:=1,J:=1,verb:=GetVerbose("Invariants"))
/*
f is a rational function or a sequence of rational functions. One of
the optional argument L or J must be set. If set, L should be a
non-empty set or sequence of non-constant rational functions, lying in
the same field, F, as f, defining a subfield K of F. Alternatively, J
should be the Quade ideal of K, or the ideal returned by QuadeIdeal()
with the option 'JustI'. The function tests whether f lies in K. If f
is a sequence, a sequence of boolen values will be returned.
*/

    if J cmpeq 1 then
        if L cmpeq 1 then
	    error "Runtime error in 'MemberSubRationalField': L or J must be set";
	end if;
	J:=QuadeIdealInner(L: JustI,verb:=verb);
    end if;
    J:=EasyIdeal(J);
    Fy:=Generic(J);
    F:=CoefficientRing(Fy);
    n:=Rank(F);
    P:=Integers(F);
    pre:=hom<P -> Fy | [Fy.i: i in [1..n]]>;
    if Type(f) eq SeqEnum then
        fs:=f;
    else
        fs:=[f];
    end if;
    d:=[pre(Numerator(g)): g in fs] cat [pre(Denominator(g)): g in fs];
    // d:=[NormalForm(g,J): g in d];
    d:=NormalForm(d,J);
    res:=[d[i] eq Fy!(fs[i])*d[#fs+i]: i in [1..#fs]];
    delete d;
    if Type(f) ne SeqEnum then res:=res[1]; end if;
    return res;
end function;

/*
Membership in an invariant field. To be run by 'f in FI'
*/
MemberOfInvariantField:=function(FI,f: DontUseDerksenIdeal:=false)

    g:=Numerator(f);
    h:=Denominator(f);
    if GroupType(FI) in {"permutation group","finite matrix group"} then
        for s in Generators(Group(FI)) do
	    if h*g^s ne g*h^s then return false; end if;
	end for;
	return true;
    elif assigned FI`DerksenIdeal and not DontUseDerksenIdeal then
        return MemberSubRationalField(f: J:=DerksenIdeal(FI));
	/* As shown in my paper on computing invariant fields, the Derksen
	ideal coincides with the Quade ideal. */
    end if;
    
    P:=Integers(FunctionField(FI));
    n:=Rank(P);
    IG:=GroupIdeal(FI);
    A:=Representation(FI);
    J:=EasyIdeal(IG);
    PJ:=Generic(J);
    PS:=PolynomialRing(PJ,n);
    emb:=hom<P->PS | [PS.i: i in [1..n]]>;
    rho:=hom<P->PS | [&+[PJ!(A[i][j])*PS.j: j in [1..n]]: i in [1..n]]>;
    d:=emb(h)*rho(g)-emb(g)*rho(h);
    coeffs:=Coefficients(d);
    coeffs:=NormalForm(coeffs,J);
    return &and[c eq 0: c in coeffs];
end function;

/* This should be made available to the user */
MinimizeFieldGenerators:=function(L:
    BottomUpTo:=0,mingens:=0,verb:=GetVerbose("Invariants"));
/*
L is a set or sequence of non-constant elements of a rational function
field. This function selects a minimal (in the sense of 'irredundant')
subset of L which generates the same subfield as L. The function
returns a sequence. If mingens is set, the function stops when a
generating set with so many elements is reached. When BottomUpTo is
set, the function first tries to eliminate generators by testing if
they lie in the subfield generaed by a small number of elements from
L. This small number is limited by BottomUpTo.
*/

    if verb ge 2 then
	"Start minimization with",#L,"elements";
    end if;
    if #L eq 0 then return []; end if;
    S:={f: f in L};
    if Type(L) eq SeqEnum then Ll:=L; else Ll:=SetToSequence(S); end if;
    
    // Start by trying to eliminate generators bottom up
    for s:=1 to BottomUpTo do
        if #S eq s or #S le mingens then
	    S:=Sort(SetToSequence(S),
	        func<f,g | TotalDegree(f)-TotalDegree(g)>);
	    return S;
	end if;
	sets:=Subsets(S,s);
	sets:=Sort(SetToSequence(sets),func<A,B |
	    &+[TotalDegree(f): f in A] - &+[TotalDegree(f): f in B]>);
	for U in sets do
	    if not U subset S then continue U; end if;
	    J:=QuadeIdealInner(U: JustI);
	    cand:=Sort(SetToSequence(S diff U),
	        func<f,g | TotalDegree(g) - TotalDegree(f)>);
	    if verb ge 2 then
	        "Test if generators numbered",[Position(Ll,g): g in cand],
		" lie in the subfield of generators numbered",
	        {Position(Ll,g): g in U};
		time rid:=MemberSubRationalField(cand: J:=J,verb:=verb);
	    else
	        rid:=MemberSubRationalField(cand: J:=J,verb:=verb);
	    end if;
	    delete J;
	    rid:=[cand[i]: i in [1..#cand] | rid[i]];
	    if #rid eq 0 then continue U; end if;
	    S:=S diff SequenceToSet(rid);
	    if verb ge 2 then
	        "Eliminated generators numbered",[Position(Ll,f): f in rid],
		"Left with generators numbered ",{Position(Ll,g): g in S};
	    end if;
	    if #S eq s or #S le mingens then
		S:=Sort(SetToSequence(S),
		    func<f,g | TotalDegree(f)-TotalDegree(g)>);
		return S;
	    end if;
	end for;
	if #S eq s+1 or #S le mingens then
	    S:=Sort(SetToSequence(S),
	        func<f,g | TotalDegree(f)-TotalDegree(g)>);
	    return S;
	end if;
    end for;
    
    // Now go top down
    cand:=Sort(SetToSequence(S),func<f,g | TotalDegree(g) - TotalDegree(f)>);
    for f in cand do
	if #S eq BottomUpTo+1 then
	    S:=Sort(SetToSequence(S),
		func<f,g | TotalDegree(f)-TotalDegree(g)>);
	    return S;
	end if;
	if verb ge 2 then
	    "Test if generator numbered",Position(Ll,f),"can be eliminated";
	    time b:=MemberSubRationalField(f: L:=S diff {f},verb:=verb);
	else
	    b:=MemberSubRationalField(f: L:=S diff {f},verb:=verb);
	end if;
	if b then
	    Exclude(~S,f);
	    if verb ge 2 then
	        "Eliminated generator numbered",Position(Ll,f),
		    ", left with those numbered",{Position(Ll,g): g in S};
	    end if;
	    if #S le mingens then
	        S:=Sort(SetToSequence(S),
	            func<f,g | TotalDegree(f)-TotalDegree(g)>);
	        return S;
	    end if;
	end if;
    end for;
    S:=Sort(SetToSequence(S),func<f,g | TotalDegree(f)-TotalDegree(g)>);
    S := [Normalize(f): f in S];
    return S;
end function;

/*
This should be run by FundamentalInvariants(R) in case Type(R) eq
FldInvar.
Should also be a function accessible by the user by itself.
*/
MuellerQuadeBeth:=function(FI: 
    nominimize:=false,BottomUpTo:=0,mingens:=0,verb:=GetVerbose("Invariants"))
/*
Run the algorithm by Mueller-Quade and Beth for computing the
invariant field of a linear algebraic or finite group. The
function will return minimal (in the sense of 'non-redundant')
generators as a sequence. 'nominimize' turns off
minimization. 'BottomUpTo' and 'mingens' are passed to
'MinimizeFieldGenerators'.
*/

    if assigned FI`FundamentalInvariants then
        return FI`FundamentalInvariants;
    end if;
    if verb ge 1 then
        "Compute the Derksen ideal";
	time D:=DerksenIdealField(FI: verb:=verb);
    else 
        D:=DerksenIdealField(FI: verb:=verb);
    end if;
    L:=&cat[Coefficients(f): f in GroebnerBasis(D)];
    delete D;
    L:={f: f in L | not f in CoefficientRing(FunctionField(FI))};
    if not nominimize then
        if verb ge 1 then
	    "Minimize generators of the invariant field. Initially have",
	    #L,"generators.";
	    time L:=MinimizeFieldGenerators(L:
	        BottomUpTo:=BottomUpTo,mingens:=mingens);
	else
	    L:=MinimizeFieldGenerators(L:
	        BottomUpTo:=BottomUpTo,mingens:=mingens);
	end if;
    else
	L:=Sort(SetToSequence(L),func<f,g | TotalDegree(f) - TotalDegree(g)>);
    end if;

    L := [Normalize(f): f in L];
    FI`FundamentalInvariants:=L;
    return L;
end function;

/*
This should be made available for the user but NOT run by
FundamentalInvariants, since it seems to be considerably slower than
MuellerQuadeBeth.
ONLY for finite groups.
*/

FleischmannKemperWoodcock:=function(FI: 
    nominimize:=false,BottomUpTo:=0,mingens:=0,verb:=GetVerbose("Invariants"))
/*
Run the algorithm by Fleischmann, Kemper and Woodcock for computing
the invariant field of a finite group. The function will return
minimal (in the sense of 'non-redundant') generators as a
sequence. 'nominimize' turs off minimization. 'BottomUpTo' and
'mingens' are passed to 'MinimizeFieldGenerators'.
*/

    if assigned FI`FundamentalInvariants then
        return FI`FundamentalInvariants;
    end if;
    if verb gt 0 then
	"Use FleischmannKemperWoodcock";
    end if;
    F:=FunctionField(FI);
    n:=Rank(F);
    G:=Group(FI);
    FTu:=PolynomialRing(F,2);
    AssignNames(~FTu,["T","u"]);
    if verb ge 1 then
        "Compute product of polynomials";
	time f:=&*[&+[Numerator(F.i)^g*FTu.2^(i-1): i in [1..n]] - FTu.1:
	    g in G];
	"Compute orbit polynomials";
	time L:=[&*[FTu.1-h: h in Orbit(G,Numerator(F.i))]: i in [1..n]];
    else 
        f:=&*[&+[Numerator(F.i)^g*FTu.2^(i-1): i in [1..n]] - FTu.1:g in G];
	L:=[&*[FTu.1-h: h in Orbit(G,Numerator(F.i))]: i in [1..n]];
    end if;
    L:=Coefficients(f) cat &cat[Coefficients(h): h in L];
    delete f;
    L:={f: f in L | not f in CoefficientRing(FunctionField(FI))};
    if not nominimize then
        if verb ge 1 then
	    "Minimize generators of the invariant field. Initially have",
	    #L,"generators.";
	    time L:=MinimizeFieldGenerators(L:
	        BottomUpTo:=BottomUpTo,mingens:=mingens);
	else
	    L:=MinimizeFieldGenerators(L:
	        BottomUpTo:=BottomUpTo,mingens:=mingens);
	end if;
    else
        L:=Sort(SetToSequence(L),func<f,g | TotalDegree(f) - TotalDegree(g)>);
    end if;
    L := [Normalize(f): f in L];
    FI`FundamentalInvariants:=L;
    return L;
end function;

/*******************************************************************************
		    External invariant field functions
*******************************************************************************/

intrinsic DerksenIdeal(IF::FldInvar) -> RngMPol
{The Derksen ideal of the invariant field IF.}

    if not assigned IF`DerksenIdeal then
	IF`DerksenIdeal := DerksenIdealField(IF);
    end if;
    return IF`DerksenIdeal;
end intrinsic;

//////

intrinsic FundamentalInvariants(
    IF::FldInvar: Minimize := true, Min:=0, BottomUpTo:=0,
    Al := "BethMuellerQuade"
) -> []
{Fundamental invariants of the invariant field IF.}

    if not assigned IF`FundamentalInvariants then
	if Al cmpeq "BethMuellerQuade" then
	    func := MuellerQuadeBeth;
	elif Al cmpeq "FleischmannKemperWoodcock" then
	    require not IsAG(IF): "Group must be finite for FleischmannKemperWoodcock algorithm";
	    func := FleischmannKemperWoodcock;
	else
	    require false:
	    "Al must be \"BethMuellerQuade\" or \"FleischmannKemperWoodcock\"";
	end if;

	IF`FundamentalInvariants := func(
	    IF: nominimize := not Minimize,
	    mingens:=Min, BottomUpTo:=BottomUpTo
	);
    end if;
    return IF`FundamentalInvariants;
end intrinsic;

//////

intrinsic MinimizeGenerators(L::{[FldFunRatElt]}: Min := 0, BottomUpTo := 0)
    -> []
{A minimal (in the sense of 'irredundant') subset of L which generates
the same subfield as L.}

    return MinimizeFieldGenerators(L: BottomUpTo:=BottomUpTo, mingens:=Min);
end intrinsic;

intrinsic QuadeIdeal(L::{[FldFunRatElt]}: Fy:=1, LargeIdeal:=false) -> RngMPol
{The Quade ideal of L}
    require #L gt 0: "Argument must be non-empty";
    require non_constants(L): "Argument must have non-constants";
    return QuadeIdealInner(L: Fy := Fy, JustI := LargeIdeal);
end intrinsic;

/*
intrinsic 'in'(f::FldFunRat, IF::FldInvar) -> BoolElt
{Whether f is in IF}

    return MemberOfInvariantField(IF, f);
end intrinsic;
*/
