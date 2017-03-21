freeze;

///////////////////////////////////////////////////////////////////////
// adjoints.m
//	Contents:
//		calculation of a system of adjoint curves
//		functions to prepare resolution graphs for adjoints
///////////////////////////////////////////////////////////////////////


intrinsic Adjoints(C::Crv,d::RngIntElt) -> LinearSys
{The linear system of adjoint curves of degree d to C}
    P2 := Ambient(C);
    require IsOrdinaryProjective(P2) and  (Dimension(P2) eq 2):
	"Curve must line in the ordinary projective plane";
    deg := Degree(C);

    /* mch 5/7/06 - test for only ordinary singularities. If true,
	use the new ordinary curve functions */
    boo,_,Iadj := HasOnlyOrdinarySingularities(C);
    if boo then
	lin :=  AdjointLinearSystemFromIdeal(Iadj,d);
	return LinearSystem(LinearSystem(P2,Max(d,1)),Sections(lin));
    end if;
    
    /* mch 6/1/05 - must deal with singular points over extn! */
    bExt := HasSingularPointsOverExtension(C);
    if bExt then
	Fext := Ring(Universe(SingularPointsOverSplittingField(C)));
	C := BaseChange(C,Fext);
	P2old := P2;
	P2 := Ambient(C);
    end if;
    
    // set up the complete linear system containing the adjoints
    // being careful to not use anything having a factor of C
    L := LinearSystem(P2,d);
    // choose a complement to the span of C if d >= deg
    L := Complement(L,C);
    // find the singular points of C
    sg := SingularPoints(C);

    // taking each singularity in turn, impose germ conditions on L
    for p in sg do
	vprint Adjoint: "singular germ",p;
	G := ResolutionGraph(C,p);
	ng := Size(G);

	// restrict L to pass through p with the required multiplicity
	//P,C := ProjectiveRepresentative(p);
	//m := Multiplicity(C,P);
	m := Multiplicity(C,p);
	vprint Adjoint: "restricting multiplicity at a singular point";
	L := LinearSystem(L,P2!p,m-1);

	// run through the vertices of G
	ti := TransverseIntersections(G);
	for i in [1..ng] do
	    v := G ! i;
	    np := Places(v);
	    if np eq 0 then
		continue;
	    end if;

	    mult := Multiplicity(v);
	    can := CanonicalMultiplicity(v);
	    ppm := ProjectivePatchMap(v);
	    vprint Adjoint: "adjoint restriction";
	    L := LinearSystem(L,ppm,2,Integers()!(mult-can));
     
	end for;	// v in VG
    end for;		// p in sg

    /* now must restrict back to original basefield if bExt */
    if bExt then
	CRE := CoordinateRing(P2);
	CR := CoordinateRing(P2old);
	Fold := BaseRing(CR);
	Ts := Monomials( (&+[CR.i : i in [1..Rank(CR)]])^d );
	TsE := ChangeUniverse(Ts,CRE);
	M := Matrix(Fext,#Sections(L),#TsE,[
		[MonomialCoefficient(l,t) : t in TsE] : l in Sections(L)]);
        if &and[m in Fold : m in Eltseq(M)] then //expected case!
	    M := Matrix(Fold,M);
	else
	    M := EchelonForm(M);
	    assert &and[m in Fold : m in Eltseq(M)];
	    M := Matrix(Fold,M);
	end if;
	L := LinearSystem(P2old,[ &+[M[i,j]*Ts[j]: j in [1..#Ts]] :
					i in [1..Nrows(M)] ]);	
    end if;

    return L;
end intrinsic;


///////////////////////////////////////////////////////////////////////

intrinsic AdjointGraph(C::Crv,p::Pt) -> GrphRes
{The resolution graph of p with multiplicities reduced by the canonical class}
// maybe this is irrelevant. in any case, it messes up the original graph.
    G := ResolutionGraph(C,p);
    m := Multiplicities(G);
    k := CanonicalClass(G);
    m1 := [ m[i] - k[i] : i in [1..#m] ];
    SetMultiplicities(~G,m1);
    return G;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Adjoint linear system on a curve of genus >= 2
///////////////////////////////////////////////////////////////////////

intrinsic AdjointLinearSystem(C::Crv) -> LinearSys
{The plane linear system which pulls back to the complete
canonical linear system on the resolution of C}
    deg := Degree(C) - 3;
    return Adjoints(C,deg);
end intrinsic;

intrinsic CanonicalLinearSystem(C::Crv) -> LinearSys
{The plane linear system which pulls back to the complete
canonical linear system on the resolution of C}
    deg := Degree(C) - 3;
    return Adjoints(C,deg);
end intrinsic;

