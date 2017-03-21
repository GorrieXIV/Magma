freeze;

///////////////////////////////////////////////////////////////////////
// pencil_res.m
//	Contents:
//		splice diagrams at infinity of plane jacobian pencils
//		pulling functions back along splice diagrams at infinity
//		irregular values
//		associated functions
///////////////////////////////////////////////////////////////////////


forward fiddle_multiplicities;
intrinsic ResolutionGraph(P::LinearSys) -> GrphRes
{The dual graph of the resolution at infinity of the jacobian pencil P}
    require IsJacobianPencil(P): "Linear system is not a Jacobian pencil";
    if not assigned P`resolution_graph then
        g := ResolutionGraph(P,0,1);
 
        // calculate the multiplicities: small fiddle to be done.
        mults := fiddle_multiplicities(g);
        SetMultiplicities(~g,mults);
 
        // recalculate the transverse intersections using the fibre at infinity:
        // the singularity calculation returns the negative of what we want.
        CalculateTransverseIntersections(~g);
        ti := [ -t : t in TransverseIntersections(g) ];
        SetTransverseIntersections(~g,ti);
 
        // calculate the canonical class: no problem here bcs it _is_ canonical
        CalculateCanonicalClass(~g);
 
        P`resolution_graph := g;
    end if;
    return P`resolution_graph;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Splice diagrams at infinity
///////////////////////////////////////////////////////////////////////


intrinsic CalculateRegularSpliceDiagram(P::LinearSys) -> GrphSpl
{The splice diagram at infinity of the plane jacobian pencil P}
    require IsJacobianPencil(P): "Linear system is not a Jacobian pencil";
    // get hold of the resolution graph at infinity
    G := ResolutionGraph(P);
    // reduce to get the splice diagram but without contracting vertex 1
    S := SpliceDiagram(G,G!1);
    return S;
end intrinsic;

forward fiddle_maps;
intrinsic ResolutionGraph(P::LinearSys,a::RngElt,b::RngElt) -> GrphRes
{The resolution graph at infinity of the plane jacobian pencil P}
// If P : f = c where c varies and f is the polynomial used to create P, this
// routine analyses the singularities of (f-a)*(f-b) = 0 at infinity.
// If these fibres are both regular, the transverse intersections will
// simply be twice those of the regular splice diagram.
// Otherwise one must calculate by hand how they split up.
// This is usually called by the intrinsic 'ResolutionGraph(P)' which
// uses a multiplicity calculation to derive the regular diagram from
// that of any pair of fibres.
    A := AffineAmbient(P);
    require Dimension(A) eq 2:
	"P must be a jacobian pencil of plane curves";
    B := BasePoints(P);
    f0 := GeneratingPolynomial(P);
    f1 := f0 - a;
    f2 := f0 - b;
    C := Curve(A,f1*f2);	// the union of two fibres of P
    Cbar := ProjectiveClosure(C);	// the closure of two fibres of P

    // run through the base points of P calculating resolution graphs of
    // the union of two (possibly irregular) fibres there.
    graphs := [];	// the sequence of singularity res graphs at infinity
    pts := [];
    for b in B do
	G := ResolutionGraph(Cbar,b: M:=0,K:=0);
	// a hack to be able to calculate values of pencil on G: these points
	// will be recorded with the graph at the end.
	pts cat:= [ b : i in [1..Size(G)] ];
	// change of coords for the blowup maps
	fiddle_maps(~G,b);
	Append(~graphs,G);
    end for;

    // glue all the resolution graphs together with an extra vertex
    initialvxs := [ G ! 1 : G in graphs ];
    deg := Degree(P);
    base_blowup := &+[ BaseBlowupContribution(gg) : gg in graphs ];
    G := MakeResolutionGraph( Digraph<1|>, [ 1 + base_blowup ], [ 0 ] );
    v0 := G ! 1;
    for v in initialvxs do
	G := Connect(v0,v);
	v0 := G ! 1;
    end for;

    // calculate the patch maps
    prepm := [];
    length := 1;
    for G in graphs do
	ppmG := PrePatchMaps(G);
	for i in [2..Size(G)] do
	    //Remove(~ppmG,1);	// this is the id map on the glued vertex
	    if IsDefined(ppmG,i) then
		prepm[length+i] := ppmG[i];
	    end if;
	end for;
	length +:= Size(G);
    end for;
    SetPrePatchMaps(~G,prepm);

    // hack to be able to calculate values of pencil on G: the calculation
    // later on needs to know where to evaluate functions.
    base_pts := [];
    for i in [2..Size(G)] do
	base_pts[i] := pts[i-1];
    end for;
    G`base_points := base_pts;

    return G;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Irregular values
///////////////////////////////////////////////////////////////////////

intrinsic HorizontalVertices(g::GrphRes) -> SetEnum
{The set of vertices of g having arrows attached}
    return { i : i in [1..Size(g)] | TransverseIntersections(g)[i] ne 0 };
end intrinsic;

intrinsic IrregularVertices(g::GrphRes) -> SetEnum
{The set of vertices of g that lie just beyond a horizontal vertex}
    // i'm after those vertices which have a horizontal vertex rootside
    set := { Integers() | };
    vg := VertexSet(UnderlyingGraph(g));
    for i in HorizontalVertices(g) do
	outvxs := [ Index(EndVertices(e)[2]) : e in OutEdges(vg!i) ];
	set join:= SequenceToSet(outvxs);
    end for;
    return set;
end intrinsic;

intrinsic StronglyHorizontalVertices(g::GrphRes) -> SetEnum
{The set of horizontal vertices of g which meet strongly irregular vertices}
    vg := VertexSet(UnderlyingGraph(g));
    return { Index(EndVertices(InEdge(vg!i))[1]) : i in IrregularVertices(g) };
end intrinsic;

intrinsic HorizontalFunction(P::LinearSys,S::RngUPol,i::RngIntElt) -> SeqEnum
{The univariate polynomials in S of P at horizontal vertex i in the resolution}
    require IsJacobianPencil(P): "Linear system is not a Jacobian pencil";
    G := ResolutionGraph(P);
    require i in HorizontalVertices(G):
	"Third argument must be the index of a horizontal vertex";
    // f,g are the pullbacks of the def'g fn of P and z^deg(P) along the i-th
    // exceptional curve E_i. They are defined on the 'far' patch of E_i so
    // their ratio f/g does not take the value infinity along E_i.
    f,g := PolynomialPair(P,i);
    R := Parent(f); x := R.1; y := R.2;
    // Use the point of the projective plane above which vertex i lies
    // together with f,g to calculate the polynomial.
    pts := G`base_points;
    pt := pts[i];
    if Coordinates(pt)[1] eq 0 then
	ev := [x,1,0];
	mapfuns := [S.1,1,0];
    else
	ev := [1,y,0];
	mapfuns := [1,S.1,0];
    end if;
    compmap := hom< R -> S | mapfuns >;
    f1 := Evaluate(f,ev);
    g1 := Evaluate(g,ev);
    upoly := compmap(R ! (f1/g1));
    return upoly;
end intrinsic;

intrinsic IrregularValues(P::LinearSys,i::RngIntElt) -> SetEnum
{Irregular values of P appearing at horizontal vertex of index i in the
resolution graph}
    require IsJacobianPencil(P): "Linear system is not a Jacobian pencil";
    k := BaseRing(Ambient(P));
    U := PolynomialRing(k); u := U.1;
    p := HorizontalFunction(P,U,i);
    vals := { k | };
    if i in StronglyHorizontalVertices(ResolutionGraph(P)) then
	// the value of p along the exceptional curve beyond i is irregular.
	vals join:= { k | Evaluate(p,0) };
    end if;
    vals join:= { k | Evaluate(p,r[1]) : r in Roots(Derivative(p)) };
    return vals;
end intrinsic;

intrinsic StronglyIrregularValues(P::LinearSys) -> SetEnum
{The finite values of the generating polynomial of P on its resolution graph}
    require IsJacobianPencil(P): "Linear system is not a Jacobian pencil";
    k := BaseRing(Ambient(P));
    irr_vals := { k | };
    f := ProjectivePolynomial(P);
    R := Parent(f);
    // run through the strongly horizontal vxs comparing f with z^deg there
    for v in StronglyHorizontalVertices(P) do
	f1,g1 := PolynomialPair(P,v);
	// the pencil upstairs is defined by f1 = a*g1. i want to kill
	// the variable defining the exceptional curve, z = 0 in either case.
	f1temp := Evaluate(f1,3,0);
	gcd := GCD(f1temp,g1);
	f2 := R ! (f1temp/gcd);
	g2 := R ! (g1/gcd);
	pt := (ResolutionGraph(P)`base_points)[v];
	if Coordinates(pt)[1] eq 0 then
	    ev := [0,1,0];
	else
	    ev := [1,0,0];
	end if;
	// now the value of a i require is f2/g2.
	irr_val := Evaluate(R ! f2, ev) / Evaluate(g2,ev);
	Include(~irr_vals,irr_val);
    end for;
    return irr_vals;
end intrinsic;

intrinsic PolynomialPair(P::LinearSys,i::RngIntElt) -> RngMPolElt,RngMPolElt
{The pullback of f:z^d to the vertex i of the resolution graph of P}
    require IsJacobianPencil(P): "Linear system is not a Jacobian pencil";
    f := ProjectivePolynomial(P);
    g := InfinitePolynomial(P);
    R := Parent(f);
    G := ResolutionGraph(P);
    pm := ProjectivePatchMap(G!i);
    //f1 := Pullback(pm,f);
    //g1 := Pullback(pm,g);
    f1 := f@@pm;
    g1 := g@@pm;
    gcd := GCD(f1,g1);
    f2 := R ! (f1/gcd);
    g2 := R ! (g1/gcd);
    return f2,g2;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Associated functions
///////////////////////////////////////////////////////////////////////

fiddle_multiplicities := function(G)
// Calculate the multiplicities on G, resolution graph of a jacobian pencil.
// The underlying graph of G is directed away from a vertex corresponding
// to the line at infinity.
// This calculation uses the already available version for singularity
// resolution graphs so needs to be modified for this case.
// The initial calculation returns the multiplicities of the unique divisor
// supported on G which is numerically trivial when added to the birational
// transforms of the two fibres used to calculate G.
// The fibre at infinity is known to be connected, the vertex 1 is a
// part of it and the graph is directed away from vertex 1 So i run
// along paths until i see a zero and then set zero everywhere beyond that
// on the path.
// The result 'mults' of this calculation is -2 times the fibre at infinity.
    mults := Multiplicities(G);
    ChangeUniverse(~mults,Integers());
    // Traverse G setting multiplicities to 0 beyond any 0 already there.
    g := UnderlyingGraph(G);
    for v in VertexSet(g) do
	i := Index(v);
	if mults[i] eq 0 then
	    outverts := [ EndVertices(w)[2] : w in OutEdges(v) ];
	    for w in outverts do
		mults[Index(w)] := 0;
	    end for;
	end if;
    end for;
    // Multiplicities were calculated for the union of 2 fibres so halve them
    if not &and[ m mod 2 eq 0 : m in mults ] then
	error "Parity error in multiplicity calculation";
    end if;
    mults1 := [ Integers() | -m/2 : m in mults ];
    return mults1;
end function;

fiddle_maps := procedure(~G,b);
// The prepatch maps on the graph have moved the base singularity that the
// blowup was at point [0,0,1]. I have to include the translation back.
// This is dependent on the way Patch(C::CurvePlProj) chooses its
// coordinates: it makes a natural choice.
// Remember that b will always be at infinity.
    PM := PrePatchMaps(G);
    coords := Coordinates(b);
    k := BaseRing(Scheme(b));
    P := Ambient(Scheme(b));
    // split into two cases to determine which coordinate change to use
    if coords eq [ k | 1,0,0 ] then
	t := map< P -> P | [P.2,P.3,P.1] >;
	//tinv := RationalMap(P,P,[P.3,P.1,P.2]);
    else
	xcoord := coords[1];
	t := map< P -> P | [P.1 - xcoord,P.3,P.2] >;
	//tinv := RationalMap(P,P,[P.1 + xcoord,P.2,P.3]);
    end if;
    // make the new sequences by conjugation with the coordinate change
    PMnew := [];
    for i in [1..#PM] do
	if IsDefined(PM,i) then
	    pmold := PM[i];
	    PMnew[i] := pmold cat [ t ];
	end if;
    end for;
    // assign the new maps
    G`pre_patch_maps := PMnew;
end procedure;


///////////////////////////////////////////////////////////////////////
//		Intrinsics with pencil argument
///////////////////////////////////////////////////////////////////////

intrinsic HorizontalVertices(P::LinearSys) -> SetEnum
{The set of horizontal vertices in the resolution graph of P}
    return HorizontalVertices(ResolutionGraph(P));
end intrinsic;

intrinsic IrregularVertices(P::LinearSys) -> SetEnum
{The set of initial irregular vertices of the resolution graph of P}
    return IrregularVertices(ResolutionGraph(P));
end intrinsic;

intrinsic StronglyHorizontalVertices(P::LinearSys) -> SetEnum
{The set of horizontal vertices in the resolution graph of P which meet
strongly irregular exceptional curves}
    return StronglyHorizontalVertices(ResolutionGraph(P));
end intrinsic;

