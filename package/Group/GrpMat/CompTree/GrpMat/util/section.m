//$Id:: section.m 1773 2010-02-24 07:35:33Z eobr007                        $:

freeze;

declare verbose UserUtil, 10;

// Useful information computed by MeatAxe
// For each factor of a module, get one record of this type
MeatAxeMapData := recformat<
    mproj : Map,                 // Projection from big group to small group
    mprojGen : Map,              // Projection from big group to small group
    mprojFactory : UserProgram,  // Creates projection w.r.t. a CBM
    pproj : Map,                 // Projection from big module to small module
    pprojFactory : UserProgram,  // Creates projection w.r.t. a CBM
    vsProj : Map,                // Projection from big space to small space
    vsProjFactory : UserProgram, // Creates projection w.r.t. a CBM
    genIndices : SeqEnum,        // Indices of small gens in list of big gens
    image : GrpMat,              // Group corresponding to factor
    factor : ModGrp,             // The factor
    slpMap : Map,                // Evaluates SLPs of small group in big group
    slpCoercion : Map,           // Maps small SLPs to big SLPs
    left : RngIntElt,            // Left position of factor w.r.t CBM
    top : RngIntElt>;            // Top position of factor w.r.t. CBM

// Useful information computed by MeatAxe
// Data about filtration of O_2 of the group of the module
// ie the module splits up as a number of blocks, and for each block we
// store one of these records
FiltrationMapData := recformat<
    mproj : Map,                // Projection from big group to block
    mprojFactory : UserProgram, // Creates projection w.r.t. a CBM
    fullMatSpace : ModMatFld,   // Full KMatrixSpace of block
    matBlock : ModMatFld,       // KMatrixSpace subspace of block
    fullKSpace : ModTupFld,     // Full VectorSpace of block
    kBlock : ModTupFld,         // VectorSpace subspace of block
    fullModule : ModGrp,        // Full GModule of block
    module : ModGrp,            // GModule subspace of block (not assigned)
    moduleMap : Map,            // Map from KMatrixSpace to module
    blockMap : Map,             // Map from VectorSpace to module
    left : RngIntElt,           // Left position of block w.r.t CBM
    top : RngIntElt,            // Top position of block w.r.t. CBM
    height : RngIntElt,         // Height of block
    width : RngIntElt,          // Width of block
    topFactor : RngIntElt,      // Factor above the block
    rightFactor : RngIntElt,    // Factor to the right of block
    gens : SeqEnum>;            // Generators of block module (not assigned)

// This is due to Mark Stather
function LayersData(G)
    /* Fixes data corresponding to the decomposition of the natural G Module */
    M := GModule(G);
    E, F, mat := CompositionSeries(M);
    mat := Generic(G) ! mat^(-1);
    return [* M, E, F, mat *];
end function;

// This is due to Mark Stather
function AllLTModules(G, LayersData)

    D := LayersData;
    E := D[2];
    F := D[3];
    mat := D[4];

    K := CoefficientRing(G);
    q := #K;
    p := Characteristic(K);
    e := Degree(K);
    A, alpha := AdditiveGroup(K);
    
    gens := [G.i : i in [1 .. Ngens(G)]];
    conjgens := [mat * G.i * mat^(-1) : i in [1 .. Ngens(G)]];

    // Construct embedings of the blocks inside GL(ed,p)
    gensoverp := [* [**] : i in [1 .. #E] *];

    // also need their transpose^-1's
    gensoverpT := [* [**] : i in [1 .. #E] *];

    tm := Cputime();
    for i in [1 .. #E] do
	for j in [1 .. #gens] do
	    g := conjgens[j];
	    g1 := ExtractBlock(g, Dimension(E[i]) - Dimension(F[i]) + 1,
		Dimension(E[i]) - Dimension(F[i]) + 1,
		Dimension(F[i]), Dimension(F[i]));

	    
	    vprintf UserUtil, 4 : "Write %o over field %o\n",
		GL(NumberOfRows(g1), K), PrimeField(K);
	    
	    _, embed := WriteOverSmallerField(GL(NumberOfRows(g1), K),
		PrimeField(K));
	    vprint UserUtil, 4 : "Done!";

	    vprint UserUtil, 4 : "Write matrix over smaller field", g1;
	    g1p := Function(embed)(g1);
	    vprint UserUtil, 4 : "Done!";
	    
	    //g1p := EmbedMat(g1, p, e);
	    
	    Append(~gensoverp[i], g1p);
	    g2p := g1p^(-1);
	    g2pT := MatrixAlgebra(PrimeField(K), NumberOfRows(g1p)) ! 0;
	    
	    // Do some funny transpose thing
	    for i1 in [1 .. (NumberOfRows(g1p) div e)] do
		for j1 in [1 .. (NumberOfRows(g1p) div e)] do
		    InsertBlock(~g2pT, ExtractBlock(g2p, (i1 - 1) * e + 1,
			(j1 - 1) * e + 1, e, e), (j1 - 1) * e + 1,
			(i1 - 1) * e + 1);
		end for;
	    end for;
	    Append(~gensoverpT[i], g2pT);
	end for;
    end for;
    vprint UserUtil, 2 : "Taken ", RealField(5) ! Cputime(tm),
	" to construct all the blocks";

    Mods := [ [] : i in [1 .. (#F - 1)] ];
    L := [];
    phi := [**];

    for n in [1 .. (#E - 1)] do
	for i in [1 .. (#E - n)] do
	    j := i + n;
	    mats := [];
	    for k in [1 .. #gens] do       
		if p ne q then
		    g1 := gensoverp[i][k];
		    g2 := gensoverpT[j][k];
		    dg1 := NumberOfRows(g1);
		    dg2 := NumberOfRows(g2);
		    m := MatrixAlgebra(PrimeField(K), (dg1 * dg2) div e) ! 0;
		
		    for i1 in [1 .. (dg2 div e)] do 
			for i2 in [1 .. (dg2 div e)] do
			    a := ExtractBlock(g2, (i1 - 1) * e + 1,
				(i2 - 1) * e + 1, e, e);
			    for j1 in [1 .. (dg1 div e)] do
				for j2 in [1 .. (dg1 div e)] do
				    b := ExtractBlock(g1, (j1 - 1) * e + 1,
					(j2 - 1) * e + 1, e, e);
				    InsertBlock(~m, a * b,
					(i1 - 1) * dg1 + (j1 - 1) * e + 1,
					(i2 - 1) * dg1 + (j2 - 1) * e + 1); 
				end for;
			    end for;
			end for;
		    end for; 
		    x := m;
		else
		    x := KroneckerProduct(gensoverpT[j][k], gensoverp[i][k]);
		end if;
		Append(~mats,x);
	    end for;
	    Append(~Mods[n],GModule(G,mats));
	end for;
    
	L[n] := DirectSum(Mods[n]);
	d := Dimension(L[n]);

	phi[n] := function(x)
	    x := mat * x * mat^(-1);
	counti := 1;
	countj := Dimension(E[n]) + 1;
	elt := [];
	for i in [1 .. (#E - n)] do
	    j := i + n;
	    v := ExtractBlock(x, countj, counti, Dimension(F[j]),
		Dimension(F[i]));
	    v := Eltseq(v);
	    v2 := &cat[Eltseq(v[k] @@ alpha) : k in [1 .. #v] ];
	    elt := elt cat v2;
	    counti +:= Dimension(F[i]);
	    countj +:= Dimension(F[j]);
	end for;
	return L[n] ! elt;
    end function;
end for;  
return L, phi;
end function;

function MeatAxeMaps(G :
    Factors := func<M | CompositionSeries(M)>,
    Form := "unknown", FindForm := true, Filtration := true)
    /* Split up the natural module M of G and fill the MeatAxeMapData structure
    for each composition factor. Also compute the filtration of O_2(G) and
    fill the FiltrationMapData structure for each block in the filtration.

    Returns the sequence of MeatAxeMapData records corresponding to the
    composition factors of M, a composition series of M, the corresponding
    composition factors of M and change of basis, and finally the sequence of
    FiltrationMapData records.

    The composition series and factors are computed using the function Factors,
    which must have the same input and output as CompositionSeries(ModGrp).

    If Category(Form) is AlgMatElt, it is assumed to be a symmetric bilinear
    form or symplectic form which is preserved by G. In this case the vector
    spaces in the MeatAxeMapData structures for each non-trivial composition
    factor are equipped with this inner product. */
    local M, series, factors, cbm, preDim, meatAxeData, H, mproj,
	indices, W, slpCoercion, pproj, images, field, formG, formH, VG, VH,
	vsProjFactory, filtration, row, col, width, height, preHeight,
	preWidth, block, blockSpace, moduleMap, layer, products, proj;
    
    vprint UserUtil, 1 : "Entering MeatAxe maps";

    M := GModule(G);
    field := CoefficientRing(G);

    vprint UserUtil, 2 : "Find composition factors";
    series, factors, cbm := Factors(M);
    preDim := 0;
    meatAxeData := [];
    
    formG := Form;
    if Category(formG) eq AlgMatElt then
	VG := VectorSpace(field, Degree(G), formG);
    else
	VG := VectorSpace(G);
    end if;
    
    vprint UserUtil, 2 : "Check composition factors";
    for N in factors do
	H := ActionGroup(N);

	// Get projection of matrix group to diagonal group
	mprojFactory := func<cbm | hom<G -> H | x :-> Generic(H) !
	Submatrix(cbm * (Parent(cbm) ! x) * cbm^(-1), preDim + 1, preDim + 1,
	    Degree(H), Degree(H))>>;
	mproj := mprojFactory(cbm);

	mprojFactoryGen := func<cbm | hom<G -> H | x :-> 
	Submatrix(cbm * (Parent(cbm) ! x) * cbm^(-1), preDim + 1, preDim + 1,
	    Degree(H), Degree(H))>>;
	mprojGen := mprojFactoryGen(cbm);
	
	// Get indices of used large generators
	images := [Function(mproj)(g) : g in UserGenerators(G)];
	H := sub<Generic(H) | images>;
	indices := [Index(images, g) : g in UserGenerators(H)];
	vprint UserUtil, 8 : images, UserGenerators(H), indices;
	assert forall{j : j in indices | j gt 0};

	// Get coercion of SLPs from small to large
	W := WordGroup(G);
	slpCoercion := hom<WordGroup(H) -> W | [W.i : i in indices]>;
	slpMap := hom<WordGroup(H) -> G | [G.i : i in indices]>;

	// Get projection of large space to small space
	pprojFactory := func<cbm | hom<M -> N | [<x, N ! [v[j] :
	j in [preDim + 1 .. preDim + Dimension(N)]]>
	    where v is x * cbm^(-1) : x in Basis(M)]>>;

	VH := VectorSpace(H);
	if IsAbsolutelyIrreducible(H) and not IsTrivial(H) and FindForm then
	    vprint UserUtil, 2 : "Find symmetric bilinear form";
	    flag, formH := SymmetricBilinearForm(H);
	    vprint UserUtil, 2 : "Done";
	
	    if flag then
		VH := VectorSpace(field, Degree(H), formH);
	    end if;
	end if;
	
	// Get projection of corresponding vector spaces
	vsProjFactory := func<cbm | hom<VG -> VH | [<x, VH ! [v[j] :
	j in [preDim + 1 .. preDim + Dimension(VH)]]>
	    where v is x * cbm^(-1) : x in Basis(VG)]>>;
	
	Append(~meatAxeData, rec<MeatAxeMapData |
	    mproj := mproj,
	    mprojGen := mprojGen,
	    pproj := pprojFactory(cbm),
	    genIndices := indices,
	    mprojFactory := mprojFactory,
	    pprojFactory := pprojFactory,
	    slpCoercion := slpCoercion,
	    image := H,
	    slpMap := slpMap,
	    left := preDim + 1,
	    top := preDim + 1,
	    factor := N,
	    vsProjFactory := vsProjFactory,
	    vsProj := vsProjFactory(cbm)>);
	preDim +:= Dimension(N);
    end for;

    filtration := [];
    if Filtration then
	vprint UserUtil, 2 : "Find tensor products";

	// Get all projections to block below diagonal
	products := [[TensorProduct(Dual(factors[i]), factors[i + j]) :
	    i in [1 .. #factors - j]] :  j in [1 .. #factors - 1]];
	
	vprint UserUtil, 2 : "Find filtration";
	
	for j in [1 .. #products] do
	    layer := [];
	    for i in [1 .. #products[j]] do
		row := i;
		col := i + j;
		
		// Calculate block dimensions and position
		height := Dimension(factors[col]);
		width := Dimension(factors[row]);
		preHeight := col gt 1 select &+[Dimension(factors[k]) :
		    k in [1 .. col - 1]] else 0;
		preWidth := row gt 1 select &+[Dimension(factors[k]) :
		    k in [1 .. row - 1]] else 0;
		
		// Get block as vector space
		block := KMatrixSpace(field, height, width);
		blockSpace := KSpace(field, height * width);
		
		moduleMap := hom<block -> products[j][i] |
		[products[j][i] ! ElementToSequence(b) : b in Basis(block)]>;
		blockProj := hom<block -> blockSpace |
		[blockSpace ! ElementToSequence(b) : b in Basis(block)]>;
		
		// Projection into block
		proj := func<cbm | hom<G -> block | x :-> block !
		Submatrix(cbm * (Parent(cbm) ! x) * cbm^(-1),
		    preHeight + 1, preWidth + 1, height, width)>>;
		
		Append(~layer, rec<FiltrationMapData | mproj := proj(cbm),
		    mprojFactory := proj,
		    left := preWidth + 1,
		    top := preHeight + 1,
		    width := width,
		    height := height,
		    fullMatSpace := block,
		    fullKSpace := blockSpace,
		    fullModule := products[j][i],
		    topFactor := row,
		    rightFactor := col,
		    blockMap := blockProj,
		    moduleMap := moduleMap>);
		preHeight +:= height;
	    end for;
	    
	    Append(~filtration, layer);
	end for;
	vprint UserUtil, 1 : "MeatAxe maps finished";
    end if;
    
    return meatAxeData, series, factors, cbm, filtration;
end function;

/* extract from g rows & columns listed in index */

ExtractAction := function (g, index)
   E := [];
   F := BaseRing (Parent (g));
   if Type (index) eq SetEnum then 
      index := Sort (SetToSequence (index)); 
   end if;
   for i in index do 
      for j in index do
         // E cat:= (ExtractBlock (g, i, j, 1, 1));
         Append (~E, g[i][j]);
      end for;
   end for;
   return GL(#index, F) ! (E);
end function;

/* extract chosen composition factor */

ExtractFactor := function (G, index)
   U := UserGenerators (G);
   if Type (index) eq SetEnum then 
      index := Sort (SetToSequence (index)); 
   end if;
   X := [ExtractAction (U[i], index): i in [1..#U]];
   H := sub < GL(#index, BaseRing (G)) | X >;
   H`UserGenerators := X;
   if assigned G`UserGenerators then
      assert #H`UserGenerators eq #G`UserGenerators;
   end if;
   return H;
end function;

/* return action of matrix g on composition factors of G */

MatrixBlocks := function (G, g)

   CF := G`CompositionFactors;
   COB := G`ChangeOfBasis;
   F := BaseRing (G);
   d := Degree (G);
   e := [* *];
   I := COB * g * COB^-1;
   offset := 0;
   for i in [1..#CF] do 
      k := Dimension (CF[i]);
      e[i] := GL (k, F) ! ExtractBlock (I, offset + 1, offset + 1, k, k);
      offset +:= k;
   end for;
   return e;
end function;

intrinsic Sections (G:: GrpMat) -> List, GrpMatElt  
{Actions on module composition factors of G and change-of-basis matrix}
   M := GModule (G);
   F := BaseRing (G);
   _, CF, COB := CompositionSeries (M);
   G`CompositionFactors := CF;
   G`ChangeOfBasis := Generic(G) ! COB;
   U := UserGenerators (G);

   U := UserGenerators (G);
   E := [MatrixBlocks (G, U[j]): j in [1..#U]];
   sections := [* *];
   for i in [1..#CF] do
      k := Dimension (CF[i]);
      gens := [E[j][i]: j in [1..#U]];
      sections[i] := sub <GL(k, F) | gens>;
      sections[i]`UserGenerators := gens;
   end for;

   return sections, COB;
end intrinsic;

/* identify groups in L */

IdentifySections := function (L)  
   sl := [* *];
   for i in [1..#L] do
      C := L[i];
      F := BaseRing (C);
      dets := {Determinant (g): g in Generators (C)};
      if #dets gt 0 then 
         o := LCM ([Order (x): x in dets]);
      else 
         o := 1;
      end if;
      if Degree (C) gt 1 then 
         flag := RecognizeClassical (C);
      else 
         flag := false;
      end if;
      sl[i] := <Degree (C), flag, o>;
   end for;
   return sl;
end function;
