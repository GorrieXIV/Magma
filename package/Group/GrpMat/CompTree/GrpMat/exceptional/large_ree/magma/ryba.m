/******************************************************************************
 *
 *    ryba.m    Large Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2005-06-30
 *
 *    Version   : $Revision:: 2346                                           $:
 *    Date      : $Date:: 2012-10-16 05:48:18 +1100 (Tue, 16 Oct 2012)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: ryba.m 2346 2012-10-15 18:48:18Z jbaa004                       $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose LargeReeRyba, 10;

import "involution.m": initialiseCentraliser, centraliserMembershipBatch,
    getCentraliserEvenOrderElementBatch;
import "../../../util/dihedral.m" : DihedralTrick;
import "../../../util/basics.m" : MatSLP;

// Stored information used by Ryba
// Big Ree has two conjugacy class of involutions, so we precompute two
// involution centralisers
LargeReeMembershipInfo := recformat<
    involutionSz : Rec,
    centraliserSz : GrpMat,
    involutionSL2 : Rec,
    centraliserSL2 : GrpMat>;

declare attributes GrpMat : LargeReeMembershipData;

forward RybaTrick, RybaTrickBatch, RybaInitialisation;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic LargeReeStandardConstructiveMembership(G :: GrpMat,
    g :: GrpMatElt :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, wordGroup := WordGroup(G)) -> BoolElt,
    GrpSLPElt
    { Ryba trick for 2F_4(q) }

    flag, slps := LargeReeStandardConstructiveMembership(G, [g] :
	CheckInput := CheckInput, Randomiser := Randomiser,
	wordGroup := wordGroup);
    if flag then
	return true, slps[1];
    else
	return false, _;
    end if;
end intrinsic;

intrinsic LargeReeStandardConstructiveMembership(G :: GrpMat,
    batch :: SeqEnum[GrpMatElt]
    : Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, wordGroup := WordGroup(G)) -> BoolElt,
    SeqEnum[GrpSLPElt]
    { Ryba trick for 2F_4(q) }
    
    if CheckInput then
	if not LargeReeStandardRecogniser(G) then
	    error "G must be a Big Ree group in natural representation";
	end if;
    end if;
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    // Trivial checks
    if not forall{g : g in batch | CoefficientRing(G) eq CoefficientRing(g) and
	Degree(G) eq Degree(g) and
	LargeReeStandardMembership(g)} then
	return false, _;
    end if;

    
    // Precompute centralisers
    if not assigned G`LargeReeMembershipData then
	vprint LargeReeRyba, 1 : "Initialise Ryba";
	RybaInitialisation(G, wordGroup);
    end if;
    
    vprint LargeReeRyba, 1 : "Perform Ryba trick";
    return RybaTrickBatch(G, batch : wordGroup := wordGroup);
/*
    if not HasCompositionTree(G) then
	T := CompositionTree(G);
    end if;

    slps := [];
    slpMap := CompositionTreeNiceToUser(G);
    for g in batch do
	slp := CompositionTreeElementToWord(G, g);
	Append(~slps, slpMap(slp));
    end for;

    return Evaluate(slps, UserGenerators(wordGroup));
*/
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

procedure RybaInitialisation(G, W : invol := rec<MatSLP | mat := Identity(G),
    slp := Identity(W)>)
    local j1, j2, C1, C2, class1, class2, elements, element, slp, l,
	r, flag;

    assert assigned G`RandomProcess;
    
    vprint LargeReeRyba, 1 : "Initialise Ryba trick";

    if IsIdentity(invol`mat^2) and not IsIdentity(invol`mat) then
	j1 := invol`mat;
	slp := invol`slp;
    else
	vprint LargeReeRyba, 2 : "Find Sz involution";

	// Get Sz-involution
	j1, slp := LargeReeSzInvolution(G : CheckInput := false,
	    Randomiser := G`RandomProcess, wordGroup := W);
    end if;
    
    assert W cmpeq Parent(slp);

    // Find Sz-centraliser
    repeat
	vprint LargeReeRyba, 2 : "Find Sz centraliser";

	C1 := LargeReeInvolutionCentraliser(G, j1, slp :
	    Randomiser := G`RandomProcess, CheckInput := false);

	vprint LargeReeRyba, 2 : "Initialise Sz centraliser";

	// Compute all O_2 blocks
	//flag := initialiseCentraliser(C1);
	_ := CompositionTree(C1);
	flag := true;
    until flag;

    repeat
	vprint LargeReeRyba, 2 : "Find SL2 involution";
	
	// Take even order element of SL2 type from O_2(C1)
	// Apparently this is usually of SL2 type when C1 centralises an
	// Sz involution
	j2 := getCentraliserEvenOrderElementBatch(C1, 1);
	j2 := j2[1];
	
	// Power up to an involution
	l, r := Quotrem(Order(j2`mat : Proof := false), 2);
	assert r eq 0;
	j2`mat ^:= l;
	j2`slp ^:= l;

	// Check that we got an SL2-involution
	class2 := LargeReeInvolutionClass(j2`mat);
    until class2 eq "2B";
    
    assert W cmpeq Parent(j2`slp);

    // Find centraliser of SL2 type
    repeat
	vprint LargeReeRyba, 2 : "Find SL2 centraliser";

	C2 := LargeReeInvolutionCentraliser(G, j2`mat, j2`slp :
	    Randomiser := G`RandomProcess, CheckInput := false);
	assert class2 eq C2`LargeReeInvolCentraliserData`class;
	
	vprint LargeReeRyba, 2 : "Initialise SL2 centraliser";

	// Compute all O_2 blocks
	//flag := initialiseCentraliser(C2);
        _ := CompositionTree(C2);
	flag := true;
    until flag;

    // Store data    
    G`LargeReeMembershipData := rec<LargeReeMembershipInfo |
	involutionSz := rec<MatSLP | mat := j1, slp := slp>,
	centraliserSz := C1,
	involutionSL2 := j2,
	centraliserSL2 := C2>;

    vprint LargeReeRyba, 1 : "Ryba initialisation done";
end procedure;

function RybaTrickBatch(G, batch : wordGroup := WordGroup(G))
    local h, slpH, l, r, x, y, z, slpX, C_y, C_x, C_z, slpY, slpZ, slpHG,
	class_x, class_y, class_z, elements, element;

    assert assigned G`RandomProcess;
    assert assigned G`LargeReeMembershipData;
    
    vprint LargeReeRyba, 1 : "Entering Ryba trick";

    z_batch := [];
    h_batch := [];

    // Build batch of z's and h's from corresponding g's
    for g in batch do
	// Get element of even order, involving g
	// We need an Sz-type element, which we are very likely to get
	class_z := "";
	mat := g;
	slp := Identity(wordGroup);
	repeat
	    vprint LargeReeRyba, 2 : "Use trick to find Sz-involution z";
	    
	    v, w := Random(G`RandomProcess);
	    mat := v * mat;
	    
	    // Work in SLP group without redundant generators
	    slp := w * (Parent(w) ! slp);
	    elements := EvenOrderElement(G : Element :=
		rec<MatSLP | mat := mat, slp := slp>,
		Randomiser := G`RandomProcess, CheckInput := false);
	    
	    // Save SLPs as elements in group with redundant generators
	    ChangeUniverse(~elements, CartesianProduct(Generic(G), wordGroup));

	    repeat
		ExtractRep(~elements, ~element);
		h := element[1];
		slpH := element[2];
		
		// h is g_1 * v * g, slpH is (SLP of g_1) * w
		l, r := Quotrem(Order(h : Proof := false), 2);
		assert r eq 0;
		
		// Get first involution
		z := h^l;
		slpZ := Identity(wordGroup);
		
		class_z := LargeReeInvolutionClass(z);
		
		if class_z eq "Unknown" then
		    return false, _;
		end if;
	    until class_z eq "2A" or IsEmpty(elements);
	until class_z eq "2A";
	
	assert Parent(slpH) cmpeq wordGroup;
	Append(~z_batch, rec<MatSLP | mat := z, slp := slpZ>);
	Append(~h_batch, rec<MatSLP | mat := h, slp := slpH>);
    end for;
    
    // Get batch of x's for corresponding g's
    // We find smaller batches until all of them are of class 2B
    x_batch := [];
    repeat
	vprint LargeReeRyba, 2 :
	    "Find x-batch of SL2-involution in Sz-centraliser";
	
	x_test_batch := getCentraliserEvenOrderElementBatch(
	    G`LargeReeMembershipData`centraliserSz, #batch - #x_batch);

	vprint LargeReeRyba, 3 : "Got x-batch";

	for i in [1 .. #x_test_batch] do
	    l, r := Quotrem(Order(x_test_batch[i]`mat : Proof := false), 2);
	    assert r eq 0;
	    
	    x_test_batch[i]`mat ^:= l;
	    x_test_batch[i]`slp ^:= l;

	    if LargeReeInvolutionClass(x_test_batch[i]`mat) eq "2B" then
		Append(~x_batch, x_test_batch[i]);
	    end if;
	end for;
    until #x_batch eq #batch;

    assert forall{x : x in x_batch | IsCoercible(wordGroup, x`slp)};

    // Build batch of y's from x's and z's
    // These can be of different involution classes
    // Also build batch of conjugating elements from x's to SL2 invol
    
    y_batch_mat := [];
    x_conjugators := [];
    for i in [1 .. #batch] do
	vprint LargeReeRyba, 2 : "Get final involution y";

	// x * z must have even order since they are not conjugate
	// z is of class 2A and x of class 2B, if our check if correct
	y := x_batch[i]`mat * z_batch[i]`mat;
	l, r := Quotrem(Order(y : Proof := false), 2);
	assert r eq 0;
	y ^:= l;

	Append(~y_batch_mat, y);

	vprint LargeReeRyba, 2 : "Conjugate x to standard SL2 involution";
	
	// Conjugate x to our favourite SL2-involution
	conjugator := DihedralTrick(x_batch[i],
	    G`LargeReeMembershipData`involutionSL2,
	    G`RandomProcess);
	Append(~x_conjugators, conjugator);
    end for;
    
    vprint LargeReeRyba, 2 : "Express y as word in x-centraliser";

    // Get SLP for y, conjugate to our favourite involution
    // y centralises x, so y^conjugator must centralise involutionSL2
/*
    flag, slpYbatch :=
	centraliserMembershipBatch(G`LargeReeMembershipData`centraliserSL2,
	[y_batch_mat[i]^x_conjugators[i]`mat : i in [1 .. #batch]]);
    if not flag then
	return false, _;
    end if;
*/
    slpYbatch := [];
    slpYMap := CompositionTreeNiceToUser(G`LargeReeMembershipData`centraliserSL2);
    slpCoercion := G`LargeReeMembershipData`centraliserSL2`LargeReeInvolCentraliserData`slpCoercion;
    for i in [1 .. #batch] do
	g := y_batch_mat[i]^x_conjugators[i]`mat;
	flag, slp := CompositionTreeElementToWord(G`LargeReeMembershipData`centraliserSL2, g);
	if not flag then
	    return false, _;
	end if;
	//print Domain(slpYMap), Codomain(slpYMap), wordGroup;
	Append(~slpYbatch, (slpYMap * slpCoercion)(slp));
    end for;

    assert forall{slpY : slpY in slpYbatch | IsCoercible(wordGroup, slpY)};

    // Now build two batches of conjugating elements
    // depending on which involution class the y belongs to
    // Need to store indices to remember where the z's belong
    
    y_batch := [];
    y_conjugators := [];
    centralisers := [G`LargeReeMembershipData`centraliserSz,
	G`LargeReeMembershipData`centraliserSL2];
    y_centralisers := [[], []];
    z_indices := {@ @};
    
    for i in [1 .. #batch] do
	Append(~y_batch, rec<MatSLP | mat := y_batch_mat[i],
	    slp := slpYbatch[i]^x_conjugators[i]`slp^(-1)>);
	
	vprint LargeReeRyba, 2 : "Conjugate y to standard involution";
	if LargeReeInvolutionClass(y_batch[i]`mat) eq "2A" then
	    // Conjugate y to our favourite Sz-involution
	    conjugator := DihedralTrick(y_batch[i],
		G`LargeReeMembershipData`involutionSz,
		G`RandomProcess);

	    Append(~y_centralisers[1], <z_batch[i], i>);
	    Include(~z_indices, [1, #y_centralisers[1]]);
	else
	    // Conjugate y to our favourite SL2-involution
	    conjugator := DihedralTrick(y_batch[i],
		G`LargeReeMembershipData`involutionSL2,
		G`RandomProcess);
	    
	    Append(~y_centralisers[2], <z_batch[i], i>);
	    Include(~z_indices, [2, #y_centralisers[2]]);
	end if;

	Append(~y_conjugators, conjugator);
    end for;

    assert Evaluate([y_batch[i]`slp : i in [1 .. #batch]],
	UserGenerators(G)) eq [y_batch[i]`mat : i in [1 .. #batch]];
    
    // Get SLP for z's, in two batches
    // z centralises y, so z^conjugator centralises our favourite involution
    // which involution depends on each y
    z_conjugators := [];

    vprint LargeReeRyba, 2 : "Express z as word in y-centraliser";
    slpZbatches := [];
    for i in [1 .. 2] do
	H := centralisers[i];
	slpMap := CompositionTreeNiceToUser(H);
	slpCoercion := H`LargeReeInvolCentraliserData`slpCoercion;
        slpZbatch := [];
        for j in [1 .. #y_centralisers[i]] do
	    h := y_centralisers[i][j][1]`mat^y_conjugators[y_centralisers[i][j][2]]`mat;
	    flag, slp := CompositionTreeElementToWord(H, h);
	    if not flag then
		return false, _;
	    end if;
	
	    Append(~slpZbatch, (slpMap * slpCoercion)(slp));
	end for;
	/*
	flag, slpZbatch := centraliserMembershipBatch(centralisers[i],
	    [y_centralisers[i][j][1]`mat^y_conjugators[
	    y_centralisers[i][j][2]]`mat : j in [1 .. #y_centralisers[i]]]);
	if not flag then
	    return false, _;
	end if;
*/
	Append(~slpZbatches, slpZbatch);
    end for;

    // Now build batch of conjugating elements from z's to the Sz invol
    
    for i in [1 .. #batch] do
	z_batch[i] := rec<MatSLP | mat := z_batch[i]`mat,
	    slp := slpZbatches[z_indices[i][1]][
	    z_indices[i][2]]^y_conjugators[i]`slp^(-1)>;
	assert IsCoercible(wordGroup, z_batch[i]`slp);
	
	vprint LargeReeRyba, 2 : "Conjugate z to Sz-involution";
	
	// z is an Sz-involution by construction
	// Conjugate z to our favourite Sz-involution
	conjugator := DihedralTrick(z_batch[i],
	    G`LargeReeMembershipData`involutionSz, G`RandomProcess);
	Append(~z_conjugators, conjugator);
    end for;
    
    assert Evaluate([z`slp : z in z_batch], UserGenerators(G)) eq
	[z`mat : z in z_batch];
    
    vprint LargeReeRyba, 2 : "Express g as word in z-centraliser";
    
    // Get SLP for hg
    /*
    flag, slpHGbatch :=
	centraliserMembershipBatch(G`LargeReeMembershipData`centraliserSz,
	[h_batch[i]`mat^z_conjugators[i]`mat : i in [1 .. #batch]]);
    if not flag then
	return false, _;
    end if;
    */
    
    slpHGbatch := [];
    slpMap := CompositionTreeNiceToUser(G`LargeReeMembershipData`centraliserSz);
    slpCoercion := G`LargeReeMembershipData`centraliserSz`LargeReeInvolCentraliserData`slpCoercion;
    for i in [1 .. #batch] do
	h := h_batch[i]`mat^z_conjugators[i]`mat;
	flag, slp := CompositionTreeElementToWord(G`LargeReeMembershipData`centraliserSz, h);
	if not flag then
	    return false, _;
	end if;
    
        Append(~slpHGbatch, (slpMap * slpCoercion)(slp));
    end for;

    assert forall{slpHG : slpHG in slpHGbatch |
	IsCoercible(wordGroup, slpHG)};
    
    // slpHG is SLP for hg
    assert #slpHGbatch eq #z_conjugators;
    return true, [h_batch[i]`slp^(-1) *
	(wordGroup ! (slpHGbatch[i]^(z_conjugators[i]`slp^(-1)))) :
	i in [1 .. #batch]];
end function;
