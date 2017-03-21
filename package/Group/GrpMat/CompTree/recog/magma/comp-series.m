/******************************************************************************
 *
 *    comp-series.m Composition Tree Series code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B��rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-30
 *
 *    Version   : $Revision:: 3165                                           $:
 *    Date      : $Date:: 2016-03-06 04:48:46 +1100 (Sun, 06 Mar 2016)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: comp-series.m 3165 2016-03-05 17:48:46Z jbaa004                $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "recog.m" : FactorInfo, NodeTypes, RecogError;
import "classical.m" : NonSimpleClassicalNames;

// Error that indicates a composition factor failure
FactorError := recformat<
    Description : MonStgElt, 
    Error : Any>;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

// Recursively set the FactorData member of all nodes in the tree
// Use FindFactors procedures that the node has set
procedure FindCompositionSeries(~node)
    if node`Type eq NodeTypes`internal then
	FindCompositionSeries(~node`Image);
	FindCompositionSeries(~node`Kernel);
    end if;
    
    vprint CompositionTree, 1 : "Find factor data at depth", node`Depth;
    assert assigned node`FindFactors;
    
    node`FindFactors(~node);
    assert assigned node`FactorData`ToFactor;
    assert assigned node`FactorData`FactorSLPs;
    assert assigned node`FactorData`FactorToSLP;
end procedure;

// Create root`FactorData`Series and root`FactorData`FromFactor
procedure CompositionSeriesFromTree(~root)
    vprint CompositionTree, 1 : "Obtain composition factor data";
    FindCompositionSeries(~root);

    vprint CompositionTree, 1 : "Obtain composition factor generators";
    
    // Obtain all composition factor generators as group elements
    // Evaluate all factor generator SLPs in one hit
    
    root`FactorData`FactorGens := Evaluate(&cat root`FactorData`FactorSLPs,
	    UserGenerators(root`NiceData`Group));
	
    // Record number of factor generators, for series construction
    factorGenSizes := [#slps : slps in root`FactorData`FactorSLPs];

    // Insert trivial group at the beginning
    series := [sub<root`NiceData`Group | >];
    
    // Maps from factor standard copies to group
    fromFactorMaps := [* *];
    stopIdx := 0;

    vprint CompositionTree, 1 : "Build up composition series";
    
    // Construct composition series
    for i in [1 .. #factorGenSizes] do
	// Indices of generators of this factor
	startIdx := stopIdx + 1;
	stopIdx := startIdx + factorGenSizes[i] - 1;
	
	// Obtain next supergroup in series
	seriesGroup := sub<Generic(root`NiceData`Group) |
	    UserGenerators(series[i]) cat
	    root`FactorData`FactorGens[startIdx .. stopIdx]>;

	// There may be coincidences among the generators, so that we don't
	// have equality, eg if the first factor is the centre of a classical
	// group, followed by the full classical group whose generators
	// happen to include the centre generator
	assert NumberOfGenerators(seriesGroup) le
	    NumberOfGenerators(series[i]) + factorGenSizes[i];
	
	// Setup inverse maps from factor standard copies
	W, slpEval := WordGroup(seriesGroup);
	assert NumberOfGenerators(Codomain(root`FactorData`FactorToSLP[i]))
	    eq factorGenSizes[i];

	genMap := [Index(ChangeUniverse(UserGenerators(seriesGroup),
	    Generic(seriesGroup)), g) : g in
	    root`FactorData`FactorGens[startIdx .. stopIdx]];
	assert #genMap eq factorGenSizes[i];
		
	// Put factor SLPs in correct positions
	factorSLPCoercion := hom<Codomain(root`FactorData`FactorToSLP[i]) ->
	W | [W.j : j in genMap]>;
	
	// Map element from factor standard copy
	fromFactor := hom<Codomain(root`FactorData`ToFactor[i]) ->
	seriesGroup | g :-> slpEval(factorSLPCoercion(
	    Function(root`FactorData`FactorToSLP[i])(g)))>;
	
	Append(~fromFactorMaps, fromFactor);
	Append(~series, seriesGroup);
    end for;

    vprint CompositionTree, 1 : "Composition series obtained";
    
    root`FactorData`Series := series;
    root`FactorData`FromFactor := fromFactorMaps;
end procedure;

// series is a composition series for phi(H) where H <= G
// g2slp : G -> slp group
// Obtain FactorData for H by taking quotients and pulling back to G
function PullbackCompFactors(G, g2slp, phi, series, MaxQuotientOrder)
    // Remove trivial group to make things work
    if IsTrivial(series[#series]) then
	Prune(~series);
    end if;

    factorSLPs := [];
    projections := [* *];
    gold2slp := [* *];
    
    vprint CompositionTree, 7 : "Obtain composition factors";
    for i in [1 .. #series] do
	if i lt #series then
	    // Avoid hard groups, for speed
	    if Category(series[i]) in {GrpMat, GrpPerm} and
		#series[i] / #series[i + 1] gt MaxQuotientOrder then
		error Error(rec<FactorError |
		    Description := "Order too large for quotients",
		    Error := #series[i]>);
	    end if;

	    vprint CompositionTree, 8 : "Find quotient", Category(series[i]);
	    factor, proj := quo<series[i] | series[i + 1]>;
	    vprint CompositionTree, 8 : "Found quotient";
	else
	    factor := series[i];
	    proj := IdentityHomomorphism(factor);
	end if;
	
	if IsPrime(Order(factor)) then
	    factor, reduction := AbelianGroup(factor);
	else
	    if Category(factor) eq GrpPerm then
		factor, reduction := DegreeReduction(factor);
	    else
		reduction := IdentityHomomorphism(factor);
	    end if;
	end if;
	
	vprint CompositionTree, 8 : "Map generators";
	
	// Find pre-images of factor generators
	inv := Inverse(reduction) * Inverse(proj) * Inverse(phi);
	gens := {@ g : g in UserGenerators(factor) |
	    not IsIdentity(g) @};
	invGens := {@ inv(g) : g in gens @};
	
	vprint CompositionTree, 8 : "Remove redundant generators";
	
	// UserGenerators(factor) is sometimes bigger than Generators(factor)
	// eg if factor is GrpPerm with identity gens
	// Redefine factor to correct this
	assert SequenceToSet(UserGenerators(factor)) diff {Identity(factor)}
	    eq Generators(factor);
	assert #gens eq #(Generators(factor));
	factor := sub<factor | gens>;

	vprint CompositionTree, 8 : "Obtain generators SLPs";

	// SLPs of pre-images, and projections to factors
	slps := g2slp(IndexedSetToSequence(invGens));

	vprint CompositionTree, 8 : "Generators SLPs obtained";
	
	if Category(slps) ne SeqEnum then
	    slps := [slps];
	end if;
	Append(~factorSLPs, slps);
	projF := function(g)
	return reduction(proj(phi(g)));
    end function;
    
	Append(~projections, hom<G -> factor | 
	g :-> projF(g)>);
	
	// gold2slp must be a rule map
	W := WordGroup(factor);
	factor2slp := hom<factor -> W | UserGenerators(W)>;	
	Append(~gold2slp, hom<factor -> W | g :-> factor2slp(g)>);
    end for;
    vprint CompositionTree, 7 : "Composition factors found";
    
    return rec<FactorInfo |
	FactorSLPs := Reverse(factorSLPs),
	ToFactor := Reverse(projections),
	FactorToSLP := Reverse(gold2slp),
	Refined := true>;    
end function;

function PullbackSocleFactors(G, g2slp, phi, factors)    
    projections := [* *];
    gold2slp := [* *];
    factorSLPs := [];

    if #factors gt 0 then
	_, incs, projs := DirectProduct(factors);
	for i in [1 .. #incs] do
	    inc := incs[i] * Inverse(phi);
	    
	    gens := {@ g : g in UserGenerators(factors[i]) |
		not IsIdentity(g) @};
	    incGens := {@ inc(g) : g in gens @};
	    
	    // UserGenerators(factor) is sometimes bigger than
	    // Generators(factor) eg if factor is GrpPerm with identity gens
	    // Redefine factor to correct this
	    assert SequenceToSet(UserGenerators(factors[i])) diff
		{Identity(factors[i])} eq Generators(factors[i]);
	    assert #incGens eq #(Generators(factors[i]));

	    factor := sub<factors[i] | gens>;
	    W := WordGroup(factor);
	    
	    Append(~projections, hom<G -> factors[i] |
	    g :-> (phi * projs[i])(g)>);

	    // gold2slp must be a rule map
	    W := WordGroup(factor);
	    factor2slp := hom<factor -> W | UserGenerators(W)>;
	    Append(~gold2slp, hom<factor -> W | g :-> factor2slp(g)>);
	    
	    // SLPs of pre-images of factor generators
	    slps := g2slp(IndexedSetToSequence(incGens));
	    if Category(slps) ne SeqEnum then
		slps := [slps];
	    end if;
	    
	    Append(~factorSLPs, slps);
	end for;
    end if;
    
    return rec<FactorInfo |
	FactorSLPs := factorSLPs,
	ToFactor := projections,
	FactorToSLP := gold2slp,
	Refined := true>;    
end function;

// Find composition series of node`NiceData`Group using built-in machinery    
function CompositionSeriesC9Projective(H, g2slp, scalar, MaxQuotientOrder,
    verify, MaxVerifyOrder)
	
    // In case it wasn't used earlier
    vprint CompositionTree, 5 : "Set base and order on extended group";
    G := sub<Generic(H) | H, scalar>;
    if Category(H) eq GrpMat then
	flag, base := HasAttribute(H, "Base");
	if flag then
	    AssertAttribute(G, "Base", base);
	    n := scalar in H select #H else #H * scalar;
	    AssertAttribute(G, "Order", n);
	end if;
    end if;
    
    vprint CompositionTree, 5 : "Random Schreier on whole group";
    RandomSchreier(G);
    if verify or #G le MaxVerifyOrder then
	vprint CompositionTree, 5 : "Verify BSGS";
	Verify(G);
    end if;
    
    vprint CompositionTree, 5 : "Find soluble radical and quotient";   
    // N is the soluble radical at the bottom, RQ is above
    RQ, phi, N := RadicalQuotient(G);
    
    vprint CompositionTree, 5 : "Find socle and quotient";
    // Split radical quotient into socle S and SQ on top
    SQ, psi, S := SocleQuotient(RQ);

    assert {Category(SQ), Category(RQ)} eq {GrpPerm};
    assert Category(N) in {GrpMat, GrpPerm};

    vprint CompositionTree, 5 : "Obtain PC-presentation of soluble radical";
    PN, NtoPC := PCGroup(N);
    
    // Only part of the scalar may lie in H    
    scalarN := NtoPC(scalar);
    PQ, quotN := quo<PN | scalarN>;

    groups := [* PQ, S, SQ *];
    maps := [* NtoPC * quotN, phi, phi * psi *];
        
    vprint CompositionTree, 5 : "Find comp series for pieces";
    factorData := [PullbackCompFactors(G, g2slp,
	maps[i], CompositionSeries(groups[i]), MaxQuotientOrder)
	: i in [1 .. 3] | not IsTrivial(groups[i])];
        
    vprint CompositionTree, 5 : "Brute force comp series found";
        
    return rec<FactorInfo |
	FactorSLPs := &cat[data`FactorSLPs : data in factorData],
	ToFactor := &cat[data`ToFactor : data in factorData],
	FactorToSLP := &cat[data`FactorToSLP : data in factorData],
	Refined := true>;
end function;

// Find composition series of node`NiceData`Group using built-in machinery
// This assumes that the group is simple modulo scalars
function CompositionSeriesC9Simple(H, g2slp, scalar, MaxQuotientOrder,
    verify, MaxVerifyOrder)
	
    // In case it wasn't used earlier
    vprint CompositionTree, 5 : "Set base and order on extended group";
    G := sub<Generic(H) | H, scalar>;
    if Category(H) eq GrpMat then
	flag, base := HasAttribute(H, "Base");
	if flag then
	    AssertAttribute(G, "Base", base);
	    n := scalar in H select #H else #H * scalar;
	    AssertAttribute(G, "Order", n);
	end if;
    end if;
    
    vprint CompositionTree, 5 : "Random Schreier on whole group";
    RandomSchreier(G);
    vprint CompositionTree, 5 : "Group order", #G;
    if verify or #G le MaxVerifyOrder then
	vprint CompositionTree, 5 : "Verify BSGS";
	Verify(G);
    end if;
    
    vprint CompositionTree, 5 : "Find soluble radical and quotient";   
    // N is the soluble radical at the bottom, RQ is above
    RQ, phi, N := RadicalQuotient(G);
    
    assert Category(RQ) eq GrpPerm;
    assert Category(N) in {GrpMat, GrpPerm};

    vprint CompositionTree, 5 : "Obtain PC-presentation of soluble radical";
    PN, NtoPC := PCGroup(N);
    
    // Only part of the scalar may lie in H    
    scalarN := NtoPC(scalar);
    PQ, quotN := quo<PN | scalarN>;

    groups := [* PQ, RQ *];
    maps := [* NtoPC * quotN, phi *];
        
    vprint CompositionTree, 5 : "Find comp series for pieces";
    factorData := [];

    if not IsTrivial(groups[1]) then
	// Find soluble radical factors
	Append(~factorData, PullbackCompFactors(G, g2slp,
	    maps[1], CompositionSeries(groups[1]), MaxQuotientOrder));
    end if;

    if not IsTrivial(RQ) then
	// Socle consists of unique simple group
	Append(~factorData,	PullbackCompFactors(G, g2slp,
	    maps[2], [RQ, sub<RQ | >], MaxQuotientOrder));
    end if;
    
    vprint CompositionTree, 5 : "Brute force comp series found";
    
    return rec<FactorInfo |
	FactorSLPs := &cat[data`FactorSLPs : data in factorData],
	ToFactor := &cat[data`ToFactor : data in factorData],
	FactorToSLP := &cat[data`FactorToSLP : data in factorData],
	Refined := true>;
end function;

// Find composition series by splitting the group into 3 pieces
procedure CompositionSeriesC9LeafProjective(~node)
    // If group is named it must be simple modulo scalars,
    // since the C9 reduction has been applied
    // (unless it is a non-simple C8 classical group)
    
    if assigned node`LeafData`Name and
        exists{name : name in NonSimpleClassicalNames | 
                      name cmpeq node`LeafData`Name} eq false then 
	node`FactorData := CompositionSeriesC9Simple(node`NiceData`Group,
	    node`SLPMaps`EltToSLPBatch, node`Scalar, node`MaxQuotientOrder,
	    node`Verify, node`MaxBSGSVerifyOrder);
    else
	node`FactorData := CompositionSeriesC9Projective(node`NiceData`Group,
	    node`SLPMaps`EltToSLPBatch, node`Scalar, node`MaxQuotientOrder,
	    node`Verify, node`MaxBSGSVerifyOrder);
    end if;
    
    node`FactorData`FactorLeaves :=
	[node : i in [1 .. #node`FactorData`ToFactor]];
end procedure;
