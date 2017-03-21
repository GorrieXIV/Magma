/******************************************************************************
 *
 *    p_group.m Routines for p-group as matrix groups
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2007-11-09
 *
 *    Version   : $Revision:: 1766                                           $:
 *    Date      : $Date:: 2010-02-05 13:14:45 +1300 (Fri, 05 Feb 2010)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: p_group.m 1766 2010-02-05 00:14:45Z eobr007                    $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "/usr/local/magma/package/Group/GrpPC/pgrps/unipotent.m" :
    MatrixWeight, FindIncreasePower, VectorExtract;

declare verbose PGroupUtil, 10;

forward pGroupIntersection;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

function isOnDiag(i, d)
    return i in {&+[j : j in [1 .. k]] : k in [1 .. d]};
end function;

intrinsic testIntersection(d :: RngIntElt, p :: RngIntElt,
    e :: RngIntElt) -> BoolElt
    { }

    F := GF(p, e);

    SetVerbose("PGroupUtil", 5);

    
    for i in [1 .. 100000] do
	print i;

	gens1 := [LowerTriangularMatrix([isOnDiag(i, d)
	    select 1 else Random(F) : i in [1 .. d * (d + 1) div 2]])
	    : j in [1 .. 3]];
	gens2 := [LowerTriangularMatrix([isOnDiag(i, d)
	    select 1 else Random(F) : i in [1 .. d * (d + 1) div 2]])
	    : j in [1 .. 3]] cat gens1;
	
	G := sub<GL(d, F) | gens1>;
	H := sub<Generic(G) | gens2>;
	
	//H := sub<GL(d, F) | LowerTriangularMatrix([isOnDiag(i, d) select 1
	//  else Random(F) : i in [1 .. d * (d + 1) div 2]])>;
	//H := G;
	  
	S := pGroupIntersection(G, H);
	assert S eq G meet H;
    end for;
    
    return true;
end intrinsic;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function FindIncreasePower2(weight, g, u, p)
    for i in [1 .. p] do
	w := MatrixWeight(g * u^i);
	
	if w gt weight then
	    return i, w;
	end if;
    end for;
end function;

function filterElement(g, weight, processed, weights, p)

    j := 1;
    
    while weight in weights do
	j := Index(weights, weight);
	h := processed[j];

	i, w := FindIncreasePower2(weight, g, h, p);
	g *:= h^i;
	weight := w; //MatrixWeight(g * h^i);
    end while;

    if #weights gt 0 then
	while j le #weights and weight gt weights[j] do
	    j +:= 1;
	end while;
    end if;
    
    return g, weight, j;
end function;

function pGroupBase(G)
    
    F := CoefficientRing(G);
    p := Characteristic(F);

    processed := [];
    unprocessed := [g : g in UserGenerators(G)];
    unprocessed_s := {g : g in unprocessed};

    weights_p := [];
    weights_ps := {@ @};
    weights_up := [MatrixWeight(g) : g in unprocessed];
    
    while not IsEmpty(unprocessed) do
	g_w, k := Min(weights_up);
	g := unprocessed[k];
	
	Remove(~unprocessed, k);
	Remove(~weights_up, k);
	Exclude(~unprocessed_s, g);
	
	g, g_w, k := filterElement(g, g_w, processed, weights_ps, p);
	
	if not IsIdentity(g) then
	    Insert(~processed, k, g);
	    Insert(~weights_p, k, g_w);
	    weights_ps := {@ x : x in weights_p @};

	    elements := Include({(g, x) : x in Generators(G)},
		g^p) diff ({Identity(G)} join unprocessed_s);
	    unprocessed_s join:= elements;

	    elements := SetToSequence(elements);
	    weights := [MatrixWeight(g) : g in elements];
	    
	    unprocessed cat:= elements;
	    weights_up cat:= weights;
	end if;
    end while;

    return processed, weights_p, weights_ps;
end function;

function normalisingPower(g, weight, inc)
    v := VectorExtract(weight[1], g);
    return Integers() ! (inc(v[weight[2]])[weight[3]]^(-1));
end function;

procedure normaliseBase(inc, ~base, weights)
    for i in [1 .. #base] do
	base[i] ^:= normalisingPower(base[i], weights[i], inc);
    end for;
end procedure;

function pGroupIntersectionCommonFlag(P, Q)
    
    F := CoefficientRing(P);
    p := Characteristic(F);
    V, inc := VectorSpace(F, PrimeField(F));

    vprint PGroupUtil, 3 : "Find p-group bases";
    
    baseP, _, weightsP := pGroupBase(P);
    baseQ, _, weightsQ := pGroupBase(Q);

    vprint PGroupUtil, 3 : "Normalise p-group bases";

    normaliseBase(inc, ~baseP, weightsP);
    normaliseBase(inc, ~baseQ, weightsQ);
    
    weights := IndexedSetToSequence(weightsP meet weightsQ);
    Sort(~weights);
    
    eltsIn := [];
    eltsOut := [];
    outWeights := {@ @};
    
    for weight in weights do
	g := baseP[Index(weightsP, weight)];
	h := baseQ[Index(weightsQ, weight)];

	repeat
	    if g eq h then
		Append(~eltsIn, g);
		break;
	    else
		gh := g / h;
		gh_w := MatrixWeight(gh);

		if gh_w in weights then
		    u := baseP[Index(weightsP, gh_w)];
		    v := baseQ[Index(weightsQ, gh_w)];

		    print "case1";
		    assert gh_w eq MatrixWeight(u);
		    assert gh_w eq MatrixWeight(v);
		    //print gh, u, gh_w;
		    
		    i := FindIncreasePower2(weight, gh, u / v, p);
		    g *:= u^i;
		    
		    i := FindIncreasePower2(weight, gh, u / v, p);
		    h *:= v^i;

		    assert MatrixWeight(g) gt weight;
		    assert MatrixWeight(h) gt weight;		    
		elif gh_w in outWeights then
		    idx := Index(outWeights, gh_w);

		    u := eltsOut[idx][1];
		    v := eltsOut[idx][2];		    

		    print "case2";
		    assert gh_w eq MatrixWeight(u / v);
		    
		    i := FindIncreasePower2(weight, gh, u / v, p);
		    g *:= u^i;
		    h *:= v^i;
		    
		    assert MatrixWeight(g) gt weight;
		    assert MatrixWeight(h) gt weight;
		else
		    k := normalisingPower(gh, gh_w, inc);
		    Append(~eltsOut, <g^k, h^k>);
		    Include(~outWeights, gh_w);
		    
		    break;
		end if;

		assert MatrixWeight(g / h) gt gh_w;
	    end if;
	until false;
    end for;

    return eltsIn;
end function;

function pGroupIntersection(P, Q)
    F := CoefficientRing(P);
    p := Characteristic(F);
    
    vprint PGroupUtil, 1 : "Entering p-group intersection";
    
    if exists{x : x in Generators(P) join Generators(Q) |
	IsPowerOf(Order(x), p) eq false} then
       error "Input group is not a", p,"-group";
    end if;

    vprint PGroupUtil, 2 : "Find flag of first p-group";
    
    flag := pGroupFlag(P);

    vprint PGroupUtil, 2 : "Find stabiliser of flag in other p-group";

    S := Q;
    for i in Reverse([2 .. #flag]) do
	print i;
	S := UnipotentStabiliser(S, flag[i]);
    end for;

    cbm := Generic(P) ! Reverse(RowSequence(pGroupBasis(P)));
    //cbm := pGroupBasis(P);
    
    vprint PGroupUtil, 2 : "Find intersection";
    gens := pGroupIntersectionCommonFlag(P^cbm, S^cbm)^(cbm^(-1));

    vprint PGroupUtil, 1 : "Leaving p-group intersection";
    return sub<Generic(P) | gens>;
end function;

/*
intrinsic pGroupBasis(P :: GrpMat) -> GrpMatElt
    {P is a p-subgroup of GL(d, q) where q = p^e. 
     Return a change-of-basis matrix g in GL(d, q) such 
     that P^g is lower unitriangular.
    }
    local supports, V, VP, basis, U, W, conj;
    
    V := VectorSpace(P);
    F := BaseRing (P);
    p := Characteristic (F);

    if exists{x : x in Generators (P) | IsPowerOf (Order(x), p) eq false} then
       error "Input group is not a", p,"-group";
    end if;

    MA := MatrixAlgebra(F, Degree(P));
    
    supports := [* *];
    VP := V;

    // A theorem says VP < V, so loop will terminate
    repeat
	Append(~supports, VP);	
	VP := Support(VP, P);
    until Dimension(VP) eq 0;
    
    basis := [];
    for i in Reverse([1 .. #supports]) do
	U := supports[i];
	W := sub<V | basis>;

	// Add basis elements from subspace
	for v in Basis(U) do
	    if v notin sub<V | W, basis> then
		Append(~basis, V ! v);
	    end if;
	end for;
    end for;
    conj := Generic(P) ! (MA ! basis)^(-1);
    return conj;
end intrinsic;

intrinsic IsUnipotent(G:: GrpMat) -> BoolElt 
    { return true if G is unipotent group, else false }
    F := BaseRing(G);
    require IsFinite(F): "Base field for matrix group must be finite";

    p := Characteristic(F);
    d := Degree(G);

    // Initial heuristic on generators
    for g in UserGenerators(G) do
	h := g;
	i := 1;
	
	while not IsIdentity(h) and i lt d do
	    h ^:= p;
	    i +:= 1;
	end while;

	if not IsIdentity(h) then
	    return false;
	end if;
    end for;

    M := GModule(G);
    CS, CF, cbm := CompositionSeries(M);
    
    if exists{i : i in [1 .. #CF] | Dimension(CF[i]) gt 1} then 
	return false;
    end if;
    
    cbm := Generic(G) ! cbm^(-1);
    gens := [Generic(G) ! DiagonalMatrix([g[i, i] : i in [1 .. Degree(G)]]) :
	g in UserGenerators(G^cbm)];
    return forall{g : g in gens | IsIdentity(g)};
end intrinsic;
*/
