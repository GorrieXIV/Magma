/******************************************************************************
 *
 *    slp.m    MAGMA SLP code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-08-10
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: slp.m 1605 2008-12-15 09:05:48Z jbaa004                        $:
 *
 *****************************************************************************/

freeze;
     
/*
Proposal for a new straight line program mechanism in MAGMA
-----------------------------------------------------------
The current version of MAGMA, 2.12, has a mechanism for handling groups of
straight line programs, which forms an essential part of MAGMA.
In this abstraction, each group element in a group of straight line programs
is in itself an SLP, and when two elements are combined in some way a new SLP
is formed. This can lead to duplication if the two SLPs have common parts,
and therefore the lengths of the SLPs can grow unnecessarily long, which in
turn can lead to inefficiencies when evaluating an SLP.

There is an existing mechanism for adding "redundant generators" to a group of
straight line programs, so that common parts of SLPs can be taken out and
duplication avoided, but this is a bit insufficient. It would be better if this
happened automatically.

An alternative way of thinking about a straight line program group is that it
consists of a single SLP, and that each element is a pointer into this SLP.
If we think of the SLP as a kind of tree with several roots, one root for each
generator, then an element of the SLP group is a pointer to one of the nodes.

The operations one can do are multiplication, conjugation and powering of the
elements, which amounts to adding nodes to tree, with references to one or two
previous nodes.

In this way, if two elements have common parts, they will not be duplicated,
since they are in the same SLP. To evaluate an element, start by marking which
nodes in the tree are needed, ie follow the paths from the element to the
roots. Then go through the SLP from the roots, and evaluate the marked nodes,
from the generators and back to the element. By evaluating in this bottom-up
manner, one can also evaluate several elements simultaneously without any risk
of evaluating some parts of the SLP more than once.

In the code below, each SLP node is a record, and an SLP is stored as a
sequence of records. Each SLP group element is an integer, the index of the
element in the SLP. Each node has a reference count and an 'element' field
which is used during evaluation of the SLP. The marking consists of increasing
the reference count, and during the bottom-up evaluation the count is
decreased and the 'element' field is used to store the group element which has
been evaluated for the node. When the reference count reaches 0 this 'element'
will not be needed anymore during the evaluation and can be removed, thus
making sure that the garbage collector can reclaim the memory.

A possible problem is that the SLP might become unnecessarily long. If one
plays around with an SLP group and throws away SLP group elements, they will
still be a part of the SLP. To somewhat remedy this, one can undefine the
sequence elements of the SLP that don't belong to a given list of SLP group
elements, "trim the SLP", and skip undefined elements during the evaluation.

Below is also some code to compare the existing SLP machinery with our new one.
The main concern is that evaluation of SLPs on matrix groups of large degree
should be fast, and by using the comparison code below it is clear that our
new approach is faster in this case.
*/

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

procedure Rattle(~W, ~slots1, ~slots2)
    local i, j, k;

    assert #slots1 eq #slots2;
    i := Random(1, #slots1 - 1);

    repeat
	j := Random(1, #slots1 - 1);
    until j ne i;

    k := Random(1, #slots1 - 1);
    
    slots1[i] *:= slots1[j];    
    slots1[#slots1] *:= slots1[k];

    MultiplySLP(~W, slots2[i], slots2[j], ~slp);
    slots2[i] := slp;

    MultiplySLP(~W, slots2[#slots2], slots2[k], ~slp);
    slots2[#slots2] := slp;
end procedure;

intrinsic compareSLPTypes(nGens :: RngIntElt, // Number of matrix gens
    fieldSize :: RngIntElt, // Matrix base field
    dimension :: RngIntElt, // Matrix dimension
    nOps :: RngIntElt, // Nr of SLP operations to perform before eval
    maxPower :: RngIntElt, // Max exponent when taking powers
    nEvals :: RngIntElt) // Nr of SLPs to eval
    -> BoolElt
    { }

    // Fetch random matrices to use as generators
    G := GL(dimension, fieldSize);
    
    R := RandomProcess(G);
    gens := [Random(R) : i in [1 .. nGens]];

    // Create old and new SLP groups
    W1 := SLPGroup(nGens);
    W2 := CreateSLPGroup(nGens);

    // Get SLP generators
    slp1 := [W1.i : i in [1 .. nGens]];
    slp2 := SLPGroupGenerators(W2);

    slps1 := [];
    slps2 := [];
    for i in [1 .. nOps] do
	Rattle(~W2, ~slp1, ~slp2);

	Append(~slps1, slp1[#slp1]);
	Append(~slps2, slp2[#slp2]);
    end for;
    
    print "SLP Length", #W2`SLP;

    // Choose the last elements to evaluate
    slps := [#slps1 - nEvals + 1 .. #slps1];
    assert #slps eq nEvals;
    
    t := Cputime();
    result2, maxStorage := EvaluateSLPs(W2, slps2[slps], gens);
    time1 := Cputime(t);
    print time1;
    print maxStorage;

    t := Cputime();
    result1 := Evaluate(slps1[slps], gens);
    time2 := Cputime(t);
    print time2;

    assert #result1 eq #result2;
    assert forall{i : i in [1 .. #result1] | result1[i] eq result2[i]};
    
    t := Cputime();
    result1 := [Evaluate(w, gens) : w in slps1[slps]];
    time3 := Cputime(t);
    print time3;
    
    return time1, time2, time3, maxStorage;    
end intrinsic;
    
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

// SLP Group element types
SLP_GROUP_ELT_GEN  := 0;
SLP_GROUP_ELT_MULT := 1;
SLP_GROUP_ELT_CONJ := 2;
SLP_GROUP_ELT_POW  := 3;

// SLP node structure
SLPNodeDef := recformat<
    count   : RngIntElt, // Node reference count during eval
    type    : RngIntElt, // Type of node, one of the above constants
    lParent : RngIntElt, // Index of first parent
    rParent : RngIntElt, // Index of second parent, 0 if power node
    power   : RngIntElt, // Exponent for power node
    element : GrpElt>;   // Stored evaluated element, used during eval

// SLP Group structure
SLPGroupDef := recformat<
    SLP   : SeqEnum, // The straight line program, list of SLPNodeDef records
    nGens : RngIntElt>; 

declare verbose UtilSLP, 5;
forward createSLPNode, markSLPNode, evaluateSLPNode, markSLP;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic CreateSLPGroup(nGens :: RngIntElt) -> Rec
    { Create an SLP Group with initial SLP seed. }
    
    return rec<SLPGroupDef | nGens := nGens, SLP :=
	[createSLPNode(SLP_GROUP_ELT_GEN, i, 0, 0) : i in [1 .. nGens]]>;
end intrinsic;

intrinsic SLPGroupGenerators(slpGroup :: Rec) -> []
    { Return list of SLP group generators as SLP group elements }
    
    // SLP group generators are the first elements
    return [1 .. slpGroup`nGens];
end intrinsic;

intrinsic EvaluateSLPs(slpGroup :: Rec, slpGroupElts :: SeqEnum[RngIntElt],
    gens :: SeqEnum[GrpElt]) -> []
    { Evaluate SLPs on generators }
    local nodes, elements;
    
    require #gens eq slpGroup`nGens
	and forall{i : i in slpGroupElts | i gt 0 and i le #slpGroup`SLP
	and IsDefined(slpGroup`SLP, i)} : "Wrong input";

    // Make a set for constant time lookup
    nodes := {@ e : e in Sort(slpGroupElts) @};

    // Sequence of evaluated elements
    elements := [];

    // Mark all SLP nodes that we will use
    markSLP(~slpGroup`SLP, nodes);
    
    // Number of stored group elements
    storage := 0;
    maxStorage := 0;
    
    // Evaluate all necessary SLP nodes from the start, to avoid recursion
    // ie we use dynamic programming
    for node in [1 .. #slpGroup`SLP] do
	if IsDefined(slpGroup`SLP, node) and slpGroup`SLP[node]`count gt 0 then
	    evaluateSLPNode(~slpGroup`SLP, node, gens, ~element, ~storage);

	    // Count maximum number of stored elements
	    maxStorage := Max(maxStorage, storage);	    
	end if;
    end for;

    // Fetch and delete final elements
    elements := [slpGroup`SLP[node]`element : node in nodes];    
    for node in nodes do
	delete slpGroup`SLP[node]`element;
    end for;
    assert #elements eq #nodes;
        
    return elements, maxStorage;
end intrinsic;

intrinsic TrimSLPGroup(slpGroup :: Rec,
    slpGroupElts :: SeqEnum[RngIntElt]) -> Rec
    { Remove parts of SLP group that do not involve slpGroupElts }

    require forall{i : i in slpGroupElts | i gt 0 and i le #slpGroup`SLP
	and IsDefined(slpGroup`SLP, i)} : "Wrong input";

    // Mark all SLP nodes that we will use
    for node in slpGroupElts do
	markSLPNode(~slpGroup`SLP, node);
    end for;
    
    for node in [1 .. #slpGroup`SLP] do
	// Never remove SLP generators
	if IsDefined(slpGroup`SLP, node) and node gt slpGroup`nGens and
	    slpGroup`SLP[node]`count eq 0 then
	    Undefine(~slpGroup`SLP, node);
	else
	    slpGroup`SLP[node]`count := 0;
	end if;
    end for;

    return slpGroup;
end intrinsic;

intrinsic MultiplySLP(~slpGroup :: Rec, leftSLP :: RngIntElt,
    rightSLP :: RngIntElt, ~result) 
    { Multiply the two SLPs and return product SLP }
    local node;
    
    require leftSLP gt 0 and rightSLP gt 0 and leftSLP le #slpGroup`SLP and
	rightSLP le #slpGroup`SLP and IsDefined(slpGroup`SLP, leftSLP) and
	IsDefined(slpGroup`SLP, rightSLP) : "Wrong input";
    
    node := createSLPNode(SLP_GROUP_ELT_MULT, leftSLP, rightSLP, 0);
    Append(~slpGroup`SLP, node);

    result := #slpGroup`SLP;
end intrinsic;

intrinsic ConjugateSLP(~slpGroup :: Rec, leftSLP :: RngIntElt,
    rightSLP :: RngIntElt, ~result)
    { Conjugate the two SLPs and return product SLP }
    local node;
    
    require leftSLP gt 0 and rightSLP gt 0 and leftSLP le #slpGroup`SLP and
	rightSLP le #slpGroup`SLP and IsDefined(slpGroup`SLP, leftSLP) and
	IsDefined(slpGroup`SLP, rightSLP) : "Wrong input";
    
    node := createSLPNode(SLP_GROUP_ELT_CONJ, leftSLP, rightSLP, 0);
    Append(~slpGroup`SLP, node);

    result := #slpGroup`SLP;
end intrinsic;

intrinsic PowerSLP(~slpGroup :: Rec, SLP :: RngIntElt,
    power :: RngIntElt, ~result)
    { Take the SLP to the given power }
    local node;
    
    require SLP gt 0 and power ge 0 and SLP le #slpGroup`SLP and
	IsDefined(slpGroup`SLP, SLP) : "Wrong input";
    
    node := createSLPNode(SLP_GROUP_ELT_POW, SLP, 0, power);
    Append(~slpGroup`SLP, node);

    result := #slpGroup`SLP;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

procedure evaluateSLPNode(~SLP, node, gens, ~element, ~storage)
    local left, right;
    
    assert node ge 0 and node le #SLP;

    // Allow count 0 for all fetches and initial evaluation
    assert SLP[node]`count ge 0;

    // If element not already computed, then compute it from parent nodes
    if not assigned SLP[node]`element then
	case SLP[node]`type:
	when SLP_GROUP_ELT_GEN:
	    SLP[node]`element := gens[SLP[node]`lParent];
	when SLP_GROUP_ELT_MULT:
	    evaluateSLPNode(~SLP, SLP[node]`lParent, gens, ~left, ~storage);
	    evaluateSLPNode(~SLP, SLP[node]`rParent, gens, ~right, ~storage);
	    
	    SLP[node]`element := left * right;
	when SLP_GROUP_ELT_CONJ:
	    evaluateSLPNode(~SLP, SLP[node]`lParent, gens, ~left, ~storage);
	    evaluateSLPNode(~SLP, SLP[node]`rParent, gens, ~right, ~storage);

	    SLP[node]`element := left^right;
	when SLP_GROUP_ELT_POW:
	    evaluateSLPNode(~SLP, SLP[node]`lParent, gens, ~left, ~storage);
	    
	    SLP[node]`element := left^SLP[node]`power;
	end case;

	storage +:= 1;
    end if;
    
    element := SLP[node]`element;

    // Delete computed element after all fetches
    SLP[node]`count -:= 1;
    if SLP[node]`count lt 0 then
	delete SLP[node]`element;
	storage -:= 1;
    end if;
end procedure;

procedure markSLP(~SLP, nodes)

    // Reset counts
    for i in [1 .. #SLP] do
	SLP[i]`count := 0;
    end for;

    // Go downwards from highest node that we will evaluate
    highestNode := nodes[#nodes];
    assert SLP[highestNode]`count eq 0;
    
    for node in Reverse([1 .. highestNode]) do
	if IsDefined(SLP, node) then
	    if node in nodes then
		SLP[node]`count +:= 1;
	    end if;

	    if SLP[node]`count gt 0 then
		when SLP_GROUP_ELT_MULT:
		    SLP[SLP[node]`lParent]`count +:= 1;
		    SLP[SLP[node]`rParent]`count +:= 1;
		when SLP_GROUP_ELT_CONJ:
		    SLP[SLP[node]`lParent]`count +:= 1;
		    SLP[SLP[node]`rParent]`count +:= 1;
		when SLP_GROUP_ELT_POW:
		    SLP[SLP[node]`lParent]`count +:= 1;
		end case;
	    end if;
	end if;
    end for;	    
end procedure;

function createSLPNode(type, lParent, rParent, power)
    return rec<SLPNodeDef | count := 0, type := type,
	lParent := lParent, rParent := rParent, power := power>;
end function;

