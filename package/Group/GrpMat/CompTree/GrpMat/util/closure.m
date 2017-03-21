/******************************************************************************
 *
 *    closure.m Normal Closure algorithm
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm and Eamonn O'Brien
 *    Dev start : 2008-05-04
 *
 *    Version   : $Revision:: 3099                                           $:
 *    Date      : $Date:: 2015-04-16 03:42:41 +1000 (Thu, 16 Apr 2015)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: closure.m 3099 2015-04-15 17:42:41Z jbaa004                    $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

forward NormalClosureGeneration;
    
/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic NormalClosureMonteCarlo(G :: GrpMat, H :: GrpMat : slpsH :=
    [Identity(WordGroup(G)) : i in [1 .. NumberOfGenerators(H)]],
    ErrorProb := 9/10, SubgroupChainLength := Degree(G)) -> GrpMat, []
    { Monte Carlo algorithm that computes generators of the normal closure of
      H in G. From the 1993 paper by Cooperman & Finkelstein.
      Math Reviews number 1235795.

      Also returns SLPs of the generators, if slpsH are supplied as SLPs of
      the generators of H in the generators of G.

      SubgroupChainLength must be an upper bound on the length of any
      subgroup chain in H. 

      The probability that the returned elements generate a proper subgroup
      of the normal closure is bounded above by ErrorProb, assuming that
      SubgroupChainLength is correctly set.
    }
    
    return NormalClosureGeneration(G, H, UserGenerators(WordGroup(G)), slpsH :
	ErrorProb := ErrorProb, SubgroupChainLength := SubgroupChainLength);
end intrinsic;

intrinsic NormalClosureMonteCarlo(G :: GrpPerm, H :: GrpPerm : slpsH :=
    [Identity(WordGroup(G)) : i in [1 .. NumberOfGenerators(H)]],
    ErrorProb := 9/10, SubgroupChainLength := Degree(G)) -> GrpPerm, []
    { Monte Carlo algorithm that computes generators of the normal closure of
      H in G. From the 1993 paper by Cooperman & Finkelstein.
      Math Reviews number 1235795.

      Also returns SLPs of the generators, if slpsH are supplied as SLPs of
      the generators of H in the generators of G.

      SubgroupChainLength must be an upper bound on the length of any
      subgroup chain in H. 

      The probability that the returned elements generate a proper subgroup
      of the normal closure is bounded above by ErrorProb, assuming that
      SubgroupChainLength is correctly set.
    }
    
    return NormalClosureGeneration(G, H, UserGenerators(WordGroup(G)), slpsH :
	ErrorProb := ErrorProb, SubgroupChainLength := SubgroupChainLength);
end intrinsic;

intrinsic NormalClosureMonteCarlo(G :: GrpMat, H :: GrpMat, slpsG :: SeqEnum,
    slpsH :: SeqEnum :
    ErrorProb := 9/10, SubgroupChainLength := Degree(G)) -> GrpMat, []
    { Monte Carlo algorithm that computes generators of the normal closure of
      H in G. From the 1993 paper by Cooperman & Finkelstein.
      Math Reviews number 1235795.

      Also returns SLPs of the generators.
      slpsG and slpsH are SLPs of the generators of G and H, in some supergroup
      of G.

      SubgroupChainLength must be an upper bound on the length of any
      subgroup chain in H. 

      The probability that the returned elements generate a proper subgroup
      of the normal closure is bounded above by ErrorProb, assuming that
      SubgroupChainLength is correctly set.
    }
    
    return NormalClosureGeneration(G, H, slpsG, slpsH : ErrorProb := ErrorProb,
	SubgroupChainLength := SubgroupChainLength);
end intrinsic;

intrinsic NormalClosureMonteCarlo(G :: GrpPerm, H :: GrpPerm, slpsG :: SeqEnum,
    slpsH :: SeqEnum :
    ErrorProb := 9/10, SubgroupChainLength := Degree(G)) -> GrpPerm, []
    { Monte Carlo algorithm that computes generators of the normal closure of
      H in G. From the 1993 paper by Cooperman & Finkelstein.
      Math Reviews number 1235795.
      
      Also returns SLPs of the generators.
      slpsG and slpsH are SLPs of the generators of G and H, in some supergroup
      of G.

      SubgroupChainLength must be an upper bound on the length of any
      subgroup chain in H. 

      The probability that the returned elements generate a proper subgroup
      of the normal closure is bounded above by ErrorProb, assuming that
      SubgroupChainLength is correctly set.
    }
    
    return NormalClosureGeneration(G, H, slpsG, slpsH : ErrorProb := ErrorProb,
	SubgroupChainLength := SubgroupChainLength);
end intrinsic;


/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function UserGenerators(G)
    return [G.i : i in [1 .. NumberOfGenerators(G)]];
end function;

// Is this really a random element from the set of subsequences?
function RandomSubSequence(elts) 
    seq := [];
    
    for x in elts do
	if Random([true, false]) then
	    Append(~seq, x);
	end if;
    end for;
    
    return seq;
end function;

function RandomSubProduct(elts, slps)
    // Take random subset of the elements
    indices := RandomSubSequence([1 .. #elts]);

    if #indices gt 0 then
	// and multiply them
	return &* elts[indices], &* slps[indices];
    else
	return Identity(Parent(elts[1])), Identity(Parent(slps[1]));
    end if;
end function;

function NormalClosureEngine(G, H, slpsG, slpsH, iterations)
    assert NumberOfGenerators(H) eq #slpsH;
    assert NumberOfGenerators(G) eq #slpsG;

    // Starting generating set
    gens := [Generic(H) | g : g in UserGenerators(H)];
    slps := [g : g in slpsH];
    gensG := [Generic(G) | g : g in UserGenerators(G)];
    
    for i in [1 .. iterations] do
	// Add generators by adding random subproducts
	g, slp_g := RandomSubProduct(gensG, slpsG);
	u, slp_u := RandomSubProduct(gens, slps);

	Append(~gens, u^g);
	Append(~slps, slp_u^slp_g);
    end for;

    C := sub<Generic(H) | gens>;
    genMap := [Index(gens, g) : g in UserGenerators(C)];

    return C, slps[genMap];
end function;

/* The black box Monte Carlo algorithm for finding the normal closure of
 * a group.
 * By Cooperman & Finkelstein
*/
function NormalClosureGeneration(G, H, slpsG, slpsH :
    SubgroupChainLength := 10, ErrorProb := 2^(-100))

    // The closure must also be trivial
    if IsTrivial(H) then
	return sub<H | >, []; 
    end if;

    // Calculation based on the original paper
    P<c> := PolynomialAlgebra(RealField());
    p := c^2 + 8 * c * (Log(ErrorProb) / SubgroupChainLength - 1) + 16;
    minMax := [r[1] : r in Roots(p)];
    assert #minMax eq 2;
    assert minMax[1] le minMax[2];
    
    // Upper bound on number of random subproducts required to increase
    // normal closure each time
    if Floor(minMax[1]) gt 4 then
	eltsPerLevel := Floor(minMax[1]);
    else
	eltsPerLevel := Max(Ceiling(minMax[2]), 5);
    end if;
    
    vprintf CompositionTree, 8 : "Add %o random subproducts as generators\n",
	SubgroupChainLength * eltsPerLevel;

    return NormalClosureEngine(G, H, slpsG, slpsH,
	SubgroupChainLength * eltsPerLevel);
end function;

