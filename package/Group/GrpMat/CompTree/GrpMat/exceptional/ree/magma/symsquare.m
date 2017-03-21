/******************************************************************************
 *
 *    symsquare.m    Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-05-31
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: symsquare.m 1605 2008-12-15 09:05:48Z jbaa004                  $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose ReeSymSquare, 10;

import "../../../util/basics.m" : getMapFunction;
import "ree.m": ReeReductionFormat, ReeReductionMaps;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeSymmetricSquareDecompose(G :: GrpMat :
    CheckInput := true) -> Map
    { G \leq GL(27, q) is isomorphic to Ree(q). Return an
    isomorphism to Ree(q). }
    local M, E, j, preDim, homo, recognition, flag, H;
    
    if CheckInput then
	if Degree(G) ne 27 then
	    error "Ree sym square: G is not a 27-dim Ree group";
	end if;
	recognition := ReeGeneralRecogniser(G);
	if not recognition then
	    error "Ree sym square: G is not Ree";
	end if;
    end if;

    vprint ReeSymSquare, 1: "Entering Ree symmetric square decomposition";
    vprint ReeSymSquare, 2: "Decompose degree", Degree(G);

    // Take exterior square of the symmetric square
    // This has the natural 7-dim module as a composition factor, so
    // the MeatAxe will provide an easy isomorphism
    
    M := GModule(G);
    E := ExteriorSquare(M);
    series, factors, cbm := CompositionSeries(E);
    if not exists{i : i in [1 .. #factors] | Dimension(factors[i]) eq 7} then
	error "Ree Sym square: no 7-dim module found";
    end if;
    j := Max([i : i in [1 .. #factors] | Dimension(factors[i]) eq 7]);
    
    preDim := j gt 1 select &+[Dimension(factors[i]) : i in [1 .. j - 1]]
	else 0;
    H := ActionGroup(factors[j]);

    vprint ReeSymSquare, 2: "Construct homomorphism";
    homo := hom<G -> H | x :-> Generic(H) !
    Submatrix(cbm * ExteriorSquare(x) * cbm^(-1),
	preDim + 1, preDim + 1, Degree(H), Degree(H))>;
    assert Generators(H) eq {Function(homo)(x) : x in Generators(G)};

    if not assigned G`ReeReductionData then
	G`ReeReductionData := rec<ReeReductionFormat |
	    maps := rec<ReeReductionMaps | symSquare := homo>>;
    else
	if not assigned G`ReeReductionData`maps then
	    G`ReeReductionData`maps :=
		rec<ReeReductionMaps | symSquare := homo>;
	else
	    G`ReeReductionData`maps`symSquare := homo;
	end if;
    end if;
    
    vprint ReeSymSquare, 1: "Symmetric square decomposition successful";
    return homo;    
end intrinsic;


/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/
