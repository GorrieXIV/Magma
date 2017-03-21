/******************************************************************************
 *
 *    p_group.m Routines for p-group as matrix groups
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2007-11-09
 *
 *    Version   : $Revision:: 2060                                           $:
 *    Date      : $Date:: 2010-11-18 21:46:13 +1100 (Thu, 18 Nov 2010)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: p_group.m 2060 2010-11-18 10:46:13Z eobr007                    $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function Support(V, P)
    return sub<V | {v - v * p : v in Basis(V), p in Generators(P)}>;
end function;

function pGroupFlag(P) 
    V := VectorSpace(P);
    F := CoefficientRing(P);
    p := Characteristic(F);
    
    if exists{x : x in Generators (P) | IsPowerOf (Order(x), p) eq false} then
       error "Input group is not a", p,"-group";
    end if;
    
    supports := [];
    VP := V;

    // A theorem says VP < V, so loop will terminate
    repeat
	Append(~supports, VP);	
	VP := Support(VP, P);
    until Dimension(VP) eq 0;

    return supports;
end function;

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

    supports := pGroupFlag(P);
    
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

    conj := Generic(P) ! Matrix(F, Degree(P), Degree(P), basis);
    return conj^(-1);
end intrinsic;
