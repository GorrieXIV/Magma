freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//               POLYNOMIAL RINGS AND FUNCTIONS ON CURVES         //
//                          David Kohel                           //
//                       Created May 2000                         //
//                                                                //
////////////////////////////////////////////////////////////////////


// These conflict with general scheme functions or else should 
// be done generically for curves. --DRK 2002

// Transferred DivisionFunction/DivisionPsi to here from
//  C-level.

intrinsic DivisionFunction(E::CrvEll, n :: RngIntElt) -> FldFunFracSchElt
{ Returns the nth division polynomial as an element of the curve's
 function field.}
    require HasFunctionField(E) : 
		"Curve must be able to have a function field computed";
    F := FunctionField(E);
    P2 := Ambient(E);
    fx := F!(P2.1/P2.3);
    pn,pn1 := DivisionPolynomial(E,n);
    if IsOdd(n) then
	return Evaluate(pn,fx);
    else
	fy := F!(P2.2/P2.3);
	a1,_,a3 := Explode(aInvariants(E));
	return Evaluate(pn1,fx)*(fy+fy+a1*fx+a3);
    end if;
end intrinsic;

intrinsic DivisionPsi(E::CrvEll, n :: RngIntElt) -> FldFunFracSchElt
{ Returns the nth division polynomial as an element of the curve's
 function field.}
    return DivisionFunction(E,n);
end intrinsic;

