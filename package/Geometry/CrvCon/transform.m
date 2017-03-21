freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  CONIC MODELS FOR GENUS ZERO CURVES                //
//                        David Kohel, 2002/06                        //   
//                                                                    //
////////////////////////////////////////////////////////////////////////


intrinsic Conic(C::Crv) -> CrvCon, MapIsoSch
    {The conic C1 given by the (anti-)canonical embedding 
    of the genus zero curve C in the projective plane,
    followed by the birational isomorphism from C to C1.}
    // First see if there is an easy way out:
    bool, C1 := IsConic(C);
    if bool then
	funs := [P2.i : i in [1..3]] where P2 := Ambient(C);
	return C1, map< C -> C1 | funs, funs : Check:=false >;
    end if;
    K := BaseRing(C); 
    require IsField(K) : "Base ring of argument must be a field.";
    require IsProjective(C) : "Argument must be a projective model.";
    require HasFunctionField(C):
       "Argument must be irreducible and reduced";
    require Genus(C) eq 0 : "Argument must have genus 0";
    phi := DivisorMap(-CanonicalDivisor(C));
    fncs := DefiningEquations(phi);
    if #fncs ne 3 then
	F := ExactConstantField(AlgorithmicFunctionField(FunctionField(C)));
	geom_irred := (F cmpeq K);
	require geom_irred : "Argument is not geometrically irreducible";
	//else ?
	error "Sorry. Some unknown problem has occurred";
    end if;
    C1 := phi(C);
    bool,C2 := IsConic(C1);
    phi := Restriction(phi,C,C2);
    // To save potential trouble in case C is in multi-graded space
    // (which IsInvertible currently rejects), replace C by its
    // function field patch [we know that this exists & that C is integral].
    psi := map<Ca->C|DefiningPolynomials(ProjectiveClosureMap(Ambient(Ca)))>
		where Ca is AffinePatch(C,FFPatchIndex(C));

    flag, phii := IsInvertible(Expand(psi*phi));
    assert flag;

    phii := Expand(phii*psi);
    phi := map< C -> C2 | fncs, DefiningPolynomials(phii) >;
    return C2, phi;
end intrinsic;

