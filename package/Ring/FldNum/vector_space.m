freeze;
 

function GetBasis(F, E)

    // find C 
    C := Rationals();
    FC := F;
    EC := E;
    while FC ne C and EC ne C do
	if AbsoluteDegree(FC) gt AbsoluteDegree(EC) then
	    FC := CoefficientField(FC);
	elif AbsoluteDegree(FC) lt AbsoluteDegree(EC) then
	    EC := CoefficientField(EC);
	elif FC eq EC then
	    C := FC;
	    break;
	else
	    FC := CoefficientField(FC);
	    EC := CoefficientField(EC);
	end if;
    end while;

    deg_F_o_C := AbsoluteDegree(F) div AbsoluteDegree(C);
    deg_E_o_C := AbsoluteDegree(E) div AbsoluteDegree(C);

    // find primitive element of F over C 
    repeat
	x := Random(F, 2);
	M := Matrix(
	     C, deg_F_o_C, deg_F_o_C, [Eltseq(x^i, C) : i in [1 .. deg_F_o_C]]
	     );
    until Determinant(M) ne 0;

    return [x^i : i in [0 .. deg_F_o_C div deg_E_o_C - 1]];

end function;

intrinsic InternalVectorSpace(F::FldAlg, E::Fld) -> ModTupFld, Map
{}
    require Type(E) eq FldRat or IsSubfield(E, F) : 
				"Argument 2 must be a subfield of argument 1";
    return VectorSpace(F, E, GetBasis(F, E));

end intrinsic;

intrinsic VectorSpace(F::FldAlg, E::Fld) -> ModTupFld, Map
{}
    require Type(E) eq FldRat or IsSubfield(E, F) : 
				"Argument 2 must be a subfield of argument 1";
    return InternalVectorSpace(F, E);
end intrinsic;

intrinsic VectorSpace(F::FldRat, E::Fld) -> ModTupFld, Map
{}
    require Type(E) eq FldRat : 
				"Argument 2 must be a subfield of argument 1";
    V := VectorSpace(E,1);
    mp := map<F->V | x :-> x*V.1, y :-> y[1]>;
    return V,mp;
end intrinsic;

intrinsic InternalAlgebra(F::FldAlg, E::Fld) -> AlgAss, Map
{}
    require Type(E) eq FldRat or IsSubfield(E, F) : 
				"Argument 2 must be a subfield of argument 1";
    return Algebra(F, E, GetBasis(F, E));
end intrinsic;

intrinsic Algebra(F::FldAlg, E::Fld) -> AlgAss, Map
{}
    require Type(E) eq FldRat or IsSubfield(E, F) : 
				"Argument 2 must be a subfield of argument 1";
    return InternalAlgebra(F, E);
end intrinsic;

intrinsic Algebra(F::FldRat, E::Fld) -> AlgAss, Map
{}
    require Type(E) eq FldRat : 
				"Argument 2 must be a subfield of argument 1";
    A := AssociativeAlgebra<E,1|[1] : Check := false>;
    mp := map<F->A | x :-> x*A.1, y :-> y[1]>;
    return A,mp;
end intrinsic;
