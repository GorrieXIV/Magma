freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                      AUTOMORPHISMS OF CONICS                       //  
//                           David Kohel                              // 
//                                                                    // 
//////////////////////////////////////////////////////////////////////// 

declare attributes CrvCon:
   QuaternionAlgebra,
   BasisMatrix;

intrinsic QuaternionAlgebra(C::CrvCon) -> AlgQuat, AlgMatElt
    {The quaternion algebra in which automorphisms of the conic C can be represented}
    // It would be preferable to be able create the quaternion algebra 
    // with standard basis [1,i,j,k] given by (D*M)^t, such that the 
    // action is via the embedding X = i, Y = j, Z = k.
    K := BaseRing(C);
    require Characteristic(K) ne 2 :
       "Not currently implemented in characteristic 2.";
    if not assigned C`QuaternionAlgebra then
	P2 := Ambient(C);
	if Type(K) in {RngInt,FldRat} then
	    f, M := LegendrePolynomial(C);
	    sgns := [ Sign(c) : c in Coefficients(f) ];   
	    if sgns ne [1,1,1] and sgns ne [-1,-1,-1] then
		f, M := ReducedLegendrePolynomial(C);
	    end if;
	else
	    f, M := LegendrePolynomial(C);
	end if;
	abc := [ MonomialCoefficient(f,P2.i^2) : i in [1..3] ];
	A := QuaternionAlgebra< K | -abc[2]*abc[3], -abc[1]*abc[3] >;
	D := DiagonalMatrix([ K | 1, 1, 1/abc[3] ]);
	C`QuaternionAlgebra := A;
	C`BasisMatrix := Transpose(D*M);
    end if;
    return C`QuaternionAlgebra, C`BasisMatrix;
end intrinsic;

intrinsic Automorphism(C::CrvCon,x::AlgQuatElt) -> MapIsoSch
    {Given a conic C and a unit a of the quaternion algebra associated to C, 
     returns the automorphism of C to corresponding to it.}
    K := BaseRing(C);
    require Characteristic(K) ne 2 :
       "Not currently implemented in characteristic 2.";
    A, B := QuaternionAlgebra(C);
    require Parent(x) cmpeq A: 
        "Argument 2 must be an element of the " * 
        "quaternion algebra of argument 1.";
    require IsUnit(x) : "Argument 2 must be invertible.";
    // Embedd standard basis in A using basis matrix B.
    gens := [ A!([0] cat Eltseq(B[i])) : i in [1..3] ];
    // Compute the conjugation action by the quaternion x.
    imgs := [ x*y*Conjugate(x) : y in gens ];
    InvB := Adjoint(B); 
    // Pull the image elements back to coordinates basis.
    coords := Matrix([ Vector(Eltseq(z)[[2..4]])*InvB : z in imgs ]);
    return iso< C -> C | [C.i^M : i in [1..3]], [C.i^N : i in [1..3]]>
        where N := M^-1 where M := GL(3,K)!coords;
end intrinsic;
