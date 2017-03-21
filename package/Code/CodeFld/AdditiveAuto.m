freeze;
 


intrinsic PermutationGroup(C::CodeAdd) -> GrpPerm
{Return the group of permutations on the coordinates of an additive
code over GF(4)}

	/* this implementation will ork for all fields, but only this
	   permutation group, not the full auto group
	*/

    F := Alphabet(C);
    K := CoefficientField(C);

    require F eq GF(4) : "Only currently available for additive codes over GF(4)";
    
	//for general additive codes
    n := Length(C);
    k := Ngens(C);
    F := Alphabet(C);
    K := CoefficientField(C);

    m := Degree(F, K);
    p := #K;
    p1 := p - 1;

    S := Sym(n);
    Sp1 := sub<Sym(p1)|>;
    S1 := WreathProduct(WreathProduct(Sp1,sub<Sym(m)|>), S);

    G := GeneratorMatrix(C);
    G1 := KMatrixSpace(K, k, m*n) !  &cat[ Eltseq(e, K) : e in Eltseq(G) ];

    C1 := LinearCode(G1);
    A1 := AutomorphismGroup(C1);

    A2 := A1 meet S1;

    A := sub<S| {S| [(Eltseq(g)[m*i+1]-1) div m +1: i in [0..n-1]]
						: g in Generators(A2) } >;

    return A;
end intrinsic;

intrinsic PermutationGroup(Q::CodeQuantum)->GrpPerm
{Return the group of permutations on the coordinates of a
binary quantum code.}
    
    return PermutationGroup(StabiliserCode(Q));
end intrinsic;



function AdditiveAutomorphismGroupGF4Sub(C, S)
	//for GF4 codes only
	//S should either be CyclicGroup(3) (additive codes)
	// or Sym(3) (stabilzer codes)
    n := Length(C);
    k := Ngens(C);
    F := GF(4);
    K := GF(2);

    GF4 := {@ 0, 1, F.1, F.1^2 @};
    GF2 := {@ [0,0,0], [0,1,1], [1,0,1], [1,1,0] @};
    
    G := GeneratorMatrix(C);
    G1 := KMatrixSpace(K, k, 3*n) ! &cat[ GF2[Index(GF4,e)] : e in Eltseq(G)];

    C1 := LinearCode(G1);
    A1 := AutomorphismGroup(C1);

    A := A1 meet WreathProduct(S,Sym(n));

    return A;
end function;

intrinsic AutomorphismGroup(C::CodeAdd) -> GrpPerm
{Return the automorphism group of an additive code over GF(4)}
    require Alphabet(C) cmpeq GF(4) : "Only currently available for additive codes over GF(4)";

    return AdditiveAutomorphismGroupGF4Sub(C, CyclicGroup(3));	
end intrinsic;


intrinsic AutomorphismGroup(Q::CodeQuantum) -> GrpPerm
{Return the automorphism group of a binary quantum code.}

    C := StabilizerCode(Q);
    require Alphabet(C) cmpeq GF(4) : "Only currently available for binary quantum codes";

    return AdditiveAutomorphismGroupGF4Sub(C, Sym(3));	
end intrinsic;

