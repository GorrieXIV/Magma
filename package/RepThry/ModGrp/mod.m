freeze;

/*******************************************************************************
				Permutation modules
*******************************************************************************/

num_fixed_pts := func<g | Degree(Parent(g)) - Degree(g)>;

function PermChar(G)
    return CharacterRing(G)![num_fixed_pts(t[3]): t in Classes(G)];
end function;

intrinsic PermutationModule(G::GrpPerm, R::Rng: SetCharacter) -> ModGrp
{The natural permutation G-module of G over the ring R}

    M := InternalPermutationModule(G, R);

    if SetCharacter and Characteristic(R) eq 0 then
	M`Character := PermChar(G);
    end if;

    return M;

end intrinsic;

intrinsic GModule(G::GrpPerm, R::Rng: SetCharacter) -> ModGrp
{The natural permutation G-module of G over the ring R}
    return PermutationModule(G, R: SetCharacter := SetCharacter);
end intrinsic;

/*******************************************************************************
				Tensor
*******************************************************************************/

intrinsic TensorProduct(M::ModGrp, N::ModGrp) -> ModRng
{The tensor product of M and N (obtained by taking the tensor product of
each action generator of M by the corresponding action generator of N)}

    require IsIdentical(Group(M), Group(N)): "Incompatible groups";
    require IsIdentical(BaseRing(M), BaseRing(N)): "Incompatible base rings";

    T := InternalTensorProductDirect(M, N);

    if assigned M`Character and assigned N`Character then
	T`Character := M`Character * N`Character;
    end if;

    return T;

end intrinsic;
