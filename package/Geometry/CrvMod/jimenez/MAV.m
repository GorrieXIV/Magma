//3/12/2011
freeze;

/**************************************************
*                                                 *                                                                    
*        Enrique Gonzalez-Jimenez                 *         
*                                                 *                           
*   FILE: MAV.m (Modular Abelian Varieties)       *                              
*                                                 *
**************************************************/

//----------------------------------------------------------------------------
intrinsic Af(N::RngIntElt : subspace:=+1) -> ModSym
{
The decomposition over Q of Jo(N)^new.
}

	M:=ModularSymbols(N,2,subspace);
	NN:=SortDecomposition(NewformDecomposition(NewSubspace(CuspidalSubspace(M))));

	return NN;

end intrinsic;
//----------------------------------------------------------------------------
intrinsic Af(eps::GrpDrchElt : subspace:=+1) -> ModSym
{
The decomposition over Q of the subvariety of J_1(N)^new corresponding to S_2(N,eps)^new. In the +1 subspace
}

	M:=ModularSymbols(eps,2,subspace);
	NN:=SortDecomposition(NewformDecomposition(NewSubspace(CuspidalSubspace(M))));

	return NN;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////

function DirichletGroupGalois(N)
/*
Representatives for the Gal(Qbar/Q)-conjugacy classes of Dirichlet characters of level N.
*/
	G:=DirichletGroup(N,CyclotomicField(EulerPhi(N)));
	G:=GaloisConjugacyRepresentatives(G);
	//G:=<MinimalBaseRingCharacter(g) : g in G>;

	return G;

end function;


function DirichletGroupGaloisEven(N)
/*
Representatives for the Gal(Qbar/Q)-conjugacy classes of even Dirichlet characters of level N.
*/
	G:=DirichletGroupGalois(N);

	return <g :g in G | IsEven(g)>;

end function;


function Chi(N)
/*
Vectors of the Representatives for the Gal(Qbar/Q)-conjugacy classes of even Dirichlet characters of level N
*/
	G:=DirichletGroupGaloisEven(N);
	K:=Sort([<Order(G[k]),k> : k in [1..#G]]);
	KK:=[k[2] : k in K];

	return <Eltseq(G[k]) : k in KK>;
end function;


function chi(N,seq)
/*
Dirichlet character of level N corresponding to the sequence seq, in its minimal base ring.
*/
	
	G:=DirichletGroup(N,CyclotomicField(EulerPhi(N)));
	assert #seq eq #Generators(G);

        return MinimalBaseRingCharacter(G!seq);

end function;

