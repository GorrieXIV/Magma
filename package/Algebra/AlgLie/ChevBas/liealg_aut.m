freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":compute_basis_by_simp_es;

intrinsic RootAutomorphism(R::RootDtm, pi::GrpPermElt, L::AlgLie, bpos::SeqEnum, bneg::SeqEnum, bcart::SeqEnum) -> BoolElt
{ Extend the root system automorphism given by pi to the Lie algebra L of type R.
  bpos, bneg, bcart should be a Chevalley basis of L.
}
	local H, CBD, e, ee, pn, pip;

	require IsChevalleyBasis(L, R, bpos, bneg, bcart) : "bpos,bneg,bcart should be a Chevalley basis of L";
	
	if Degree(Parent(pi)) eq Rank(R) then
		pi := ExtendDynkinDiagramPermutation(R, pi);
	end if;
	if not Degree(Parent(pi)) eq 2*NumPosRoots(R) then
		error "Permutation is acting on incorrect set.";
	end if;

	H := sub<L | bcart>;
	pn := bpos cat bneg;
	CBD := NewChevBasData(R,L,H);
	CBD`EigenSpaces := [ L | pn[i^pi] : i in [1..2*NumPosRoots(R)] ];
	CBD`SCSAVectors := [ L | bcart[i^pi] : i in [1..Rank(R)]];
	CBD`IndRts := [1..2*NumPosRoots(R)];
	try
		compute_basis_by_simp_es(~CBD);
	catch e
		error "Could not compute new basis in ExtendRootAutomorphismToLie.";
	end try;
	
	if not IsChevalleyBasis(CBD) then
		error "New basis is not a ChevalleyBasis in ExtendRootAutomorphismToLie.";
	end if;
		
	Bas1 := Matrix([ Vector(v) : v in bpos cat bneg cat bcart ]);
	Bas2 := Matrix([ Vector(v) : v in CBD`BasisPos cat CBD`BasisNeg cat CBD`BasisCart ]);
	b,sol := IsConsistent(Transpose(Bas1), Transpose(Bas2));
	assert b;
	T := Transpose(sol);
	return T;
end intrinsic;
