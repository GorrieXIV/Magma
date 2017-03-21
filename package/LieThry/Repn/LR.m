freeze;

function check_partition(p)
	if Type(p) eq SeqEnum then n := #p; else n := Ncols(p); end if;
	for i in [1..n] do
		if not (IsIntegral(p[i]) and p[i] ge 0) then return false; end if;
		if (i gt 1) and (p[i-1] lt p[i]) then return false; end if;
	end for;
	return true;
end function;

/*
	Littlewood-Richardson directly, so for partitions.
*/
intrinsic LittlewoodRichardsonTensor( p::SeqEnum, q::SeqEnum ) -> SeqEnum, SeqEnum
{ Littlewood-Richardson tensor of the SL_(n-1) modules (where n = #p) described by the partitions p and q }
    return LittlewoodRichardsonTensor(ChangeRing(Vector(p), Integers()), ChangeRing(Vector(q), Integers()));
end intrinsic;

intrinsic LittlewoodRichardsonTensor( p::ModTupRngElt, q::ModTupRngElt ) -> SeqEnum, SeqEnum
{ " }
	require check_partition(p) : "p = " cat Sprintf("%o", p) cat " is not a partition.";
	require check_partition(q) : "q = " cat Sprintf("%o", q) cat " is not a partition.";
	
	if CoefficientRing(p) ne Integers() then p := ChangeRing(p, Integers()); end if;
	if CoefficientRing(q) ne Integers() then q := ChangeRing(q, Integers()); end if;
	
	require Ncols(p) eq Ncols(q) : "Partitions must be of the same length.";
	
	rp, rm := WeightsAndMultiplicities(InternalLRTensor(p, q));

    return rp, rm;
end intrinsic;

/*
	Littlewood-Richardson directly, for ``partition multisets''
*/
intrinsic LittlewoodRichardsonTensor(P::SeqEnum, M::SeqEnum[RngIntElt], Q::SeqEnum, N::SeqEnum[RngIntElt]) -> SeqEnum, SeqEnum
{ Littlewood-Richardson tensor of the SL_(n-1) modules described by the ``partition multisets'' 
  (P, M) and (Q, N)}

	require #P eq #M: "(P,M) is not a partition multiset.";
	require #Q eq #N: "(P,M) is not a partition multiset.";
	
	P2 := [ ChangeRing(Vector(p), Integers()) : p in P ];
	Q2 := [ ChangeRing(Vector(p), Integers()) : p in Q ];
	require Degree(Universe(P2)) eq Degree(Universe(Q2)) : "P and Q are not compatible.";
	if exists(i){i : i in [1..#P2] | not check_partition(P2[i])} then error Sprintf("P[%o]", i) cat " is not a partition."; end if;
	if exists(i){i : i in [1..#Q2] | not check_partition(Q2[i])} then error Sprintf("Q[%o]", i) cat " is not a partition."; end if;

	//We use a weight multiset here to aggregate the results, 
	//but it doesn't have any actual meaning as a weight multiset!
	n := Degree(Universe(P2));
	RT := RootDatum("T" cat IntegerToString(n));
	tmp := LieRepresentationDecomposition(RT);
	NP := #P2; NQ := #Q2;
	for i in [1..NP] do 
		partP := P2[i]; mpP := M[i];
		for j in [1..NQ] do 
			partQ := Q2[j]; mpQ := N[j];
			t := InternalLRTensor(partP, partQ);
			AddRepresentation(~tmp, t, mpP*mpQ);
		end for;
	end for;
	
	//return pair of sequences
	R, O := WeightsAndMultiplicities(tmp);
	return R, O;
end intrinsic;

/*
	Littlewood-Richardson indirectly, so including conversion of weights to partitions and back
*/
intrinsic LittlewoodRichardsonTensor(D::LieRepDec, E::LieRepDec) -> LieRepDec
{ Compute the tensor product of D and E using the Littlewood-Richardson rule. }

	//0. check.
	R := RootDatum(D);
	require R eq RootDatum(E) : "RootData of representations must be the same.";
	require IsIrreducible(R) and  CartanName(R)[1] eq "A" : "R must be an irreducible root datum of type A_n";

	//1. Convert D and E to partitions
	wtsD, mpsD := WeightsAndMultiplicities(D);
	partsD := [ WeightToPartition(w) : w in wtsD ];
	wtsE, mpsE := WeightsAndMultiplicities(E);
	partsE := [ WeightToPartition(w) : w in wtsE ];
	
	//2. Do Littlewood-Richardson
	partsR, mpsR := LittlewoodRichardsonTensor(partsD, mpsD, partsE, mpsE);
	
	//3. Convert back
	wtsR := [ PartitionToWeight(p) : p in partsR ];
	
	//return.
	return LieRepresentationDecomposition(R, wtsR, mpsR);
end intrinsic;

intrinsic LittlewoodRichardsonTensor(R::RootDtm, v::SeqEnum, w::SeqEnum) -> LieRepDec
{ Compute the tensor product of the R-modules with highest weights v and w using the
  Littlewood-Richardson rule }
	D := LieRepresentationDecomposition(R, v);
	E := LieRepresentationDecomposition(R, w);
	return LittlewoodRichardsonTensor(D, E);
end intrinsic;

intrinsic LittlewoodRichardsonTensor(R::RootDtm, v::ModTupRngElt, w::ModTupRngElt) -> LieRepDec
{ " }
	D := LieRepresentationDecomposition(R, v);
	E := LieRepresentationDecomposition(R, w);
	return LittlewoodRichardsonTensor(D, E);
end intrinsic;

