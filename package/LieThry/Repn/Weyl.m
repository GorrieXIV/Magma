freeze;

intrinsic WeylMatrix( R::RootDtm, w::GrpPermElt ) -> Mtrx
{ The images of the simple roots of R under the action of the Weyl word w }
	M := FundamentalWeights(R);
	RA := RootAction(CoxeterGroup(R));
	for i in [1..NumberOfRows(M)] do
		M[i] := RA(M[i], w);
	end for;
	return ChangeRing(M, Rationals());
end intrinsic;

intrinsic WeylMatrix( R::RootDtm, w::SeqEnum ) -> Mtrx
{ The images of the simple roots of R under the action of the Weyl word w }
	W := CoxeterGroup(R);
	return WeylMatrix(R, &*[W.i : i in w ]);
end intrinsic;

intrinsic AlternatingWeylSum( D::LieRepDec ) -> LieRepDec
{ Alternating Weyl sum }

	D := AlternatingDominant( D );
	wtsD, mpsD := Explode(D`WtsMps);

    R := RootDatum(D);
	dimR := Dimension(R);
	out := LieRepresentationDecomposition(R);

	rho := ChangeRing(Vector([ 1 : i in [1..dimR] ]), Rationals());

	for i in [1..#wtsD] do
		wt := wtsD[i] + rho;
		mp := mpsD[i];
		orb := WeightOrbit(R, wt : Basis := "Weight"); ///// CHANGE THIS //// USE WEYL LOOP /////
		for j in [1..#orb] do
			inswt := orb[j] - rho;
			_, l := DominantWeight(R, inswt);
			AddRepresentation(~out, inswt, (IsEven(#l) select mp else -mp));
		end for;
	end for;

	return out;
end intrinsic;

intrinsic AlternatingWeylSum( R::RootDtm, v::SeqEnum) -> LieRepDec
{ Alternating Weyl sum }
	return AlternatingWeylSum( LieRepresentationDecomposition(R, v) );
end intrinsic;
intrinsic AlternatingWeylSum( R::RootDtm, v::ModTupRngElt) -> LieRepDec
{ " }
	return AlternatingWeylSum( LieRepresentationDecomposition(R, v) );
end intrinsic;

