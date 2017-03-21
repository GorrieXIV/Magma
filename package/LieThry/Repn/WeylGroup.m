freeze;

/* These functions are straightforward using existing
   functionality; the only modification is the way in
   which elements are denoted.*/
   
/* From package/LieThry/GrpCox.m */
	inc := function( H, r )
		if assigned H`RootInclusion then
			return H`RootInclusion[r];
		else
			return r;
		end if;
	end function;

/* These are new */
intrinsic TransversalElt( W::GrpPermCox, x::GrpPermElt, H::GrpPermCox) -> GrpPermElt
{The transversal element in the coset x H. This procedure works because Magma automatically reduces the elements underway. }
  
	rank := Rank(H); N := NumPosRoots( Overdatum(W) );

	/* While the inverse of x sends inc(H,i) to a negative root, do... */
	while exists(i){ i : i in [1..rank] | inc(H,i)^(Inverse(x)) gt N } do 
		x := x * H.i;
	end while;
	return x;
end intrinsic;

intrinsic TransversalElt(W::GrpPermCox, Wl::GrpPermCox, x::GrpPermElt, Wr::GrpPermCox) -> GrpPermElt
{ The transversal element in Wl x Wr. This procedure works because Magma automatically reduces the elements underway. }

	rankl := Rank(Wl); rankr := Rank(Wr);
	N := NumPosRoots(Overdatum(W));
	
	while exists(i){ i : i in [1..rankl] | inc(Wl,i)^x gt N } do
		x := Wl.i * x;
	end while;
	
	while exists(i){ i : i in [1..rankr] | inc(Wr,i)^(Inverse(x)) gt N } do
		x := x * Wr.i;
	end while;
	return x;
end intrinsic;

intrinsic WeylWordFromAction( W::GrpPermCox, m::AlgMatElt ) -> GrpPermElt
{ The canonical Weyl word for the Weyl group element w, if it exists, whose action on the weight lattice is
  given by the square matrix m }
	
	rho := Vector([ CoefficientRing(m) | i : i in [1..Rank(W)] ]);
	wt, wrd := DominantWeight(W, rho*m : Basis := "Weight"); 
	candidate := Reverse(Eltseq(wrd));

	/* check if candidate is indeed ok */
	act := RootAction(W);
	wcand := &*[W.i : i in candidate];
	mcand := Matrix([ act(Root(W, i : Basis := "Root"), wcand) : i in [1..Rank(W)] ]);
	require mcand eq m : "Could not find appropriate Weyl group element";

	/* return candidate, as Weyl group element */
	return wcand;
end intrinsic;
