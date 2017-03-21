freeze;

import "AltDom.m":AlternatingReflections;

function Demazure_Actual( D, nr ) //->LieRepDec
    R := RootDatum(D);
	rtact := RootAction(CoxeterGroup(R));
	r := Dimension(R); 
	rt := Vector(Root( R, nr+1 : Basis := "Weight" ));
	
	reflprms := ReflectionPermutations(R);
	
	wts_mps_out := LieRepresentationDecomposition(R);
	AltRfl := AlternatingReflections(D, nr);
	Wts, Mps := Explode(AltRfl`WtsMps);

	for i in [1..#Wts] do
		x := Wts[i]; c := Mps[i]; if (c eq 0) then continue; end if;
		Mps[i] := 0;
		repeat
		    AddRepresentation(~wts_mps_out, x, c);
			if (x[nr+1] eq 0) then break; end if; /* stop if reflection hyperplane is reached */

			x2 := rtact(x, reflprms[nr+1]);
			AddRepresentation(~wts_mps_out, x2, c); /* add weight reflected in hyperplane */

			x -:= Parent(x)!rt;
			if (x[nr+1] lt 0) then break; end if; /* stop if reflection hyperplane is passed */

			pos := Position(Wts, x);
			if (pos gt 0) then
				c +:= Mps[pos];
				Mps[pos] := 0;
			end if;
		until (c eq 0);
	end for;

	return wts_mps_out;
end function;

intrinsic Demazure( D::LieRepDec, w::GrpPermElt ) -> LieRepDec
{ Starting with D, repeatedly apply the Demazure operator
	M_w_i, taking for i the successive entries of w.

  The final result of Demazure should be the same when taking for w
  different reduced Weyl words for the same element of W.
}
    W := CoxeterGroup(RootDatum(D));
	t, h := CoxeterGroup(GrpFPCox, W);
	for i in Eltseq(h(w)) do
		D := Demazure_Actual(D, i-1);
	end for;
	return D;
end intrinsic;

intrinsic Demazure( R::RootDtm, v::SeqEnum, w::GrpPermElt ) -> LieRepDec
{ The Demazure operator for the representation with highest weight v }
	return Demazure( LieRepresentationDecomposition(R, v), w );
end intrinsic;
intrinsic Demazure( R::RootDtm, v::ModTupRngElt, w::GrpPermElt ) -> LieRepDec
{ " }
	return Demazure( LieRepresentationDecomposition(R, v), w );
end intrinsic;

intrinsic Demazure( D::LieRepDec ) -> LieRepDec
{ Equivalent to Demazure(D, LongestElement(CoxeterGroup(RootDatum(D)))) }
  return Demazure( D, LongestElement(CoxeterGroup(RootDatum(D))) );
end intrinsic;
intrinsic Demazure( W::GrpPermCox, v::SeqEnum ) -> LieRepDec
{ Equivalent to Demazure( W, v, LongestElement(W) ) }
  return Demazure( LieRepresentationDecomposition(RootDatum(W), v) );
end intrinsic;
intrinsic Demazure( W::GrpPermCox, v::ModTupRngElt ) -> LieRepDec
{ " }
  return Demazure( LieRepresentationDecomposition(RootDatum(W), v) );
end intrinsic;


