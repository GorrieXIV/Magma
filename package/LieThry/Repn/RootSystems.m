freeze;

import "../Root/RootDtm.m": basisChange;

function innerProduct(R, x, y : Basis := "Standard") //-> RngIntElt
	CM := CartanMatrix(R);
	spc := RSpace(Rationals(), Rank(R));
	CM := KMatrixSpace(Rationals(), Rank(R), Rank(R))!Matrix(CM);

	if (Basis eq "Root") then
		xb := spc!x;
		yb := spc!y;
	else
		xb := spc!basisChange(R, x, Basis, "Root", false);
		yb := Eltseq(basisChange(R, y, Basis, "Root", false));
	end if;
		
	yb := spc![ RootNorm(R, j)*yb[j] : j in [1..Rank(R)] ];

	return (xb*CM, yb);
end function;

intrinsic InnerProduct(R::RootDtm, i::RngIntElt, j::RngIntElt) -> RngIntElt
{ Return the Weyl group invariant inner product of the i-th and j-th root of R }
	return innerProduct(R, Root(R, i : Basis := "Root"), Root(R, j : Basis := "Root") : Basis := "Root");
end intrinsic;

intrinsic InnerProduct(R::RootDtm, x::SeqEnum, y::SeqEnum : Basis := "Root") -> RngIntElt
{ Return the Weyl group invariant inner product of the i-th and j-th root of R }
	return innerProduct(R, x, y : Basis := Basis);
end intrinsic;

intrinsic InnerProduct(R::RootDtm, x::ModTupFldElt, y::ModTupFldElt : Basis := "Root") -> RngIntElt
{ Return the Weyl group invariant inner product of roots x and y }
	return innerProduct(R, x, y : Basis := Basis);
end intrinsic;

intrinsic InnerProduct(R::RootDtm, x::ModTupRngElt, y::ModTupRngElt : Basis := "Root") -> RngIntElt
{ Return the Weyl group invariant inner product of roots x and y }
	return innerProduct(R, x, y : Basis := Basis);
end intrinsic;


intrinsic CentralisingRoots(R::RootDtm, t::ModTupRngElt, n::RngIntElt) -> SetEnum
{ Return the roots of R centralizing t mod n}
	rnk := Rank(R);
	fld := (n gt 0) select GF(n) else Rationals();
	sp := RSpace(fld, rnk);
	x := MatrixRing(fld, rnk)!CartanMatrix(R)*(Transpose(Matrix(sp!t)));
	res := { r : r in [1..NumPosRoots(R)] | IsZero((sp!Root(R, r : Basis := "Root"))*x) };
	return res;
end intrinsic;
