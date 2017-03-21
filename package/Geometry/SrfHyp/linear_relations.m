// *********************************************************************
// * Package: linear_relations.mag                                     *
// * =============================                                     *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 2.12.11.2005                                              *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Transform linear relations by descending a tower of field       *
// *   extensions.                                                     *
// *                                                                   *
// * Example call:                                                     *
// * -------------                                                     *
// *                                                                   *
// *   Attach("linear_relations.mag");                                 *
// *   Q := Rationals();                                               *
// *   Qi<i> := NumberField(R.1^2+1) where R is PolynomialRing(Q);     *
// *   QiX<X> := FunctionField(Qi);                                    *
// *   QiXY<Y> := FunctionField(X^2 + R.1^2 - 1)                       *
// *              where R is PolynomialRing(QiX);                      *
// *   QiXYZ<Z> := FunctionField(R.1^2 - 3)                            *
// *               where R is PolynomialRing(QiXY);                    *
// *                                                                   *
// *   // define some relations                                        *
// *   V := VectorSpace(QiXYZ, 2);                                     *
// *   r0 := [ V ! [(X+i)*(X-1)/(X-i-1), (X-1)/(X+i)],                 *
// *           V ! [Y^2 - Y - 3, Y], V ! [1, Z] ];                     *
// *                                                                   *
// *   // this produces an error                                       *
// *   TransformRelations(FiniteField(2), r0);                         *
// *                                                                   *
// *   // step wise transformation                                     *
// *   r1 := TransformRelations(QiXY, r0);                             *
// *   r2 := TransformRelations(QiX, r1);                              *
// *   r3 := TransformRelations(Qi, r2);                               *
// *   r4 := TransformRelations(Q, r3); r4;                            *
// *                                                                   *
// *   // the same in one stroke                                       *
// *   TransformRelations(Q, r0);                                      *
// *                                                                   *
// *   // another example                                              *
// *   F<M,N> := FunctionField(R.1^2 + R.2^2 - 1)                      *
// *             where R is PolynomialRing(Q,2);                       *
// *   W := VectorSpace(F, 2);                                         *
// *   s0 := [ W ! [M, N] ];                                           *
// *   TransformRelations(Q, s0);                                      *
// *                                                                   *
// *********************************************************************

freeze;




// ======================================
// = Auxillary functions (not exported) =
// ======================================

// transform sequence of relations over algebraic extension fields
// ---------------------------------------------------------------
// input:  a sequence 'relations' of vectors over an algebraic
//         extension field
// output: an equivalent sequence of relations over the ground field
function TransformRelationsAlgExt(relations)
	// early abort
	if (# relations eq 0) then return []; end if;
	
	// extract info on field extension
	V := Universe(relations); F := CoefficientField(V);
	if (Type(F) eq FldNum) then E := BaseField(F);
	else  E := BaseRing(F); end if;
	
	// new relations as vector space
	nRel := Degree(V); Rel := VectorSpace(E, nRel);
	
	// transform every relation
	nrel := []; for rel in relations do
		
		// find basis representation
		hlp := [ ElementToSequence(rel[i]) : i in [1..nRel]];
		
		// produce new relations
		for i := 1 to Degree(F) do
			r := Rel ! 0; for j := 1 to nRel do
				r[j] := hlp[j][i];
			end for;
			if not IsZero(r) then
				Append(~nrel, r);
			end if;
		end for;
	end for;
	
	return nrel;
end function;


// transform sequence of relations over univariate function field
// ---------------------------------------------------------------
// input:  a sequence 'relations' of vectors over a univariate
//         function field
// output: an equivalent sequence of relations over the ground field
function TransformRelationsTransExt(relations)
	// early abort
	if (# relations eq 0) then return []; end if;
	
	// extract info on field extension
	V := Universe(relations); F := CoefficientField(V); E := BaseRing(F);
	
	// new relations as vector space
	nRel := Degree(V); Rel := VectorSpace(E, nRel);
	
	// transform every relation
	nrel := []; for rel in relations do
		
		// extract content from relation
		g := 1;
		for i := 1 to nRel do g := Lcm(g,Denominator(rel[i])); end for;
		rel2 := V ! 0;
		for i := 1 to nRel do rel2[i] := rel[i] * g; end for;
		
		g := 0;
		for i := 1 to nRel do g := Gcd(g, Numerator(rel2[i])); end for;
		rel3 := V ! 0;
		if (not g eq 0) then
			for i := 1 to nRel do rel3[i] := rel2[i] / g; end for;
		end if;
		
		// find basis representation
		num := 0;
		for i := 1 to nRel do
			num := Max(num, Degree(rel3[i]));
		end for;
		
		hlp := [];
		for i := 1 to nRel do
			seq := [];
			for j := 0 to num do
				Append(~seq,Coefficient(Numerator(rel3[i]),j));
			end for;
			Append(~hlp, seq);
		end for;
		
		// produce new relations
		for j := 1 to num+1 do
			r := Rel ! 0;
			for i := 1 to nRel do
				r[i] := hlp[i][j];
			end for;
			if not IsZero(r) then
				Append(~nrel, r);
			end if;
		end for;
	end for;
	
	return nrel;
end function;




// ======================
// = Exported functions =
// ======================

intrinsic TransformRelations(E::Fld, rels::[ModTupFldElt])
-> SeqEnum
{
Transform the sequence 'rels' of relations (given as vectors) over a
finitely generated field extension of 'E' to an equivalent sequence of
relations over 'E'.
}
	// early abort
	if (# rels eq 0) then return []; end if;
	
	// extract info on field extension
	V := Universe(rels); F := CoefficientField(V);
	
	// finished?
	if (Type(F) eq Type(E) and F eq E) then return rels; end if;
	
	// cannot decompose the field of rationals
	require not (Type(F) eq FldRat and F eq Rationals()):
		"couldn't find 'E' in field tower";
	
	// rational function field?
	if (Type(F) eq FldFunRat) then
		return TransformRelations(E, TransformRelationsTransExt(rels));
	end if;
	
	// number field?
	if (Type(F) eq FldNum) then
		return TransformRelations(E, TransformRelationsAlgExt(rels));
	end if;
	
	// algebraic function field?
	if (Type(F) eq FldFun) then
		if (Degree(F) eq Infinity()) then
			// infinite degree extension
			F2 := RationalExtensionRepresentation(F);
			V2, hom := ChangeRing(V, F2);
			rels := [ hom(x) : x in rels ];
		end if;
		// finite degree extension
		return TransformRelations(E, TransformRelationsAlgExt(rels));
	end if;
	
	error "No idea about that extension!";
end intrinsic;
