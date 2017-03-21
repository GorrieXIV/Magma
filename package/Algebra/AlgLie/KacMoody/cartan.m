freeze;

/* 
 * Affine Kac-Moody Lie algebras.
 *
 * (Generalized) Cartan matrices and related functions.
 *
 * Dan Roozemond, 2011
 */


intrinsic IsGeneralizedCartanMatrix(C::AlgMatElt) -> BoolElt
{ Whether C is a generalized Cartan matrix}
	n := Nrows(C);
	require Ncols(C) eq n : "Cartan matrices must be square.";
	
	return forall{i : i in [1..n] | C[i][i] eq 2}
		and forall{<i,j> : i,j in [1..n] | (i eq j) or C[i][j] le 0}
		and forall{<i,j> : i,j in [1..n] | (C[i][j] ne 0) or (C[j][i] eq 0)};
end intrinsic;


/* See if a Cartan matrix can be decomposed into smaller ones. 
  Returns (1) sequence of sequences of integers
          (2) sequence of smaller Cartan matrices
*/
function cartan_matrix_decompose(C)
	
	assert Nrows(C) eq Ncols(C);
	n := Nrows(C);
	
	//The connected component containing the k-th row
	function concomp(k)
		s := {k};
		queue := [k];
		while (#queue gt 0) and (#s ne n) do
			i := queue[1]; Remove(~queue, 1);
			for j in [1..n] do
				if j in s then continue; end if;
				if C[i][j] eq 0 then continue; end if;
				Include(~s, j);
				Append(~queue, j);
			end for;
		end while;
		return s;
	end function;
	
	//Split into components
	comps := [];
	todo := {1..n};
	while #todo gt 0 do
		k := Rep(todo);
		comp := concomp(k);
		todo := todo diff comp;
		Append(~comps, Sort(SetToSequence(comp)));
	end while;
	
	//Done
	return comps, [* Submatrix(C, c, c) : c in comps *];
end function;


/* Kac-Moody class corresponding to the indecomposable Cartan matrix C */
ispos := func<m | forall{ <i,j> : i in [1..Nrows(m)], j in [1..Ncols(m)] | m[i][j] gt 0 }>;
isneg := func<m | forall{ <i,j> : i in [1..Nrows(m)], j in [1..Ncols(m)] | m[i][j] lt 0 }>;
iszero := func<m | IsZero(m)>;

function kac_moody_class(C)
	assert IsGeneralizedCartanMatrix(C);
	assert2 #cartan_matrix_decompose(C) eq 1;
	
	n := Nrows(C);
	assert Ncols(C) eq n;
	
	if Determinant(C) eq 0 then
		/* Use silly linear algebra */
		n := Nullspace(Transpose(C));
		assert Dimension(n) gt 0;
		d := Transpose(Matrix(n.1));
	else
		/* Use LP approach :) */
		lhs := VerticalJoin(C, IdentityMatrix(Integers(), n));
		rels_pos := Transpose(Matrix([[1 : i in [1..2*n]]]));
		rels_neg := Transpose(Matrix([[-1 : i in [1..n]] cat [1 : i in [1..n]]]));
		rhs_pos := rels_pos; 
		rhs_neg := rels_neg;
		obj := Matrix([[1 : i in [1..n]]]);
		
		v, code := MinimalIntegerSolution(lhs, rels_pos, rhs_pos, obj);
		if code ne 0 then
			v, code := MinimalIntegerSolution(lhs, rels_neg, rhs_neg, obj);
			if code ne 0 then
				//Complete failure
				error "KacMoodyClass: Integer LP could not be solved";
			end if;
		end if;
		d := Transpose(Matrix(v));
	end if;
	
	//Check and return
	assert ispos(d);
	if iszero(C*d) then
		return "b", d;
	elif ispos(C*d) then
		return "a", d;
	elif isneg(C*d) then
		return "c", d;
	else
		error "KacMoodyClass: C*d is not zero, pos, or neg.";
	end if;
end function;

intrinsic KacMoodyClass(C::AlgMatElt) -> MonStgElt, ModMatRngElt
{ Returns the Kac-Moody class of the indecomposable generalized Cartan matrix C,
  as a string ("a", "b", or "c"), together with an appropriate positive column 
  vector theta/delta/alpha, and a string describing the class. }

	require IsGeneralizedCartanMatrix(C) : "C should be a generalized Cartan matrix";
	require #cartan_matrix_decompose(C) eq 1 : "KacMoodyClass is only for indecomposable Cartan matrices";
	
	return kac_moody_class(C);
end intrinsic;

intrinsic KacMoodyClasses(C::AlgMatElt) -> SeqEnum, SeqEnum, SeqEnum
{ Returns the Kac-Moody class of the generalized Cartan matrix C, as three sequences
  containing the output of KacMoodyClass for each component. }
	require IsGeneralizedCartanMatrix(C) : "C should be a generalized Cartan matrix";

	comps, Cmts := cartan_matrix_decompose(C);
	tps := []; vs := [* *]; descs := [];
	for CC in Cmts do
		t,v := KacMoodyClass(CC);
		Append(~tps, t); Append(~vs, v); 
	end for;
	
	return tps, vs, comps;
end intrinsic;

