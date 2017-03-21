freeze;

/* 
 * Dan Roozemond, 2010. 
 */

intrinsic LieAlgebraOfDerivations(L::AlgLie) -> AlgLie, Rec
{ The Lie algebra of derivations of the Lie algebra L. 
  Second return value is a record containing several maps.
}
	local F, i,j,dim, BasisL, Pt, LPt, D, create_der_eqns, create_der_eqn,
		eqnmat_to_vec,
		M, nsM, NewAlgBas, DerL, VSfull, v, VS, VStmp, maps;

	F := BaseRing(L);
	dim := Dimension(L);
	Pt := PolynomialRing(F, dim^2);
	LPt := ChangeRing(L,Pt);
	D := Matrix([ [ Pt.(i*dim+j+1) : j in [0..dim-1] ] : i in [0..dim-1]]);
	BasisL := Basis(L);
	VSfull := VectorSpace(F, dim^2);

	create_der_eqn := function(x,y)
		return Vector(LPt!x*LPt!y)*D 
				- (LPt!Vector(Vector(LPt!x)*D))*(LPt!y)
				- (LPt!x)*(LPt!Vector(Vector(LPt!y)*D));
	end function;
	eqn_mat_to_vec := function(p)
		local b,j,k, v;

		v := VSfull!0;
		for t in Terms(p) do
			b,j,k := IsUnivariate(t);
			if not b then error "Problem in create_der_eqns"; end if;
			v[k] +:= Coefficient(t, Pt.k, 1);
		end for;
		return v;
	end function;
	create_der_eqns := procedure(x,y, ~VS)
		local xM,yM,i,j,M, t,eqns;

		x := Vector(x); y := Vector(y);
		M := create_der_eqn(x,y);

		//fetch eqns from matrix	
		eqns := {};
		for i in [1..dim] do
			p := M[i];
			if IsZero(p) then continue; end if;
			
			v := eqn_mat_to_vec(p);
			if v notin VS then
				Include(~VS, v);
			end if;
		end for;
	end procedure;

	VS := sub< VSfull | >;
	t0 := Cputime();
	for i in [1..#BasisL] do 
		have := {VSfull | };
		for j in [(i+1)..#BasisL] do
			create_der_eqns(BasisL[i], BasisL[j], ~have);
		end for;
		VS +:= sub<VSfull | have>;
	
		vprintf ChevBas, 4: "[LieAlgebraOfDerivations] i = %3o / %3o, time = %7o s , memory = %4o M\n", i, #BasisL, Cputime() - t0, Floor(GetMemoryUsage()/10^6);
	end for;


	if Dimension(VS) eq 0 then 
		M := Transpose(Matrix(0*(VSfull.1)));
	else
		M := Transpose(Matrix(Basis(VS)));
	end if;
	vprintf ChevBas, 3: "[LieAlgebraOfDerivations] M = %o x %o\n", NumberOfRows(M), NumberOfColumns(M);

	nsM := Nullspace(M);
	vprintf ChevBas, 3: "[LieAlgebraOfDerivations] Nullspace computed; memory = %4o M\n", Floor(GetMemoryUsage()/10^6);
	if Dimension(nsM) eq 0 then error "Dimension(nsM) = 0"; end if;

	NewAlgBas := [ Matrix(dim,dim, b) : b in Basis(nsM) ];
	MLA := sub<MatrixLieAlgebra(F,dim) | NewAlgBas>;
	DerL,phi_MLA_to_DerL := LieAlgebra(MLA);
	arL := AdjointRepresentation(L);

	mp_derl_to_l := map<DerL -> L | x :-> (x @@ phi_MLA_to_DerL) @@ arL>;
	mp_l_to_derl := map<L -> DerL | x :-> phi_MLA_to_DerL(MLA!arL(x)) >;
	mp_derl_to_mats := map<DerL -> MLA | x :-> (x @@ phi_MLA_to_DerL) >;
	mp_mats_to_derl := map<MLA -> DerL | x :-> phi_MLA_to_DerL(x) >;

	maps := rec< 
		recformat< mp_DerL_to_L : Map, 
				   mp_L_to_DerL : Map, 
				   mp_DerL_to_mats : Map,
				   mp_mats_to_DerL : Map
		> | mp_DerL_to_L := mp_derl_to_l,
			mp_L_to_DerL := mp_l_to_derl,
			mp_DerL_to_mats := mp_derl_to_mats,
			mp_mats_to_DerL := mp_mats_to_derl >;
	
	return DerL, maps;
end intrinsic;



function ExtendHInDerL(L, H) //-> AlgLie, Rec
/* A certain part of the Derivation Lie Algebra of L. In particular, CSA-elements
  of DerL will be in the returned Lie Algebra LL. Second return value are several maps.

  Is a _lot_ faster than computing the full LieAlgebraOfDerivations.*/

	local F, t0, dim, arL, matsH, es,
		numvars, Pt, NewBasis, D, eltsD, c, e, i, j,
		T_NewToOld, T_OldToNew, 
		VNewBasis, MMT, Lmultnice,
		VSfull, create_der_eqn, eqn_mat_to_vec, create_der_eqns,
		VS, ID, have, M, nsM,
		solvec_to_mat, NewAlgBas, OldAlgBas, MLA, 
		LL, phi_MLA_to_LL, mp_ll_to_l, mp_l_to_ll, mp_ll_to_mats, mp_mats_to_ll, maps;

	t0 := Cputime();

	//Preliminaries
	F := BaseRing(L);
	dim := Dimension(L);

	//Construct D, with lots of zeroes
	arL := AdjointRepresentation(L);
	matsH := [ Matrix(arL(L!b)) : b in Basis(H) ];
	es := CommonEigenspaces(matsH);
	
	//We are looking for new elements of H. This means that all such elements
	//  must leave the eigenspaces es found above invariant, and thus on a
	//  suitable basis must look like a block matrix. 
	//We construct this suitable basis and this block matrix.
	numvars := &+[ Dimension(e)^2 : e in es ];
	vprintf ChevBas, 3: "[ExtendH] Number of variables = %o\n", numvars; 

	Pt := PolynomialRing(F, numvars);
	NewBasis := [];
	D := ZeroMatrix(Pt, dim, dim);
	eltsD := [];
	c := 0;
	for e in es do
		for i in [1+#NewBasis..#NewBasis+Dimension(e)] do
		for j in [1+#NewBasis..#NewBasis+Dimension(e)] do
			c +:= 1; 
			D[i][j] := Pt.c;
			Append(~eltsD, <i,j,c>);
		end for; end for;

		NewBasis cat:= Basis(e);
	end for;
	T_NewToOld := Matrix(NewBasis);
	T_OldToNew := T_NewToOld^-1;

	//Construct a new Lie algebra, with a more sparse multiplication, based on NewBasis
	vprintf ChevBas, 3: "[ExtendH] Precomputing new Lie algebra to multiply in...\n"; 
	VNewBasis := VectorSpaceWithBasis(NewBasis);
	MMT := [ [ 
		Coordinates(VNewBasis, Vector((L!NewBasis[i])*(L!NewBasis[j])))
	  : j in [1..dim] ] : i in [1..dim] ];
	Lmultnice := LieAlgebra<Pt, dim | MMT : Check := false>;
	vprintf ChevBas, 3: "[ExtendH] Done! Time: %o, Memory: %o M\n", Cputime() - t0, Floor(GetMemoryUsage()/10^6);

	//Construct equetions
	VSfull := VectorSpace(F, numvars);
	create_der_eqn := function(x,y)
		return Vector((Lmultnice!x)*(Lmultnice!y))*D
			- Vector(Lmultnice!(x*D)*Lmultnice!y)
			- Vector(Lmultnice!x*Lmultnice!(y*D));
	end function;
	eqn_mat_to_vec := function(p)
		local b,j,k, v;

		v := VSfull!0;
		for t in Terms(p) do
			b,j,k := IsUnivariate(t);
			if not b then error "Problem in create_der_eqns"; end if;
			v[k] +:= Coefficient(t, Pt.k, 1);
		end for;
		return v;
	end function;
	create_der_eqns := procedure(x,y, ~VS)
		local xM,yM,i,j,M, t,eqns;

		x := Vector(x); y := Vector(y);
		M := create_der_eqn(x,y);

		//fetch eqns from matrix	
		eqns := {};
		for i in [1..dim] do
			p := M[i];
			if IsZero(p) then continue; end if;
			
			v := eqn_mat_to_vec(p);
			if v notin VS then
				Include(~VS, v);
			end if;
		end for;
	end procedure;

	VS := sub< VSfull | >;
	ID := IdentityMatrix(Pt, dim);
	for i in [1..dim] do 
		have := {VSfull | };
		for j in [(i+1)..dim] do
			create_der_eqns(ID[i], ID[j], ~have);
		end for;
		VS +:= sub<VSfull | have>;
	
		vprintf ChevBas, 4 : "[ExtendH] i = %3o / %3o, time = %7o s , memory = %4o M\n", i, dim, Cputime() - t0, Floor(GetMemoryUsage()/10^6);
	end for;

	if Dimension(VS) eq 0 then error "No equations :s"; end if;
	M := Transpose(Matrix(Basis(VS)));
	vprintf ChevBas, 3: "[ExtendH] M = %o x %o\n", NumberOfRows(M), NumberOfColumns(M); 

	nsM := Nullspace(M);
	vprintf ChevBas, 3: "[ExtendH] Nullspace computed; memory = %4o M\n", Floor(GetMemoryUsage()/10^6); 

	if Dimension(nsM) eq 0 then error "Dimension(nsM) = 0"; end if;

	solvec_to_mat := function(v)
		local M, t;
		M := ZeroMatrix(F, dim, dim);
		for t in eltsD do
			M[t[1]][t[2]] := v[t[3]];
		end for;

		return T_OldToNew*M*T_NewToOld;
	end function;

	vprintf ChevBas, 3: "[ExtendH] Computing new elements...\n"; 
	NewAlgBas := [ solvec_to_mat(b) : b in Basis(nsM) ];
	OldAlgBas := [ arL(b) : b in Basis(L) ];
	vprintf ChevBas, 3: "[ExtendH] Computing sub<MLA>...\n"; 
	MLA := sub<MatrixLieAlgebra(F,dim) | OldAlgBas, NewAlgBas>;

	LL,phi_MLA_to_LL := LieAlgebra(MLA);

	mp_LL_to_l := map<LL -> L | x :-> (x @@ phi_MLA_to_LL) @@ arL>;
	mp_l_to_LL := map<L -> LL | x :-> phi_MLA_to_LL(MLA!arL(x)) >;
	mp_LL_to_mats := map<LL -> MLA | x :-> (x @@ phi_MLA_to_LL) >;
	mp_mats_to_LL := map<MLA -> LL | x :-> phi_MLA_to_LL(x) >;
	maps := rec< 
		recformat< mp_LL_to_L : Map, 
				   mp_L_to_LL : Map, 
				   mp_LL_to_mats : Map,
				   mp_mats_to_LL : Map
		> | mp_LL_to_L := mp_LL_to_l,
			mp_L_to_LL := mp_l_to_LL,
			mp_LL_to_mats := mp_LL_to_mats,
			mp_mats_to_LL := mp_mats_to_LL >;
	
	vprintf ChevBas, 3: "[ExtendH] Computed LL! Time: %o, Memory: %o M\n", Cputime() - t0, Floor(GetMemoryUsage()/10^6); 

	return LL, maps;
end function;
