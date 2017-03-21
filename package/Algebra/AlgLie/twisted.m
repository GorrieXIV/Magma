freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "ChevBas/chevbasmain.m":compute_basis_by_simp_es;
import "ChevBas/distort.m":ChangeBasisLie;
import "diagram_auts.m":extend_root_automorphism;
import "stsa.m":DR_IsSTSA;

construct_autom_2An := function(R)
	local n;
	assert IsIrreducible(R);
	assert CartanName(R)[1] eq "A";
	n := Rank(R);
	return extend_root_automorphism(R, Sym(n)![n..1 by -1]);
end function;

construct_autom_2Dn := function(R)
	local n;
	assert IsIrreducible(R);
	assert CartanName(R)[1] eq "D";
	n := Rank(R);
	assert n ge 4;
	return extend_root_automorphism(R, Sym(n)!([1..n-2] cat [n, n-1]));
end function;

construct_autom_3D4 := function(R)
	local n;
	assert IsIrreducible(R);
	assert CartanName(R)[1] eq "D";
	n := Rank(R);
	assert n eq 4;
	return extend_root_automorphism(R, Sym(n)![4,2,1,3]);
end function;

construct_autom_3D4OLD := function(R)
      local i, p, r, n;
      assert IsIrreducible(R);
      assert CartanName(R)[1] eq "D";
      n := Rank(R);
      assert n eq 4;
      
      r := [];
      for i in [1..2*NumPosRoots(R)] do
           p := RootPosition(R, Vector(Eltseq(Root(R,i : Basis := "Root"))[[4,2,1,3]]) : Basis := "Root");
           assert p ne 0;
           Append(~r, p);
   end for;
      
   return Sym(2*NumPosRoots(R))!r;
end function;

construct_autom_2E6 := function(R)
	local n;
	assert IsIrreducible(R);
	assert CartanName(R)[1] eq "E";
	n := Rank(R);
	assert n eq 6;
	return extend_root_automorphism(R, Sym(n)![6, 2, 5, 4, 3, 1]);
end function;

construct_autom := function(R, N)
	local tp, rnk;
	assert IsIrreducible(R);
	tp := CartanName(R)[1]; rnk := Rank(R);
	if   tp eq "A" and N eq 2 then return construct_autom_2An(R);
	elif tp eq "D" and N eq 2 then return construct_autom_2Dn(R);
	elif tp eq "D" and rnk eq 4 and N eq 3 then return construct_autom_3D4(R);
	elif tp eq "E" and rnk eq 6 and N eq 2 then return construct_autom_2E6(R);
	else
		error Sprintf("Cannot construct order %o automorphism of %o%o", N, tp, rnk);
	end if;
end function;


create_write_FFelt_over_F := function(F, FF, gen)
	//Elements of F are viewed as, well, scalars.
	//Elements of FF are viewed as vectors of length d := [FF:F] over F
	//Returns a function that writes elements of FF as such vectors 
	local d, degF, gensF, gensFFoverF, gens_vecs, vswb, c;
	
	d := Degree(FF, F);
	degF := Degree(F);
	gensF := [ Generator(F)^i : i in [0..degF-1]];
	gensFFoverF := [ FF!(gen^i) : i in [0..d-1]];
	gens_vecs := &cat[ [ Eltseq(g*h) : g in gensF] : h in gensFFoverF ];
	
	vswb := VectorSpaceWithBasis([ Vector(v) : v in gens_vecs]);
	return function(x)
		local i, j, c;
		c := Coordinates(vswb,Vector(Eltseq(FF!x)));
		return [ &+[ F | gensF[j+1]*c[degF*i + j + 1] : j in [0..degF-1] ] : i in [0..d-1] ];
	end function;
	
end function;

construct_twisted_liealg := function(R, F, pi)
	local FF, write_FFelt_overF, d, ksis, ksiimgs,
		L, dimL, p,n,c,pn, LFF, HFF, vsHFF, T,
		M, BasLFF, basLFF_wF, es,
		BasL, eltL_basF_to_basFF, eltL_basFF_to_basF,
		NewBasis, NewBasisH,
		twistL0, twist_to_orig, orig_to_twist, twistL, twistH;
	
	assert not IsTwisted(R);
	
	N := Order(pi);
	assert N in {2,3};
	FF<ksi> := ext<F | N>;

	//"ksis": Sequence of length [FF:F] containing elements ksi_0, .., ksi_{d-1} of FF, st 
	//        every element of FF can be written as a_0*ksi_0 + ... + a_{d-1}*ksi_{d-1}, a_i in F.
	//"imgksis": Sequence of d sequences of length d, elements are in F:
	//           the images under Frobenius of the ksis.
	write_FFelt_overF := create_write_FFelt_over_F(F, FF, ksi);
	d := Degree(FF, F);
	ksis := [ write_FFelt_overF(ksi^i) :  i in [0..d-1] ];
	ksiimgs := [ write_FFelt_overF((ksi^i)^(#F)) : i in [0..d-1] ];

	//Construct untwisted Lie algebra
	L := LieAlgebra(R, F);
	dimL := Dimension(L);
	p,n,c := StandardBasis(L);
	pn := p cat n;

	T := RootAutomorphism(R, pi, L, p,n,c);
	if Order(T) ne N then
		error "Lie algebra automorphism does not have expected order in construction of twisted lie algebra";
	end if;

	//Write down linear equations expressing b*wF = b, 
	//where we view the basis of L over FF as twice (or three times, for 3D4) a basis over F.
	BasLFF := BlockMatrix([ [ b*IdentityMatrix(F, dimL): b in a] : a in ksis ]);
	BasLFF_wF := BlockMatrix([ [ b*T: b in a] : a in ksiimgs ]);

	M := BasLFF-BasLFF_wF;
	es := Eigenspace(M, 0);
	if not Dimension(es) eq dimL then
		error "Unexpected dimension of 0-eigenspace in construction of twisted Lie algebra";
	end if;

	//Construct new structure constant Lie algebra over F
	LFF := ChangeRing(L, FF);
	HFF := sub<LFF | [ LFF | ChangeRing(Vector(L!b),FF) : b in c ]>;
	BasL := Basis(LFF);
	//Transforming elements in the "basis of L over FF viewed as twice basis over F" to basis of L over FF
	eltL_basF_to_basFF := function(x)
		local xx;
		xx := Eltseq(x);
		assert #xx eq d*dimL;
		return Vector(&+[ (ksi^i)*ChangeRing(Vector(xx[[dimL*i + j : j in [1..dimL]]]),FF) : i in [0..d-1] ]);
	end function;
	//Transforming elements in the normal basis of L over FF to "basis of L over FF viewed as twice basis over F" 
	eltL_basFF_to_basF := function(x)
		local xx;
		assert NumberOfColumns(x) eq dimL;
		xx := [ write_FFelt_overF(i) : i in Eltseq(x) ];
		return Vector(&cat[ [ F!(xx[i][j]) : i in [1..dimL] ] : j in [1..d] ]);
	end function;

	//Do a silly sanity check
	assert forall{ x : x in Basis(es) | x eq eltL_basFF_to_basF(eltL_basF_to_basFF(x)) };

	//Now actually construct the new structure constant Lie algebra over F (and a corresponding stsa)
	NewBasis := [ eltL_basF_to_basFF(v) : v in Basis(es) ];
	vsHFF := sub<VectorSpace(F, N*dimL) | [ eltL_basFF_to_basF(ChangeRing(Vector(L!b), FF)) : b in c ]>;
	NewBasisH := [ eltL_basF_to_basFF(v) : v in Basis(es meet vsHFF) ];
	twistL0, _, twist_to_orig, orig_to_twist := ChangeBasisLie(LFF, NewBasis);
	twistL := ChangeRing(twistL0, F);
	twistH := sub<twistL | [ twistL | ChangeRing(Vector(orig_to_twist(b)),F) : b in NewBasisH ]>;
	orig_to_twist := function(x)
		try 
			return twistL!ChangeRing(Vector(orig_to_twist(x)), F);
		catch e
			error "element not in twisted Lie algebra";
		end try;
	end function;
	
	//cache twistH
	twistL`SplitMaximalToralSubalgebra := twistH;

	return twistL, 
		map<twistL -> LFF | x :-> twist_to_orig(twistL0!Vector(x)), x :-> orig_to_twist(x)>, 
		LFF, 
		twistH, 
		HFF;
end function;

intrinsic TwistedLieAlgebra(R::RootDtm, F::FldFin) -> AlgLie, UserProgram, UserProgram, AlgLie, AlgLie, AlgLie
{ Construct the twisted Lie algebra of the specified type over the specified field. R must be a
  twisted root datum.

  Has 5 return values:
  * The Lie algebra L,
  * A homomorphism phi from L into the split Lie algebra L' (over a degree twist extension of F), with inverse,
  * L',
  * A split toral subalgebra H of L,
  * A split toral subalgebra H' of L', such that phi(H) is a subset of H'.
}
	if not IsTwisted(R) then error "TwistedLieAlgebra: R must be a twisted root datum."; end if;
	
	grp := Image(R`GammaAction`perm_ac);
	if not Ngens(grp) eq 1 then error "TwistedLieAlgebra: Twisting group must be cyclic."; end if;

	pi := grp.1;
	untwR := UntwistedRootDatum(R);
	
	L, phi, LFF, twistH, HFF := construct_twisted_liealg(untwR, F, pi);
	L`RootDatum := R;
	
	return L, phi, LFF, twistH, HFF;
end intrinsic;


function twisted_basis(L, H, R, twist) // -> AlgLie, AlgLie, Rec, AlgMatElt
/* R should be untwisted. twist should be 2 or 3.

  Returns:
  * LFF:  L over a degree twist extension field
  * HFF:  Split toral subalgebra of LFF
  * CBD:  Chevalley basis record for LFF, HFF, R
  * Frob: A matrix describing the Frobenius automorphism in the coordinates of the X_\alpha,
          \alpha \in \Delta: the fundamental root elements of the Chevalley basis.
*/
	local dimL, H0, F, FF, LFF, HFF, 
		p,n,c,CBD, vswbFF, Fhave, Fhavenw,
		nr, piwant, fxd, fxdwant,
		W, cnds, CBDnw, 
		vswbFFnw,m, scalars, i, j,
		cs, t1, t2, t3, v;

	assert not IsTwisted(R);
	assert Type(twist) eq RngIntElt;

	vprintf ChevBas, 2: "[TwistedBasis] Started for R = %o, twist = %o\n", CartanName(R), twist;	
	
	//Some constants.
	dimL := Dimension(L);
	F := BaseRing(L);
	FF := ext<F | twist>;

	//Construct *suitable* Chevalley basis of Lie algebra over bigger field
	LFF := ChangeRing(L, FF);
	H0 := sub<LFF | [ LFF | ChangeRing(Vector(L!b), FF) : b in Basis(H) ]>;
	vprintf ChevBas, 2: "[TwistedBasis] H = %o\n", H;
	vprintf ChevBas, 2: "[TwistedBasis] H0 = %o\n", H0;
	HFF := Centraliser(LFF, H0);
	if not DR_IsSTSA(LFF, HFF) then
		vprintf ChevBas, 2: "[TwistedBasis] HFF (%o-dim) was not split toral subalgebra.\n", Dimension(HFF);
		vprintf ChevBas, 2: "[TwistedBasis] Trying to compute one.\n";
		HFF := SplitToralSubalgebra(LFF : H0 := H0);
	else
		vprintf ChevBas, 2: "[TwistedBasis] HFF (%o-dim) is split toral subalgebra.\n", Dimension(HFF);
	end if;
	vprintf ChevBas, 2: "[TwistedBasis] HFF = %o\n", HFF;
	assert DR_IsSTSA(LFF, HFF);
	vprintf ChevBas, 2: "[TwistedBasis] Computing Chevalley basis of LFF...\n";
	p,n,c,CBD := ChevalleyBasis(LFF, HFF, R);
	vswbFF := VectorSpaceWithBasis([ Vector(x) : x in p cat n cat c ]);
	q := #F;
	
	//Do some Frobenius tricks
	Fhave := Matrix([ Coordinates(vswbFF, Vector([ i^q : i in Eltseq(v) ])) : v in Basis(vswbFF) ]);
	if GetVerbose("ChevBas") ge 2 then
		printf "[TwistedBasis] Fhave = \n"; IndentPush(); print Fhave; IndentPop();
	end if;
	
	//Apply a Weyl element to obtain a more suitable Chevalley basis
	nr := 2*NumPosRoots(R);
	piwant := Sym(nr)!construct_autom(R, twist);
	fxd := { i : i in [1..NumPosRoots(R)] | Fhave[i][i] ne 0 };
	fxdwnt := { i : i in [1..NumPosRoots(R)] | i^piwant eq i };
	if fxd eq fxdwnt then
		CBDnw := CBD;
		vswbFFnw := vswbFF;
		Fhavenw := Fhave;
	elif CartanName(R)[1] eq "A" and #fxd eq 0 then
		vprintf ChevBas, 2: "[TwistedBasis] fxd    = %o\n", fxd;
		if forall{i : i in [1..NumPosRoots(R)] | Fhave[i][i+NumPosRoots(R)] ne 0} then
			vprintf ChevBas, 2: "[TwistedBasis] Frobenius acts as -1 -- proving it is an outer automorphism. That will have to do.\n";
			return LFF, HFF, CBD, Fhave;
		else
			error "Unacceptable set of fixed root space elements.";
		end if;
	else
		vprintf ChevBas, 2: "[TwistedBasis] Finding suitable Weyl element: \n";
		vprintf ChevBas, 2: "[TwistedBasis] fxd    = %o\n", fxd;
		vprintf ChevBas, 2: "[TwistedBasis] fxdwnt = %o\n", fxdwnt;
		if #fxd ne #fxdwnt then
			error "Unacceptable set of fixed root space elements.";
		end if;
		W := CoxeterGroup(R);
		if CartanName(R) in {"D4", "D4 "} and twist eq 2 then
			//2D4 -- need to take into account the 3D4 autom, otherwise can possibly
			// not find suitable Weyl elt / automorphism of Lie alg
			W := sub<Sym(Degree(W)) | W, construct_autom_3D4(R) >;
		end if;
		cnds := [ w : w in W | fxd^w eq fxdwnt ];
		assert #cnds gt 0;
		w := cnds[1];
		vprintf ChevBas, 2: "[TwistedBasis] Modifying Chevalley basis...\n";
		CBDnw := CBD;
		CBDnw`IndRts := PermuteSequence(CBD`IndRts, w^-1); //transforming sequences of indices pointing to indices is painful ;)
		CBDnw`IndFund := CBDnw`IndRts[[1..Rank(R)]];
		compute_basis_by_simp_es(~CBDnw);
		assert IsChevalleyBasis(CBDnw);
		vswbFFnw := VectorSpaceWithBasis([ Vector(x) : x in CBDnw`BasisPos cat CBDnw`BasisNeg cat CBDnw`BasisCart ]);
		Fhavenw := Matrix([ Coordinates(vswbFFnw, Vector([ i^q : i in Eltseq(v) ])) : v in Basis(vswbFFnw) ]);
		if GetVerbose("ChevBas") ge 2 then
			printf "[TwistedBasis] Fhavenw = \n"; IndentPush(); print Submatrix(Fhavenw, 1, 1, Rank(R), Rank(R)); IndentPop();
		end if;
	end if;

	//Scale the root elements of the Chevalley basis.
	m := Submatrix(Fhavenw, 1, 1, Rank(R), Rank(R));
	scalars := [];
	for i in [1..Rank(R)] do 
		for j in [1..Rank(R)] do
			if m[i][j] ne 0 then Append(~scalars, m[i][j]); continue i; end if;
		end for;
		error "Not a permutation of simple root elements";
	end for;

	if SequenceToSet(scalars) ne { FF | 1 } then
		//Scale the Chevalley basis.
		//The correction factors will go into cs.
		cs := [* false : i in [1..Rank(R)] *];
		//First, fix the scalars for the roots that are fixed under delta:
		//  c^F t = c    should be satisfied
		for i in [1..Rank(R)] do
			if m[i][i] eq 0 then continue; end if;
			cs[i] := Root(1/scalars[i], q-1);
		end for;
		//Then, the order two ones:
		//  c_1^F t_1 = c_2    should  be satisfied (and t_1^F t_2 = 1)
		for i in [1..Rank(R)] do for j in [(i+1)..Rank(R)] do
			if m[i][j] eq 0 or m[j][i] eq 0 then continue; end if;
			t1 := m[i][j];
			t2 := m[j][i];
			//if not t1^q*t2 eq 1 then error "Cannot scale."; end if;
			cs[i] := 1;
			cs[j] := (cs[i])^q*t1;
		end for; end for;
		//Then, the order three ones (...)
		for i in [1..Rank(R)] do for j in [(i+1)..Rank(R)] do for k in [(i+1)..Rank(R)] do
			if m[i][j] eq 0 or m[j][k] eq 0 or m[k][i] eq 0 then continue; end if;
			t1 := m[i][j];
			t2 := m[j][k];
			t3 := m[k][i];
			cs[i] := Root(1/(t1*(t2^q)*t3), q-1);
			cs[j] := ((cs[i])^q)*t1;
			cs[k] := ((cs[j])^q)*t2;
		end for; end for; end for;

		assert forall{i : i in [1..#cs] | cs[i] cmpne false};
		cs := [ FF | c : c in cs ];	
	
		//Apply the scalars and go :)
		vprintf ChevBas, 2: "[TwistedBasis] Scaling Chevalley basis, cs = %o\n", cs;
		for i in [1..Rank(R)] do
			CBDnw`EigenSpaces[CBDnw`IndRts[i]] := cs[i]*CBDnw`EigenSpaces[CBDnw`IndRts[i]];
		end for;
		compute_basis_by_simp_es(~CBDnw);
		assert IsChevalleyBasis(CBDnw);
		vswbFFnw := VectorSpaceWithBasis([ Vector(x) : x in CBDnw`BasisPos cat CBDnw`BasisNeg cat CBDnw`BasisCart ]);
		Fhavenw := Matrix([ Coordinates(vswbFFnw, Vector([ i^q : i in Eltseq(v) ])) : v in Basis(vswbFFnw) ]);
		if GetVerbose("ChevBas") ge 2 then
			printf "[TwistedBasis] Fhavenw = \n"; IndentPush(); print Submatrix(Fhavenw, 1, 1, Rank(R), Rank(R)); IndentPop();
		end if;
	end if;

	/*
	//This shows that the elements of L are the stable points under T*F
	pi := construct_autom(R, twist);
	T := RootAutomorphism(R, pi, LFF, CBDnw`BasisPos,CBDnw`BasisNeg,CBDnw`BasisCart);	
	printf "Images of basis elements of L under T F:\n";
	for b in Basis(LFF) do
		printf "b = %o\n", Coordinates(vswbFFnw, Vector(b));
		printf "(b*T)^F = %o\n", [ i^q : i in Coordinates(vswbFFnw, Vector(b*T)) ];
	end for;
	*/
	
	//Done!
	Fhavenw := Submatrix(Fhavenw, 1, 1, Rank(R), Rank(R));
	return LFF, HFF, CBDnw, Fhavenw;
end function;

intrinsic TwistedBasis(L::AlgLie, H::AlgLie, R::RootDtm) -> AlgLie, AlgLie, Rec, AlgMatElt
{ Input: (Twisted) root datum R, Lie algebra L with split toral subalgebra H.

  Returns:
  * LFF:          L over a degree twist extension field
  * phi:          Map from L to LFF
  * ChevBasData:  Chevalley basis record for LFF, HFF, R
  * Frob:         A matrix describing the Frobenius automorphism in the coordinates of the X_\alpha,
                  \alpha \in \Delta: the fundamental root elements of the Chevalley basis.
}
	if IsTwisted(R) then
		LK, HK, ChevBas, frob :=  twisted_basis(L, H, UntwistedRootDatum(R), TwistingDegree(R));
	else
		if CartanName(R) in {"D4", "D4 "} then error "TwistedBasis: in the D4 case a twisted root datum should be given."; end if;
		LK, HK, ChevBas, frob :=  twisted_basis(L, H, R, 2);
	end if;
	
	LK`SplitMaximalToralSubalgebra := HK;
	phi := map<L -> LK | x :-> LK!Vector(x)>;
	return LK, phi, ChevBas, frob;
end intrinsic;


