freeze;

/* 
 * Dan Roozemond, 2010. 
 *
 * References: 
 * - Carter, Simple Groups of Lie Type, 1972, p. 57
 */

import "diag.m":simdiag;
import "cartints.m":pairing_e_alphast, pairing_alpha_f, compute_required_Nrs,
	findrchaininset, compute_cartints_and_degrees;
import "chevbasdata.m":NewChevBasData;

ismultof := function(a, b)
	//returns i st i*a = b
	local N, nzp, t;

	N := NumberOfColumns(a);
	nzp := exists(i){ i : i in [1..N] | a[i] ne 0};
	if nzp then
		//a is nonzero
		t := b[i]/a[i];
		if ( t*a eq b ) then 
			return t; 
		else
			return false;
		end if;
	elif IsZero(b) then
		//a and b both zero
		return One(BaseRing(a));
	else
		//a is zero, b is not
		return false;
	end if;
end function;

findeigenv := function(h, x)
	if IsZero(x) then return 0; end if;
	return ismultof(x, x*h);
end function;


printmat := procedure(n,v) 
	printf "%o = \n",n; 
	IndentPush(); 
	print v; 
	IndentPop(); 
end procedure;




mult_dim_eigenspc_byev := function(ev)
	local dup, todo, p;

	dup := []; todo := {1..#ev};
	while #todo gt 0 do
		i := Representative(todo);
		p := [ j : j in [1..#ev] | ev[j] eq ev[i] ];
		if #p gt 1 then
			Append(~dup, p);
		end if;
	
		todo diff:= Seqset(p);
	end while;

	return dup;
end function;
mult_dim_eigenspc := function(CBD)
	return mult_dim_eigenspc_byev(CBD`EigenVectors);
end function;

findeigenspcLH := function(L, H)
	//H should be a splitting cartan subalgebra
	//Note that the result assumes H to be acting from the *right*
	//This returns a basis of L on which the basis elements of H
	// act diagonally.
	local Hb,Lb, arL, espcs, evls, rcart,
		espos,
		i,j,v,
		F, LHS, RHS;

	if Type(H) cmpeq SeqEnum then
		Hb := [ L!b : b in H ];
	else
		Hb := [ L!b : b in Basis(H) ];
	end if;
	Lb := Basis(L);
	arL := AdjointRepresentation(L : ComputePreImage := false);
	F := BaseRing(L);


	espcs, evls := simdiag([ arL(b) : b in Hb]);
	rpos := [L|]; rvals := [];
	for i in [1..#espcs] do 
		try
			rpos cat:= [ L | b : b in Basis(espcs[i]) ];
			rvals cat:= [ Vector(evls[i]) : j in [1..Dimension(espcs[i])] ];
		catch errr
			//This happens if the field was enlarged by findeigenspcLH, 
			// i.e. H was not a proper SplittingCartanSubalgebra.
			error "H was not a SCSA in findeigenspcLH";
		end try;
	end for;
	rcart := Hb;

	/* Check */
	for i in [1..#rcart] do for j in [1..#rpos] do
		v := findeigenv(rcart[i],rpos[j]);
		if v cmpeq false then
			printf "Diagonalization failed! i = %o, j = %o\n", i,j;
			return false, _, _;
		end if;
	end for; end for;

	return rpos, rvals, rcart;
end function;

findeigenspc := procedure(~CBD : ForceNew := false)
	if (not ForceNew) and (assigned CBD`EigenSpaces) then return; end if;

	CBD`EigenSpaces, CBD`EigenVectors, CBD`SCSAVectors := findeigenspcLH(CBD`L,CBD`H);
end procedure;

findeigenspc_notinH := procedure(~CBD : ForceNew := false)
	local i, es, ev, cart, remvd;

	if (not ForceNew) and (assigned CBD`EigenSpaces) then return; end if;
	
	findeigenspc(~CBD : ForceNew := true);
	
	i := 1; remvd := 0;
	while i le #CBD`EigenVectors do
		if CBD`EigenSpaces[i] in CBD`H then
			Remove(~(CBD`EigenVectors), i);
			Remove(~(CBD`EigenSpaces), i);
			remvd +:= 1;
		else
			i +:= 1;
		end if;
	end while;

	if remvd lt Dimension(CBD`H) then
		error "findeigenspc_notinH: Eigenspaces with all-zero eigenvalues cause trouble";
	end if;

end procedure;

compute_cart_by_posnegs := function(CBD)
	local R, L, rnk, NPR, h, es,
		vzwb, RHS, LHS, RHS_CB3, LHS_CB3, RHS_CB2, LHS_CB2,
		i,j,k, M, 
		zm,eahi,b, V, ns, newh, VtoMat;

	R := CBD`R; L := CBD`L;
	rnk := Rank(R); 
	dim := Dimension(R);
	NPR := NumPosRoots(R);
	h := CBD`SCSAVectors;
	hmat := Matrix(CBD`SCSAVectors);
	es := CBD`EigenSpaces[CBD`IndRts];
	assert #es eq 2*NumPosRoots(R);

	/*
	 Solution will be matrix of size 1 x (rnk*dim + rnk)
	 make it into a rnk x dim matrix and a 1 x rnk matrix.
	 - The first rnk x dim encodes the new basis for H,
 	 - The second encodes the scalar multiples that the simple neg 
	   rts need to be multiplied with.
	 (We also compute such scalar multiples for the non-simple neg
	  rts, but they are not used; instead it's "safer" to recompute
	  them later on)
	*/
	SolVecToMat := function(v)
		return Matrix([
			[ v[(j-1)*dim + (k-1) + 1] : k in [1..dim] ]
			: j in [1..dim] ]),
			Vector([ v[dim*dim + k ] : k in [1..rnk] ]);
	end function;
	vswb := VectorSpaceWithBasis([ Vector(b) : b in h ]);

	//This encodes: For \alpha a positive root:
	//  sum_{i=1}^n <e_i, alpha^*> rcart[i] = [ mu_{-alpha} X_{-alpha} , X_{alpha} ]
	//  where rcart[i] = sum_{j=1}^n lambda_ij  h_i
	//So the lambda_ij and mu_{-alpha} are the rnk*dim + NPR variables mentioned
	// above in VtoMat
	LHSs := [
		VerticalJoin([
		VerticalJoin([
			pairing_e_alphast(R, j, i)*Vector(Coordinates(vswb, Vector(h[k])))
			: k in [1..dim]
		]) : j in [1..dim]
		])
		: i in [1..NPR] ];
	zeromat := Matrix([ [ CBD`F | 0  : i in [1..dim] ] ]);
	LHSnw := [];
	for i in [1..NPR] do
		M := LHSs[i];
		for j in [1..(i-1)] do M := VerticalJoin(M, zeromat); end for;
		M := VerticalJoin(M, -Matrix([Vector(Coordinates(vswb, Vector(L!es[i+NPR]*L!es[i])))]));
		for j in [(i+1)..NPR] do M := VerticalJoin(M, zeromat); end for;
		LHSnw[i] := M;
	end for;

	bigM := HorizontalJoin(LHSnw);
	nsBigM := Basis(Nullspace(bigM));
	if #nsBigM eq 0 then
		vprintf ChevBas, 1: "WARNING -- no solution in compute_cart_by_posnegs\n";
		return false, _, _ ; 
	end if;
	
	/* So nsBigM contains vectors of length rnk*dim + RNK, describing
	   the solutions for the h_i (the rnk*dim part) and for the
	   e_{-alpha} (the RNK part).

		We use this result to solve the h_i using CB2. 

		[ e_alpha, h_i ] = <alpha, f_i> e_alpha

		Denote the m solution rows above by lambda^(k)_{ij}, then
		h_i will be sum_{k=1}^m ( sum_{j=1}^n lambda^(k)_{ij} h_j )
	*/

	zm := ZeroMatrix(CBD`F, rnk, rnk*Dimension(L));
	m := #nsBigM;
	hki := [ SolVecToMat(Vector(nsBigM[k]))*hmat : k in [1..m] ];

	LHS_CB2 := ZeroMatrix(CBD`F, m, 0);
	RHS_CB2 := ZeroMatrix(CBD`F, 1, 0);
	for i in [1..dim] do
		lhs := HorizontalJoin([
				VerticalJoin([ 
				Vector( (L!es[alpha])*(L!hki[k][i]) )
				: k in [1..m] ])
		: alpha in [1..rnk] ]);

		rhs := HorizontalJoin([
			Matrix([ pairing_alpha_f(R,alpha,i)*es[alpha] ])
			: alpha in [1..rnk] ]);

		LHS_CB2 := HorizontalJoin(LHS_CB2, lhs);
		RHS_CB2 := HorizontalJoin(RHS_CB2, rhs);
	end for;

	b,V,ns := IsConsistent(LHS_CB2, RHS_CB2);
	if not b then return false, _, _ ; end if;

	SolCart, SolNeg := SolVecToMat(V[1]*Matrix(nsBigM));
	if Dimension(ns) gt 0 then
		vprintf ChevBas, 2: "WARNING -- Exceptional ambiguity in h_i!\n";

		///*
		//	Live with it. Do nothing except make sure that cart is spanned OK.
		//*/
		//if Rank(SolCart) lt rnk then
		//	SolCart, SolNeg := SolVecToMat(
		//		(V + Matrix(Basis(ns)[1]))*Matrix(nsBigM)
		//	);
		//	if Rank(SolCart) lt rnk then
		//		error "Cannot find proper new basis.";
		//	end if;
		//end if;
	end if;

	newh := SolCart*hmat;
	
	if (Rank(newh) lt dim) then
		/* newh contains additional h's. */
		nsh := [ SolVecToMat(n*Matrix(nsBigM)) : n in Basis(ns) ];
		assert #nsh + Rank(newh) eq dim;
		nsh := [ n*hmat : n in nsh ];
		avail := {i : i in [1..#nsh]};

		while (Rank(newh) lt dim) and (#avail gt 0) do
			zrs := {i : i in [1..dim] | IsZero(newh[i]) };
			changed := false;
			for k in avail do
				t := newh + nsh[k];
				nwzrs := {i : i in [1..dim] | IsZero(t[i])};
				if #nwzrs lt #zrs and nwzrs subset zrs then
					changed := true;
					newh := t;
					Exclude(~avail, k);
					break;
				end if;
			end for;
			if not changed then break; end if;
		end while;
		
		if Rank(newh) lt dim then
			vprintf ChevBas, 1: "WARNING -- Could not Cartan elements sufficiently fixed\n";
			return false,_,_;
		end if;
	end if;
	newneg := [ L!(Vector(SolNeg[i] * es[NPR+i])) : i in [1..rnk] ];

	//We tried to maximize the rank of newh, but if it is not enough something
	// else has apparently gone wrong.
	if Rank(newh) lt NumberOfRows(newh) then
		vprintf ChevBas, 1: "WARNING -- Could not get rank up high enough in compute_cart_by_posnegs!\n";
		return false,_,_;
	end if;
	
	newh := [ L!newh[i] : i in [1..dim] ];
	newneg := [ L!(Vector(SolNeg[i] * es[NPR+i])) : i in [1..rnk] ];
	
	return true, newh, newneg;
end function;

scale_rpos_using_required_Nrs := procedure(~CBD, ~rpos, ~rneg, k)
	//Instead of scaling k by doing rpos[i]*rpos[j] = ? * k,
	//   we try rpos[i]*rpos[k] = ? rpos[j]. Maybe that works.
	//This is actually in many cases a better approach, because
	//   this uses CBD`IndRts

	local changed, ok, i, j, L, R, posneg, NPR, c, x, xgood;

	compute_required_Nrs(~CBD);
	R := CBD`R;
	L := CBD`L;
	NPR := NumPosRoots(R);

	posneg := [];
	for i in [1..NPR] do
		if IsDefined(rpos, i) then posneg[i] := rpos[i]; end if;
		if IsDefined(rneg, i) then posneg[i+NPR] := rneg[i]; end if;
	end for;

	x := L!(CBD`EigenSpaces[CBD`IndRts[k]]);
	for i in [1..2*NPR] do
		if not IsDefined(posneg, i) then continue; end if;

		j := RootPosition(R, Root(R,i) + Root(R,k));
		if j eq 0 then continue; end if;
		if not IsDefined(posneg, j) then continue; end if;

		if IsZero(L!posneg[i]*x) then continue; end if;

		d := ismultof(L!posneg[i]*x, posneg[j]);
		if d cmpeq false or d eq 0 then error "Hmz."; end if;
		c := CBD`RequiredNrs[i][k];
		//So we have e_i*e_k = (1/d)*e_j, but we should have e_i*e_k = c*e_j.

		if k le NPR then rpos[k] := c*d*x;
		else			 rneg[k-NPR] := c*d*x;
		end if;
	end for;
end procedure;


compute_basis_by_simp_es := procedure(~CBD)
	local R, L, rpos, rneg, rcart, 
			i, j, k, p, N, BL, rnk,
			h, cons, V, NPR,
			LHS, RHS, rts, rt1, rt2;

	R := CBD`R; L := CBD`L;
	rpos := CBD`EigenSpaces[CBD`IndRts[1..Rank(R)]];
	N := Dimension(L);
	NPR := NumPosRoots(R);
	rnk := Rank(R);
	dim := Dimension(R);
	BL := Basis(L);

	rcart := [L|];
	rneg := [L|];

	/* scale cart appropriately */
	/* We do, for every (to be) element of the CSA, */
	for i in [1..rnk] do
		LHS := HorizontalJoin([
			Matrix([ (L!rpos[k])*(L!((CBD`SCSAVectors)[j])) : j in [1..dim] ])
			: k in [1..rnk] ]);
		RHS := HorizontalJoin([
			Matrix([ pairing_alpha_f(R,k,i)*rpos[k] ])
			: k in [1..rnk] ]);
			
		cons,V,ns := IsConsistent(LHS, RHS);
		if not cons then 
			error "Could not find suitable cartan :(";
		end if;

		h := false;
		if ( Dimension(ns) eq 0 ) then
			h := V[1]*Matrix(CBD`SCSAVectors);
		else
			//"Just" using posrt*negrt is valid only in the adjoint case (!)
			// so we should not do that.

			//Try something (completely) different
			if IsDefined(CBD`IndRts, i+NPR) then
				b, r1, r2 := compute_cart_by_posnegs(CBD);
				if not b then printf "compute_cart_by_posnegs failed\n"; end if;
				if b then
					rcart := r1;
					rneg := r2;
					break i;
				end if;
			end if;
		end if;

		if (h cmpeq false) then
			error "Freedom choosing cartan -- Don't know what to do.";
		end if;

		Append(~rcart, h);
	end for;
	
	
	//Compute the simple negative roots by solving
	// [e_{-r},h_j] = <alpha_f> e_{-r}
	// [e_{-a},e_a] = sum_{i=1}^n <e_i, a*>h_i
	if #rneg eq 0 then
		for i in [1..rnk] do
			LHS := HorizontalJoin([ 
				Matrix([ Vector(b*rcart[j] - pairing_alpha_f(R, NPR+i,j)*b ) : b in BL])
				: j in [1..rnk] ]
			);
			RHS := ZeroMatrix(BaseRing(L),1,rnk*#BL);

			LHS := HorizontalJoin(LHS,
				Matrix([ Vector( b*rpos[i] ) : b in BL ])
			);
			RHS := HorizontalJoin(RHS,
				Matrix(Vector(&+[ pairing_e_alphast(R,j,i)*rcart[j] : j in [1..rnk] ]))
			);

			cons,v,n := IsConsistent(LHS, RHS);
			if not cons then
				error "Could not find (any!) satisfactory e[-..]"; 
			end if;

			if (Dimension(n) eq 0) then 
				rneg[i] := L!(v[1]*Matrix(BL));
			else
				x := Vector(CBD`EigenSpaces[CBD`IndRts[NPR+i]]);
				c := ismultof(x*LHS, RHS[1]);

				if (c cmpne false) then
					rneg[i] := c*x;
				else
					error "Stop. Could not find unique e[-..]";
				end if;
			end if;

		end for;
	end if;

	/* compute non-simple roots */
	//Compute the non-simple roots from the simple ones
	// and the extraspecial signs.
	//First, we do it the trivial way, by just using only
	//  the given ExtraspecialSigns.
	ok := true;
	rts := Roots(R); 
	for es in CBD`ExtraspecialSigns do
		rt1 := rts[es[1]]; rt2 := rts[es[2]];
		k := Position(rts, rt1+rt2);
		p := (findrchaininset(rts, rt1, rt2))[1];
		if k eq 0 then 
			error "oh jee :("; 
		end if;
		if not IsZero(BaseRing(L)!(p+1)) then 
			rpos[k] := 1/(es[3]*(p+1))*rpos[es[1]]*rpos[es[2]];
			rneg[k] := 1/(-es[3]*(p+1))*rneg[es[1]]*rneg[es[2]];
		else
			ok := false; break es;
		end if;
	end for;

	//If that failed, we try to use the extraspecial signs that
	//  follow from the standard ones, which may be nonzero.
	//This is significantly slower.
	//Should consider moving this into a separate procedure.
	if not ok then
		todo := [ k : k in [1..NPR] | not IsDefined(rpos,k) ];
		while #todo gt 0 do
			for k in todo do
				scale_rpos_using_required_Nrs(~CBD, ~rpos, ~rneg, k);
				scale_rpos_using_required_Nrs(~CBD, ~rpos, ~rneg, k+NPR);
			end for;

			oldtodo := todo;
			todo := [ k : k in [1..NPR] | not IsDefined(rpos,k) ];
	
			if todo eq [] then break; end if;

			if todo eq oldtodo then
				//Pick one randomly
				vprintf ChevBas, 2: "Could not compute all non-simple roots.... Picking one randomly\n";

				k := todo[1];
				Remove(~todo, 1);

				//Guarantee [x_-\alpha, x_\alpha] = sum < e_i, a* > h_i \n";
				xp := L!(CBD`EigenSpaces[CBD`IndRts[k]]);
				yp := L!(CBD`EigenSpaces[CBD`IndRts[k+NPR]]);
				cp := &+[ pairing_e_alphast(R,i,k)*rcart[i] : i in [1..rnk] ];

				c := ismultof(cp, xp*yp);
				rpos[k] := xp/c;
				rneg[k] := yp;

			end if;
		end while;

		ok := #todo eq 0;
	end if;


	CBD`BasisPos := rpos;
	CBD`BasisNeg := rneg;
	CBD`BasisCart := rcart;
end procedure;


pullback := procedure(fromCBD, ~toCBD, imgs_of_simple_rts : pi := false)
	local RtoR, ret, i, j,k,p, fromL, toL, overw, pulledBackES;

	rnkfrom := Rank(fromCBD`R);
	if pi cmpeq false then pi := Identity(Sym(rnkfrom)); end if;

	fromL := fromCBD`L; toL := toCBD`L;

	RtoR := function(k)
		v := Eltseq(Root(fromCBD`R, k : Basis := "Root"));
		v := PermuteSequence(v, pi);

		w := &+[ Root(toCBD`R,imgs_of_simple_rts[i])*v[i] : i in [1..rnkfrom] ];

		return RootPosition(toCBD`R,w);
	end function;

	//And then pull back.
	ret := assigned toCBD`IndRts select toCBD`IndRts else [];
	for i in [1..#fromCBD`IndRts] do

		p := [ j : j in [1..toCBD`NRoots] | Rank(Matrix([ 
			Vector(toL!(fromL!(fromCBD`EigenSpaces[fromCBD`IndRts[i]]))), 
			Vector(toCBD`EigenSpaces[j])
			])) eq 1 ];

		if #p ne 1 then
			error Sprintf("i = %o\np = %o\nwhoops -- cannot pull back eigenspace", i, p);
		end if;

		k := RtoR(i);
		if k eq 0 then
			error "whoops -- imgs_of_simple_rts must have been incorrect in pullback.";
		end if;

		ret[k] := p[1];
	end for;


	//Done & return
	toCBD`IndRts := ret;
end procedure;



recompute_eigenvectors := procedure(~CBD)
	local L, H;
	L := CBD`L; H := CBD`H;
	CBD`EigenVectors := [ Vector([ ismultof(L!e, L!e*L!h) : h in Basis(CBD`H) ]) : e in CBD`EigenSpaces ];
end procedure;


/* Attempts to fix the scalars of a Chevalley basis (p,n,c) of L, wrt
 * root datum R. 1st return value b is whether successfull or not;
 * if b, then 2nd, 3rd, 4th are new p,n,c.
 */
function fix_chevbas_scalars(L, R, p, n, c)
	CBD := NewChevBasData(R, L, sub<L|c>);
	CBD`SCSAVectors := c;
	CBD`EigenSpaces := p cat n;
	CBD`IndRts := [1..2*NumPosRoots(R)];
	if IsChevalleyBasis(L, R, p,n,c) then
		CBD`BasisPos := p;
		CBD`BasisNeg := n;
		CBD`BasisCart := c;
		return true, p,n,c, CBD;
	end if;
	
	try
		compute_basis_by_simp_es(~CBD);
	catch e
		vprintf ChevBas, 2 : "[fix_chevbas_scalars] compute_basis_by_simp_es failed.\n";
		return false, _, _, _, _;
	end try;
	
	if not IsChevalleyBasis(CBD) then
		vprintf ChevBas, 2 : "[fix_chevbas_scalars] compute_basis_by_simp_es succeeded, but not IsChevalleyBasis\n";
		return false, _, _, _, _;
	end if;
	
	return true, CBD`BasisPos, CBD`BasisNeg, CBD`BasisCart, CBD;
end function;


