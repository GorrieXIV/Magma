freeze;

/* 
 * Dan Roozemond, 2010. 
 * Updated in June 2011.
 */

//NOTE: Designed to work in characteristic 2 only.
import "quo_with_pullback.m":quo_with_pullback;
import "stsa.m":DR_IsSTSA;
forward recursionstep;

pb_rf := recformat< to_elt:UserProgram, to_subalg:UserProgram >;

/* Definition of split elements */
issplit := function(arh)
	local mp;
	assert Type(arh) eq AlgMatElt;
	mp := Factorization(MinimalPolynomial(arh));
	return forall{m : m in mp | (m[2] eq 1) and (Degree(m[1]) eq 1) };
end function;

/* Functions for finding h in an A1 subalgebra */
function findh_by_lineqs(N, B : alpha := 1)
	//Finds an element in (the Lie algebra) N that sends every 
	//(Lie algebra) element of (the sequence) B to itself.
	//Elements of B should be in N.
	local LHS, RHS, b, h, ns;
	LHS := HorizontalJoin([
		VerticalJoin(
			[ Vector(N!x*N!b) : b in Basis(N) ]
		) : x in B ]);
	RHS := HorizontalJoin([ alpha*Vector(N!x) : x in B ]);
	
	b,h,ns := IsConsistent(LHS,RHS);
	//assert b;
	if not b then
		vprintf STSA, 2: "[STSAc2] \"assert b\" failed :s\n";
		return N!0, false;
	end if;
	
	return N!(h[1]), ns;
end function;


//This is what we want:
function isok(h, M, arM, L, arL, pbtoL)
	local arh, arLh, sn, S0;
	
	if (h cmpeq false) then return false; end if;
	if IsZero(h) then return false; end if;
	
	//split in M?
	arh := Matrix(arM(h));
	if issplit(arh) then
		vprintf STSA, 2: "[STSAc2] new h (= %o) is split (in M)\n", h;
	else
		vprintf STSA, 2: "[STSAc2] new h is NOT split.\n"; 
		return false;
	end if;
	
	//split in L (elt)
	Lh := L!((pbtoL`to_elt)(h));
	sn := issplit(Matrix(arL(Lh)));
	if sn then
		vprintf STSA, 2: "[STSAc2] pullback (elt) of new h (= %o) is split (in L)\n", Lh;
	else
		vprintf STSA, 2: "[STSAc2] pullback (elt) of new h is NOT split in L. (%o)\n", sn;
		return false;
	end if;

	//split in L (subalg)
	Lh_sub := ChangeUniverse(Basis((pbtoL`to_subalg)(h)), L);
	arLh_sub := [ Matrix(arL(L!b)) : b in Lh_sub ];
	sn := { issplit(m) : m in arLh_sub };
	if sn eq {true} then
		vprintf STSA, 2: "[STSAc2] pullback (subalg) of new h (= %o) is split (in L)\n", Lh_sub;
	else
		vprintf STSA, 2: "[STSAc2] pullback (subalg) of new h is NOT split in L. (%o)\n", sn;
		return false;
	end if;
	
	//restrictable?
	// ok, pmap := IsRestrictable(L);
	// assert ok;
	// qmap := pmap^(Degree(BaseRing(L)));
	// sn := { qmap(L!b) eq L!b : b in Lh_sub };
	// if sn eq {true} then
	// 	vprintf STSA, 2: "[STSAc2] qmap for h is OK, too.\n";
	// else
	// 	vprintf STSA, 2: "[STSAc2] qmap(L!b) != L!b.\n";
	// 	return false;
	// end if;

	return true;
end function;

//Scale vector so that first nonzero entry is 1
function mk_monic(v)
	for i in [1..Ncols(v)] do
		if not IsZero(v[i]) then
			return v/v[i];
		end if;
	end for;
	return v;
end function;

//Try to construct a split semisimple element from an eigenspace
// 1st return value: whether success
// 2nd return value: split semisimple element (a good one, or just one that we've seen)
// 3nd return value: control path taken through function
function findSplitSemisimpleElt(V, M, arM, L, arL, pbtoL, seenhs)
	local S, I, SS, II, candh, cp, rndnonzero;

	S := sub<M | [ M!b : b in Basis(V) ]>;
	SS := S*S;
	vprintf STSA, 3: "[STSAc2] findSplitSemisimpleElt, M = %o, V = %o, S = %o, SS = %o\n", Dimension(M), Dimension(V), Dimension(S), Dimension(SS);
	
	rndnonzero := function(T)
		local x;
		assert Dimension(T) gt 0;
		repeat x := Random(T); until not IsZero(x);
		return x;
	end function;
		
	candh := false; cp := "";
	if Dimension(SS) eq 1 then
		cp := "A"; vprintf STSA, 3: "-> %o", cp;
		candh := M!(Basis(SS)[1]);
	else
		I := ideal<M | [ M!b : b in Basis(V) ]>;
		II := I*I;
		vprintf STSA, 3: "[STSAc2]       I = %o, II = %o\n", Dimension(I), Dimension(II);
		if Dimension(II) eq Dimension(I) and (Dimension(SS) eq 2 or Dimension(SS) eq 3) then
			cp := "B"; vprintf STSA, 3: "-> %o", cp;
			candh := M!rndnonzero(SS);
		elif IsEven(Dimension(I)) and Dimension(I) ne 0 and Dimension(II) eq 0 and Dimension(SS) eq 0 then
			cp := "C"; vprintf STSA, 3: "-> %o", cp;
			candh := findh_by_lineqs(M, [M!b : b in Basis(I)]);
		elif Dimension(S) eq 6 and Dimension(II) eq Dimension(S) and Dimension(SS) eq 2 then
			cp := "D"; vprintf STSA, 3: "-> %o", cp;
			candh := M!rndnonzero(SS);
		elif IsEven(Dimension(I)) and Dimension(I) ne 0 and Dimension(II) ne 0 and Dimension(SS) eq 0 then
			cp := "E"; vprintf STSA, 3: "-> %o", cp;
			candh := findh_by_lineqs(I, [M!b : b in Basis(S)]);
		elif (Dimension(V) mod 2) eq 0 then
			cp := "F1"; vprintf STSA, 3: "-> %o", cp;
			n := Dimension(V) div 2;
			if Dimension(SS) ne 0 then
				cp := "F2"; vprintf STSA, 3: "-> %o", cp;
				candh := M!rndnonzero(SS);
			end if;
		else
			candh := false; cp := "X";
		end if;
	end if;
	
	if (candh cmpeq false) then
		vprintf STSA, 3: "-> no candh\n", cp;
		return false, Zero(M), cp;
	elif mk_monic(candh) in seenhs then
		vprintf STSA, 3: "-> mk_monic(candh) in seenhs, so: no. cp = %o.\n", cp;
		return false, Zero(M), cp;
	elif isok(candh, M, arM, L, arL, pbtoL) then
		vprintf STSA, 3: "-> OK (path: %o)\n", cp;
		return true, candh, cp;
	else
		vprintf STSA, 3: "-> not OK (path: %o)\n", cp;
		return false, candh, cp;
	end if;
end function;

recursionstep := function(M, L, pbtoL : MaxRandomElts := 150, RndOnly := false)
	local arM, arL, ZM, hs, sn, ok, h, H0, Mp, inj, pbsa, pbtoLnw,
		cnt, arh, ev, e, newh, cp, cpf;
	
	vprintf STSA, 1: "[STSAc2] M = %o\n", M;
	arM := AdjointRepresentation(M : ComputePreImage := false);
	arL := AdjointRepresentation(L : ComputePreImage := false);
	IndentPush();
	ZM := Center(M);
	vprintf STSA, 1: "[STSAc2] Center(M) = %o\n", ZM;
	
	//If M has a center, we simply take that out, and we're done
	if (Dimension(ZM) gt 0) then
		vprintf STSA, 1: "[STSAc2] ZM is %o-dim; continuing in M/h (?)\n", Dimension(ZM);
		hs := [ M!b : b in Basis(ZM) ];
		Lhs := [ L | (pbtoL`to_elt)(h) : h in hs ];
		// restrok,pmap := IsRestrictable(L); assert restrok; qmap := pmap^Degree(BaseRing(L));
		// sn := [ issplit(Matrix(arL(h))) and (qmap(h) eq h) : h in Lhs ];
		sn := [ issplit(Matrix(arL(h))) : h in Lhs ];
		vprintf STSA, 2: "-> sn = %o\n", sn;
		
		//Verify splitness
		ok := [ hs[i] : i in [1..#hs] | sn[i]  ];
		if #ok gt 0 then
			h := ok[1];
			
			//Construct quotient
			H0 := sub<M | h>;
			CMH0 := Centraliser(M, H0);
			Mp, inj, pbelt, pbsa := quo_with_pullback(CMH0, H0);
			vprintf STSA, 2: "-> Mp = %o\n", Mp;

			//Construct map up to L
			pbtoLnw := rec<pb_rf | to_elt := func<x | L!((pbtoL`to_elt)(pbelt(x))) >, 
				to_subalg := func<x | sub<L | [ (pbtoL`to_subalg)(b) : b in Basis(pbsa(x)) ]> > >;

			//Done!
			IndentPop();

			return Mp, h, pbsa, inj, pbtoLnw, "center";
		end if;

		vprintf STSA, 1: "[STSAc2] Not continuing in M/h after all.\n";
	end if;

	//Find a semisimple h
	if Dimension(M) eq 1 then MaxRandomElts := Min(5, MaxRandomElts); end if;
	cp := ""; seenhs := {M | };
	for cnt in [1..MaxRandomElts+Dimension(M)] do
		vprintf STSA, 2: "[STSAc2] cnt = %o\n", cnt; 
		
		//get an h
		if (not RndOnly) and (cnt le Dimension(M)) then
			h := M.cnt;
		else
			h := Random(M);
			if IsZero(h) then continue; end if;
		end if;
		
		//if h itself is split, we are happy.
		if isok(h, M, arM, L, arL, pbtoL) then
			cp := "hit";
			break cnt;
		end if;
		
		//Otherwise, try to find a split h using its eigenspaces.
		arh := Matrix(arM(h));
		ev := SetToSequence(Eigenvalues(arh));
		for e in ev do
			vprintf STSA, 3: "[STSAc2] e = %o\n", e;
			if IsZero(e[1]) then continue; end if;
			ok, newh, cpf := findSplitSemisimpleElt(Eigenspace(arh, e[1]), M, arM, L, arL, pbtoL, seenhs);
			if ok then
				h := newh;
				cp := Sprintf("fssse(%o)", cpf);
				break cnt;
			else
				Include(~seenhs, mk_monic(newh));
				h := false;
				//if there is just not enough choice, we break early rather than keep trying
				if (cnt gt 5) and (#seenhs le 1) then break cnt; end if;
			end if;
		end for;
		
		//Unsuccesfull, apparently, so we continue the infinite loop.
		h := false;
	end for;
	
	if h cmpeq false then
		if (IsEven(Dimension(M)) and (Dimension(ZM) eq Dimension(M)) and (Dimension(M*M) eq 0)) 
			or Dimension(M) eq 1 then
			//This is where we end up in some of the Cn SC cases. 
			//Apparently, nothing was split -- but we won't be able to find 
			// something here as these are just root spaces.
			vprintf STSA, 1: "[STSAc2] Bailing out: Z(M) = M, [M,M] = 0.\n";
			IndentPop();
			return sub<M | >, [M|], _, _, _, "-";
		end if;
		
		error "\"endless\" loop in recursionstep."; 
	end if;

	//Continue somewhere else
	H0 := sub<M | h>;
	Mp, inj, pbelt, pbsa := quo_with_pullback(Centraliser(M, H0), H0);
	vprintf STSA, 2: "-> Mp = %o\n", Mp;
	
	//Construct map up to L
	vprintf STSA, 2: "-> pbtoL(h) = %o\n", (pbtoL`to_elt)(h);
	pbtoLnw := rec<pb_rf | to_elt := func<x | L!((pbtoL`to_elt)(pbelt(x))) >, 
		to_subalg := func<x | sub<L | [ (pbtoL`to_subalg)(b) : b in Basis(pbsa(x)) ]> > >;
	
	//Done!
	IndentPop();
	return Mp, h, pbsa, inj, pbtoLnw, cp;
end function;

/* Where it all comes together */
//constructH pulls semisimple elements all the way back up to L
constructH := function(L, arL, pbtoLs, hs)
	local BasH, i, sn;
		
	//BasH := &join[ SequenceToSet(&cat[ [ L | b : b in Basis(pbtoLs[i](x)) ] : x in hs[i] ]) : i in [1..#hs] ];
	BasH := &join[ SequenceToSet([ L | (pbtoLs[i]`to_elt)(x) : x in hs[i] ]) : i in [1..#hs] ];
	vprintf STSA, 3: "[constructH] #BasH = %o\n", #BasH;
	
	sn := [ <b,issplit(Matrix(arL(L!b)))> : b in BasH ];
	vprintf STSA, 3: "[constructH] splitness: %o\n", {* s[2] : s in sn *};
	if {s[2] : s in sn} ne {true} then error "STOP!!"; end if;

	H := sub<L | BasH>;
	vprintf STSA, 3: "[constructH] Dimension(sub<L | BasH>) = %o\n", Dimension(H);
	
	return H;
end function;
//mainrecursion repeatedly calls recursionstep
mainrecursion := function(L : StartH := false, AimForDim := false, RndOnly := false)
	local M, M0, ZM, pbtoL, b, hs, basm, hp, arL, arLhs, pbsa, MinL, sn, cps, cp;
	
	arL := AdjointRepresentation(L : ComputePreImage := false);
	M := L;
	//pairs of functions that pullback from M to L:
	pbtoLs := [ rec<pb_rf | to_elt := func<x|L!x>, to_subalg := func<x | sub<L|x> > > ]; 	
	pbtoL := pbtoLs[1];    //initial pullback back from M to L
	hs := [* *];           //elements of M that end up in H
	H := sub<M | >;        
	cps := [* *];          //control path -- for debugging etc.
	
	//Get started with something if startH is set
	if StartH cmpne false then
		//Mimic the result of recursion step for each of the basis elements of H
		basH := [ M!(L!b) : b in Basis(StartH) ];
		while #basH gt 0 do
			//Get a new element
			h := basH[1];
			Remove(~basH, 1);
			
			//Construct the relevant objects
			H0 := sub<M | h>;
			M, inj, pb, pbsa := quo_with_pullback(Centraliser(M, H0), H0);
			pbtoL := rec<pb_rf | to_elt := func<x | (pbtoL`to_elt)(pb(x))>, 
								to_subalg := func<x | sub<L | [ (pbtoL`to_subalg)(b) : b in Basis(pbsa(x)) ]> > >;

			//Append to the data...
			Append(~pbtoLs, pbtoL);
			Append(~hs, [h]);

			//Pull down the remaining basis elements
			basH := [ M | inj(b) : b in basH ];
		end while;
	
		//Just check...
		H := constructH(L, arL, pbtoLs, hs);
		b := DR_IsSTSA(L,H);
		vprintf STSA, 1: "[STSAc2] Getting started with an H pre-given; H = %o-dim, STSA: %o\n", Dimension(H), b;
		if not b then error "Pre-given H didn't work out."; end if;
	end if;
		
	//Here is the actual recursion
	while (Dimension(M) gt 0) and ((AimForDim cmpeq false) or (Dimension(H) lt AimForDim)) do
		/* Do the recursion step */
		M, h, _,_,pbtoL, cp := recursionstep(M, L, pbtoLs[#pbtoLs] : RndOnly := RndOnly);
		vprintf STSA, 3 : "[STSAc2] recursionstep returns; Dimension(M) = %o, Type(h) = %o\n", Dimension(M), Type(h);
		
		/* Parse the result. */
		if Dimension(M) eq 0 and Type(h) eq SeqEnum and #h eq 0 then
			//This is the "code" for: we are done (Cn SC is the culprit)
		elif Type(h) eq AlgLieElt then
			Append(~hs, [h]);
			Append(~pbtoLs, pbtoL);
		elif Type(h) eq SeqEnum then
			Append(~hs, h);
			Append(~pbtoLs, pbtoL);
		else
			error Sprintf("Cannot handle h of type %o", Type(h));
		end if;

		//Print progress in each step, for fun.
		vprintf STSA, 3: "[STSAc2] Calling ConstructH...\n"; 
		IndentPush();
		H := constructH(L, arL, pbtoLs, hs);
		IndentPop();
		vprintf STSA, 3: "[STSAc2] Done. Dim(H) = %o\n", Dimension(H);
		
		b := DR_IsSTSA(L,H);
		Append(~cps, <cp, H>);
		vprintf STSA, 1: "H = %o, STSA: %o\n", H, b;
		if not b then
			error "!!! This broke the splitness of H. Bailing out!!!";
		end if;
	end while;
	
	vprintf STSA, 1: "[STSAc2] Done. Control paths taken: %o\n", cps;
	return H, cps;
end function;


function findSTSAChar2(L : MaxTries := 10, StartH := false, TryMaximal := true, RndOnly := false) //->AlgLie
/* A split Cartan subalgebra (split maximal toral subalgebra) of the 
structure constant Lie algebra L that is defined over a finite field
of characteristic 2. The algorithm used is Monte Carlo, and has only
been tested for reductive Lie algebras. */
	local F, H, i, e;
	
	F := BaseRing(L);
	assert Characteristic(F) eq 2;
	assert IsFinite(F);
	
	/* We look in the p-restrictable part of L */
	if StartH cmpeq false then
		vprintf STSA, 1 : "[STSAc2] Computing restrictable part of L...\n"; 
		restr, pmap := IsRestrictable(L);
		if not restr then error "L is not restrictable. Is it reductive?"; end if;
		qmap := pmap^(Degree(F));
		LL := sub<L | [ qmap(b) : b in Basis(L) ]>;
		if Dimension(LL) eq 0 then LL := L; end if; //A1[SC] patch
	else
		LL := L;
	end if;
	
	/* Find a dimension to "aim" for (if TryMaximal is set to `true')
	 * If L is (reductive and) split this should always be attainable; however if 
	 *    L is a twisted Lie algebra then this is almost never attainable -- possibly
	 *    resulting in a lot of wasted time (in view of MaxTries above)
	 */
	if Type(TryMaximal) eq RngIntElt then
		error if TryMaximal le 0, "TryMaximal as integer should be positive.";
		aim_for_dim := TryMaximal;
		TryMaximal := true;
		vprintf STSA, 1: "[STSAc2] Dim(L) = %o, Dim(LL) = %o, aiming for Dim(H) = %o\n", Dimension(L), Dimension(LL), aim_for_dim;
	elif TryMaximal cmpeq true then
		aim_for_dim := ReductiveRank(LL : Check := false);
		if (aim_for_dim ne 0) then
			vprintf STSA, 1: "[STSAc2] Dim(L) = %o, Dim(LL) = %o, aiming for Dim(H) = %o\n", Dimension(L), Dimension(LL), aim_for_dim;
		else
			//A1[SC] patch
			TryMaximal := false;
			aim_for_dim := false;
			vprintf STSA, 1: "[STSAc2] Dim(L) = %o, Dim(LL) = %o.\n", Dimension(L), Dimension(LL);
		end if;
	else
		TryMaximal := false;
		aim_for_dim := false;
	end if;
	
	foundrf := recformat< HH, H, cps, happy >;
	seq_found := [];
	found_max_dim := -1;
	
	/* For C_n, SC, we prefer those H that split C_L(H) into A1's. */
	split2_CnSC := function(L, H)
		CLH := Centraliser(L,H);
		if Dimension(CLH) eq Dimension(H) then return true; end if;
		dsd := DirectSumDecomposition(CLH);
		return {Dimension(d) : d in dsd} subset {1,3};
	end function;
	
	for i in [1..MaxTries] do
		try
			HH, cps := mainrecursion(LL : StartH := StartH, RndOnly := RndOnly or (i ne 1), AimForDim := aim_for_dim);
			vprintf STSA, 1: "[STSAc2] HH = %o\n", HH;
			assert HH cmpne false;
			
			dimHH := Dimension(HH);
			if (not TryMaximal) or (dimHH ge aim_for_dim) or (dimHH ge found_max_dim) then
				found_max_dim := dimHH;
				H := sub<L | [ L!(LL!b) : b in Basis(HH) ]>;
				happy := split2_CnSC(L, H);
				found := rec<foundrf | HH := HH, H := H, cps := cps, happy := happy >;
				Append(~seq_found, found);
			end if;
		catch e
			vprintf STSA, 1: "error in findSTSAChar2: %o\n", e;
			e := false;
			HH := false;
		end try;
		
		if (HH cmpne false) and ((not TryMaximal) or (dimHH ge aim_for_dim)) and (happy) then break; end if;
	end for;
	
	if found_max_dim ne -1 then
		assert found_max_dim eq Maximum([ Dimension(r`H) : r in seq_found ]);
		/* Select one of maximal dimension -- in case of ties select one that has happy = true */
		cands := [ r : r in seq_found | Dimension(r`H) eq found_max_dim ];
		cands2 := [ r : r in cands | r`happy ];
		if #cands2 gt 0 then
			r := Representative(cands2);
		else
			assert #cands gt 0;
			r := Representative(cands);
		end if;
		assert DR_IsSTSA(L, r`H);
		vprintf STSA, 1 : "[STSAc2] Done. Dim(H) = %o\n", Dimension(H);
		return r`H, r`cps;
	else
		error "findSTSAChar2 failed.";
	end if;
		
end function;



