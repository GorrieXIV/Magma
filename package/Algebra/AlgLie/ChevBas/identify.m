freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasdata.m":NewChevBasData;
import "identify_liealg_of_simp_grp.m":identify_liealgebra_of_simple_group;
import "identify_simple_liealg.m":identify_simple_liealg;
import "identify_twisted.m":identify_twisted;
import "../stsa.m":DR_IsSTSA;
import "../stsa-char2.m":findSTSAChar2;
import "../stsa-char3.m":findSTSACharNot2;
import "../derlie.m":ExtendHInDerL;

declare attributes AlgLie : ReductiveType, DidComputeSTSA;
redtp_recfmt := recformat<R, str, DSD, infos, H, assume_almost_simple>;

directsum_with_injections := function(Q)
	local i, inj, retR, retInj, rnks, cumrnks, simprtsRetR;

	assert #Q ge 1;

	//Make the direct sum
	retR := Q[1]; 
	for i in [2..#Q] do retR := DirectSum(retR, Q[i]); end for;

	//Make the injections
	simprtsRetR := [ RootPosition(retR, SimpleRoots(retR)[i]) : i in [1..Rank(retR)] ];
	rnks := [ Rank(R) : R in Q ];
	cumrnks := [ 0 ] cat [ &+(rnks[[1..i]]) : i in [1..#rnks] ];
	retInj := [*
		(rnks[i] ne 0) select
			hom< Q[i] -> retR | simprtsRetR[[cumrnks[i]+1..cumrnks[i]+rnks[i]]] >
		else
			false
		: i in [1..#Q] 
	*];

	//Done!
	return retR, retInj;
end function;

all_isogenies := function(tp, rnk)
	local sg, fg, inj, n, sgs, sgmt, sgcnt;

	fg := FundamentalGroup(tp cat IntegerToString(rnk));
	r := [* *];
	sgs := Subgroups(fg);
	sgmt := {* sg`order : sg in sgs *};
	sgcnt := [ 96 : i in [1..Maximum(sgmt)] ]; //96 <=> "a" etc
	
	for sg in sgs do
		_, inj := sub<fg | sg`subgroup>;
		n := IntegerToString(sg`order); 
		if (Multiplicity(sgmt, sg`order) gt 1) then
			sgcnt[sg`order] +:= 1;
			n cat:= CodeToString(sgcnt[sg`order]);
		end if;
		Append(~r, <n, inj>);
	end for;
	
	//Not strictly necessary, but a good idea nonetheless, despite
	//   the fact that it almost doubles the number of cases.
	Append(~r, <"Ad", "Ad">);
	Append(~r, <"SC", "SC">);

	return r;
end function;


nice_fullname_irred_rootdtm := function(R)
	local x, tp, ai, aiposs, p, phi, m;

	tp := CartanName(R)[1];

	if Determinant(CartanMatrix(R)) eq 1 then
		x := "";
	elif IsAdjoint(R) then
		x := "Ad";
	elif IsSimplyConnected(R) then
		x := "SC";
	elif (tp ne "D") or IsOdd(Rank(R)) then
		x := Sprintf("%2o", Order(IsogenyGroup(R)));
	else
		//Quite an ugly sort of hack, here...

		//What are the possible isogenies for Dn?
		ai := [ a : a in all_isogenies("D", Rank(R)) | a[1] notin {"Ad", "SC"} ];
		aiposs := [ { Eltseq(a[2](g)) : g in Domain(a[2]) } : a in ai ];

		//What isogeny is thisone?
		_,_,phi := IsogenyGroup(R);
		p := { Eltseq(phi(g)) : g in Domain(phi) };
		m := [ i : i in [1..#ai] | aiposs[i] eq p ];

		if #m eq 1 then x := ai[m[1]][1];
		else            x := Sprintf("%o?", Order(IsogenyGroup(R)));
		end if;
	end if;

	return CartanName(R) cat (#x gt 0 select "[" cat x cat "]" else "");
end function;

could_be_An := function(L, subL, subH, todoone)
	//Returns b, subLn, subHn, i
	//* b: whether subL could be an intermediate An, to which a one-dim
	//     trivial Lie algebra should be adjoined; if so:
    //* subLn: the new Lie algebra
	//* subHn: the new CSA
	//* i: the index of todoone that should be removed
	local n, subLn, C, i;

	n := Dimension(subH);

	if (#todoone eq 0) or (Dimension(subL) ne ((n+2)^2)-2) then
		return false, _, _, _; 
	end if;

	i := 1;
	C := todoone[i];
	subLn := sub<L | [ L!b : b in Basis(subL) ] cat [ L!b : b in Basis(C) ] >;
	
	return true, subLn, i;
end function;

function glue_constituents_back_together(L,H,Rs,CBDs)
	local retR, rootInjs, retCBD, R, CBD, phi;
	
	//Glue back together: R
	retR, rootInjs := directsum_with_injections(Rs);
	vprintf ChevBas, 2: "[ID]: R = %o\n", retR; 

	//Glue back together: CBD
	retCBD := NewChevBasData(retR, L, H);
	retCBD`BasisPos := [ L | ];
	retCBD`BasisNeg := [ L | ];
	retCBD`BasisCart := [ L | ];
	for i in [1..#CBDs] do 
		R := Rs[i]; CBD := CBDs[i]; phi := rootInjs[i];

		if Rank(R) gt 0 then
			//Normal thing
			for j in [1..Rank(R)] do
				(retCBD`BasisCart)[RootPosition(retR, phi(Root(R,j)))] 
					:= L!(CBD`BasisCart[j]);
			end for;

			for j in [1..NumPosRoots(R)] do
				(retCBD`BasisPos)[RootPosition(retR, phi(Root(R,j)))] 
					:= L!(CBD`BasisPos[j]);
				(retCBD`BasisNeg)[RootPosition(retR, phi(Root(R,j + NumPosRoots(R)))) - NumPosRoots(retR) ]
					:= L!(CBD`BasisNeg[j]);
			end for;
		else
			//Toral root datum
			(retCBD`BasisCart) cat:= [ L!b : b in CBD`BasisCart ];
		end if;
	end for;
	
	return retR, retCBD;
end function;

/* Careful when changing this! It is used directly by IsIsomorphic, too */
function identify_liealg_not_directsum(L, H : Select := "All", hintR := false) //-> SeqEnum, Tup
	local ret, ret0, tstart, tfirst, tt, proc;
	
	ret := [];
	tstart := Cputime(); tfirst := false;
	
	for proc in [* identify_liealgebra_of_simple_group, identify_simple_liealg, identify_twisted *] do
		ret0, tt := proc(L, H : Select := Select, hintR := hintR);
		ret cat:= ret0;

		if Select eq "First" and #ret gt 0 then 
			return ret, <Cputime()-tt, Cputime()-tstart>;
		elif tfirst cmpeq false and #ret gt 0 then
			tfirst := tt;
		end if;
	end for;
	
	//Done.
	if tfirst cmpeq false then tfirst := Cputime(); end if;
	return ret, <tfirst-tstart, Cputime()-tstart>;
end function;

/* Try to find a better STSA (than Hp) for Lp -- hopefully aiding ReductiveType.
 *   For now only active in D4, SC case.
 */
// --> todo: generalise this to general DnSC
function patch_stsa(L, H)
	p := Characteristic(BaseRing(L));
	n := Dimension(H);
	dim_z_DnSC := IsOdd(n) select 1 else 2;
	dimL := Dimension(L);
	if (p eq 2) and (dimL eq 2*n^2-n)  and (Dimension(Centre(L)) eq dim_z_DnSC) then
		//use ExtendHInDerL rather than LieAlgebraOfDerivations since this is much faster and we know
		//   the resulting Lie algebra to be identical.
		DerL, mps := ExtendHInDerL(L, H); 
		if Dimension(DerL) ne dimL then 
			vprintf ChevBas, 3 : "[ReductiveType-patch_stsa]: DnSC: Dim(DerL) = %o != Dim(L)\n", Dimension(DerL); 
			return false; 
		end if;
		
		//Check that DerL is indeed of type D4, Ad.
		try
			R, _, _, extra := ReductiveType(DerL : AssumeAlmostSimple);
		catch err
			vprintf ChevBas, 3 : "[ReductiveType-patch_stsa]: DnSC: ReductiveType failed for DerL.\n";
			return false; 			
		end try;
		if R ne RootDatum(Sprintf("D%o",n) : Isogeny := "Ad") then
			vprintf ChevBas, 3 : "[ReductiveType-patch_stsa]: DnSC: DerL is not DnAd.\n";
			return false; 			
		end if;

		//Use DerL's split toral subalgebra to make a nice one for L.
		mp1 := mps`mp_L_to_LL;
		LinDerL := sub<DerL | [ mp1(b) : b in Basis(L)]>;
		assert Dimension(LinDerL) eq dimL-dim_z_DnSC;
		HDerL := extra[1]`ChevBasData`H;
		assert Dimension(HDerL) eq n;
		
		//Compose; return.
		mp2 := mps`mp_LL_to_L;
		Hn := sub<L | Centre(L), sub<L | [ mp2(DerL!b) : b in Basis(HDerL meet LinDerL) ]> >;
		assert Dimension(Hn) eq n;
		return Hn;
	end if;
	return false;
end function;

intrinsic ReductiveType(L::AlgLie, H::AlgLie : AssumeAlmostSimple := false) -> RootDtm, MonStgElt, SeqEnum, SeqEnum
{ 
Attempt to identify the reductive Lie algebra L with a split toral subalgebra H.
Returns four values. The first is a root datum, the second is a string describing
the isomorphism type of L, the third is a decomposition Q of L into direct summands,
and the fourth is a sequence of records containing extra information on each of 
the elements of Q.
}
	if (assigned L`ReductiveType) then
		rt := L`ReductiveType;
		if (rt`H cmpeq H) and ((not rt`assume_almost_simple) or AssumeAlmostSimple) then
			return rt`R, rt`str, rt`DSD, rt`infos;
		end if;
	end if;
	
	if not (assigned L`DidComputeSTSA) then L`DidComputeSTSA := false; end if;

	if Characteristic(CoefficientRing(L)) eq 0 then
		require IsSplittingCartanSubalgebra(L,H) : "H is not a splitting Cartan subalgebra of L.";
		require Dimension(H*H) eq 0 : "H is not a splitting Cartan subalgebra of L.";
	else
		vprintf ChevBas, 2 : "[ReductiveType] Checking STSA...\n";
		require DR_IsSTSA(L,H) : "H is not a split toral subalgebra of L.";
	end if;
	
	hintR := false;
	if (assigned L`RootDatum) and (IsIrreducible(L`RootDatum)) then
		vprintf ChevBas, 2 : "[ReductiveType] L`RootDatum is assigned and irred. Using that.\n";
		hintR := L`RootDatum;
		DSD := [L];
	elif AssumeAlmostSimple or IsSimple(L) then
		vprintf ChevBas, 2 : "[ReductiveType] AssumeAlmostSimple or IsSimple.\n";
		DSD := [L];
	else
		vprintf ChevBas, 2 : "[ReductiveType] Computing DirectSumDecomposition...\n";
		DSD := DirectSumDecomposition(L);
	end if;
	
	/* Merge all Abelian constituents into one. */
	ab := [ i : i in [1..#DSD] | IsAbelian(DSD[i]) ];
	if #ab gt 1 then
		A := sub<L | &cat[ [ L!b : b in Basis(M) ] : M in DSD[ab] ]>;
		DSD := [ DSD[i] : i in [1..#DSD] | i notin ab ] cat [A];
	end if;
	
	/* For each constituent... */
	R := false; str := false; infos := []; 
	for i in [1..#DSD] do
		Lp := DSD[i]; Hp := Lp meet H; Hpn := false;
		vprintf ChevBas, 2 : "[ReductiveType] Working on L' (dim %o) w/ H' (dim %o)\n...", Dimension(Lp), Dimension(Hp);
		
		Q := identify_liealg_not_directsum(Lp, Hp : Select := "First", hintR := hintR);
		
		//in some cases, if this failed and we computed the STSA ourselves, we may patch it.
		if (L`DidComputeSTSA) and (#Q eq 0) then
			Hpn := patch_stsa(Lp, Hp);
			if Hpn cmpne false then
				vprintf ChevBas, 2 : "[ReductiveType] Failed & L`DidComputeSTSA. Computed Hpn: %o\n", Hpn;
				Q := identify_liealg_not_directsum(Lp, Hpn : Select := "First", hintR := hintR);
				if #Q ne 0 then
					vprintf ChevBas, 2 : "[ReductiveType] Hpn did the job! Patching things now.\n";
					Hp := Hpn;
					if #DSD eq 1 then
						H := Hp;
					else
						Hnw := sub<L | [ DSD[j] meet H : j in [1..#DSD] | j ne i] cat [Hp] >;
						assert Dimension(Hnw) eq Dimension(H);
						H := Hnw;
					end if;
				end if;
			end if;
		end if;
		
		if #Q eq 0 then 
			error Sprintf("Could not identify constituent %o of dimension %o, split toral subalgebra dimension %o", i, Dimension(Lp), Dimension(Hp));
		end if;
		assert #Q eq 1;
		
		q := Q[1]; Append(~infos, q);
		if R cmpeq false then R := q`R; else R := DirectSum(R, q`R); end if;
		if str cmpeq false then 
			str := q`str;
		else
			if i eq 2 then str := "Direct sum of " cat str; end if;
			str := str cat (i lt #DSD select ", " else " and ") cat q`str;
		end if;
	end for;
	
	if not assigned L`SplitMaximalToralSubalgebra then
		L`SplitMaximalToralSubalgebra := H;
	end if;
	L`ReductiveType := rec<redtp_recfmt | R := R, str := str, DSD := DSD, infos := infos, H := H, assume_almost_simple := AssumeAlmostSimple>;
	
	return R, str, DSD, infos;
end intrinsic;

intrinsic ReductiveType(L::AlgLie : AssumeAlmostSimple := false) -> RootDtm, MonStgElt, SeqEnum, SeqEnum
{ 
Attempt to identify the reductive Lie algebra L defined over a finite field k.
Returns four values. The first is a root datum, the second is a string describing
the isomorphism type of L, the third is a decomposition Q of L into direct summands,
and the fourth is a sequence of records containing extra information on each of 
the elements of Q. 
}
	if (assigned L`ReductiveType) then
		rt := L`ReductiveType;
		if ((not rt`assume_almost_simple) or AssumeAlmostSimple) then
			return rt`R, rt`str, rt`DSD, rt`infos;
		end if;
	end if;

	k := BaseRing(L);
	if Characteristic(k) eq 0 then
		H := SplittingCartanSubalgebra(L);
		return ReductiveType(L, H : AssumeAlmostSimple := AssumeAlmostSimple);
	elif Characteristic(k) gt 3 then
		H := SplitMaximalToralSubalgebra(L);
		return ReductiveType(L, H : AssumeAlmostSimple := AssumeAlmostSimple);
	else
		/* We might make bad choices for the split toral subalgebra -- so we have ourselves a couple of tries... */
		if assigned L`SplitMaximalToralSubalgebra then
			H0 := L`SplitMaximalToralSubalgebra;
			MAXTRIES := 2;
		else
			H0 := false;
			MAXTRIES := 10;
		end if;

		case Characteristic(k): 
			when 2: thef := func<L,i | findSTSAChar2(L : RndOnly := (i ge 2))>;
			when 3: thef := func<L,i | findSTSACharNot2(L)>;
			else:	error "Whoa!";
		end case;
			
		for i in [1..MAXTRIES] do
			try
				if ((i eq 1) and (H0 cmpne false)) then
					H := H0;
					L`DidComputeSTSA := false;
				else
					H := thef(L, i);
					L`DidComputeSTSA := true;
				end if;
				return ReductiveType(L, H : AssumeAlmostSimple := AssumeAlmostSimple);
			catch e
				if GetVerbose("ChevBas") ge 2 then
					printf "[ReductiveType] char. %o; attempt %o of %o failed.\n", Characteristic(k), i, MAXTRIES;
					IndentPush(); e; IndentPop();
				end if;
				laste := e;
			end try;
		end for;
		
		error Sprintf("%o", laste);
	end if;

end intrinsic;
