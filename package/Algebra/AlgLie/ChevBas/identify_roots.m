freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasmain.m":ismultof;
import "cartints.m":cartint_for_L;

fundrtsset_by_cartints := function(M)
	//Follow procedure described in the thesis...
	local posi, posv, tormv, i, j, p, N;	
	
	//Find system of positive roots
	N := NumberOfColumns(M); assert N eq NumberOfRows(M);
	posi := []; posv := {@ @};
	for i in [1..N] do for j in [1..N] do
		if not IsZero(M[i][j]) then
			if M[i][j] gt 0 then Append(~posi, i); Include(~posv, M[i]); end if;
			break j;
		end if;
	end for; end for;
	
	//Find nonsimple roots
	tormv := {};
	for i in [1..#posi] do for j in [(i+1)..#posi] do
		p := Position(posv, posv[i] + posv[j]);
		if p ne 0 then Include(~tormv, posi[p]); end if;
	end for; end for;
		
	//Return the remainder
	return { i : i in posi | i notin tormv };
end function;
	

compute_posnegpairs := procedure(~CBD)
	local c, n, n2, i, e, todo, ret, retposneg, L;

	if assigned CBD`PosNegPairs then
		return;
	end if;

	L := CBD`L;
	retposneg := {}; 
	todo := {1..CBD`NRoots};
	while #todo gt 0 do
		e := CBD`EigenVectors[Representative(todo)];
		c := { i : i in [1..CBD`NRoots] | CBD`EigenVectors[i] eq -e or
			CBD`EigenVectors[i] eq e };
		if #c ne 2 then
			error "Cannot select PNP (2)";
		end if;

		Include(~retposneg, c);
		todo diff:= c;
	end while;

	CBD`PosNegPairs := retposneg;
end procedure;

compute_cartints_and_degrees := procedure(~CBD)
	/* degree(i) := #{j : cartint(i,j) = -1 } */
	local M, deg, a, n;

	//We avoid computing them more than once
	if assigned CBD`CartInts then return; end if;

	compute_posnegpairs(~CBD);
	n := CBD`NRoots;
	M := ZeroMatrix(Integers(), n,n);
	deg := [Integers()| 0 : i in [1..n]];

	for i in [1..n] do for j in [1..n] do
		a := cartint_for_L(CBD, i, j);
		if a cmpeq false then
			printf "Could not compute Cartan Integer for roots %o and %o\n", i, j;
			error "Stop.";
		end if;
		M[i][j] := a; 
		if a eq -1 then deg[i] +:= 1; end if;
	end for; end for;

	CBD`CartInts := M;
	CBD`Degs := deg;
end procedure;

extend_simple_rts := function(CBD)
	local L, R, es, ev,
		i, j, k, NPR, ret, rt, rt2, smch, pairs, x;

	L := CBD`L;
	R := CBD`R;
	es := CBD`EigenSpaces; ev := CBD`EigenVectors;
	ret := CBD`IndFund;
	rnk := Rank(R);
	NPR := NumPosRoots(R);
	retcands := [* [] : i in [1..2*NPR] *];
	smch := CBD`char in {2,3};

	pairs := [];
	if smch then
		pairs := [* [* *] : i in [1..2*NPR] *];
		for i in [1..2*NPR] do for j in [(i+1)..2*NPR] do
			k := RootPosition(R, Root(R,i) + Root(R,j));
			if k ne 0 then
				Append(~(pairs[k]), <i,j>);
			end if;
		end for; end for;
	end if;

	//First simple negative roots, then the nonsimples
	for i in [NPR+1..NPR+rnk] cat [rnk+1..NPR] cat [NPR+rnk+1..2*NPR] do
		if IsDefined(ret,i) then continue; end if;

		rt := Root(R,i : Basis := "Root");
		rt2 := &+[ rt[i]*ev[CBD`IndFund[i]] : i in [1..rnk] ];\
		if (IsZero(rt2)) then
			//print " --> root is zero";
			continue;
		end if;
		k := [ j : j in [1..#ev] | ev[j] eq rt2 and j notin ret ];
		if #k eq 0 then 
			return false, ret, _;
		elif #k gt 1 then
			if not smch then
				print "Characteristic of the field is big enough, but still trouble?";
				return false, ret, _;
			end if;
			//See how eigenspaces hold up...
			if i in [NPR+1..NPR+rnk] then
				//simple neg rt.
				j := 1; while j le #k do
					x := es[ret[i-NPR]]*es[k[j]];
					//x should be in cartan and nonzero
					if IsZero(x) then Remove(~k, j);
					else			  j +:= 1;
					end if;
				end while;
			else
				//nonsimple
				//check pairs
				j := 1;
				while j le #k do
					ok := true;

					//check against minus this root, should end up in H
					j0 := (i gt NPR select i-NPR else i+NPR);
					if IsDefined(ret,j0) then
						if es[ret[j0]]*es[k[j]] notin CBD`H then
							ok := false;
						end if;
					end if;

					//check agains pairs that should add up to this root
					prs := pairs[i];
					for pr in prs do
						if not ok then break; end if;

						if not (IsDefined(ret,pr[1]) and IsDefined(ret,pr[2])) then 
							continue;
						end if;
						x := (L!es[ret[pr[1]]])*(L!es[ret[pr[2]]]);
						if not IsZero(x) and not x in sub<L|es[k[j]]> then
							ok := false;
							break;
						end if;
					end for;

					if not ok then Remove(~k, j); 
					else			j +:=1;
					end if;
				end while;

			end if;

			if #k gt 1 then
				print "    Ambiguity in identifying roots!";
			end if;
		end if;

		if #k eq 1 then
			ret[i] := k[1];
		elif #k gt 1 then
			retcands[i] := k;
		end if;
	end for;

	if exists{i : i in [1..2*NumPosRoots(R)] | not IsDefined(ret,i)} then
		return false, ret, retcands;
	end if;

	return true, ret;
end function;

angles_and_degrees_fundset := function(CBD)
	local angles, deg, indfundset;

	indfundset := Setseq(CBD`IndFundSet);
	if #indfundset eq 0 then
		error "Error: Number of simple roots is 0";
	end if;

	angles := Matrix([[ CBD`CartInts[i][j] : j in indfundset] : i in indfundset]);
	deg := [ #[j : j in [1..#indfundset] | angles[i][j] eq -1 ] : i in [1..#indfundset] ];
	
	return angles, deg, indfundset;
end function;

identify_simple_rts_An := function(CBD)
	local angles, deg, ep, c, ret, i,j,n;

	/* note: ret contains elements in [1..n], indexing elements
		of indfund. They are mapped to indices of es/ev only 
		upon returning */
	ret := [Integers()|]; 
	n := Rank(CBD`R);

	angles, deg, simpseq := angles_and_degrees_fundset(CBD);

	//Exception
	if n eq 1 then
		return true, simpseq[[1]];
	end if;

	//Select endpoints of the diagram
	ep := [i : i in [1..n] | deg[i] eq 1];
	if #ep ne 2 then return false,_; end if;
	ret[1] := ep[1];
	ret[n] := ep[2];
	
	//Identify intermediate points
	for i in [2..(n-1)] do
		c := [ j : j in [1..n] | angles[ret[i-1]][j] eq -1 and j notin ret ];
		if #c eq 0 then return false,_; end if;
		ret[i] := c[1];
	end for;
	
	//Check whether n-1-st node is OK
	if not angles[ret[n-1]][ret[n]] eq -1 then return false,_; end if;

	//Done
	return true, simpseq[ret];
end function;

identify_simple_rts_D1 := function(CBD)
	local b, retA, ret;

	b,retA := identify_simple_rts_An(CBD);
	if not b then return false,_; end if;
	return true, retA;
end function;
identify_simple_rts_D3 := function(CBD)
	local b, retA, ret;

	b,retA := identify_simple_rts_An(CBD);
	if not b then return false,_; end if;

	ret := retA[[2,1,3]];

	return true, ret;
end function;
identify_simple_rts_Dn := function(CBD)
	local angles, deg, ep, tr, c, ret, i,j,n;

	/* note: ret contains elements in [1..n], indexing elements
		of indfund. They are mapped to indices of es/ev only 
		upon returning */
	ret := [Integers()|]; 
	n := Rank(CBD`R);
	
	if (n eq 1) then
		return identify_simple_rts_D1(CBD);
	elif (n eq 2) then
		//D2 = A1 + A1
		error "D2 is not irreducible";
	elif (n eq 3) then 
		return identify_simple_rts_D3(CBD);
	end if;

	angles, deg, simpseq := angles_and_degrees_fundset(CBD);

	//Identify point of degree three
	ep := [i: i in [1..n] | deg[i] eq 3];
	if #ep ne 1 then return false,_; end if;
	tr := ep[1];
	ret[n-2] := tr;

	//Identify end points: points of degree
	//  1 incident with tr
	ep := [i : i in [1..n] | deg[i] eq 1 and angles[i][tr] eq - 1];
	if #ep ne (n eq 4 select 3 else 2) then return false,_; end if;
	ret[n-1] := ep[1]; ret[n] := ep[2];

	//Identify the rest
	for i in [n-3..1 by -1] do
		c := [ j : j in [1..n] | angles[ret[i+1]][j] eq -1 and j notin ret ];
		if #c eq 0 then return false,_; end if;
		ret[i] := c[1];
	end for;

	//Check whether 1st node is OK
	if not angles[ret[1]][ret[2]] eq -1 then return false,_; end if;

	//Done
	return true, simpseq[ret];
end function;

identify_simple_rts_En := function(CBD)
	local angles, deg, ep, ep2, series, reqc,
		tr, b,c, ret, i,j,k,n;

	/* note: ret contains elements in [1..n], indexing elements
		of indfund. They are mapped to indices of es/ev only 
		upon returning */
	ret := [Integers()|]; 
	n := Rank(CBD`R);

	angles, deg, simpseq := angles_and_degrees_fundset(CBD);

	//Identify point of degree three
	ep := [i: i in [1..n] | deg[i] eq 3];
	if #ep ne 1 then return false,_; end if;
	tr := ep[1];
	ret[4] := tr;

	//Find points incident with tr
	ep := [i : i in [1..n] | angles[i][tr] eq -1];
	if #ep ne 3 then return false,_; end if;

	// Identify end point: point of degree
	//  1 incident with tr
	ep2 := [i : i in ep | deg[i] eq 1];
	ep := [i : i in ep | deg[i] ne 1];
	if #ep2 ne 1 then return false,_; end if;
	ret[2] := ep2[1];

	//Identify the two series going in each direction
	series := [ [tr, ep[1]], [tr, ep[2]] ];
	for i in [1..2] do
		b := true; k := #series[i];
		while b do
			c := [ j : j in [1..n] | 
				angles[series[i][k]][j] eq -1 and j notin series[i] ];
			if #c ne 0 then
				Append(~series[i], c[1]);
				k +:= 1;
			else
				b := false;
			end if;
		end while;
	end for;

	//Map these two series on the roots
	c := [ #s : s in series ];
	if c[1] gt c[2] then Reverse(~c); Reverse(~series); end if;
	reqc := []; reqc[6] := [3,3]; reqc[7] := [3,4]; reqc[8] := [3,5];
	if c ne reqc[n] then return false,_ ; end if;
	ret[1] := series[1][3];
	ret[3] := series[1][2];
	for i in [5..n] do ret[i] := series[2][i-3]; end for;

	//Done
	return true, simpseq[ret];
end function;

identify_simple_rts_BC1 := function(CBD, tp)
	local b, retA, ret;

	b,retA := identify_simple_rts_An(CBD);
	if not b then return false,_; end if;

	return true, retA;
end function;
identify_simple_rts_BCn := function(CBD, tp)
	local cis, deg, ep, tr, c, ret, i,j,n;

	/* note: ret contains elements in [1..n], indexing elements
		of indfund. They are mapped to indices of es/ev only 
		upon returning */
	ret := [Integers()|]; 
	n := Rank(CBD`R);

	if (n eq 1) then 
		return identify_simple_rts_BC1(CBD, tp);
	end if;

	cis, deg, simpseq := angles_and_degrees_fundset(CBD);

	//Identify point where length changes (a -2 occurs),
	// and the long (?) root
	ep := [ <i,j>: i in [1..n] | 
		exists(j){j : j in [1..n] | cis[i][j] eq -2 } ];
	if #ep ne 1 then return false,_; end if;
	if tp eq "B" then
		tr := ep[1][1];
		ret[n-1] := tr;
		ret[n] := ep[1][2];
	elif tp eq "C" then
		tr := ep[1][2];
		ret[n-1] := tr;
		ret[n] := ep[1][1];
	else
		return false, _;
	end if;

	//Identify the rest
	for i in [n-2..1 by -1] do
		c := [ j : j in [1..n] | cis[ret[i+1]][j] eq -1 and j notin ret ];
		if #c eq 0 then return false,_; end if;
		ret[i] := c[1];
	end for;

	//Done
	return true, simpseq[ret];
end function;
identify_simple_rts_Bn := func<CBD | identify_simple_rts_BCn(CBD, "B")>;
identify_simple_rts_Cn := func<CBD | identify_simple_rts_BCn(CBD, "C")>;

identify_simple_rts_F4 := function(CBD)
	local cis, deg, ep, tr, c, ret, i,j,n;

	/* note: ret contains elements in [1..n], indexing elements
		of indfund. They are mapped to indices of es/ev only 
		upon returning */
	ret := [Integers()|]; 
	n := Rank(CBD`R);

	cis, deg, simpseq := angles_and_degrees_fundset(CBD);

	//Identify point where length changes (a -2 occurs),
	// and the long (?) root
	ep := [ <i,j>: i in [1..n] | 
		exists(j){j : j in [1..n] | cis[i][j] eq -2 } ];
	if #ep ne 1 then return false,_; end if;
	ret[2] := ep[1][1]; 
	ret[3] := ep[1][2];

	//Identify the rest
	c := [ j : j in [1..n] | cis[j][ret[2]] eq -1 and j notin ret ];
	if #c eq 0 then return false,_; end if;
	ret[1] := c[1];
	c := [ j : j in [1..n] | cis[ret[3]][j] eq -1 and j notin ret ];
	if #c eq 0 then return false,_; end if;
	ret[4] := c[1];

	//Done
	return true, simpseq[ret];
end function;

identify_simple_rts_G2 := function(CBD)
	local cis, deg, ep, tr, c, ret, i,j,n;

	/* note: ret contains elements in [1..n], indexing elements
		of indfund. They are mapped to indices of es/ev only 
		upon returning */
	ret := [Integers()|]; 
	n := Rank(CBD`R);

	cis, deg, simpseq := angles_and_degrees_fundset(CBD);

	//Identify point where length changes (a -3 occurs),
	ep := [ <i,j>: i in [1..n] | 
		exists(j){j : j in [1..n] | cis[i][j] eq -3 } ];
	if #ep ne 1 then return false,_; end if;
	ret[2] := ep[1][1]; 
	ret[1] := ep[1][2];

	//Done
	return true, simpseq[ret];
end function;





identify_simple_rts := procedure(~CBD)
	local b, r, rnk, tp;

	if not IsIrreducible(CBD`R) then
		error "Cannot identify roots for non-irreducible root data yet.";
	elif Rank(CBD`R) eq 0 then
		error "Cannot identify roots for trivial root data yet.";
	else
		tp := CartanName(CBD`R)[1];
		rnk := Rank(CBD`R);
		if   tp eq "A" then b,r := identify_simple_rts_An(CBD);
		elif tp eq "B" then b,r := identify_simple_rts_Bn(CBD);
		elif tp eq "C" then b,r := identify_simple_rts_Cn(CBD);
		elif tp eq "D" then b,r := identify_simple_rts_Dn(CBD);
		elif tp eq "E" then b,r := identify_simple_rts_En(CBD);
		elif <tp,rnk> eq <"F",4> then b,r := identify_simple_rts_F4(CBD);
		elif <tp,rnk> eq <"G",2> then b,r := identify_simple_rts_G2(CBD);
		else
			error "Cannot identify roots for root data of type " cat tp;
		end if;
	end if;

	if not b then
		error "Failed to identify roots for root datum of type " cat CartanName(CBD`R);
	end if;

	CBD`IndFund := r;
end procedure;


compute_idrts := procedure(~CBD : PermuteRoots := false)
	local ok;

	compute_cartints_and_degrees(~CBD);
	vprintf ChevBas, 3: "[IDRTS] Degrees: %o\n", CBD`Degs; 

	CBD`IndFundSet := fundrtsset_by_cartints(CBD`CartInts);
	vprintf ChevBas, 3: "[IDRTS] FundSet: %o\n", CBD`IndFundSet; 

	identify_simple_rts(~CBD);
	vprintf ChevBas, 3: "[IDRTS] Fund: %o\n", CBD`IndFund; 

	ok, CBD`IndRts := extend_simple_rts(CBD);
	if not ok then error "Error: Could not extend simple rts"; end if;

	if PermuteRoots cmpne false then
		CBD`IndRts := PermuteSequence(CBD`IndRts, PermuteRoots);
	end if;

	vprintf ChevBas, 3: "[IDRTS] IndRts: %o\n", CBD`IndRts; 
end procedure;

check_indrts := function(CBD) 
	local i,j,k,b,c,r, 
		R,L,es, indrts,
		xij, xk;

	vprint ChevBas, 4: "-------------------------------"; 

	R := CBD`R;
	L := CBD`L;
	es := CBD`EigenSpaces;
	indrts := CBD`IndRts;

	r := true;
	for i in [1..CBD`NRoots] do
		for j in [(i+1)..CBD`NRoots] do
			if not IsDefined(indrts, i) or 
				not IsDefined(indrts,j) or
				j -i eq Floor(CBD`NRoots/2) then
				continue;
			end if;
	
			k := RootPosition(R, Root(R,i) + Root(R,j));
			if k eq 0 then
				b := IsZero( (L!es[indrts[i]])*(L!es[indrts[j]]) );
				c := b select "" else " (k=0)";
			elif not IsDefined(indrts,k) then
				b := false;
				c := " (indrts[k] not defined)";
			else
				xk := L!es[indrts[k]];
				xij := (L!es[indrts[i]])*(L!es[indrts[j]]);
				b := (ismultof(xk, xij) cmpne false);
				c := b select "" else " (eigenspc don't match)";
			end if;

			r := r and b;
			if b then continue; end if;

			vprintf ChevBas, 4: "i = %o, j = %o, k = %o, ok = %o%o\n", i, j, k, b, c;

		end for;
	end for;

	if (r) then vprint ChevBas, 4: "[All OK]"; end if;
	vprintf ChevBas, 4: "-------------------------------"; 

	return r;
end function;
