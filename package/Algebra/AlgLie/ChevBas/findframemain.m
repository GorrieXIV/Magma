freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasmain.m":ismultof,mult_dim_eigenspc;

MultMat := procedure(L, seq : Extr := false)
	local f;

	if Extr then
		f := func<i,j | L!seq[i]*(L!seq[i]*L!seq[j]) >;
	else
		f := func<i,j | L!seq[i]*L!seq[j] >;
	end if;

	IndentPush();
	Matrix([[IsZero(f(i,j)) select 0 else 1 : j in [1..#seq] ] : i in [1..#seq] ]);
	IndentPop();
end procedure;

insert_found_frame := procedure(~CBD, newspaces, newpairs)
	/* Update CBD so that its eigenspaces contain all the vectors
	   in the sequence newspaces, and include the corresponding 
	   newpairs into CBD`PosNegPairs.

	   newpairs may be "false", in which case it is automatically
	     created, and is assumed to be {2*i,2*i-1}_i

	   It's a bit messy, but all straightforward.
	*/

	local L, dubs, VSfull, oldspcs, 
		newbases,
		k, x, b, i,j,p,
		imgsofindices;

	//Take care of "optional" arguments.
	if newpairs cmpeq false then
		if (#newspaces mod 2) ne 0 then 
			error "insert_found_frame: newpairs is optional *only* if newspaces contains an even number of elements!";
		end if;

		newpairs := [ {2*i-1, 2*i} : i in [1..(#newspaces div 2)] ];
	end if;

	//Construct original spaces as vectorspaces.
	L := CBD`L;
	VSfull := VectorSpace(BaseRing(L), Dimension(L));
	dubs := mult_dim_eigenspc(CBD);
	oldspcs := [ sub<VSfull | [ Vector(b) : b in CBD`EigenSpaces[d] ] > : d in dubs ];

	//See which original spaces the new pairs are in
	newbases := [[] : s in oldspcs];
	for k in [1..#newspaces] do
		x := Vector(L!(newspaces[k]));
		b := false;
		for i in [1..#oldspcs] do
			if x in oldspcs[i] then
				b := true;
				Append(~(newbases[i]), <x,k>);
			end if;
		end for;
		if not b then
			error "Cannot insert spaces (1)";
		end if;
	end for; 

	//Check whether every space is fully given in the newspaces, and the
	//  "newbases" computed above.
	imgsofindices := [];
	for i in [1..#oldspcs] do
		if #(newbases[i]) gt 0 and (Dimension(oldspcs[i]) ne #(newbases[i])) then
			IndentPush();
			printf "oldspcs[%o] = \n", i; IndentPush(); oldspcs[i]; IndentPop();
			printf "but newbases[%o] = \n", i; IndentPush(); newbases[2]; IndentPop();
			IndentPop();
			error "Incompletely given space. Cannot insert spaces (2)";
		end if;
	end for;

	//Replace CBD`EigenSpaces by the new ones.
	for i in [1..#oldspcs] do
		for j in [1..#newbases[i]] do
			(CBD`EigenSpaces)[dubs[i][j]] := L!(newbases[i][j][1]);
			imgsofindices[newbases[i][j][2]] := dubs[i][j];
		end for;
	end for;

	//Adapt CBD`PosNegPairs. First remove old ones, then add new ones.
	if not assigned CBD`PosNegPairs then
		CBD`PosNegPairs := {};
	else
		CBD`PosNegPairs := { p : p in CBD`PosNegPairs | 
			forall{i : i in p | i notin imgsofindices } 
		};
	end if;
	for p in newpairs do
		if not forall{ i : i in p | IsDefined(imgsofindices,i)} then continue; end if;
		Include(~(CBD`PosNegPairs), { imgsofindices[i] : i in p });
	end for;
end procedure;



split_using_nullspace := function(L, Vin, pr)
	//Splits in two:
	//1: where both elements of the pair act as zero
	//2: where one or none of the elements of the pair does

	BVin := Basis(Vin);

	LHS := VerticalJoin([ 
		HorizontalJoin([ Vector(L!b*L!(p)) : p in pr ])
			: b in BVin ]);

	ns := Nullspace(LHS);

	return sub<Vin | [ b*Matrix(BVin) : b in Basis(ns) ]>;
end function;



function verify_straight_pair_pair(x1, y1, x2, y2)
	if ismultof(x1, y1) cmpne false then
		return false;
	end if;
	if ismultof(x2, y2) cmpne false then
		return false;
	end if;
	if IsZero(x1*y2) and IsZero(x2*y1) then
		return true;
	end if;
	if IsZero(x1*x2) and IsZero(y1*y2) then
		return true;
	end if;
	return false;
end function;
function verify_straight_pair_pair_by_indices(CBD, pr1, pr2)
	local p1, n1, p2, n2;
	if (Type(pr1) eq SeqEnum) then
		p1 := (CBD`L)!(CBD`EigenSpaces[pr1[1]]);
		n1 := (CBD`L)!(CBD`EigenSpaces[pr1[2]]);
		p2 := (CBD`L)!(CBD`EigenSpaces[pr2[1]]);
		n2 := (CBD`L)!(CBD`EigenSpaces[pr2[2]]);
	elif (Type(pr1) eq SetEnum) then
		p1 := (CBD`L)!(CBD`EigenSpaces[Min(pr1)]);
		n1 := (CBD`L)!(CBD`EigenSpaces[Max(pr1)]);
		p2 := (CBD`L)!(CBD`EigenSpaces[Min(pr2)]);
		n2 := (CBD`L)!(CBD`EigenSpaces[Max(pr2)]);
	else
		error "Unexpected variable type in verify_straight_pair_pair_by_indices";
	end if;
	return verify_straight_pair_pair(p1, n1, p2, n2);
end function;
function verify_straight(CBD)
	local i, j, ti, tj, pnp, es;
	if not assigned CBD`PosNegPairs then
		return false, "CBD`PosNegPairs not assigned.";
	end if;

	pnp := Setseq(CBD`PosNegPairs);
	es := CBD`EigenSpaces;

	for i in [1..#pnp] do for j in [(i+1)..#pnp] do
		ti := Setseq(pnp[i]); tj := Setseq(pnp[j]);
		if not verify_straight_pair_pair(
			es[ti[1]], es[ti[2]], es[tj[1]], es[tj[2]]) then

			if GetVerbose("ChevBas") ge 3 then
				printf "Pairs %o and %o: ERR\n", pnp[i], pnp[j]; 
				IndentPush();
				MultMat(CBD`L, CBD`EigenSpaces[ti cat tj]);
				IndentPop();
			end if;

			return false, Sprintf("Pairs %o and %o are not OK", pnp[i], pnp[j]);
		end if;
		vprintf ChevBas, 4: "Pairs %o and %o: OK\n", pnp[i], pnp[j]; 
	end for; end for;

	if #(&join(CBD`PosNegPairs)) ne #CBD`EigenSpaces then
		return false, "CBD`PosNegPairs is not complete.";
	end if;

	return true, "";
end function;


solve_quadr_gf_char2 := function(D)
	/* Solve x^2 + d1 x + d2 = 0 , for <d1,d2> in D
		Works only for Galois Fields of Characteristic 2

       returns b (boolean whether solutions exist),
		       v (a solution),
               n (nullspace -- add any element to v to get other solutions)
	*/
	local F, a, n, tovec, fromvec, LHS, RHS, b, V, N;

	if Type(D) eq Tup then D := [D]; end if;
	
	F := Parent(D[1][1]); a := F.1; n := Degree(F);
	tovec := func<x | Vector(Eltseq(x))>;
	fromvec := func<v | &+[ v[i]*((F.1)^(i-1)) : i in [1..NumberOfColumns(v)] ]>;

	LHS := HorizontalJoin([
			Matrix([ tovec(a^(2*i)) : i in [0..n-1] ])
			+ Matrix([ tovec(d[1]*(a^i)) : i in [0..n-1] ])
			: d in D ]);
	RHS := Vector(HorizontalJoin([ tovec(-d[2]) : d in D ]));
	
	b,V,N := IsConsistent(LHS, RHS);
	if b then
		return true, fromvec(V), [ fromvec(x) : x in Basis(N) ];
	else
		return false, _, _;
	end if;

end function;

find_acting_like_root := function(L, X, W)
	/*Solve: [x1 + ax2, [x1 + ax2,wi]] = 0, to a
	  i.e. [x1[x1,wi]] + a([x1[x2,wi]]+[x2[x1,wi]]) + a^2 [x2[x2,wi]] = 0
	*/
	local x1, x2, i, j, x1x1w, x1x2w, x2x2w, b, v, n, x;
	x1 := Random(X); x2 := Random(X);
	
	x1x1w := [ Vector(L!x1*(L!x1*L!w)) : w in Basis(W) ];
	x1x2w := [ Vector(L!x1*(L!x2*L!w)) + Vector(L!x2*(L!x1*L!w)) : w in Basis(W) ];
	x2x2w := [ Vector(L!x2*(L!x2*L!w)) : w in Basis(W) ];
	D := {};
	for j in [1..2] do for i in [1..Dimension(L)] do 
		if x2x2w[j][i] eq 0 and x1x2w[j][i] ne 0 then
			//Solution found!
			v := x1x1w[j][i]/x1x2w[j][i];
			return x1 + v*x2;
		elif x2x2w[j][i] ne 0 then
			//Add to quadratic todo
			Include(~D, < x1x2w[j][i]/x2x2w[j][i], x1x1w[j][i]/x2x2w[j][i]>); 
		end if;
	end for; end for;

	if #D eq 0 then
		//Everything will do?
		return x1;
	else
		b,v,n := solve_quadr_gf_char2(SetToSequence(D));
		if not b then return false; end if;
		return x1 + v*x2;
	end if;
end function;

findframe_pair_pair_A2 := function(L, xp,xm, yp,ym)
	local X, Y, xp2, xm2, yp2, ym2;

	//This can actually be done more efficiently, but 
	// that involves writing code. This works, too ;)

	X := VectorSpaceWithBasis([ Vector(xp), Vector(xm) ]);
	Y := VectorSpaceWithBasis([ Vector(yp), Vector(ym) ]);

	repeat
		xp2 := find_acting_like_root(L, X, Y);
		xm2 := find_acting_like_root(L, X, Y);
		if xp2 cmpeq false or xm2 cmpeq false then
			error "Error in findframe_pair_pair_A2";
		end if;
	until Rank(Matrix([xp2, xm2])) gt 1;

	repeat
		yp2 := find_acting_like_root(L, Y, X);
		ym2 := find_acting_like_root(L, Y, X);
		if yp2 cmpeq false or ym2 cmpeq false then
			error "Error in findframe_pair_pair_A2";
		end if;
	until Rank(Matrix([yp2, ym2])) gt 1;

	return L!xp2, L!xm2, L!yp2, L!ym2;
end function;








commut_mat := function(CBD, Q1, Q2)
	local L, es;
	L := CBD`L;
	es := CBD`EigenSpaces;
	return Matrix([[
		IsZero((L!es[q1])*(L!es[q2])) select 0 else 1 
		: q2 in Q2 ] : q1 in Q1]);
end function;

pairs_commute := function(CBD, pr1, pr2)
	local L, es;
	L := CBD`L;
	es := CBD`EigenSpaces;
	return forall{ <i,j> : i in pr1, j in pr2 | IsZero(L!(es[i])*L!(es[j])) };
end function;

findframe_pair_pair := procedure(~CBD, pr1, pr2 : SkipChecks := false)
	local xp, xm, yp, ym;

	if (not SkipChecks) and (pairs_commute(CBD, pr1, pr2)) then
		//Nothing to do
		return;
	end if;

	xp := (CBD`L)!((CBD`EigenSpaces)[pr1[1]]);
	xm := (CBD`L)!((CBD`EigenSpaces)[pr1[2]]);
	yp := (CBD`L)!((CBD`EigenSpaces)[pr2[1]]);
	ym := (CBD`L)!((CBD`EigenSpaces)[pr2[2]]);

	if (not SkipChecks) and (verify_straight_pair_pair(xp, xm, yp, ym)) then
		//This pair is already straight.
		return;
	end if;

	//We do A2 in every case, to save time... But this may not be appropriate.
	xp2, xm2, yp2, ym2 := findframe_pair_pair_A2(CBD`L, xp, xm, yp, ym);

	//If we failed, we don't change anything.
	if not verify_straight_pair_pair((CBD`L)!xp2, (CBD`L)!xm2, (CBD`L)!yp2, (CBD`L)!ym2) then
		return;
	end if;

	//Change contents of CBD
	(CBD`EigenSpaces)[pr1[1]] := xp2;
	(CBD`EigenSpaces)[pr1[2]] := xm2;
	(CBD`EigenSpaces)[pr2[1]] := yp2;
	(CBD`EigenSpaces)[pr2[2]] := ym2;
end procedure;


findframe_comm_quad_pair_pair := procedure(~CBD, quad, pivotpair1, pivotpair2)
	es := CBD`EigenSpaces;
	L := CBD`L;
	Q := es[quad]; 

	//We fix e_gamma, e_{-gamma}
	ep := es[pivotpair1[1]]; em := es[pivotpair1[2]];

	//Then compute e_{a+b+g} and e_{-(a+b+g)} since that's the image under
	//  the action of e_g on Q
	bla := [ Vector(ep*q) : q in Q ] cat [ Vector(em*q) : q in Q ];
	VSeabg := sub<Universe(bla)|bla>;
	eabg := L!(Basis(VSeabg)[1]);
	emabg := L!(Basis(VSeabg)[2]);

	//Then compute the entries of the quad from there.
 	_,v1,ns1 := IsConsistent(
		Matrix([Vector(Eltseq(ep*q) cat Eltseq(em*q)) : q in Q]), 
		Vector(Eltseq(eabg) cat Eltseq(0*eabg) ));
 	_,v2,ns2 := IsConsistent(
		Matrix([Vector(Eltseq(em*q) cat Eltseq(ep*q)) : q in Q]), 
		Vector(Eltseq(eabg) cat Eltseq(0*eabg) ));
 	_,v3,ns3 := IsConsistent(
		Matrix([Vector(Eltseq(ep*q) cat Eltseq(em*q)) : q in Q]), 
		Vector(Eltseq(emabg) cat Eltseq(0*emabg) ));
 	_,v4,ns4 := IsConsistent(
		Matrix([Vector(Eltseq(em*q) cat Eltseq(ep*q)) : q in Q]), 
		Vector(Eltseq(emabg) cat Eltseq(0*emabg) ));

	MQ := Matrix(Q);
	(CBD`EigenSpaces)[quad[1]] := L!(v1*MQ); //e_{a+b}
	(CBD`EigenSpaces)[quad[2]] := L!(v4*MQ); //e_{-(a+b)}
	(CBD`EigenSpaces)[quad[3]] := L!(v2*MQ); //e_{(a+b+2g)}
	(CBD`EigenSpaces)[quad[4]] := L!(v3*MQ); //e_{-(a+b+2g)}

	(CBD`EigenSpaces)[pivotpair1[1]] := ep;
	(CBD`EigenSpaces)[pivotpair1[2]] := em;
	(CBD`EigenSpaces)[pivotpair2[1]] := eabg;
	(CBD`EigenSpaces)[pivotpair2[2]] := emabg;

	Include(~(CBD`PosNegPairs), {quad[1], quad[2]});
	Include(~(CBD`PosNegPairs), {quad[3], quad[4]});
end procedure;

findframe_all_pairs := procedure(~CBD)
	//Straightens all pairs in PosNegPairs (!)
	local prs, noncomm, cnt, b, i, j, v, x, L, prind, todoset, todoseq;

	L := CBD`L;

	//prs is the sequence of pairs
	//noncomm[i][j] := ( prs[i] and prs[j] do not commute)
	//<i,j> in todo := ( prs[i] needs to be straightened wrt prs[j] )

	//Initialize prs
	prs := [ Setseq(p) : p in CBD`PosNegPairs | #p eq 2 ];

	//Initialize noncomm
	noncomm := ZeroMatrix(GF(2), #prs, #prs);
	for i in [1..#prs] do for j in [(i+1)..#prs] do
		b := forall{ a : a,b in [1,2] | 
			IsZero(L!(CBD`EigenSpaces[prs[i][a]])*L!(CBD`EigenSpaces[prs[j][b]])) };
		noncomm[i][j] := b select 0 else 1;
		noncomm[j][i] := b select 0 else 1;
	end for; end for;

	//Initialize todo
	todoset := { <i,j> : i,j in [1..#prs] | (i lt j) and (noncomm[i][j] eq 1) };
	todoseq := SetToSequence(todoset);

	//Straighten all the paris until there is nothing left to do
	cnt := 0;
	while #todoset gt 1 do
		vprintf ChevBas, 4: "[findframe_all_pairs] #todo = %o\n", #todoset;

		//Make sure we don't run into an infinite loop.
		cnt +:= 1; 
		if cnt gt 2*((#prs)^2) then
			error "findframe_all_pairs: Ran into an infinite loop.";
		end if;

		//Pick a (pair,pair)-pair, and straighten it.
		prind := todoseq[1];
		Exclude(~todoset, prind);
		Remove(~todoseq, 1);

		if verify_straight_pair_pair_by_indices(CBD, prs[prind[1]], prs[prind[2]]) then
			//Nothing to do for this pair
			continue;
		end if;

		//Try to straighten this pair...
		findframe_pair_pair(~CBD, prs[prind[1]], prs[prind[2]] : SkipChecks);

		//If we failed, change nothing
		if not verify_straight_pair_pair_by_indices(CBD, prs[prind[1]], prs[prind[2]]) then
			continue;
		end if;

		//If we succeeded, add all possible changed pairs of pairs to todo
		for i in [1,2] do
			v := noncomm[prind[i]];
			for j in [1..#prs] do
				if not IsZero(v[j]) then 
					x := {prind[i],j}; x := <Min(x), Max(x)>;
					if (x notin todoset) and (x ne prind) then
						Include(~todoset, x);
						Append(~todoseq, x);
					end if;
				end if;
			end for;
		end for;
	end while;
end procedure;
