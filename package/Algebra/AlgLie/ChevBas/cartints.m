freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasmain.m":ismultof;

pairing_e_f := func<R,i,j | (i eq j) select 1 else 0 >;
pairing_e_alphast := func<R,i,j | Coroot(R,j)[i] >;
pairing_alpha_f := func<R,i,j | Root(R,i)[j] >;
pairing_alpha_alphast := func<R,i,j | CartanInteger(R,i,j) >;

findminofroot := function(CBD, i)
	local c, j, r, ev;

	if not assigned CBD`PosNegPairs then
		ev := CBD`EigenVectors;
		c := 0;
		for j in [1..CBD`NRoots] do
			if i eq j then continue; end if;
			if ev[j] ne -(ev[i]) then continue; end if;

			c +:= 1;
			r := j;
		end for;
		if c ne 1 then
			error "angle: cannot uniquely identify minus of root " cat IntegerToString(i);
		end if;
		return r;
	else
		if not exists(c){c : c in CBD`PosNegPairs | i in c} then
			error "angle: cannot find minus of root " cat IntegerToString(i);
		end if;
		return Representative(c diff {i});
	end if;
end function;

findrchaininset := function(S, rr, ss)
	//Finds an r-chain through s:
	//ch = [ -pr+s, .., s, ..., qr+s ]
	//returns p,q,ch;

	local p, q, t, ch;
	p := 0; q := 0; 
	ch := [ ss ];

	t := ss;
	while true do
		p +:= 1;
		t -:= rr;
		if t notin S then break; end if;
		if t in ch then 
			error "Field too small to find root chain. "; 
		end if;
		Insert(~ch, 1, t);
	end while;

	t := ss;
	while true do
		q +:= 1;
		t +:= rr;
		if t notin S then break; end if;
		if t in ch then 
			error "Field too small to find root chain."; 
		end if;
		Append(~ch, t);
	end while;

	return <p-1, q-1, ch>;
end function;

cartint_by_chain := function(S, a, b)
	local e,t;
	//<\beta, \alpha\ch> = p - q.

	//Special values for a = +- b
	if a eq b then return 2; end if;
	if a eq -b then return -2; end if;

	//Chain is through a, with b
	t := findrchaininset(S, b, a);
	return t[1] - t[2];
end function;

cartint_for_L_simply_laced := function(CBD, i, j)
	//In the simply laced case, the chains can never be very long,
	//   so even in char.2 there is not an issue:
	//<\beta, \alpha\ch> = p - q.
	local p,q, x,y, miny;

	if i eq j then return 2; end if;
	if {i,j} in CBD`PosNegPairs then return -2; end if;

	x := (CBD`L)!(CBD`EigenSpaces[j]);
	y := (CBD`L)!(CBD`EigenSpaces[i]);
	minx := (CBD`L)!(CBD`EigenSpaces[findminofroot(CBD,j)]);
	p := (IsZero(minx*y) select 0 else 1);
	q := (IsZero(x*y) select 0 else 1);

	assert not ((p eq 1) and (q eq 1));
	return p-q;
end function;

cartint_for_L_doubly_laced_charnot2 := function(CBD, i, j)
	//In the doubly laced case, the chains can never be very long,
	//   so only issues in char. 2:
	//<\beta, \alpha\ch> = p - q.
	local p,q, x,y, miny;

	if i eq j then return 2; end if;
	if {i,j} in CBD`PosNegPairs then return -2; end if;

	x := (CBD`L)!(CBD`EigenSpaces[j]);
	y := (CBD`L)!(CBD`EigenSpaces[i]);
	minx := (CBD`L)!(CBD`EigenSpaces[findminofroot(CBD,j)]);
	if   not IsZero(minx*(minx*y)) then p := 2;
	elif not IsZero(minx*y) then p := 1;
	else p := 0;
	end if;
	if   not IsZero(x*(x*y)) then q := 2;
	elif not IsZero(x*y) then q := 1;
	else q := 0;
	end if;

	assert not ((p eq 2) and (q eq 2));

	return p-q;
end function;


compute_required_Nrs := procedure(~CBD)
	local e, s,p,n, pn, i, j, k, R, R1, R2, S, SC, NPR;

	/*Should actually use StructureConstants intrinsic,
	     but that's too much of a pain since that also
	     involves resolving what basis elements are where
		 in the Lie algebra. 
	  Or using posnegcar from package/LieThry/Const.m
      So we, annoyingly, do it this way..
	*/

	if assigned CBD`RequiredNrs then
		return;
	end if;

	R0 := CBD`R;
	ESS := CBD`ExtraspecialSigns;
	NPR := NumPosRoots(R0);
	rnk := Rank(R0);

	//Transfer my extraspecial signs to this copy of R
	R := RootDatum(SimpleRoots(R0), SimpleCoroots(R0));
	R1 := [ e[1] : e in ESS ]; 
	R2 := [ e[2] : e in ESS ];
	 S := [ e[3] : e in ESS ];
	R`ExtraspecialPairs := [ R1, R2 ];
	R`ExtraspecialSigns := S;

	//Create Lie algebra, read off Nrs from there
	L := LieAlgebra(R, Rationals());
	p,n := StandardBasis(L); pn := p cat n;
	ret := ZeroMatrix(Integers(), #pn, #pn);
	for i in [1..#pn] do for j in [(i+1)..#pn] do
		k := RootPosition(R, Root(R,i) + Root(R,j));
		if k eq 0 then continue; end if;
	
		s := ismultof(pn[k], pn[i]*pn[j]);
		if s cmpeq false then error "Could not find Nrs :s"; end if;

		ret[i][j] := s;
		ret[j][i] := -s;
	end for; end for;

	CBD`RequiredNrs := ret;
end procedure;

cartint_for_L := function(CBD, i, j)
	local e, t;

	//First, we try by chains, which works except if the characteristic is 2 or 3
	if CBD`char notin {2,3} then
		return cartint_by_chain(CBD`EigenVectors, CBD`EigenVectors[i], CBD`EigenVectors[j]);	
	end if;

	//In the simply laced case:
	if IsSimplyLaced(CBD`R) then
		return cartint_for_L_simply_laced(CBD,i,j);
	end if;

	//In the doubly laced case, char != 2
	if CBD`char ne 2 and CartanName(CBD`R)[1] ne "G" then
		return cartint_for_L_doubly_laced_charnot2(CBD, i, j);
	end if;

	//If that does not work, we fail.
	error Sprintf("Cannot compute cartan integer for %o in characteristic %o",
		CartanName(CBD`R), CBD`char);
end function;


findrchain := function(R, r, s)
	//r and s are root indices in R
	//Finds an r-chain through s:
	//ch = [ -pr+s, .., s, ..., qr+s ]
	//returns p,q,ch;

	return findrchaininset(Roots(R), Root(R,r), Root(R,s));
end function;

