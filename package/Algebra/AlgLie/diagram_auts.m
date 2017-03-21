freeze;

/* 
 * Dan Roozemond, 2010. 
 */

an_diagram_auts := function(rnk)
	local G;

	G := Sym(rnk);
	
	if rnk in {1,2} then
		return G;
	else
		return sub<G | (1,rnk)>;
	end if;
end function;

dn_diagram_auts := function(rnk)
	local G;

	G := Sym(rnk);
	
	if rnk in {1,2} then
		return G;
	elif rnk eq 3 then
		return sub<G | (2,3) >;
	elif rnk eq 4 then
		return sub<G | (1,3),(1,4) >;
	else
		return sub<G | (rnk-1,rnk)>;
	end if;
end function;

extend_root_automorphism := function(R, pi)
	local Q, j, r, rn;

	assert Degree(Parent(pi)) eq Rank(R);

	Q := [ i^pi : i in [1..Rank(R)] ];
	for i in [Rank(R)+1..2*NumPosRoots(R)] do
		r := Root(R,i : Basis := "Root");
		rn := Vector(PermuteSequence(Eltseq(r), pi^-1));
		j := RootPosition(R, rn : Basis := "Root");
		if j eq 0 then
			printf "%o -> %o\n", r, rn;
			error "extend_diagram_aut: Invalid automorphism?";
		end if;
		Q[i] := j;
	end for;

	return Sym(2*NumPosRoots(R))!Q;
end function;
