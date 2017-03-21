freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "findframe.m":findframe;
import "chevbasmain.m":ismultof;

chevbasis_A1_Ad_char2 := procedure(~CBD)
	//x*y = h, h is central.

	local x, y, h, c, L;

	L := CBD`L;

	findframe(~CBD);

	if CBD`NRoots eq 0 then
		error "This is not the adjoint A_1";
	end if;

	//Check
	x := CBD`EigenSpaces[1]; y := CBD`EigenSpaces[2]; h := CBD`SCSAVectors[1];
	if ismultof(L!h, (L!x)*(L!y)) cmpeq false then
		error "Could not create chevalley basis for A1 over characteristic 2";
	end if;
	
	//Scale
	c := ismultof(L!x, (L!x)*(L!h));
	if c cmpeq false then error "Problem in chevbasis_A1_Ad_char2"; end if;
	
	//x*h should be 1*x
	h := h/c;
	if L!y*L!h ne L!y then error "Problem in chevbasis_A1_Ad_char2"; end if;

	//Done
	CBD`BasisPos := [x];
	CBD`BasisNeg := [y];
	CBD`BasisCart := [h];
end procedure;


chevbasis_A1_SC_char2 := procedure(~CBD)
	//x*y = 0; x*h = x, y*h = y;

	local h, V, bs, L, x, y;

	L := CBD`L;
	if (Dimension(Centre(L)) ne 1) then
		error "This is not the simply connected A_1";
	end if;

	h := L!(Basis(Centre(L))[1]);
	V := Complement(VectorSpace(BaseRing(L), 3), VectorSpaceWithBasis([Vector(h)]));
	bs := Basis(V);
	
	//Check
	if ismultof(L!h, (L!bs[1])*(L!bs[2])) cmpeq false then
		error "Could not create chevalley basis for A1 over characteristic 2";
	end if;

	//Scale
	x := bs[1]; y := bs[2];
	c := ismultof(L!h, L!x*L!y);
	if c cmpeq false then error "Problem in chevbasis_A1_SC_char2"; end if;
	
	//x*y should be 1*h
	x := x/c;

	CBD`BasisPos := [L | x];
	CBD`BasisNeg := [L | y];
	CBD`BasisCart := [L | h];
end procedure;

chevbasis_A1_char2 := procedure(~CBD)
	local issc;

	if CBD`R cmpeq false then
		issc := Dimension(Centre(CBD`L)) eq 1;
		if issc then
			print "[A1 is SC]";
			CBD`R := RootDatum("A1" : Isogeny := "SC");
		else
			print "[A1 is Ad]";
			CBD`R := RootDatum("A1" : Isogeny := "Ad");
		end if;
	else
		issc := IsSimplyConnected(CBD`R);
	end if;

	if issc then chevbasis_A1_SC_char2(~CBD);
	else		 chevbasis_A1_Ad_char2(~CBD);
	end if;
end procedure;

