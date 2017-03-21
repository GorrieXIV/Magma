freeze;

import "ChevBas/identify.m":identify_liealg_not_directsum;


declare verbose AlgLieIsom, 3;

intrinsic IsIsomorphism(phi::Map[AlgLie, AlgLie] : CheckInv := true) -> BoolElt
{ Check whether phi is an isomorphism of Lie algebras }
	L1 := Domain(phi);
	L2 := Codomain(phi);
	dL1 := Dimension(L1);
	
	//Stupid check
	if dL1 ne Dimension(L2) then
		vprintf AlgLieIsom,3 : "[IsIsomorphic] Dim(L1) != Dim(L2)\n";
		return false;
	end if;
	
	//Check it's a homomorphism
	for i,j in [1..dL1] do
		if phi((L1.i)*(L1.j)) eq phi(L1.i)*phi(L1.j) then continue; end if;
		
		//whoops
		vprintf AlgLieIsom,3 : "[IsIsomorphic] Not a homomorphism: phi(L1.%o*L1.%o) != phi(L1.%o)*phi(L1.%o)\n", i, j, i, j;
		return false;
	end for;
	
	//Check whether image is full Lie alg
	S2 := sub<L2 | [ phi(x) : x in Basis(L1) ]>;
	if Dimension(S2) ne Dimension(L2) then
		vprintf AlgLieIsom,3 : "[IsIsomorphic] Image generates a %o-dim subalgebra of L2 instead of the full L2 (%o-dim)\n", Dimension(S2), Dimension(L2);
		return false;
	end if;
	
	//Check the inverse, too
	if CheckInv then
		if HasPreimageFunction(phi) then
			ok := IsIsomorphism(Inverse(phi) : CheckInv := false);
			if not ok then
				vprintf AlgLieIsom,3 : "[IsIsomorphic] Inverse is not an isomorphism.\n";
				return false;
			end if;
		else
			vprintf AlgLieIsom, 3 : "[IsIsomorphic] Warning: Preimage function not defined!\n";
		end if;
	end if;

	//ok :)
	return true;
end intrinsic;

/* The is_known_isomorphic* things below all return three things:
 1) whether isomorphism is known
 2) if (1) then whether isomorphic
 3) if (2) then isomorphism, if not (2) then string describing why not isomorphic
*/

function is_known_isomorphic_abelian(L1, L2)
	assert Dimension(L1) eq Dimension(L2);
	ab1 := IsAbelian(L1);
	ab2 := IsAbelian(L2);
	if not ab1 and not ab2 then return false, _, _; end if;
	if ab1 and not ab2 then return true, false, "L1 is abelian, L2 is not."; end if;
	if ab2 and not ab1 then return true, false, "L2 is abelian, L1 is not."; end if;
	
	return true, true, map<L1 -> L2 | x :-> L2!Vector(x), x :-> L1!Vector(x)>;
end function;

//if L1[k1] and L2[k2] are "standard" cases
function reductive_isom_std_std(L1, data1, k1, L2, data2, k2)
	R1 := data1[k1]`R;
	sbas1 := data1[k1]`ChevBasData`BasisPos cat data1[k1]`ChevBasData`BasisNeg cat data1[k1]`ChevBasData`BasisCart;
	
	R2 := data2[k2]`R;
	if R1 cmpeq R2 then
		sbas2 := data2[k2]`ChevBasData`BasisPos cat data2[k2]`ChevBasData`BasisNeg cat data2[k2]`ChevBasData`BasisCart;
	else
		S2 := data2[k2]`ChevBasData`L;
		H2 := data2[k2]`ChevBasData`H;
		idQ := identify_liealg_not_directsum(S2, H2 : Select := "First", hintR := R1);
		if #idQ eq 0 then return false, _, _; end if;
		data2a := idQ[1];
		assert data2a`R eq R1;
		sbas2 := data2a`ChevBasData`BasisPos cat data2a`ChevBasData`BasisNeg cat data2a`ChevBasData`BasisCart;
		ChangeUniverse(~sbas2, S2); //just to be sure..
	end if;
	
	if GetAssertions() ge 1 then
		S1 := sub<L1 | sbas1>;
		M1 := Matrix([ Vector(S1!b) : b in sbas1 ]);
		S2 := sub<L2 | sbas2>;
		M2 := Matrix([ Vector(S2!b) : b in sbas2 ]);
		trmat := Matrix(M1)^-1*Matrix(M2);
		sphi := hom<S1 -> S2 | x :-> S2!Vector(Vector(S1!x)*trmat)>;
		ok := IsIsomorphism(sphi);
		vprintf AlgLieIsom, 1 : "[AlgLieIsom-RedSS]   IsIsomorphism(sphi): %o\n", ok;
		assert ok;
	end if;
	
	return true, sbas1, sbas2;
end function;

//if L1[k1] and L2[k2] are nonstd cases, i.e., both are simple components of a non-simple lie alg of simple alg. gp
// e.g. An char n+1, D4 char. 2, G2 char. 3
function reductive_isom_nonstd_nonstd(L1, dsd1, data1, k1, L2, dsd2, data2, k2)
	d1 := data1[k1]; d2 := data2[k2];
	R1 := d1`R; R2 := d2`R;
	
	S1 := dsd1[k1]; S2 := dsd2[k2];
	if R1 cmpne R2 then
		vprintf AlgLieIsom, 1: "[AlgLieIsom-RedNN]   R1 != R2.\n";
		return false, _, _;
	end if;
	
	//phi1: L1 (simple, smaller) -> LLL1 (split, with type R1)
	//phi1i its inverse
	//phi2: L2 (simple, smaller) -> LLL2 (split, with type R2 -- should be identical to R1)
	//phi2i its inverse
	//psi: LLL1 -> LLL2
	
	//phi1
	LLL1 := d1`extra`LLL;
	phi1 := d1`extra`maps`mp_L_to_LL;
	assert Domain(phi1) cmpeq S1;
	
	//phi2i
	LLL2 := d2`extra`LLL;
	phi2i := d2`extra`maps`mp_LL_to_L;
	assert Codomain(phi2i) cmpeq S2;
	
	//psi
	basLLL1 := d1`extra`ChevBasData`BasisPos cat d1`extra`ChevBasData`BasisNeg cat d1`extra`ChevBasData`BasisCart;
	assert Universe(basLLL1) eq LLL1;
	basLLL2 := d2`extra`ChevBasData`BasisPos cat d2`extra`ChevBasData`BasisNeg cat d2`extra`ChevBasData`BasisCart;
	assert Universe(basLLL2) eq LLL2;
	tr := Matrix(basLLL1)^-1*Matrix(basLLL2);
	psi := hom<LLL1 -> LLL2 | x :-> LLL2!Vector(Vector(LLL1!x)*tr)>;
	assert IsIsomorphism(psi);
	
	//Compose.
	sbas1 := [ L1 | b : b in Basis(S1) ];
	sbas2 := [ L2 | Vector(S2!phi2i(psi(phi1(S1!b)))) : b in Basis(S1) ];
	if GetAssertions() ge 1 then
		st1 := ChangeUniverse(sbas1, S1);
		st2 := ChangeUniverse(sbas2, S2);
		nw := Matrix(st2)*(Matrix(st1)^-1);
		tau := hom<S1 -> S2 | x :-> S2!(Vector(Vector(S1!x)*nw)) >;
		assert IsIsomorphism(tau);
	end if;
	
	return true, sbas1, sbas2;
end function;

//if L1[k1] is std, and L2[k2] is a simple part of..
function reductive_isom_std_nonstd(L1, dsd1, data1, k1, L2, dsd2, data2, k2)
	R1 := data1[k1]`R;
	sbas1 := data1[k1]`ChevBasData`BasisPos cat data1[k1]`ChevBasData`BasisNeg cat data1[k1]`ChevBasData`BasisCart;
	
	S2 := data2[k2]`L;
	H2 := data2[k2]`H;
	idQ := identify_liealg_not_directsum(S2, H2 : Select := "First", hintR := R1);
	if #idQ eq 0 then return false, _, _; end if;
	data2a := idQ[1];
	assert data2a`R eq R1;
	sbas2 := data2a`ChevBasData`BasisPos cat data2a`ChevBasData`BasisNeg cat data2a`ChevBasData`BasisCart;
	ChangeUniverse(~sbas2, S2); //just to be sure..

	if GetAssertions() ge 1 then
		S1 := sub<L1 | sbas1>;
		M1 := Matrix([ Vector(S1!b) : b in sbas1 ]);
		S2 := sub<L2 | sbas2>;
		M2 := Matrix([ Vector(S2!b) : b in sbas2 ]);
		trmat := Matrix(M1)^-1*Matrix(M2);
		sphi := hom<S1 -> S2 | x :-> S2!Vector(Vector(S1!x)*trmat)>;
		ok := IsIsomorphism(sphi);
		vprintf AlgLieIsom, 1 : "[AlgLieIsom-RedSN]   IsIsomorphism(sphi): %o\n", ok;
		assert ok;
	end if;

	return true, sbas1, sbas2;
end function;

//if L2[k2] is std, and L1[k1] is a simple part of..
function reductive_isom_nonstd_std(L1, dsd1, data1, k1, L2, dsd2, data2, k2)
	ok, sbas1, sbas2 := reductive_isom_std_nonstd(L2, dsd2, data2, k2, L1, dsd1, data1, k1);
	if ok then
		return true, sbas2, sbas1;
	else
		return false, _, _;
	end if;
end function;


function is_known_isomorphic_reductive(L1, L2 : H1 := false, H2 := false) //-> BoolElt, BoolElt, (Map or String)
	assert Dimension(L1) eq Dimension(L2);

	//Do reductive types on both.
	try
		if H1 cmpeq false then 	R1, str1, dsd1, data1 := ReductiveType(L1); 
		else 					R1, str1, dsd1, data1 := ReductiveType(L1, H1); 
		end if;
		vprintf AlgLieIsom, 1 : "\n[AlgLieIsom-Red] L1 is: %o\n", str1;
		if H2 cmpeq false then 	R2, str2, dsd2, data2 := ReductiveType(L2); 
		else 					R2, str2, dsd2, data2 := ReductiveType(L2, H2); 
		end if;
		vprintf AlgLieIsom, 1 : "[AlgLieIsom-Red] L2 is: %o\n", str2;
	catch err
		if GetVerbose("AlgLieIsom") ge 1 then
			"IsIsomorphic: ReductiveType failed. Error:"; IndentPush(); err; IndentPop();
		end if;
		return false, _, _;
	end try;
	
	//Good. Now all we have to do is map the bases onto each other.
	assert #dsd1 eq #data1;
	
	//Using data1, map Chevalley bases onto each other
	dims1 := [ Dimension(d) : d in dsd1 ];
	dims2 := [ Dimension(d) : d in dsd2 ];
	assert #dims1 eq #data1;
	assert #dims2 eq #dims1;
	bas1 := [L1|]; bas2 := [L2|];
	avail2 := [i : i in [1..#data1]];
	for k1 in [1..#data1] do
		R1 := data1[k1]`R;
		dim1 := dims1[k1];
		isstd1 := 2*NumPosRoots(R1)+Rank(R1) eq dim1;
		vprintf AlgLieIsom, 1 : "[AlgLieIsom-Red] Working on %o-th (%o-dim) component of L1...\n", k1, dim1;
		k2cands := [ k2 : k2 in avail2 | dims2[k2] eq dim1 ];
		
		for k2 in k2cands do
			R2 := data2[k2]`R;
			dim2 := dims2[k2];
			isstd2 := 2*NumPosRoots(R2)+Rank(R2) eq dim2;
			vprintf AlgLieIsom, 1 : "[AlgLieIsom-Red]   Comparing to %o-th component of L2...\n", k2;
			if isstd1 and isstd2 then
				ok, sbas1, sbas2 := reductive_isom_std_std(L1, data1, k1, L2, data2, k2);
			elif not isstd1 and not isstd2 then
				ok, sbas1, sbas2 := reductive_isom_nonstd_nonstd(L1, dsd1, data1, k1, L2, dsd2, data2, k2);
			elif isstd1 and not isstd2 then
				ok, sbas1, sbas2 := reductive_isom_std_nonstd(L1, dsd1, data1, k1, L2, dsd2, data2, k2);
			elif not isstd1 and isstd2 then
				ok, sbas1, sbas2 := reductive_isom_nonstd_std(L1, dsd1, data1, k1, L2, dsd2, data2, k2);
			else
				error "WHOA!";
			end if;

			if ok then thek2 := k2; break; end if;
		end for;
		
		if not ok then
			if #k2cands eq 0 then
				r := Sprintf("No match in L2 for %o-dim component of L1 (of type %o).", dim1, R1);
			elif #k2cands eq 1 then
				r := Sprintf("%o-dim component of L1 of type %o didn't match %o", dim1, R1, data2[k2cands[1]]`R);
			else
				r := Sprintf("%o-dim component of L1 of type %o didn't match against any of: \n%o", dim1, R1, [ data2[k2]`R : k2 in k2cands ]);
			end if;
			return true, false, r;
		end if;
		
		//Good, we found this!
		assert forall{x : x in sbas1 | L1!x in dsd1[k1] };
		assert forall{x : x in sbas2 | L2!x in dsd2[thek2] };
		bas1 cat:= sbas1;
		bas2 cat:= sbas2;
		Exclude(~avail2, thek2);
	end for;
		
	//Cool, that worked. Compose map, return.
	transmat := Matrix(bas1)^-1*Matrix(bas2);
	transmatinv := transmat^-1;
	phi := hom<L1 -> L2 | x :-> L2!Vector(Vector(L1!x)*transmat), y :-> L1!Vector(Vector(L2!y)*transmatinv) >;
	assert IsIsomorphism(phi);
	
	return true, true, phi;
end function;	

function is_known_isomorphic_nilpotent(L1, L2) //-> BoolElt, BoolElt, (Map or String)
	assert Dimension(L1) eq Dimension(L2);

	np1 := IsNilpotent(L1);
	np2 := IsNilpotent(L2);
	if not np1 and not np2 then return false, _, _; end if;
	if np1 and not np2 then return true, false, "L1 is nilpotent, L2 is not."; end if;
	if np2 and not np1 then return true, false, "L2 is nilpotent, L1 is not."; end if;

	//The database only has data up to dimension 6, or dimension 5 if char. is 2
	F := CoefficientRing(L1);
	if Dimension(L1) gt 6 then return false, _, _; end if;
	if (Characteristic(F) eq 2) and (Dimension(L1) gt 5) then return false, _, _; end if;
	
	try
		tp1, prm1, phi1 := IdDataNLAC(L1);
		vprintf AlgLieIsom, 2 : "\n[AlgLieIsom]    Nilpotent: tp1 = %o, prm1 = %o\n", tp1, prm1;
		tp2, prm2, phi2 := IdDataNLAC(L2);
		vprintf AlgLieIsom, 2 : "[AlgLieIsom]    Nilpotent: tp2 = %o, prm2 = %o\n", tp2, prm2;
	catch err
		if GetVerbose("AlgLieIsom") ge 1 then
			print "Problem with IdDataNLAC.\n";
			IndentPush();
			print err;
			IndentPop();
		end if;
		return false, _, _;
	end try;
	
	function strip_prms_from_tp(s)
		p := Position(s, "(");
		if p eq 0 then return s; else return s[[1..p-1]]; end if;
	end function;
	tp1 := strip_prms_from_tp(tp1);
	tp2 := strip_prms_from_tp(tp2);
	
	//If there are parameters, we can decide isomorphism, but we cannot mostly not construct a map :(
	if tp1 ne tp2 then
		return false, _, _;
	end if;

	assert #prm1 eq #prm2;
	if prm1 eq prm2 then
		constrmap := true;
		isisom := true;
	else 
		assert #prm1 eq 1; //property of Nilp. Lie alg database.
		isisom := IsSquare(prm1[1]/prm2[1]);
		constrmap := false;
	end if;
	
	if isisom and constrmap then
		phi1i := Inverse(phi1);
		phi2i := Inverse(phi2);
		phi := map<L1 -> L2 | x :-> phi2i(Vector(phi1(x))), x :-> phi1i(Vector(phi2(x)))>;
		return true, true, phi;
	else
		return true, isisom, false;
	end if;
end function;

function solvable_case_prms_must_be_identical(L1, id1, phi1, prm1, L2, id2, phi2, prm2);
	if prm1 ne prm2 then
		return true, false, Sprintf("Solvable database shows that L%o_%o(%o) is not isomorphic to L%o_%o(%o)", Dimension(L1), id1, prm1, Dimension(L2), id2, prm2);
	else
		phi1i := Inverse(phi1);
		phi2i := Inverse(phi2);
		phi := map<L1 -> L2 | x :-> phi2(Vector(phi1i(x))), x :-> phi1(Vector(phi2i(x)))>;
		return true, true, phi;
	end if;
end function;
function solvable_case_aslashb_square(L1, id1, phi1, prm1, L2, id2, phi2, prm2);
	assert #prm1 eq 1; assert #prm2 eq 1;
	sq := IsSquare(prm1[1]/prm2[1]);
	if sq then
		return true, sq, false;
	else
		return true, false, Sprintf("Solvable database shows that L%o_%o(%o) is not isomorphic to L%o_%o(%o)", Dimension(L1), id1, prm1, Dimension(L2), id2, prm2);
	end if;
end function;
function solvable_case_4_7(L1, id1, phi1, prm1, L2, id2, phi2, prm2);
	assert #prm1 eq 2; assert #prm2 eq 2;
	F := BaseRing(L1);
	alpha := PolynomialRing(F).1;
	if (prm1[1] eq 0) and (prm2[1] eq 0) then
		rts := { r[1] : r in Roots(prm1[2]-alpha^2*prm2[2]) };
	elif (prm1[2] eq 0) and (prm2[2] eq 0) then
		rts := { r[1] : r in Roots(prm1[1]-alpha^3*prm2[1]) };
	else
		rts := { r[1] : r in Roots(prm1[1]-alpha^3*prm2[1]) } meet { r[1] : r in Roots(prm1[2]-alpha^2*prm2[2]) };
	end if;
	if #rts eq 0 then
		return true, false, Sprintf("Solvable database shows that L%o_%o(%o) is not isomorphic to L%o_%o(%o)", Dimension(L1), id1, prm1, Dimension(L2), id2, prm2);
	else
		return true, true, false;
	end if;
end function;
function solvable_case_4_9(L1, id1, phi1, prm1, L2, id2, phi2, prm2);
	assert #prm1 eq 1; assert #prm2 eq 1;
	F := BaseRing(L1);
	alpha := PolynomialRing(F).1;
	a := prm1[1]; b := prm2[1];
	if Characteristic(F) ne 2 then
		rts := { r[1] : r in Roots((a+1/4) - alpha^2*(b+1/4)) };
	else
		rts := { r[1] : r in Roots(alpha^2 + alpha + a + b) };
	end if;
	if #rts eq 0 then
		return true, false, Sprintf("Solvable database shows that L%o_%o(%o) is not isomorphic to L%o_%o(%o)", Dimension(L1), id1, prm1, Dimension(L2), id2, prm2);
	else
		return true, true, false;
	end if;
end function;
function solvable_case_4_10(L1, id1, phi1, prm1, L2, id2, phi2, prm2);
	assert #prm1 eq 1; assert #prm2 eq 1;
	F := BaseRing(L1);
	assert Characteristic(F) eq 2;
	_<X,Y> := PolynomialRing(F,2);
	a := prm1[1]; b := prm2[1];
	if IsFinite(F) then 
		return true, true, false;
	else
		sqa := IsSquare(a); sqb := IsSquare(b);
		if sqa and sqb then
			//a & b both squares
			return true, true, false;
		elif sqa ne sqb then
			//a a square or b not, or vice versa
			return true, false, Sprintf("Solvable database shows that L%o_%o(%o) is not isomorphic to L%o_%o(%o) (%o is a square, %o isn't)", Dimension(L1), id1, prm1, Dimension(L2), id2, prm2, sqa select a else b, sqa select b else a);
		else
			error "solvable_case_4_10: Cannot decide isomorphism!";
		end if;
	end if;
end function;
function solvable_case_4_11(L1, id1, phi1, prm1, L2, id2, phi2, prm2);
	assert #prm1 eq 2; assert #prm2 eq 2;
	F := BaseRing(L1);
	assert Characteristic(F) eq 2;
	a,b := Explode(prm1); c,d := Explode(prm2);
	assert a ne 0; assert b ne 1; assert c ne 0; assert d ne 1;
	delta := (b+1)/(d+1);
	if IsSquare(a/c) and IsSquare((delta^2+(b+1)*delta+b)/c) then
		return true, true, false;
	else
		return true, false, Sprintf("Solvable database shows that L%o_%o(%o) is not isomorphic to L%o_%o(%o)", Dimension(L1), id1, prm1, Dimension(L2), id2, prm2);
	end if;
end function;


SolvableCaseFunctions := AssociativeArray();
SolvableCaseFunctions[<3,3>] := solvable_case_prms_must_be_identical;
SolvableCaseFunctions[<3,4>] := solvable_case_aslashb_square;
SolvableCaseFunctions[<4,3>] := solvable_case_prms_must_be_identical;
SolvableCaseFunctions[<4,6>] := solvable_case_prms_must_be_identical;
SolvableCaseFunctions[<4,7>] := solvable_case_4_7;
SolvableCaseFunctions[<4,9>] := solvable_case_4_9;
SolvableCaseFunctions[<4,10>] := solvable_case_4_10;
SolvableCaseFunctions[<4,11>] := solvable_case_4_11;
SolvableCaseFunctions[<4,13>] := solvable_case_prms_must_be_identical;
SolvableCaseFunctions[<4,14>] := solvable_case_aslashb_square;


function is_known_isomorphic_solvable(L1, L2) //-> BoolElt, BoolElt, (Map or String)
	assert Dimension(L1) eq Dimension(L2);

	solv1 := IsSolvable(L1);
	solv2 := IsSolvable(L2);
	if not solv1 and not solv2 then return false, _, _; end if;
	if solv1 and not solv2 then return true, false, "L1 is solvable, L2 is not."; end if;
	if solv2 and not solv1 then return true, false, "L2 is solvable, L1 is not."; end if;
	
	/* Only known up to dimension 4 */
	if Dimension(L1) gt 4 then return false, _, _; end if;
	
	/* Get ids */
	try
		tp1, prm1, phi1 := IdDataSLAC(L1);
		vprintf AlgLieIsom, 2 : "\n[AlgLieIsom]    Solvable: tp1 = %o, prm1 = %o\n", tp1, prm1;
		tp2, prm2, phi2 := IdDataSLAC(L2);
		vprintf AlgLieIsom, 2 : "[AlgLieIsom]    Solvable: tp2 = %o, prm2 = %o\n", tp2, prm2;
	catch err
		if GetVerbose("AlgLieIsom") ge 1 then
			print "Problem with IdDataSLAC.\n";
			IndentPush();
			print err;
			IndentPop();
		end if;
		return false, _, _;
	end try;
	
	/* Strip */
	exptp := function(tp)
		mtch, _, ss := Regexp("^L([0-9]+)_([0-9]+)\\(.*$", tp);
		assert mtch;
		assert #ss eq 2;
		return StringToInteger(ss[1]), StringToInteger(ss[2]);
	end function;
	dim1, id1 := exptp(tp1);
	dim2, id2 := exptp(tp2);
	assert (dim1 eq dim2)  and (dim1 eq Dimension(L1));
	assert (id1 ne id2) or (#prm1 eq #prm2);
	
	/* Evaluate data. */
	if id1 ne id2 then 
		return true, false, Sprintf("L1 has isomorphism class %o in the database, L2 has class %o", id1, id2);
	elif prm1 eq prm2 then
		phi1i := Inverse(phi1);
		phi2i := Inverse(phi2);
		phi := map<L1 -> L2 | x :-> phi2(Vector(phi1i(x))), x :-> phi1(Vector(phi2i(x)))>;
		return true, true, phi;
	else
		/* A long list of cases, because the relation between parameters and isomorphism depends
		   on the id found... */
		ok, f := IsDefined(SolvableCaseFunctions, <Dimension(L1), id1>);
		if not ok then
			vprintf AlgLieIsom, 1 : "[AlgLieIsom] SolvableCaseFunction[<%o, %o>] is not defined!\n", Dimension(L1), id1;
			return false, _, _;
		end if;
		ki, ii, phi := f(L1, id1, phi1, prm1, L2, id2, phi2, prm2);
		return ki, ii, phi;
	end if;
end function;


intrinsic IsKnownIsomorphic(L1::AlgLie, L2::AlgLie : H1 := false, H2 := false) -> BoolElt, .
{ Check whether the Lie algebras L1 and L2 are isomorphic.
Returns whether known as 1st value; 
if so, then true/false as 2nd value; 
if true then map as 3rd value (or false if it couldn't be computed), if false then string (reason) as 3rd value.

Pass split Cartan/toral subalgebras as optional parameters.
Currently only works for reductive Lie algebras and small-dimensional nilpotent and solvable Lie algebras.
}
	require CoefficientRing(L1) cmpeq CoefficientRing(L2) : "Coefficient rings must be identical.";

	//Stupid.
	if Dimension(L1) ne Dimension(L2) then
		return true, false, "Different dimensions";
	end if;
	
	//Try abelian
	vprintf AlgLieIsom, 1 : "[AlgLieIsom] Abelian... ";
	bknown, isi, r := is_known_isomorphic_abelian(L1, L2);
	vprintf AlgLieIsom, 1 : "known = %o\n", bknown;
	if bknown then return bknown, isi, r; end if;

	//Try nilpotent
	vprintf AlgLieIsom, 1 : "[AlgLieIsom] Nilpotent... ";
	bknown, isi, r := is_known_isomorphic_nilpotent(L1, L2);
	vprintf AlgLieIsom, 1 : "known = %o\n", bknown;
	if bknown then return bknown, isi, r; end if;
	
	//Try solvable
	vprintf AlgLieIsom, 1 : "[AlgLieIsom] Solvable... ";
	bknown, isi, r := is_known_isomorphic_solvable(L1, L2);
	vprintf AlgLieIsom, 1 : "known = %o\n", bknown;
	if bknown then return bknown, isi, r; end if;
	
	//Try reductive
	vprintf AlgLieIsom, 1 : "[AlgLieIsom] Reductive...";
	bknown, isi, r := is_known_isomorphic_reductive(L1, L2 : H1 := H1, H2 := H2);
	vprintf AlgLieIsom, 1 : "[AlgLieIsom] known = %o\n", bknown;
	if bknown then return bknown, isi, r; end if;
	
	//Failure.
	return false, _, _;
end intrinsic;

intrinsic IsIsomorphic(L1::AlgLie, L2::AlgLie : H1 := false, H2 := false) -> BoolElt, .
{ Check whether the Lie algebras L1 and L2 are isomorphic.
Returns true/false as 1st value; if true then map as 2nd value, if false then string (reason) as 2nd value.

Pass split Cartan/toral subalgebras as optional parameters.
Currently only works for reductive Lie algebras and small-dimensional nilpotent and solvable Lie algebras.
}
	bknown, bisom, r := IsKnownIsomorphic(L1, L2 : H1 := H1, H2 := H2);
	error if not bknown, "Cannot decide isomorphism between these two Lie algebras.";
	
	assert assigned bisom;
	assert assigned r;
	if ISA(Type(r), Map) then assert IsIsomorphism(r); end if;

	return bisom, r; 
end intrinsic;

intrinsic Isomorphism(L1::AlgLie, L2::AlgLie : H1 := false, H2 := false) -> BoolElt, .
{ Find an isomorphism between the L1 and L2.

Pass split Cartan/toral subalgebras as optional parameters.
Currently only works for reductive Lie algebras and small-dimensional nilpotent and solvable Lie algebras.
}
	b, phi := IsIsomorphic(L1, L2 : H1 := H1, H2 := H2);
	error if not b, "Isomorphism: Lie algebras are not isomorphic.";
	error if not ISA(Type(phi), Map), "Isomorphism: Lie algebras are isomorphic, but can't produce a map.";
	return phi;

end intrinsic;





