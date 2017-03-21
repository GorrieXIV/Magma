freeze;

get_standard_gens_ON := function(S)
    P := RandomProcess(S);
    repeat
	b := Random(P);
	ord := Order(b);
    until ord in {12, 20, 28};
    b := b ^ (ord div 4);
    a := b ^ 2;
    repeat
	b := b ^ Random(P);
	ab := a*b;
    until Order(ab) eq 11;
    return a,b;
end function;

ONIdentify := function(group:max:=true,Print:=0)
    A := PermutationGroup(ATLASGroup("ONd2"));
    G := A;
    c := A.1; d := A.2;
    cdd := c*d^2;
    a := (d^2)^(cdd^2); b := d;
    simp := sub<A | a, b>;
    simp`Order := 460815505920;
    if Print gt 1 then print "Calling FPGroupStrong"; end if;
    F, phi := FPGroupStrong(simp);
    soc := Socle(group);
    aut := Index(group, soc);
    aut_str := aut eq 1 select "" else ":2";
    if Print gt 1 then printf "group is O'N%o\n", aut_str; end if;
    ga, gb:= get_standard_gens_ON(soc);
    soc := sub< soc | ga,gb >;
    soc`Order := 460815505920;
    newgens := [ group | ga, gb];
    newgens_grp := sub<group|newgens>;
    newgens_grp`Order := 460815505920;
    for g in Generators(group) do
	if not g in newgens_grp then
	    Append(~newgens,g);
	    newgens_grp := sub<group|newgens>;
	    newgens_grp`Order := 2*460815505920;
	end if;
    end for;
    group := newgens_grp;
    ims := [ A | a, b];
    homom :=  hom< soc -> simp | ims >;
    for  i in [Ngens(soc)+1..Ngens(group)] do
	g := group.i;
	CG := A; ce := Id(A);
	for j in [1..2] do
	    x := homom(soc.j^g);
	    CGx := Centraliser(CG, x);
	    isc, h := IsConjugate(CG, simp.j^ce, x: RightSubgroup := CGx);
	    if not isc then error "Conjugation error in Aut(O'N)"; end if;
	    CG := CGx;
	    ce := ce*h;
	end for;
	Append(~ims,ce);
    end for;
    newgens := ims;
    ims_grp := sub<A|ims>;
    ims_grp`Order := #group;
    for g in Generators(A) do
	if not g in ims_grp then
	    Append(~ims,g);
	    ims_grp := sub<A|ims>;
	    ims_grp`Order := 2*460815505920;
	end if;
    end for;
    A := ims_grp;
    homom :=  hom< group -> A | newgens >;

    maximals:= [];
    if not max then 
	return homom, A, maximals, F, phi;
    end if;

    /* words for maximal subgroup generators found in Birmingham Atlas */

    ab := a*b; abb := ab*b; ababb := ab*abb;

    /* J1 */
    M := sub<simp | a^(abb^7), ((ab^2*ababb^2)^4)^(ababb^6) >;
    M`Order := 175560;
    Append(~maximals, M);

    /* 4.L(3,4):2 */
    M := sub<simp | (ababb^10, b)^14, ababb >;
    M`Order := 161280;
    Append(~maximals, M);

    /* (3^2:4 ? A6).2 */
    f := function(S)
        w1 := S.1;
	w2 := S.2;
	w3 := w1 * w2;
	w4 := w3 * w2;
	w5 := w3 * w4;
	w6 := w3 * w5;
	w7 := w6 * w3;
	w8 := w7 * w4;
	w9 := w7 * w8;
	w2 := w9 * w9;
	w1 := w9 * w9;
	w7 := w6 * w4;
	w8 := w7^19;
	w9 := w8^-1;
	w10 := w9 * w1;
	w1 := w10 * w8;
	w7 := w4 * w6;
	w8 := w7^17;
	w6 := w5 * w4;
	w7 := w6 * w3;
	w9 := w7^8;
	w7 := w8 * w9;
	w6 := w7^-1;
	w8 := w6 * w2;
	w2 := w8 * w7;
	return [w1,w2];
    end function;
    M := sub<simp | f(simp) >;
    M`Order := 25920;
    Append(~maximals, M);

    /* 3^4:2^(1+4).D_10 */
    f := function(S)
      w1 := S.1;
      w2 := S.2;
      w3 := w1 * w2;
      w4 := w3 * w2;
      w5 := w3 * w4;
      w6 := w3 * w5;
      w7 := w6 * w3;
      w8 := w7 * w4;
      w9 := w7 * w8;
      w2 := w9 * w9;
      w1 := w9 * w9;
      w7 := w6 * w4;
      w8 := w7^19;
      w9 := w8^-1;
      w10 := w9 * w1;
      w1 := w10 * w8;
      w8 := w4 * w6;
      w6 := w5 * w4;
      w7 := w6 * w3;
      w9 := w7^12;
      w7 := w8 * w9;
      w6 := w7^-1;
      w8 := w6 * w2;
      w2 := w8 * w7;
      return [w1,w2];
    end function;
    M := sub<simp | f(simp) >;
    M`Order := 25920;
    Append(~maximals, M);

    /* 4^3.L(3,2) */
    M := sub<simp | a^(ab^4), ((ab^2*ababb^2)^4)^(abb^4) >;
    M`Order := 10752;
    Append(~maximals, M);

    if aut eq 1 then
	/* L(3,7):2 twice */
	M := sub<simp | a^b, b^(abb^2) >; 
	M`Order := 3753792;
	Append(~maximals, M);
	Append(~maximals, M^c);

	/* L(2, 31) twice */
	M := sub< simp | a^(ab^3), (ababb*b)^4>;
	M`Order := 14880;
	Append(~maximals, M);
	Append(~maximals, M^c);

	/* M11 twice */
	f := function(S)
	  w1 := S.1;
	  w2 := S.2;
	  w3 := w1 * w2;
	  w4 := w3 * w2;
	  w5 := w3 * w4;
	  w6 := w3 * w5;
	  w7 := w6 * w3;
	  w8 := w7 * w4;
	  w9 := w7 * w8;
	  w2 := w9 * w9;
	  w7 := w6 * w4;
	  w8 := w7^4;
	  w9 := w8^-1;
	  w10 := w9 * w1;
	  w1 := w10 * w8;
	  w7 := w4 * w6;
	  w8 := w7^19;
	  w6 := w5 * w4;
	  w7 := w6 * w3;
	  w9 := w7^2;
	  w7 := w8 * w9;
	  w6 := w7^-1;
	  w8 := w6 * w2;
	  w2 := w8 * w7;
	  return [w1,w2];
	end function;
	M := sub<simp | f(simp) >;
	M`Order := 7920;
	Append(~maximals, M);
	Append(~maximals, M^c);

	/* A7 twice */
	f := function(S)
	  w1 := S.1;
	  w2 := S.2;
	  w3 := w1 * w2;
	  w4 := w3 * w2;
	  w5 := w3 * w4;
	  w6 := w3 * w5;
	  w9 := w2 * w5;
	  w2 := w9 * w9;
	  w8 := w6 * w4;
	  w9 := w8^-1;
	  w10 := w9 * w1;
	  w1 := w10 * w8;
	  w7 := w4 * w6;
	  w8 := w7^10;
	  w6 := w5 * w4;
	  w7 := w6 * w3;
	  w9 := w7^3;
	  w7 := w8 * w9;
	  w6 := w7^-1;
	  w8 := w6 * w2;
	  w2 := w8 * w7;
	  return [w1,w2];
	end function;
	M := sub<simp | f(simp) >;
	M`Order := 2520;
	Append(~maximals, M);
	Append(~maximals, M^c);

    else

	assert aut eq 2;

	/* 7^(1+2):(3 ? D_16) meet simp */
	f := function(S)
	  w1 := S.1;
	  w2 := S.2;
	  w3 := w1 * w2;
	  w4 := w3 * w2;
	  w5 := w4 * w2;
	  w6 := w5 * w5;
	  w4 := w3^3;
	  w3 := w6 * w4;
	  w1 := w3^5;
	  w4 := w2 * w2;
	  w2 := w3 * w6;
	  w3 := w2 * w5;
	  w2 := w3^-1;
	  w5 := w2 * w4;
	  w2 := w5 * w3;
	  return [w1,w2];
	end function;
	M := sub<G | f(G) >;
	M`Order := 16464;
	M := IntersectionWithNormalSubgroup(M, simp: Check := false);
	Append(~maximals, M);

	/* 31:30 meet simp */
	f := function(S)
	  w1 := S.1;
	  w2 := S.2;
	  w3 := w1 * w2;
	  w4 := w3 * w2;
	  w5 := w4 * w2;
	  w6 := w5 * w3;
	  w7 := w6 * w3;
	  w6 := w5 * w7;
	  w5 := w6 * w3;
	  w6 := w4 * w3;
	  w4 := w6 * w7;
	  w3 := w5^4;
	  w2 := w4^-1;
	  w5 := w2 * w3;
	  w2 := w5 * w4;
	  return [w1,w2];
	end function;
	M := sub<G | f(G) >;
	M`Order := 930;
	M := IntersectionWithNormalSubgroup(M, simp: Check := false);
	Append(~maximals, M);

	/* A6:2 meet simp */
	f := function(S)
	  w1 := S.1;
	  w2 := S.2;
	  w3 := w1 * w2;
	  w4 := w3 * w2;
	  w5 := w4 * w2;
	  w6 := w4 * w3;
	  w4 := w6 * w6;
	  w6 := w5 * w5;
	  w5 := w3^3;
	  w3 := w6 * w5;
	  w5 := w3^10;
	  w3 := w4 * w2;
	  w2 := w3^-1;
	  w4 := w2 * w5;
	  w2 := w4 * w3;
	  return [w1,w2];
	end function;
	M := sub<G | f(G) >;
	M`Order := 720;
	M := IntersectionWithNormalSubgroup(M, simp: Check := true);
	Append(~maximals, M);

	/* L(2,7).2 meet simp */
	f := function(S)
	  w1 := S.1;
	  w2 := S.2;
	  w3 := w1 * w2;
	  w4 := w3 * w2;
	  w5 := w4 * w2;
	  w6 := w5 * w3;
	  w7 := w5 * w6;
	  w8 := w3 * w3;
	  w3 := w7 * w8;
	  w5 := w3^10;
	  w3 := w2 * w2;
	  w2 := w3 * w6;
	  w3 := w2 * w4;
	  w4 := w3 * w6;
	  w2 := w4^-1;
	  w3 := w2 * w5;
	  w2 := w3 * w4;
	  return [w1,w2];
	end function;
	M := sub<G | f(G) >;
	M`Order := 336;
	M := IntersectionWithNormalSubgroup(M, simp: Check := false);
	Append(~maximals, M);

    end if;

    return homom, A, maximals, F, phi;

end function;
